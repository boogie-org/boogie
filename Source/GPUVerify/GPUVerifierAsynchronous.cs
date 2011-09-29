using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    class GPUVerifierAsynchronous : GPUVerifier
    {

        private Microsoft.Boogie.Type ThreadIdType;
        private String ThreadIdParameterName;

        private HashSet<int> BarrierIds = new HashSet<int>();



        public GPUVerifierAsynchronous(Program program)
            : base(program)
        {

            ReservedNames.Add("base");
            ReservedNames.Add("offset_x");
            ReservedNames.Add("offset_y");
            ReservedNames.Add("offset_z");
            ReservedNames.Add("is_write");
            ReservedNames.Add("AT_BARRIER");
            ReservedNames.Add("REACHED_NEXT_BARRIER");

            CheckWellFormedness();
        }

        override internal int Check()
        {
            TypeSynonymDecl ThreadIdDecl = CheckExactlyOneThreadIdType(Program);
            ThreadIdType = new TypeSynonymAnnotation(ThreadIdDecl.tok, ThreadIdDecl, new TypeSeq());
            
            return base.Check();
        }


        protected override void CheckKernelImplementation()
        {
            base.CheckKernelImplementation();

            // Clear the local variables
            KernelImplementation.LocVars = new VariableSeq();

            foreach (LocalVariable LV in ThreadLocalVariables)
            {
                // Make each local variable a global map from threadid to the usual type
                GlobalVariable GV = new GlobalVariable(LV.tok, LV.TypedIdent);
                TypeSeq IndexType = new TypeSeq();
                IndexType.Add(ThreadIdType);
                GV.TypedIdent.Type = new MapType(GV.TypedIdent.Type.tok, new TypeVariableSeq(), IndexType, LV.TypedIdent.Type);
                Program.TopLevelDeclarations.Add(GV);
                KernelProcedure.Modifies.Add(new IdentifierExpr(GV.tok, GV));
            }

            foreach (LocalVariable LV in TileStaticVariables)
            {
                // Promote each tile-static variable to global
                GlobalVariable GV = new GlobalVariable(LV.tok, LV.TypedIdent);
                GV.TypedIdent.Type = LV.TypedIdent.Type;
                Program.TopLevelDeclarations.Add(GV);
                KernelProcedure.Modifies.Add(new IdentifierExpr(GV.tok, GV));
            }

            LocalVariableAccessReplacer replacer = new LocalVariableAccessReplacer(this);

            replacer.VisitImplementation(KernelImplementation);

            // Check that each barrier has a positive integer id
            // Check that these ids are all distinct
            foreach (Block B in KernelImplementation.Blocks)
            {
                foreach (Cmd C in B.Cmds)
                {
                    if (IsBarrier(C))
                    {
                        CallCmd Barrier = C as CallCmd;

                        int BarrierId = QKeyValue.FindIntAttribute(Barrier.Attributes, "barrier_id", -1);
                        if (BarrierId < 1)
                        {
                            Error(Barrier, "Barrier must have positive integer attribute \"barrier_id\"");
                        }
                        else if (BarrierIds.Contains(BarrierId))
                        {
                            Error(Barrier, "Each barrier call must have a unique integer attribute \"barrier_id\" - duplicate id {0} detected", BarrierId);
                        }
                        else
                        {
                            BarrierIds.Add(BarrierId);
                        }
                    }
                }

            }


        }

        protected override void CheckKernelParameters()
        {
            if (KernelProcedure.InParams.Length != 1)
            {
                Error(KernelProcedure, "Kernel procedure must take exactly one argument, of type {0}", ThreadIdType.ToString());
            }
            else
            {
                if (!KernelProcedure.InParams[0].TypedIdent.Type.Equals(ThreadIdType))
                {
                    Error(KernelProcedure, "Argument to kernel procedure has wrong type - {0} instead of {1}", KernelProcedure.InParams[0].TypedIdent.Type.ToString(), ThreadIdType.ToString());
                }

                ThreadIdParameterName = KernelProcedure.InParams[0].TypedIdent.Name;

            }

            if (KernelProcedure.OutParams.Length != 0)
            {
                Error(KernelProcedure, "Kernel procedure must not return any results");
            }
        }



        private TypeSynonymDecl CheckExactlyOneThreadIdType(Program program)
        {
            return CheckSingleInstanceOfAttributedEntity<TypeSynonymDecl>(program, "thread_id");
        }

        private T CheckSingleInstanceOfAttributedEntity<T>(Program program, string attribute) where T : Declaration
        {
            T attributedEntity = null;
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                if (!QKeyValue.FindBoolAttribute(decl.Attributes, attribute))
                {
                    continue;
                }

                if (decl is T)
                {
                    if (attributedEntity == null)
                    {
                        attributedEntity = decl as T;
                    }
                    else
                    {
                        Error(decl, "\"{0}\" attribute specified for {1}, but it has already been specified for procedure {2}", attribute, decl.ToString(), attributedEntity.ToString());
                    }
                }
                else
                {
                    Error(decl, "\"{0}\" attribute applied to wrong sort of declaration {1}", attribute, decl.ToString());
                }
            }

            if (attributedEntity == null)
            {
                Error(program, "\"{0}\" attribute has not been specified for any procedure.  You must mark exactly one procedure with this attribute", attribute);
            }

            return attributedEntity;
        }


        internal void AddBarrierId(int BarrierId)
        {
            BarrierIds.Add(BarrierId);
        }

        internal int MaxBarrierId()
        {
            int result = -1;
            foreach (int i in BarrierIds)
            {
                if (i > result)
                {
                    result = i;
                }
            }
            return result;
        }

        public void AddInitialAndFinalBarriers()
        {
            // Add barrier to start of first block, if it doesn't already start with a barrier
            if (!IsBarrier(KernelImplementation.Blocks[0].Cmds[0]))
            {
                CmdSeq NewCmds = new CmdSeq();
                NewCmds.Add(MakeBarrierCmd(0));
                foreach (Cmd C in KernelImplementation.Blocks[0].Cmds)
                {
                    NewCmds.Add(C);
                }
                KernelImplementation.Blocks[0].Cmds = NewCmds;
            }

            CmdSeq FinalBarrierCmdSeq = new CmdSeq();

            int FinalBarrierId = MaxBarrierId() + 1;

            FinalBarrierCmdSeq.Add(MakeBarrierCmd(FinalBarrierId));

            string FinalBarrierLabel = "barrier_label" + FinalBarrierId;

            Block FinalBarrierBlock = new Block(Token.NoToken, FinalBarrierLabel, FinalBarrierCmdSeq, new ReturnCmd(Token.NoToken));

            foreach (Block B in KernelImplementation.Blocks)
            {
                if (B.TransferCmd is ReturnCmd)
                {
                    BlockSeq BlockSeq = new BlockSeq();
                    BlockSeq.Add(FinalBarrierBlock);
                    StringSeq StringSeq = new StringSeq();
                    StringSeq.Add(FinalBarrierLabel);
                    B.TransferCmd = new GotoCmd(Token.NoToken, StringSeq, BlockSeq);
                }
            }

            KernelImplementation.Blocks.Add(FinalBarrierBlock);

        }

        private Cmd MakeBarrierCmd(int BarrierId)
        {
            Debug.Assert(!BarrierIds.Contains(BarrierId));
            AddBarrierId(BarrierId);
            CallCmd Result = new CallCmd(Token.NoToken, BarrierProcedure.Name, new ExprSeq(), new IdentifierExprSeq());
            Result.Attributes = new QKeyValue(Token.NoToken, "barrier_id", new List<object>(new object[] { Expr.Literal(BarrierId) }), null);
            return Result;
        }


        private static Implementation CloneImplementation(Implementation Impl, string NewName)
        {
            Implementation Result = new Implementation(Impl.tok, NewName, Impl.TypeParameters, Impl.InParams, Impl.OutParams, Impl.LocVars, new List<Block>());

            Dictionary<Block, Block> OldToNew = new Dictionary<Block, Block>();

            foreach (Block B in Impl.Blocks)
            {
                Block NewB = CloneBlock(B);

                OldToNew.Add(B, NewB);

                Result.Blocks.Add(NewB);

            }

            foreach (Block NewB in Result.Blocks)
            {
                if (NewB.TransferCmd is GotoCmd)
                {
                    GotoCmd NewGotoCmd = NewB.TransferCmd as GotoCmd;

                    for (int i = 0; i < NewGotoCmd.labelTargets.Length; i++)
                    {
                        Block NewSuccessor;
                        bool found = OldToNew.TryGetValue(NewGotoCmd.labelTargets[i], out NewSuccessor);
                        Debug.Assert(found);

                        NewGotoCmd.labelTargets[i] = NewSuccessor;
                    }

                }
            }

            return Result;
        }


        private static Block CloneBlock(Block B)
        {
            Block NewB = new Block(B.tok, B.Label, new CmdSeq(), null);

            foreach (Cmd C in B.Cmds)
            {
                NewB.Cmds.Add(C); // The contents of each command is *not* cloned
            }

            if (B.TransferCmd is ReturnCmd)
            {
                NewB.TransferCmd = new ReturnCmd((B.TransferCmd as ReturnCmd).tok);
            }
            else
            {
                GotoCmd GotoCmd = B.TransferCmd as GotoCmd;
                NewB.TransferCmd = new GotoCmd(GotoCmd.tok, new StringSeq(), new BlockSeq());
                GotoCmd NewGotoCmd = NewB.TransferCmd as GotoCmd;
                for (int i = 0; i < GotoCmd.labelNames.Length; i++)
                {
                    NewGotoCmd.labelNames.Add(GotoCmd.labelNames[i]);
                    NewGotoCmd.labelTargets.Add(GotoCmd.labelTargets[i]);
                }
            }
            return NewB;
        }


        private static void AppendDuplicateBlockToStartOfImplementation(Implementation Impl, int i)
        {
            Block NewBlock = CloneBlock(Impl.Blocks[i]);
            NewBlock.Label = "entry_barrier";

            List<Block> NewBlocks = new List<Block>();

            NewBlocks.Add(NewBlock);

            foreach (Block B in Impl.Blocks)
            {
                NewBlocks.Add(B);
            }

            Impl.Blocks = NewBlocks;

        }

        private Implementation ConstructBarrierToNextBarriersImplementation(Block B, String NewProcedureName)
        {
            Implementation NewImplementation = CloneImplementation(KernelImplementation, NewProcedureName);

            AppendDuplicateBlockToStartOfImplementation(NewImplementation, KernelImplementation.Blocks.IndexOf(B));

            // Iterate through all blocks except first, immediately following barrier calls with "return"

            for (int i = 1; i < NewImplementation.Blocks.Count; i++)
            {
                if (IsBarrier(NewImplementation.Blocks[i]))
                {
                    // This is a barrier so we don't want control to get any further.
                    // To ensure this, we simply remove any commands following the barrier,
                    // and make the transfer command into a "return".
                    CmdSeq NewCmdSeq = new CmdSeq();
                    NewCmdSeq.Add(NewImplementation.Blocks[i].Cmds[0]);
                    NewImplementation.Blocks[i].Cmds = NewCmdSeq;
                    NewImplementation.Blocks[i].TransferCmd = new ReturnCmd(Token.NoToken);
                }
            }

            NewImplementation.PruneUnreachableBlocks();
            return NewImplementation;
        }

        private void SanityCheckKernel()
        {
            foreach (Block C in KernelImplementation.Blocks)
            {
                if (C.TransferCmd is GotoCmd)
                {
                    foreach (Block D in (C.TransferCmd as GotoCmd).labelTargets)
                    {
                        Debug.Assert(KernelImplementation.Blocks.Contains(D));
                    }
                }
            }
        }


        private void GenerateSpanA(Block A)
        {
            SanityCheckKernel();
            Debug.Assert(IsBarrier(A));

            String NewProcedureName = MakeSpanAProcedureName(A);
            Procedure NewProcedure = CloneKernelProcedure(NewProcedureName);

            AddTrackingVariablesToModifiesSet(A.tok, NewProcedure.Modifies);

            AddInlineAttribute(NewProcedure);

            Implementation NewImplementation = ConstructBarrierToNextBarriersImplementation(A, NewProcedureName);

            if (!CommandLineOptions.OnlyDivergence)
            {
                InstrumentWithRaceDetection(NewImplementation);
            }

            AddBarrierTracking(NewImplementation);

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);

        }

        private string MakeSpanAProcedureName(Block A)
        {
            return "Span_" + GetBarrierId(A);
        }

        private string MakeSpanABProcedureName(Block A, Block B)
        {
            return "Span_" + GetBarrierId(A) + "_" + GetBarrierId(B);
        }

        private static CtorType MakeArrayBaseType(IToken tok)
        {
            return new CtorType(tok, new TypeCtorDecl(tok, "ArrayBase", 0), new TypeSeq());
        }

        private IdentifierExpr MakeBaseVariable(IToken tok)
        {
            TypeSeq typeSeq = new TypeSeq();
            typeSeq.Add(ThreadIdType);
            return new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, "base", new MapType(tok, new TypeVariableSeq(), typeSeq, MakeArrayBaseType(tok)))));
        }

        private IdentifierExpr MakeOffsetVariable(IToken tok, string Dimension)
        {
            TypeSeq typeSeq = new TypeSeq();
            typeSeq.Add(ThreadIdType);
            return new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, "offset_" + Dimension, new MapType(tok, new TypeVariableSeq(), typeSeq, Microsoft.Boogie.Type.Int))));
        }

        private IdentifierExpr MakeOffsetXVariable(IToken tok)
        {
            return MakeOffsetVariable(tok, "x");
        }

        private IdentifierExpr MakeOffsetYVariable(IToken tok)
        {
            return MakeOffsetVariable(tok, "y");
        }

        private IdentifierExpr MakeOffsetZVariable(IToken tok)
        {
            return MakeOffsetVariable(tok, "z");
        }

        private IdentifierExpr MakeIsWriteVariable(IToken tok)
        {
            TypeSeq typeSeq = new TypeSeq();
            typeSeq.Add(ThreadIdType);
            return new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, "is_write", new MapType(tok, new TypeVariableSeq(), typeSeq, Microsoft.Boogie.Type.Bool))));
        }

        private void InstrumentWithRaceDetection(Implementation Impl)
        {
            foreach (Block B in Impl.Blocks)
            {
                CmdSeq NewCmds = new CmdSeq();

                foreach (Cmd C in B.Cmds)
                {
                    ReadCollector rc = new ReadCollector(GlobalVariables, TileStaticVariables);
                    rc.Visit(C);
                    WriteCollector wc = new WriteCollector(GlobalVariables, TileStaticVariables);
                    wc.Visit(C);

                    if (wc.FoundWrite())
                    {
                        CallCmd LogWriteCmd;
                        if (CommandLineOptions.NewRaceDetectionMethod)
                        {
                            LogWriteCmd = new CallCmd(C.tok, "LOG_WRITE_" + wc.GetAccess().v.Name, ConstructLogAccessParametersNewMethod(C.tok, wc.GetAccess()), new IdentifierExprSeq());
                        }
                        else
                        {
                            LogWriteCmd = new CallCmd(C.tok, "LOG_WRITE", ConstructLogAccessParameters(C.tok, wc.GetAccess()), new IdentifierExprSeq());
                        }
                        NewCmds.Add(LogWriteCmd);
                    }

                    foreach (AccessRecord read in rc.accesses)
                    {
                        CallCmd LogReadCmd;
                        if (CommandLineOptions.NewRaceDetectionMethod)
                        {
                            LogReadCmd = new CallCmd(C.tok, "LOG_READ_" + read.v.Name, ConstructLogAccessParametersNewMethod(C.tok, read), new IdentifierExprSeq());
                        }
                        else
                        {
                            LogReadCmd = new CallCmd(C.tok, "LOG_READ", ConstructLogAccessParameters(C.tok, read), new IdentifierExprSeq());
                        }
                        NewCmds.Add(LogReadCmd);
                    }

                    NewCmds.Add(C);
                }
                B.Cmds = NewCmds;
            }
        }

        private ExprSeq ConstructLogAccessParametersNewMethod(IToken tok, AccessRecord access)
        {
            ExprSeq InParams = new ExprSeq();
            InParams.Add(access.IndexZ);
            InParams.Add(access.IndexY);
            InParams.Add(access.IndexX);
            InParams.Add(MakeThreadIdExpr(tok));
            return InParams;
        }

        private ExprSeq ConstructLogAccessParameters(IToken tok, AccessRecord access)
        {
            ExprSeq InParams = new ExprSeq();
            InParams.Add(new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, access.v.Name + "_base", Microsoft.Boogie.Type.Int))));
            InParams.Add(access.IndexZ);
            InParams.Add(access.IndexY);
            InParams.Add(access.IndexX);
            InParams.Add(MakeThreadIdExpr(tok));
            return InParams;
        }

        private void GenerateBarrierAToBarrierBProcedure(Block A, Block B)
        {
            Debug.Assert(IsBarrier(A));
            Debug.Assert(IsBarrier(B));

            if (!BarrierReachesBarrier(A, B))
            {
                return;
            }

            String NewProcedureName = MakeSpanABProcedureName(A, B);
            Procedure NewProcedure = CloneKernelProcedure(NewProcedureName);
            Implementation NewImplementation = ConstructBarrierToNextBarriersImplementation(A, NewProcedureName);

            AddInlineAttribute(NewProcedure);

            NewProcedure.Modifies.Add(MakeReachedNextBarrierVariable(B.tok));

            Block NewA = NewImplementation.Blocks[0];
            Block NewB = null;
            for (int i = 1; i < NewImplementation.Blocks.Count; i++)
            {
                if (IsBarrier(NewImplementation.Blocks[i]) && GetBarrierId(B) == GetBarrierId(NewImplementation.Blocks[i]))
                {
                    NewB = NewImplementation.Blocks[i];
                    break;
                }
            }
            Debug.Assert(NewB != null);

            NewImplementation.ComputePredecessorsForBlocks();

            HashSet<Block> NodesToKeep = BlocksReaching(NewB);

            Debug.Assert(NodesToKeep.Count > 1);

            foreach (Block D in NewImplementation.Blocks)
            {
                if (D.TransferCmd is GotoCmd)
                {
                    GotoCmd GotoCmd = D.TransferCmd as GotoCmd;
                    GotoCmd NewGotoCmd = new GotoCmd(GotoCmd.tok, new StringSeq(), new BlockSeq());
                    for (int i = 0; i < GotoCmd.labelNames.Length; i++)
                    {
                        if (NodesToKeep.Contains(GotoCmd.labelTargets[i]))
                        {
                            NewGotoCmd.labelNames.Add(GotoCmd.labelNames[i]);
                            NewGotoCmd.labelTargets.Add(GotoCmd.labelTargets[i]);
                        }
                    }
                    D.TransferCmd = NewGotoCmd;
                }
            }

            NewImplementation.PruneUnreachableBlocks();

            AddReachedNextBarrierTracking(NewImplementation, A, B);

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);

        }

        private bool BarrierReachesBarrier(Block A, Block B)
        {
            Debug.Assert(IsBarrier(A));
            Debug.Assert(IsBarrier(B));

            Implementation NewImplementation = ConstructBarrierToNextBarriersImplementation(A, "noname");

            for (int i = 1; i < NewImplementation.Blocks.Count; i++)
            {
                if (IsBarrier(NewImplementation.Blocks[i]) && GetBarrierId(B) == GetBarrierId(NewImplementation.Blocks[i]))
                {
                    return true;
                }
            }

            return false;
        }

        private static void AddInlineAttribute(Procedure NewProcedure)
        {
            NewProcedure.AddAttribute("inline", new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(1)) });
        }

        private Procedure CloneKernelProcedure(string NewProcedureName)
        {
            RequiresSeq NewRequiresSeq = new RequiresSeq();
            foreach(Requires r in KernelProcedure.Requires)
            {
                NewRequiresSeq.Add(r);
            }
            EnsuresSeq NewEnsuresSeq = new EnsuresSeq();
            foreach (Ensures e in KernelProcedure.Ensures)
            {
                NewEnsuresSeq.Add(e);
            }
            IdentifierExprSeq NewModifiesSeq = new IdentifierExprSeq();
            foreach (IdentifierExpr ies in KernelProcedure.Modifies)
            {
                NewModifiesSeq.Add(ies);
            }
            return new Procedure(KernelProcedure.tok, NewProcedureName, KernelProcedure.TypeParameters, KernelProcedure.InParams, KernelProcedure.OutParams, NewRequiresSeq, NewModifiesSeq, NewEnsuresSeq);
        }

        private void AddBarrierTracking(Implementation Impl)
        {
            Debug.Assert(IsBarrier(Impl.Blocks[0]));
            CmdSeq NewBlock0Commands = new CmdSeq();

            NewBlock0Commands.Add(Impl.Blocks[0].Cmds[0]);

            NewBlock0Commands.Add(MakeAssignToAtBarrier(Impl.Blocks[0].Cmds[0].tok, -1));

            for (int i = 1; i < Impl.Blocks[0].Cmds.Length; i++)
            {
                NewBlock0Commands.Add(Impl.Blocks[0].Cmds[i]);
            }

            Impl.Blocks[0].Cmds = NewBlock0Commands;

            for (int i = 1; i < Impl.Blocks.Count; i++)
            {
                if (IsBarrier(Impl.Blocks[i]))
                {
                    // At this stage, the barrier should be followed immediately by a return
                    Debug.Assert(Impl.Blocks[i].Cmds.Length == 1);

                    Impl.Blocks[i].Cmds.Add(MakeAssignToAtBarrier(Impl.Blocks[i].Cmds[0].tok, GetBarrierId(Impl.Blocks[i])));

                }
            }

        }


        private void AddReachedNextBarrierTracking(Implementation Impl, Block A, Block B)
        {
            Debug.Assert(IsBarrier(Impl.Blocks[0]) && GetBarrierId(Impl.Blocks[0]) == GetBarrierId(A));

            for (int i = 1; i < Impl.Blocks.Count; i++)
            {
                if (IsBarrier(Impl.Blocks[i]))
                {
                    // At this stage, the barrier should be followed immediately by a return
                    Debug.Assert(Impl.Blocks[i].Cmds.Length == 1 && GetBarrierId(Impl.Blocks[i]) == GetBarrierId(B));

                    Impl.Blocks[i].Cmds.Add(MakeSetReachedNextBarrier(Impl.Blocks[i].Cmds[0].tok));

                }
            }
        }


        private AssignCmd MakeAssignCmd(IToken tok, AssignLhs lhs, Expr rhs)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            lhss.Add(lhs);
            List<Expr> rhss = new List<Expr>();
            rhss.Add(rhs);
            return new AssignCmd(tok, lhss, rhss);
        }

        private AssignCmd MakeAssignToAtBarrier(IToken tok, int p)
        {
            List<Expr> indexes = new List<Expr>();
            indexes.Add(MakeThreadIdExpr(tok));
            return MakeAssignCmd(tok, new MapAssignLhs(tok, new SimpleAssignLhs(tok, MakeAtBarrierVariable(tok)), indexes), new LiteralExpr(tok, BigNum.FromInt(p)));
        }

        private AssignCmd MakeSetReachedNextBarrier(IToken tok)
        {
            List<Expr> indexes = new List<Expr>();
            indexes.Add(MakeThreadIdExpr(tok));
            return MakeAssignCmd(tok, new MapAssignLhs(tok, new SimpleAssignLhs(tok, MakeReachedNextBarrierVariable(tok)), indexes), new LiteralExpr(tok, true));
        }

        private NAryExpr MakeAtBarrierAccess(IToken tok, string ThreadIdName)
        {
            ExprSeq args = new ExprSeq();
            args.Add(MakeAtBarrierVariable(tok));
            args.Add(MakeThreadIdExpr(tok, ThreadIdName));
            return new NAryExpr(tok, new MapSelect(tok, 1), args);
        }

        private NAryExpr MakeReachedNextBarrierAccess(IToken tok, string ThreadIdName)
        {
            ExprSeq args = new ExprSeq();
            args.Add(MakeReachedNextBarrierVariable(tok));
            args.Add(MakeThreadIdExpr(tok, ThreadIdName));
            return new NAryExpr(tok, new MapSelect(tok, 1), args);
        }

        private IdentifierExpr MakeAtBarrierVariable(IToken tok)
        {
            TypeSeq IndexType = new TypeSeq();
            IndexType.Add(ThreadIdType);
            return new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, "AT_BARRIER", new MapType(tok, new TypeVariableSeq(), IndexType, Microsoft.Boogie.Type.Int))));
        }

        private IdentifierExpr MakeReachedNextBarrierVariable(IToken tok)
        {
            TypeSeq IndexType = new TypeSeq();
            IndexType.Add(ThreadIdType);
            return new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, "REACHED_NEXT_BARRIER", new MapType(tok, new TypeVariableSeq(), IndexType, Microsoft.Boogie.Type.Bool))));
        }

        private static HashSet<Block> BlocksReaching(Block B)
        {
            HashSet<Block> Result = new HashSet<Block>();
            ComputeReachingBlocksRecursive(B, Result);
            return Result;
        }

        private static void ComputeReachingBlocksRecursive(Block B, HashSet<Block> Result)
        {
            if (Result.Contains(B))
            {
                return;
            }

            Result.Add(B);
            foreach (Block C in B.Predecessors)
            {
                ComputeReachingBlocksRecursive(C, Result);
            }
        }

        private static HashSet<Block> BlocksReachableFrom(Block B)
        {
            HashSet<Block> Result = new HashSet<Block>();
            ComputeReachableBlocksRecursive(B, Result);
            return Result;
        }

        private static void ComputeReachableBlocksRecursive(Block B, HashSet<Block> Result)
        {
            if (Result.Contains(B))
            {
                return;
            }
            Result.Add(B);
            if (B.TransferCmd is GotoCmd)
            {
                foreach (Block C in (B.TransferCmd as GotoCmd).labelTargets)
                {
                    ComputeReachableBlocksRecursive(C, Result);
                }
            }
        }




        private Block FindBarrierBlock(Implementation Impl, int BarrierId)
        {
            foreach (Block B in Impl.Blocks)
            {
                if (B.Cmds.Length > 0 && IsBarrier(B.Cmds[0]) && GetBarrierId(B) == BarrierId)
                {
                    return B;
                }
            }

            Debug.Assert(false);

            return null;
        }

        private int GetBarrierId(Cmd C)
        {
            Debug.Assert(IsBarrier(C));
            return QKeyValue.FindIntAttribute((C as CallCmd).Attributes, "barrier_id", -1);
        }

        public int GetBarrierId(Block A)
        {
            Debug.Assert(A.Cmds.Length > 0);
            return GetBarrierId(A.Cmds[0]);
        }

        public bool IsBarrier(Cmd C)
        {
            return C is CallCmd && (C as CallCmd).callee == BarrierProcedure.Name;
        }

        public bool IsBarrier(Block B)
        {
            return B.Cmds.Length > 0 && IsBarrier(B.Cmds[0]);
        }




        public void SplitBlocksAtBarriers()
        {

            for (int i = 0; i < KernelImplementation.Blocks.Count; i++)
            {
                Block B = KernelImplementation.Blocks[i];

                List<CmdSeq> Segments = new List<CmdSeq>();
                CmdSeq CurrentSequence = new CmdSeq();
                foreach (Cmd C in B.Cmds)
                {
                    if (IsBarrier(C))
                    {
                        if (CurrentSequence.Length > 0)
                        {
                            Segments.Add(CurrentSequence);
                            CurrentSequence = new CmdSeq();
                        }
                    }

                    CurrentSequence.Add(C);
                }
                if (CurrentSequence.Length > 0)
                {
                    Segments.Add(CurrentSequence);
                }

                if (Segments.Count > 1)
                {
                    TransferCmd OriginalTransferCmd = B.TransferCmd;

                    // Set the block's commands to be the first command sequence
                    B.Cmds = Segments[0];
                    B.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq());
                    Block LastBlock = B;
                    for (int j = 1; j < Segments.Count; j++)
                    {
                        Block NewBlock = new Block(Token.NoToken, "barrier_label_" + GetBarrierId(Segments[j][0]), Segments[j], new GotoCmd(Token.NoToken, new BlockSeq()));
                        KernelImplementation.Blocks.Add(NewBlock);
                        (LastBlock.TransferCmd as GotoCmd).AddTarget(NewBlock);
                        LastBlock = NewBlock;
                    }
                    LastBlock.TransferCmd = OriginalTransferCmd;

                }

            }
        }

        private bool ContainsInternalBarrier(Block B)
        {
            bool first = true;
            foreach (Cmd C in B.Cmds)
            {
                if (first)
                {
                    first = false;
                    continue;
                }

                if (C is CallCmd)
                {
                    CallCmd Call = C as CallCmd;
                    if (QKeyValue.FindBoolAttribute(Call.Proc.Attributes, "barrier"))
                    {
                        return true;
                    }
                }

            }

            return false;
        }



        internal Implementation GetKernel()
        {
            return KernelImplementation;
        }

        internal void GenerateSpanAProcedures()
        {
            foreach (Block B in KernelImplementation.Blocks)
            {
                if (IsBarrier(B) && (GetBarrierId(B) < MaxBarrierId()))
                {
                    GenerateSpanA(B);
                }
            }
        }

        internal void GenerateSpanABProcedures()
        {
            foreach (Block A in KernelImplementation.Blocks)
            {
                if (IsBarrier(A))
                {
                    foreach (Block B in KernelImplementation.Blocks)
                    {
                        if (IsBarrier(B))
                        {
                            GenerateBarrierAToBarrierBProcedure(A, B);
                        }
                    }
                }
            }
        }

        internal IdentifierExpr MakeThreadIdExpr(IToken tok, string name)
        {
            return new IdentifierExpr(tok, new LocalVariable(tok, new TypedIdent(tok, name, ThreadIdType)));
        }

        internal IdentifierExpr MakeThreadIdExpr(IToken tok)
        {
            return MakeThreadIdExpr(tok, ThreadIdParameterName);
        }


        internal void AddArrayBaseDeclarations()
        {
            foreach (Variable V in GlobalVariables)
            {
                Program.TopLevelDeclarations.Add(new Constant(V.tok, new TypedIdent(V.tok, V.Name + "_base", MakeArrayBaseType(V.tok)), true));
            }

            foreach (Variable V in TileStaticVariables)
            {
                Program.TopLevelDeclarations.Add(new Constant(V.tok, new TypedIdent(V.tok, V.Name + "_base", MakeArrayBaseType(V.tok)), true));
            }
        }


        internal void AddArrayTrackingDeclarations()
        {
            foreach (Variable V in GlobalVariables)
            {
                GenerateLoggingVariablesForArray(V);
            }

            foreach (Variable V in TileStaticVariables)
            {
                GenerateLoggingVariablesForArray(V);
            }
        }

        private void GenerateLoggingVariablesForArray(Variable V)
        {
            Program.TopLevelDeclarations.Add(MakeWrittenBooleanVariable(V));
            Program.TopLevelDeclarations.Add(MakeWrittenOffsetVariable(V, "x"));
            Program.TopLevelDeclarations.Add(MakeWrittenOffsetVariable(V, "y"));
            Program.TopLevelDeclarations.Add(MakeWrittenOffsetVariable(V, "z"));
            Program.TopLevelDeclarations.Add(MakeReadBooleanVariable(V));
            Program.TopLevelDeclarations.Add(MakeReadOffsetVariable(V, "x"));
            Program.TopLevelDeclarations.Add(MakeReadOffsetVariable(V, "y"));
            Program.TopLevelDeclarations.Add(MakeReadOffsetVariable(V, "z"));
        }

        private GlobalVariable MakeWrittenOffsetVariable(Variable V, string Dimension)
        {
            return new GlobalVariable(V.tok, new TypedIdent(V.tok, V.Name + "_written_offset_" + Dimension, MakeThreadIdToIntType(V.tok)));
        }

        private GlobalVariable MakeWrittenOffsetVariable(string Dimension)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "written_offset_" + Dimension, MakeThreadIdToIntType(Token.NoToken)));
        }

        private GlobalVariable MakeWrittenBooleanVariable(Variable V)
        {
            return new GlobalVariable(V.tok, new TypedIdent(V.tok, V.Name + "_written", MakeThreadIdToBoolType(V.tok)));
        }

        private GlobalVariable MakeWrittenBooleanVariable()
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "written", MakeThreadIdToBoolType(Token.NoToken)));
        }

        private GlobalVariable MakeReadOffsetVariable(Variable V, string Dimension)
        {
            return new GlobalVariable(V.tok, new TypedIdent(V.tok, V.Name + "_read_offset_" + Dimension, MakeThreadIdToIntType(V.tok)));
        }

        private GlobalVariable MakeReadOffsetVariable(string Dimension)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "read_offset_" + Dimension, MakeThreadIdToIntType(Token.NoToken)));
        }

        private GlobalVariable MakeReadBooleanVariable(Variable V)
        {
            return new GlobalVariable(V.tok, new TypedIdent(V.tok, V.Name + "_read", MakeThreadIdToBoolType(V.tok)));
        }

        private GlobalVariable MakeReadBooleanVariable()
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "read", MakeThreadIdToBoolType(Token.NoToken)));
        }

        private Microsoft.Boogie.Type MakeThreadIdToIntType(IToken tok)
        {
            TypeSeq index = new TypeSeq();
            index.Add(ThreadIdType);
            return new MapType(tok, new TypeVariableSeq(), index, Microsoft.Boogie.Type.Int);
        }

        private Microsoft.Boogie.Type MakeThreadIdToBoolType(IToken tok)
        {
            TypeSeq index = new TypeSeq();
            index.Add(ThreadIdType);
            return new MapType(tok, new TypeVariableSeq(), index, Microsoft.Boogie.Type.Bool);
        }



        internal void GenerateSpanA_VCs()
        {
            foreach (Block A in KernelImplementation.Blocks)
            {
                if (IsBarrier(A) && (GetBarrierId(A) < MaxBarrierId()))
                {
                    GenerateSpanA_VC(A);
                }
            }
        }

        private void GenerateSpanA_VC(Block A)
        {
            VariableSeq InParams = new VariableSeq();
            InParams.Add(new LocalVariable(A.tok, new TypedIdent(A.tok, "__i", ThreadIdType)));
            InParams.Add(new LocalVariable(A.tok, new TypedIdent(A.tok, "__j", ThreadIdType)));

            VariableSeq OutParams = new VariableSeq();

            IdentifierExprSeq Modifies = new IdentifierExprSeq();
            foreach (IdentifierExpr ie in KernelProcedure.Modifies)
            {
                Modifies.Add(ie);
            }

            AddTrackingVariablesToModifiesSet(A.tok, Modifies);

            RequiresSeq Requires = new RequiresSeq();
            Requires.Add(new Requires(false, MakePreconditionExpr(A)));
            AddDistinctSameTile(A.tok, Requires, "__i", "__j");

            if (!CommandLineOptions.OnlyDivergence)
            {
                AddNothingInitiallyTracked(A.tok, Requires, "__i", "__j");
            }

            EnsuresSeq Ensures = new EnsuresSeq();

            if (!CommandLineOptions.OnlyDivergence)
            {
                AddNoRace(A.tok, Ensures, "__i", "__j");
            }
            AddSameBarrier(A.tok, Ensures, "__i", "__j");

            string SpanACorrect = "Check_Span_" + GetBarrierId(A) + "_Correct";

            Procedure NewProcedure = new Procedure(A.tok, SpanACorrect, new TypeVariableSeq(), InParams, OutParams, Requires, Modifies, Ensures);

            List<Block> Blocks = new List<Block>();

            Blocks.Add(new Block());

            Blocks[0].TransferCmd = new ReturnCmd(A.tok);

            Blocks[0].Label = "entry";

            Blocks[0].Cmds = new CmdSeq();

            ExprSeq i = new ExprSeq();
            i.Add(new IdentifierExpr(A.tok, new LocalVariable(A.tok, new TypedIdent(A.tok, "__i", ThreadIdType))));
            Blocks[0].Cmds.Add(new CallCmd(A.tok, MakeSpanAProcedureName(A), i, new IdentifierExprSeq()));

            ExprSeq j = new ExprSeq();
            j.Add(new IdentifierExpr(A.tok, new LocalVariable(A.tok, new TypedIdent(A.tok, "__j", ThreadIdType))));
            Blocks[0].Cmds.Add(new CallCmd(A.tok, MakeSpanAProcedureName(A), j, new IdentifierExprSeq()));

            Implementation NewImplementation = new Implementation(A.tok, SpanACorrect, new TypeVariableSeq(), InParams, OutParams, new VariableSeq(), Blocks);

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);

        }

        private void AddNothingInitiallyTracked(IToken tok, RequiresSeq Requires, string i, string j)
        {
            Contract.Requires(Requires != null);

            if (CommandLineOptions.NewRaceDetectionMethod)
            {
                foreach (Variable V in GlobalVariables)
                {
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeReadBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, i) }))));
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeReadBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, j) }))));
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeWrittenBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, i) }))));
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeWrittenBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, j) }))));
                }

                foreach (Variable V in TileStaticVariables)
                {
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeReadBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, i) }))));
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeReadBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, j) }))));
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeWrittenBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, i) }))));
                    Requires.Add(new Requires(false, Expr.Not(Expr.Select(new IdentifierExpr(tok, MakeWrittenBooleanVariable(V)), new Expr[] { MakeThreadIdExpr(tok, j) }))));
                }
            }
            else
            {
                Requires.Add(new Requires(false, Expr.And(BaseEqualsNothing(tok, i), BaseEqualsNothing(tok, j))));
            }
        }

        private Expr BaseEqualsNothing(IToken tok, string i)
        {
            ExprSeq MapSelectArgs = new ExprSeq();
            MapSelectArgs.Add(MakeBaseVariable(tok));
            MapSelectArgs.Add(MakeThreadIdExpr(tok, i));
            return Expr.Eq(new NAryExpr(tok, new MapSelect(tok, 1), MapSelectArgs), new IdentifierExpr(tok, new GlobalVariable(tok, new TypedIdent(tok, "nothing", MakeArrayBaseType(tok)))));
        }

        private void AddSameBarrier(IToken tok, EnsuresSeq Ensures, string i, string j)
        {
            ExprSeq args1 = new ExprSeq();
            args1.Add(MakeAtBarrierVariable(tok));
            args1.Add(MakeThreadIdExpr(tok, i));

            ExprSeq args2 = new ExprSeq();
            args2.Add(MakeAtBarrierVariable(tok));
            args2.Add(MakeThreadIdExpr(tok, j));

            Ensures.Add(new Ensures(false, Expr.Eq( new NAryExpr(tok, new MapSelect(tok, 1), args1), new NAryExpr(tok, new MapSelect(tok, 1), args2) ) ) );

        }

        private void AddNoRace(IToken tok, EnsuresSeq Ensures, string i, string j)
        {
            if (CommandLineOptions.NewRaceDetectionMethod)
            {
                AddNoRaceNewMethod(tok, Ensures, i, j);
            }
            else
            {
                AddNoRaceOldMethod(tok, Ensures, i, j);
            }

        }

        private void AddNoRaceOldMethod(IToken tok, EnsuresSeq Ensures, string i, string j)
        {
            ExprSeq RaceArgs = new ExprSeq();
            RaceArgs.Add(MakeBaseVariable(tok));
            RaceArgs.Add(MakeOffsetZVariable(tok));
            RaceArgs.Add(MakeOffsetYVariable(tok));
            RaceArgs.Add(MakeOffsetXVariable(tok));
            RaceArgs.Add(MakeIsWriteVariable(tok));
            RaceArgs.Add(MakeThreadIdExpr(tok, i));
            RaceArgs.Add(MakeThreadIdExpr(tok, j));

            NAryExpr RaceExpr = new NAryExpr(tok, new FunctionCall(new IdentifierExpr(tok, "race", Microsoft.Boogie.Type.Bool)), RaceArgs);
            Ensures.Add(new Ensures(false, Expr.Not(RaceExpr)));
        }


        private void AddNoRaceNewMethod(IToken tok, EnsuresSeq Ensures, string i, string j)
        {
            foreach (Variable V in GlobalVariables)
            {
                AddNoWriteWriteRace(tok, Ensures, i, j, V);
                AddNoReadWriteRace(tok, Ensures, i, j, V);
            }

            foreach (Variable V in TileStaticVariables)
            {
                AddNoWriteWriteRace(tok, Ensures, i, j, V);
                AddNoReadWriteRace(tok, Ensures, i, j, V);
            }

        }

        private void AddNoWriteWriteRace(IToken tok, EnsuresSeq Ensures, string i, string j, Variable V)
        {
            ExprSeq RaceArgs = new ExprSeq();
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenBooleanVariable(V)));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenOffsetVariable(V, "z")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenOffsetVariable(V, "y")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenOffsetVariable(V, "x")));
            RaceArgs.Add(MakeThreadIdExpr(tok, i));
            RaceArgs.Add(MakeThreadIdExpr(tok, j));
            NAryExpr RaceExpr = new NAryExpr(tok, new FunctionCall(new IdentifierExpr(tok, "race_W_W", Microsoft.Boogie.Type.Bool)), RaceArgs);
            Ensures.Add(new Ensures(false, Expr.Not(RaceExpr)));
        }

        private void AddNoReadWriteRace(IToken tok, EnsuresSeq Ensures, string i, string j, Variable V)
        {
            ExprSeq RaceArgs = new ExprSeq();
            RaceArgs.Add(new IdentifierExpr(tok, MakeReadBooleanVariable(V)));
            RaceArgs.Add(new IdentifierExpr(tok, MakeReadOffsetVariable(V, "z")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeReadOffsetVariable(V, "y")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeReadOffsetVariable(V, "x")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenBooleanVariable(V)));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenOffsetVariable(V, "z")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenOffsetVariable(V, "y")));
            RaceArgs.Add(new IdentifierExpr(tok, MakeWrittenOffsetVariable(V, "x")));
            RaceArgs.Add(MakeThreadIdExpr(tok, i));
            RaceArgs.Add(MakeThreadIdExpr(tok, j));
            NAryExpr RaceExpr = new NAryExpr(tok, new FunctionCall(new IdentifierExpr(tok, "race_R_W", Microsoft.Boogie.Type.Bool)), RaceArgs);
            Ensures.Add(new Ensures(false, Expr.Not(RaceExpr)));
        }




        private void AddDistinctSameTile(IToken tok, RequiresSeq Requires, string i, string j)
        {
            ExprSeq args = new ExprSeq();
            args.Add(new IdentifierExpr(tok, new LocalVariable(tok, new TypedIdent(tok, i, ThreadIdType))));
            args.Add(new IdentifierExpr(tok, new LocalVariable(tok, new TypedIdent(tok, j, ThreadIdType))));
            Requires.Add(new Requires(false, new NAryExpr(tok, new FunctionCall(new IdentifierExpr(tok, "distinct_same_tile", Microsoft.Boogie.Type.Bool)), args)));
        }

        private NAryExpr MakePreconditionExpr(Block B)
        {
            ExprSeq PreconditionArgs = new ExprSeq();
            foreach (Variable v in MakeFormulaFunctionArguments(B.tok, false))
            {
                PreconditionArgs.Add(new IdentifierExpr(B.tok, v));
            }

            NAryExpr nary = new NAryExpr(B.tok, new FunctionCall(new IdentifierExpr(B.tok, MakePreconditionName(B), Microsoft.Boogie.Type.Bool)), PreconditionArgs);
            return nary;
        }

        private void AddTrackingVariablesToModifiesSet(IToken tok, IdentifierExprSeq Modifies)
        {
            if (CommandLineOptions.NewRaceDetectionMethod)
            {
                foreach (Variable V in GlobalVariables)
                {
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadBooleanVariable(V)));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadOffsetVariable(V, "z")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadOffsetVariable(V, "y")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadOffsetVariable(V, "x")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenBooleanVariable(V)));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenOffsetVariable(V, "z")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenOffsetVariable(V, "y")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenOffsetVariable(V, "x")));
                }

                foreach (Variable V in TileStaticVariables)
                {
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadBooleanVariable(V)));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadOffsetVariable(V, "z")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadOffsetVariable(V, "y")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeReadOffsetVariable(V, "x")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenBooleanVariable(V)));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenOffsetVariable(V, "z")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenOffsetVariable(V, "y")));
                    Modifies.Add(new IdentifierExpr(V.tok, MakeWrittenOffsetVariable(V, "x")));
                }
                Modifies.Add(MakeAtBarrierVariable(tok));

            }
            else
            {
                Modifies.Add(MakeBaseVariable(tok));
                Modifies.Add(MakeOffsetXVariable(tok));
                Modifies.Add(MakeOffsetYVariable(tok));
                Modifies.Add(MakeOffsetZVariable(tok));
                Modifies.Add(MakeIsWriteVariable(tok));
                Modifies.Add(MakeAtBarrierVariable(tok));
            }
        }

        internal void GenerateSpanAB_VCs()
        {
            foreach (Block A in KernelImplementation.Blocks)
            {
                if (IsBarrier(A))
                {
                    foreach (Block B in KernelImplementation.Blocks)
                    {
                        if (IsBarrier(B) && BarrierReachesBarrier(A, B))
                        {
                            GenerateSpanAB_VCs(A, B);
                        }
                    }
                }
            }
        }

        private void GenerateSpanAB_VCs(Block A, Block B)
        {
            GenerateVC_AToB_Pre(A, B);
            GenerateVC_AToB_Induction(A, B);
            GenerateVC_AToB_Post(A, B);
        }

        private ForallExpr MakeAllReachedNextBarrierExpr(IToken tok)
        {
            VariableSeq i = new VariableSeq();
            i.Add(MakeThreadIdExpr(tok, "__i").Decl);
            ForallExpr forallexpr = new ForallExpr(tok, i, MakeReachedNextBarrierAccess(tok, "__i"));
            return forallexpr;
        }

        private ForallExpr MakeNoneReachedNextBarrierExpr(IToken tok)
        {
            VariableSeq i = new VariableSeq();
            i.Add(MakeThreadIdExpr(tok, "__i").Decl);
            ForallExpr forallexpr = new ForallExpr(tok, i, Expr.Not(MakeReachedNextBarrierAccess(tok, "__i")));
            return forallexpr;
        }

        private string MakeIHName(Block A, Block B)
        {
            return "IH_" + GetBarrierId(A) + "_" + GetBarrierId(B);
        }


        private NAryExpr MakeIHExpr(Block A, Block B)
        {
            ExprSeq IHArgs = new ExprSeq();
            foreach (Variable v in MakeFormulaFunctionArguments(B.tok, true))
            {
                IHArgs.Add(new IdentifierExpr(B.tok, v));
            }

            NAryExpr nary = new NAryExpr(B.tok, new FunctionCall(new IdentifierExpr(A.tok, MakeIHName(A, B), Microsoft.Boogie.Type.Bool)), IHArgs);
            return nary;
        }

        private Expr MakeThreadNotReachedNextBarrierExpr(IToken tok, string ThreadIdName)
        {
            return Expr.Not(MakeReachedNextBarrierAccess(tok, ThreadIdName));
        }

        private void GenerateVC_AToB_Pre(Block A, Block B)
        {
            string ProcedureName = "Check_" + GetBarrierId(A) + "_to_" + GetBarrierId(B) + "_Pre";

            Procedure NewProcedure = new Procedure(A.tok, ProcedureName, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
            NewProcedure.Requires.Add(new Requires(false, MakePreconditionExpr(A)));
            NewProcedure.Requires.Add(new Requires(false, MakeNoneReachedNextBarrierExpr(A.tok)));
            NewProcedure.Ensures.Add(new Ensures(false, MakeIHExpr(A, B)));

            Implementation NewImplementation = new Implementation(A.tok, ProcedureName, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new VariableSeq(), new List<Block>());

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);
        }

        private void GenerateVC_AToB_Induction(Block A, Block B)
        {
            string ProcedureName = "Check_" + GetBarrierId(A) + "_to_" + GetBarrierId(B) + "_Induction";

            VariableSeq InParams = new VariableSeq();
            InParams.Add(MakeThreadIdExpr(A.tok).Decl);

            IdentifierExprSeq Modifies = new IdentifierExprSeq();
            foreach (IdentifierExpr ie in KernelProcedure.Modifies)
            {
                Modifies.Add(ie);
            }

            Modifies.Add(MakeReachedNextBarrierVariable(B.tok));

            Procedure NewProcedure = new Procedure(A.tok, ProcedureName, new TypeVariableSeq(), InParams, new VariableSeq(), new RequiresSeq(), Modifies, new EnsuresSeq());
            NewProcedure.Requires.Add(new Requires(false, MakeIHExpr(A, B)));
            NewProcedure.Requires.Add(new Requires(false, MakeThreadNotReachedNextBarrierExpr(A.tok, ThreadIdParameterName)));
            NewProcedure.Ensures.Add(new Ensures(false, MakeIHExpr(A, B)));

            Implementation NewImplementation = new Implementation(A.tok, ProcedureName, new TypeVariableSeq(), InParams, new VariableSeq(), new VariableSeq(), new List<Block>());
            NewImplementation.Blocks.Add(new Block());
            NewImplementation.Blocks[0].Label = "entry";
            NewImplementation.Blocks[0].TransferCmd = new ReturnCmd(A.tok);
            NewImplementation.Blocks[0].Cmds = new CmdSeq();
            ExprSeq i = new ExprSeq();
            i.Add(MakeThreadIdExpr(A.tok));
            NewImplementation.Blocks[0].Cmds.Add(new CallCmd(A.tok, MakeSpanABProcedureName(A, B), i, new IdentifierExprSeq()));

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);
        }

        private void GenerateVC_AToB_Post(Block A, Block B)
        {
            string ProcedureName = "Check_" + GetBarrierId(A) + "_to_" + GetBarrierId(B) + "_Post";

            Procedure NewProcedure = new Procedure(A.tok, ProcedureName, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
            NewProcedure.Requires.Add(new Requires(false, MakeIHExpr(A, B)));
            NewProcedure.Requires.Add(new Requires(false, MakeAllReachedNextBarrierExpr(B.tok)));
            NewProcedure.Ensures.Add(new Ensures(false, MakePreconditionExpr(B)));

            Implementation NewImplementation = new Implementation(A.tok, ProcedureName, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new VariableSeq(), new List<Block>());

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);

        }

        internal void GenerateFormulaSkeletons(string filename)
        {
            Program FormulaSkeletons = new Program();

            foreach (Block B in KernelImplementation.Blocks)
            {
                if (IsBarrier(B))
                {
                    FormulaSkeletons.TopLevelDeclarations.Add(MakeSkeletonFormula(B, MakePreconditionName(B), false));
                }
            }

            foreach (Block A in KernelImplementation.Blocks)
            {
                if (IsBarrier(A))
                {
                    foreach (Block B in KernelImplementation.Blocks)
                    {
                        if (IsBarrier(B) && BarrierReachesBarrier(A, B))
                        {
                            FormulaSkeletons.TopLevelDeclarations.Add(MakeSkeletonFormula(B, MakeIHName(A, B), true));
                        }
                    }
                }
            }

            using (TokenTextWriter writer = new TokenTextWriter(filename))
            {
                FormulaSkeletons.Emit(writer);
            }


        }

        private string MakePreconditionName(Block B)
        {
            return "Pre_" + GetBarrierId(B);
        }

        private Function MakeSkeletonFormula(Block B, string FunctionName, bool isIH)
        {

            Function precondition = new Function(B.tok, FunctionName, MakeFormulaFunctionArguments(B.tok, isIH), MakeFunctionReturnTemp(B.tok));

            precondition.AddAttribute("inline", new object[] { });

            precondition.Body = new LiteralExpr(B.tok, true);
            return precondition;
        }

        private Variable MakeFunctionReturnTemp(IToken tok)
        {
            return new LocalVariable(tok, new TypedIdent(tok, "result", Microsoft.Boogie.Type.Bool));
        }

        private VariableSeq MakeFormulaFunctionArguments(IToken tok, bool isIH)
        {
            VariableSeq arguments = new VariableSeq();

            foreach (Variable v in ThreadLocalVariables)
            {
                arguments.Add(v);
            }

            foreach (Variable v in TileStaticVariables)
            {
                arguments.Add(v);
            }

            foreach (Variable v in GlobalVariables)
            {
                arguments.Add(v);
            }

            if (isIH)
            {
                arguments.Add(MakeReachedNextBarrierVariable(tok).Decl);
            }
            return arguments;
        }

        internal void AddRaceCheckingFunctions()
        {
            AddRaceCheckingWWFunction();
            AddRaceCheckingRWFunction();
        }

        private void AddRaceCheckingRWFunction()
        {
            IToken tok = Token.NoToken;

            VariableSeq args = new VariableSeq();
            args.Add(MakeReadBooleanVariable());
            args.Add(MakeReadOffsetVariable("z"));
            args.Add(MakeReadOffsetVariable("y"));
            args.Add(MakeReadOffsetVariable("x"));
            args.Add(MakeWrittenBooleanVariable());
            args.Add(MakeWrittenOffsetVariable("z"));
            args.Add(MakeWrittenOffsetVariable("y"));
            args.Add(MakeWrittenOffsetVariable("x"));
            args.Add(MakeThreadIdExpr(tok, "__i").Decl);
            args.Add(MakeThreadIdExpr(tok, "__j").Decl);
            Function func = new Function(tok, "race_R_W", args, MakeFunctionReturnTemp(tok));
            func.AddAttribute("inline", new object[] { });

            Expr ReadOccurred = Expr.Select( new IdentifierExpr(tok, MakeReadBooleanVariable()),      new Expr[] { MakeThreadIdExpr(tok, "__i") });
            Expr WriteOccurred = Expr.Select( new IdentifierExpr(tok, MakeWrittenBooleanVariable()),      new Expr[] { MakeThreadIdExpr(tok, "__j") });
            Expr SameZ = Expr.Eq(Expr.Select(new IdentifierExpr(tok, MakeReadOffsetVariable("z")), new Expr[] { MakeThreadIdExpr(tok, "__i") }), Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("z")), new Expr[] { MakeThreadIdExpr(tok, "__j") }));
            Expr SameY = Expr.Eq(Expr.Select(new IdentifierExpr(tok, MakeReadOffsetVariable("y")), new Expr[] { MakeThreadIdExpr(tok, "__i") }), Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("y")), new Expr[] { MakeThreadIdExpr(tok, "__j") }));
            Expr SameX = Expr.Eq(Expr.Select(new IdentifierExpr(tok, MakeReadOffsetVariable("x")), new Expr[] { MakeThreadIdExpr(tok, "__i") }), Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("x")), new Expr[] { MakeThreadIdExpr(tok, "__j") }));

            func.Body = Expr.And(ReadOccurred, Expr.And(WriteOccurred, Expr.And(SameZ, Expr.And(SameY, SameX))));

            Program.TopLevelDeclarations.Add(func);
        }

        private void AddRaceCheckingWWFunction()
        {
            IToken tok = Token.NoToken;

            VariableSeq args = new VariableSeq();
            args.Add(MakeWrittenBooleanVariable());
            args.Add(MakeWrittenOffsetVariable("z"));
            args.Add(MakeWrittenOffsetVariable("y"));
            args.Add(MakeWrittenOffsetVariable("x"));
            args.Add(MakeThreadIdExpr(tok, "__i").Decl);
            args.Add(MakeThreadIdExpr(tok, "__j").Decl);
            Function func = new Function(tok, "race_W_W", args, MakeFunctionReturnTemp(tok));

            func.AddAttribute("inline", new object[] { });

            Expr WriteOccurred_i = Expr.Select(new IdentifierExpr(tok, MakeWrittenBooleanVariable()), new Expr[] { MakeThreadIdExpr(tok, "__i") });
            Expr WriteOccurred_j = Expr.Select(new IdentifierExpr(tok, MakeWrittenBooleanVariable()), new Expr[] { MakeThreadIdExpr(tok, "__j") });
            Expr SameZ = Expr.Eq(Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("z")), new Expr[] { MakeThreadIdExpr(tok, "__i") }), Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("z")), new Expr[] { MakeThreadIdExpr(tok, "__j") }));
            Expr SameY = Expr.Eq(Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("y")), new Expr[] { MakeThreadIdExpr(tok, "__i") }), Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("y")), new Expr[] { MakeThreadIdExpr(tok, "__j") }));
            Expr SameX = Expr.Eq(Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("x")), new Expr[] { MakeThreadIdExpr(tok, "__i") }), Expr.Select(new IdentifierExpr(tok, MakeWrittenOffsetVariable("x")), new Expr[] { MakeThreadIdExpr(tok, "__j") }));

            func.Body = Expr.And(WriteOccurred_i, Expr.And(WriteOccurred_j, Expr.And(SameZ, Expr.And(SameY, SameX))));

            Program.TopLevelDeclarations.Add(func);
        
        }

        internal void AddLoggingProcedures()
        {
            foreach (Variable V in GlobalVariables)
            {
                AddLoggingProcedures(V);
            }

            foreach (Variable V in TileStaticVariables)
            {
                AddLoggingProcedures(V);
            }
        }

        private void AddLoggingProcedures(Variable V)
        {
            AddLogReadProcedure(V);
            AddLogWriteProcedure(V);
        }

        private void AddLogAccessProcedure(Variable V, Variable AccessedBooleanVariable, Variable AccessedOffsetVariableZ, Variable AccessedOffsetVariableY, Variable AccessedOffsetVariableX, string ReadOrWrite)
        {
            VariableSeq inParams = new VariableSeq();

            Variable zParam = new LocalVariable(V.tok, new TypedIdent(V.tok, "__z", Microsoft.Boogie.Type.Int));
            Variable yParam = new LocalVariable(V.tok, new TypedIdent(V.tok, "__y", Microsoft.Boogie.Type.Int));
            Variable xParam = new LocalVariable(V.tok, new TypedIdent(V.tok, "__x", Microsoft.Boogie.Type.Int));
            Variable tidParam = MakeThreadIdExpr(V.tok, "__i").Decl;

            inParams.Add(zParam);
            inParams.Add(yParam);
            inParams.Add(xParam);
            inParams.Add(tidParam);

            IdentifierExprSeq modifies = new IdentifierExprSeq();

            modifies.Add(new IdentifierExpr(V.tok, AccessedBooleanVariable));
            modifies.Add(new IdentifierExpr(V.tok, AccessedOffsetVariableZ));
            modifies.Add(new IdentifierExpr(V.tok, AccessedOffsetVariableY));
            modifies.Add(new IdentifierExpr(V.tok, AccessedOffsetVariableX));

            Procedure LogAccessProcedure = new Procedure(V.tok, "LOG_" + ReadOrWrite + "_" + V.Name, new TypeVariableSeq(), inParams, new VariableSeq(), new RequiresSeq(), modifies, new EnsuresSeq());
            AddInlineAttribute(LogAccessProcedure);

            CmdSeq loggingCommands = new CmdSeq();

            List<Expr> indexes = new List<Expr>();
            indexes.Add(new IdentifierExpr(V.tok, tidParam));

            loggingCommands.Add(MakeMapAssignCommand(V.tok, AccessedBooleanVariable, new IdentifierExpr(V.tok, tidParam), new LiteralExpr(V.tok, true)));
            loggingCommands.Add(MakeMapAssignCommand(V.tok, AccessedOffsetVariableZ, new IdentifierExpr(V.tok, tidParam), new IdentifierExpr(V.tok, zParam)));
            loggingCommands.Add(MakeMapAssignCommand(V.tok, AccessedOffsetVariableY, new IdentifierExpr(V.tok, tidParam), new IdentifierExpr(V.tok, yParam)));
            loggingCommands.Add(MakeMapAssignCommand(V.tok, AccessedOffsetVariableX, new IdentifierExpr(V.tok, tidParam), new IdentifierExpr(V.tok, xParam)));

            Block dontLog = new Block(V.tok, "dont_log", new CmdSeq(), new ReturnCmd(V.tok));
            Block log = new Block(V.tok, "log", loggingCommands, new ReturnCmd(V.tok));

            StringSeq successor_labels = new StringSeq();
            successor_labels.Add("dont_log");
            successor_labels.Add("log");

            BlockSeq successor_blocks = new BlockSeq();
            successor_blocks.Add(dontLog);
            successor_blocks.Add(log);

            Block entry = new Block(V.tok, "entry", new CmdSeq(), new GotoCmd(V.tok, successor_labels, successor_blocks));

            List<Block> blocks = new List<Block>();
            blocks.Add(entry);
            blocks.Add(dontLog);
            blocks.Add(log);

            Implementation LogAccessImplementation = new Implementation(V.tok, "LOG_" + ReadOrWrite + "_" + V.Name, new TypeVariableSeq(), inParams, new VariableSeq(), new VariableSeq(), blocks);

            Program.TopLevelDeclarations.Add(LogAccessProcedure);
            Program.TopLevelDeclarations.Add(LogAccessImplementation);
        }

        private AssignCmd MakeMapAssignCommand(IToken tok, Variable map, Expr index, Expr value)
        {
            
            List<Expr> indexes = new List<Expr>();
            indexes.Add(index);
            return MakeAssignCmd(tok, new MapAssignLhs(tok, new SimpleAssignLhs(tok, new IdentifierExpr(tok, map)), indexes), value);
        }

        private void AddLogWriteProcedure(Variable V)
        {
            Variable AccessedBooleanVariable = MakeWrittenBooleanVariable(V);
            Variable AccessedOffsetVariableZ = MakeWrittenOffsetVariable(V, "z");
            Variable AccessedOffsetVariableY = MakeWrittenOffsetVariable(V, "y");
            Variable AccessedOffsetVariableX = MakeWrittenOffsetVariable(V, "x");
            string ReadOrWrite = "WRITE";
            AddLogAccessProcedure(V, AccessedBooleanVariable, AccessedOffsetVariableZ, AccessedOffsetVariableY, AccessedOffsetVariableX, ReadOrWrite);
        }

        private void AddLogReadProcedure(Variable V)
        {
            Variable AccessedBooleanVariable = MakeReadBooleanVariable(V);
            Variable AccessedOffsetVariableZ = MakeReadOffsetVariable(V, "z");
            Variable AccessedOffsetVariableY = MakeReadOffsetVariable(V, "y");
            Variable AccessedOffsetVariableX = MakeReadOffsetVariable(V, "x");
            string ReadOrWrite = "READ";
            AddLogAccessProcedure(V, AccessedBooleanVariable, AccessedOffsetVariableZ, AccessedOffsetVariableY, AccessedOffsetVariableX, ReadOrWrite);
        }

        override internal void doit()
        {
            // TODO: check that no non-barrier procedures are called from the kernel

            AddInitialAndFinalBarriers();

            SplitBlocksAtBarriers();


            if (CommandLineOptions.formulaSkeletonsFile != null)
            {
                Console.WriteLine("Generating skeleton formulas to \"" + CommandLineOptions.formulaSkeletonsFile + "\" and exiting");
                GenerateFormulaSkeletons(CommandLineOptions.formulaSkeletonsFile);
                Environment.Exit(0);
            }

            GenerateSpanAProcedures();

            GenerateSpanABProcedures();

            GenerateSpanA_VCs();

            GenerateSpanAB_VCs();

            if (!CommandLineOptions.OnlyDivergence)
            {
                if (CommandLineOptions.NewRaceDetectionMethod)
                {
                    AddArrayTrackingDeclarations();
                    AddRaceCheckingFunctions();
                    AddLoggingProcedures();
                }
                else
                {
                    AddArrayBaseDeclarations();
                }
            }

            if (CommandLineOptions.outputFile == null)
            {
                CommandLineOptions.outputFile = "temp_ready_to_verify.bpl";
            }

            using (TokenTextWriter writer = new TokenTextWriter(CommandLineOptions.outputFile))
            {
                Program.Emit(writer);
            }
        }
    }

}
