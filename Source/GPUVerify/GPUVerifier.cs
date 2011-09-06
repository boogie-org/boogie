using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class GPUVerifier : CheckingContext
    {

        HashSet<string> ReservedNames;

        private Program Program;
        private Procedure KernelProcedure;
        private Implementation KernelImplementation;
        private Procedure BarrierProcedure;
        private Microsoft.Boogie.Type ThreadIdType;
        private String ThreadIdParameterName;

        private HashSet<int> BarrierIds = new HashSet<int>();

        private HashSet<Variable> ThreadLocalVariables = new HashSet<Variable>();
        private HashSet<Variable> TileStaticVariables = new HashSet<Variable>();
        private HashSet<Variable> GloalVariables = new HashSet<Variable>();


        public GPUVerifier(Program program)
            : base((IErrorSink)null)
        {
            this.Program = program;

            ReservedNames = new HashSet<string>();
            ReservedNames.Add("base");
            ReservedNames.Add("offset_x");
            ReservedNames.Add("offset_y");
            ReservedNames.Add("offset_z");
            ReservedNames.Add("AT_BARRIER");

            CheckWellFormedness();
        }

        private void CheckWellFormedness()
        {
            int errorCount = check(Program);
            if (errorCount != 0)
            {
                Console.WriteLine("{0} GPUVerify format errors detected in {1}", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                Environment.Exit(1);
            }
        }

        internal int check(Program program)
        {
            BarrierProcedure = CheckExactlyOneBarrierProcedure(program);
            KernelProcedure = CheckExactlyOneKernelProcedure(program);
            TypeSynonymDecl ThreadIdDecl = CheckExactlyOneThreadIdType(program);
            ThreadIdType = new TypeSynonymAnnotation(ThreadIdDecl.tok, ThreadIdDecl, new TypeSeq());

            if (ErrorCount > 0)
            {
                return ErrorCount;
            }

            if (BarrierProcedure.InParams.Length != 0)
            {
                Error(BarrierProcedure, "Barrier procedure must not take any arguments");
            }

            if (BarrierProcedure.OutParams.Length != 0)
            {
                Error(BarrierProcedure, "Barrier procedure must not return any results");
            }

            FindGlobalVariables(program);

            CheckKernelImplementation(program);

            return ErrorCount;
        }

        private void FindGlobalVariables(Program program)
        {
            foreach (Declaration D in program.TopLevelDeclarations)
            {
                if (D is Variable && (D as Variable).IsMutable)
                {
                    if (!ReservedNames.Contains((D as Variable).Name))
                    {
                        GloalVariables.Add(D as Variable);
                    }
                }
            }
        }


        private void CheckKernelImplementation(Program Program)
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


            foreach (Declaration decl in Program.TopLevelDeclarations)
            {
                if (!(decl is Implementation))
                {
                    continue;
                }

                Implementation Impl = decl as Implementation;

                if (Impl.Proc == KernelProcedure)
                {
                    KernelImplementation = Impl;
                    break;
                }

            }

            if (KernelImplementation == null)
            {
                Error(Token.NoToken, "*** Error: no implementation of kernel procedure");
                return;
            }

            // Collect up the local and tile_static variables
            foreach (LocalVariable LV in KernelImplementation.LocVars)
            {
                if (QKeyValue.FindBoolAttribute(LV.Attributes, "tile_static"))
                {
                    TileStaticVariables.Add(LV);
                }
                else
                {
                    ThreadLocalVariables.Add(LV);
                }
            }

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



        private Procedure CheckExactlyOneKernelProcedure(Program program)
        {
            return CheckSingleInstanceOfAttributedProcedure(program, "kernel");
        }

        private Procedure CheckExactlyOneBarrierProcedure(Program program)
        {
            return CheckSingleInstanceOfAttributedProcedure(program, "barrier");
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

        internal HashSet<Variable> GetGlobalVariables()
        {
            return GloalVariables;
        }

        internal HashSet<Variable> GetTileStaticVariables()
        {
            return TileStaticVariables;
        }

        internal HashSet<Variable> GetThreadLocalVariables()
        {
            return ThreadLocalVariables;
        }


        private Procedure CheckSingleInstanceOfAttributedProcedure(Program program, string attribute)
        {
            Procedure attributedProcedure = null;

            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                if (!QKeyValue.FindBoolAttribute(decl.Attributes, attribute))
                {
                    continue;
                }

                if (decl is Procedure)
                {
                    if (attributedProcedure == null)
                    {
                        attributedProcedure = decl as Procedure;
                    }
                    else
                    {
                        Error(decl, "\"{0}\" attribute specified for procedure {1}, but it has already been specified for procedure {2}", attribute, (decl as Procedure).Name, attributedProcedure.Name);
                    }

                }
                else
                {
                    Error(decl, "\"{0}\" attribute can only be applied to a procedure", attribute);
                }
            }

            if (attributedProcedure == null)
            {
                Error(program, "\"{0}\" attribute has not been specified for any procedure.  You must mark exactly one procedure with this attribute", attribute);
            }

            return attributedProcedure;
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


        private void ComputeBarrierToNextBarriersProcedure(Block B)
        {
            SanityCheckKernel();
            Debug.Assert(IsBarrier(B));

            String NewProcedureName = "Barrier_" + GetBarrierId(B) + "_to_next_barriers";
            Procedure NewProcedure = new Procedure(KernelProcedure.tok, NewProcedureName, KernelProcedure.TypeParameters, KernelProcedure.InParams, KernelProcedure.OutParams, KernelProcedure.Requires, KernelProcedure.Modifies, KernelProcedure.Ensures);

            NewProcedure.Modifies.Add(MakeBaseVariable(B.tok));
            NewProcedure.Modifies.Add(MakeOffsetXVariable(B.tok));
            NewProcedure.Modifies.Add(MakeOffsetYVariable(B.tok));
            NewProcedure.Modifies.Add(MakeOffsetZVariable(B.tok));
            NewProcedure.Modifies.Add(MakeIsWriteVariable(B.tok));

            Implementation NewImplementation = ConstructBarrierToNextBarriersImplementation(B, NewProcedureName);

            InstrumentWithRaceDetection(NewImplementation);

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);

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
                    ReadCollector rc = new ReadCollector(this);
                    rc.Visit(C);
                    WriteCollector wc = new WriteCollector(this);
                    wc.Visit(C);

                    if (wc.FoundWrite())
                    {
                        AccessRecord write = wc.GetAccess();
                        ExprSeq InParams = ConstructLogAccessParameters(C, write);
                        NewCmds.Add(new CallCmd(C.tok, "LOG_WRITE", InParams, new IdentifierExprSeq()));
                    }

                    foreach (AccessRecord read in rc.accesses)
                    {
                        ExprSeq InParams = ConstructLogAccessParameters(C, read);
                        NewCmds.Add(new CallCmd(C.tok, "LOG_READ", InParams, new IdentifierExprSeq()));
                    }

                    NewCmds.Add(C);
                }
                B.Cmds = NewCmds;
            }
        }

        private ExprSeq ConstructLogAccessParameters(Cmd C, AccessRecord access)
        {
            ExprSeq InParams = new ExprSeq();
            InParams.Add(new IdentifierExpr(C.tok, new GlobalVariable(C.tok, new TypedIdent(C.tok, access.v.Name + "_base", Microsoft.Boogie.Type.Int))));
            InParams.Add(access.IndexZ);
            InParams.Add(access.IndexY);
            InParams.Add(access.IndexX);
            InParams.Add(MakeThreadIdExpr(C.tok));
            return InParams;
        }

        private void ComputeBarrierAToBarrierBProcedure(Block A, Block B)
        {
            Debug.Assert(IsBarrier(A));
            Debug.Assert(IsBarrier(B));

            String NewProcedureName = "Barrier_" + GetBarrierId(A) + "_to_" + GetBarrierId(B);
            Procedure NewProcedure = new Procedure(KernelProcedure.tok, NewProcedureName, KernelProcedure.TypeParameters, KernelProcedure.InParams, KernelProcedure.OutParams, KernelProcedure.Requires, KernelProcedure.Modifies, KernelProcedure.Ensures);
            Implementation NewImplementation = ConstructBarrierToNextBarriersImplementation(A, NewProcedureName);

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
            if (NewB == null)
            {
                // No path between the barriers -- nothing to do
                return;
            }

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

            Program.TopLevelDeclarations.Add(NewProcedure);
            Program.TopLevelDeclarations.Add(NewImplementation);

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

            int NumBlocksBeforeSplitting = KernelImplementation.Blocks.Count;

            for (int i = 0; i < NumBlocksBeforeSplitting; i++)
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

        internal void ComputeBarrierToNextBarriersProcedures()
        {
            foreach (Block B in KernelImplementation.Blocks)
            {
                if (IsBarrier(B) && (GetBarrierId(B) < MaxBarrierId()))
                {
                    ComputeBarrierToNextBarriersProcedure(B);
                }
            }
        }

        internal void ComputeBarrierToBarrierPairs()
        {
            foreach (Block A in KernelImplementation.Blocks)
            {
                if (IsBarrier(A))
                {
                    foreach (Block B in KernelImplementation.Blocks)
                    {
                        if (IsBarrier(B))
                        {
                            ComputeBarrierAToBarrierBProcedure(A, B);
                        }
                    }
                }
            }
        }

        internal IdentifierExpr MakeThreadIdExpr(IToken tok)
        {
            return new IdentifierExpr(tok, new LocalVariable(tok, new TypedIdent(tok, ThreadIdParameterName, ThreadIdType)));
        }



        internal void AddArrayBaseDeclarations()
        {
            foreach (Variable V in GetGlobalVariables())
            {
                Program.TopLevelDeclarations.Add(new Constant(V.tok, new TypedIdent(V.tok, V.Name + "_base", MakeArrayBaseType(V.tok)), true));
            }

            foreach (Variable V in GetTileStaticVariables())
            {
                Program.TopLevelDeclarations.Add(new Constant(V.tok, new TypedIdent(V.tok, V.Name + "_base", MakeArrayBaseType(V.tok)), true));
            }
        }
    }

}
