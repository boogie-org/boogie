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
    abstract class RaceInstrumenterBase : IRaceInstrumenter
    {
        protected GPUVerifier verifier;

        public INonLocalState NonLocalStateToCheck;

        public int onlyLog1;
        public int onlyLog2;
        public bool failedToFindSecondAccess;
        public bool addedLogWrite;
        private int logAddCount;

        private Dictionary<string, Procedure> logAccessProcedures = new Dictionary<string, Procedure>();

        public RaceInstrumenterBase()
        {
            onlyLog1 = -1;
            onlyLog2 = -1;
            failedToFindSecondAccess = false;
            addedLogWrite = false;
            logAddCount = 0;
        }

        public void setVerifier(GPUVerifier verifier)
        {
            this.verifier = verifier;
            NonLocalStateToCheck = new NonLocalStateLists();
            foreach(Variable v in verifier.NonLocalState.getGlobalVariables())
            {
                NonLocalStateToCheck.getGlobalVariables().Add(v);
            }
            foreach(Variable v in verifier.NonLocalState.getGroupSharedVariables())
            {
                NonLocalStateToCheck.getGroupSharedVariables().Add(v);
            }
        }

        protected abstract void AddRequiresNoPendingAccess(Variable v);

        private void AddNoReadOrWriteCandidateInvariants(WhileCmd wc, Variable v)
        {
            // Reasoning: if READ_HAS_OCCURRED_v is not in the modifies set for the
            // loop then there is no point adding an invariant
            //
            // If READ_HAS_OCCURRED_v is in the modifies set, but the loop does not
            // contain a barrier, then it is almost certain that a read CAN be
            // pending at the loop head, so the invariant will not hold
            //
            // If there is a barrier in the loop body then READ_HAS_OCCURRED_v will
            // be in the modifies set, but there may not be a live read at the loop
            // head, so it is worth adding the loop invariant candidate.
            //
            // The same reasoning applies for WRITE

            if (verifier.ContainsBarrierCall(wc.Body))
            {
                AddNoReadOrWriteCandidateInvariant(wc, v, "READ", "1");
                AddNoReadOrWriteCandidateInvariant(wc, v, "WRITE", "1");
                if (!CommandLineOptions.Symmetry)
                {
                    AddNoReadOrWriteCandidateInvariant(wc, v, "READ", "2");
                }
                AddNoReadOrWriteCandidateInvariant(wc, v, "WRITE", "2");
            }
        }

        private void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v)
        {
            AddNoReadOrWriteCandidateRequires(Proc, v, "READ", "1");
            AddNoReadOrWriteCandidateRequires(Proc, v, "WRITE", "1");
            if (!CommandLineOptions.Symmetry)
            {
                AddNoReadOrWriteCandidateRequires(Proc, v, "READ", "2");
            }
            AddNoReadOrWriteCandidateRequires(Proc, v, "WRITE", "2");
        }

        private void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v)
        {
            AddNoReadOrWriteCandidateEnsures(Proc, v, "READ", "1");
            AddNoReadOrWriteCandidateEnsures(Proc, v, "WRITE", "1");
            if (!CommandLineOptions.Symmetry)
            {
                AddNoReadOrWriteCandidateEnsures(Proc, v, "READ", "2");
            }
            AddNoReadOrWriteCandidateEnsures(Proc, v, "WRITE", "2");
        }

        protected abstract void AddNoReadOrWriteCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, string OneOrTwo);

        public void AddRaceCheckingCandidateInvariants(Implementation impl, WhileCmd wc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateInvariants(wc, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(impl, wc, v, "READ");
                AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(impl, wc, v, "WRITE");
                AddGroupStrideAccessCandidateInvariants(impl, wc, v, "READ");
                AddGroupStrideAccessCandidateInvariants(impl, wc, v, "WRITE");
            }
        }

        private void AddGroupStrideAccessCandidateInvariants(Implementation impl, WhileCmd wc, Variable v, string accessKind)
        {
            foreach (Expr e in GetOffsetsAccessed(wc.Body, v, accessKind))
            {
                if (!TryGenerateCandidateForStrideVariable(impl, wc, v, e, accessKind))
                {
                    if (e is IdentifierExpr)
                    {
                        foreach(Expr f in GetExpressionsFromWhichVariableIsAssignedInLoop(wc.Body, (e as IdentifierExpr).Decl))
                        {
                            TryGenerateCandidateForStrideVariable(impl, wc, v, f, accessKind);
                        }
                    }
                }
            }
        }

        private bool TryGenerateCandidateForStrideVariable(Implementation impl, WhileCmd wc, Variable v, Expr e, string accessKind)
        {
            foreach (string w in
                verifier.mayBeTidPlusConstantAnalyser.GetMayBeTidPlusConstantVars(impl.Name))
            {
                if (!verifier.ContainsNamedVariable(
                    LoopInvariantGenerator.GetModifiedVariables(wc.Body), w))
                {
                    continue;
                }

                // Check also live

                if (!IsLinearFunctionOfVariable(e, w))
                {
                    continue;
                }

                Debug.Assert(!verifier.uniformityAnalyser.IsUniform(impl.Name, w));

                Variable wVariable = new LocalVariable(wc.tok, new TypedIdent(wc.tok, w,
                        Microsoft.Boogie.Type.GetBvType(32)));

                Expr indexModPow2EqualsTid = ExprModPow2EqualsTid(
                    new IdentifierExpr(wc.tok, wVariable),
                    verifier.mayBeTidPlusConstantAnalyser.GetIncrement(impl.Name, w));

                verifier.AddCandidateInvariant(wc, new VariableDualiser(1, verifier.uniformityAnalyser, impl.Name).VisitExpr(indexModPow2EqualsTid.Clone() as Expr));
                verifier.AddCandidateInvariant(wc, new VariableDualiser(2, verifier.uniformityAnalyser, impl.Name).VisitExpr(indexModPow2EqualsTid.Clone() as Expr));

                Expr offsetExpr = new IdentifierExpr(Token.NoToken, GPUVerifier.MakeOffsetXVariable(v, accessKind));
                Expr invertedOffset = InverseOfLinearFunctionOfVariable(e, w, offsetExpr);

                Expr invertedOffsetModPow2EqualsTid = ExprModPow2EqualsTid(
                    invertedOffset,
                    verifier.mayBeTidPlusConstantAnalyser.GetIncrement(impl.Name, w));

                Expr candidateInvariantExpr = Expr.Imp(
                        new IdentifierExpr(Token.NoToken, ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, accessKind)),
                        invertedOffsetModPow2EqualsTid);

                verifier.AddCandidateInvariant(wc, new VariableDualiser(1, verifier.uniformityAnalyser, impl.Name).VisitExpr(candidateInvariantExpr.Clone() as Expr));

                if (accessKind.Equals("WRITE") || !CommandLineOptions.Symmetry)
                {
                    verifier.AddCandidateInvariant(wc, new VariableDualiser(2, verifier.uniformityAnalyser, impl.Name).VisitExpr(candidateInvariantExpr.Clone() as Expr));
                }

                return true;

            }
            return false;
        }

        private HashSet<Expr> GetExpressionsFromWhichVariableIsAssignedInLoop(StmtList stmts, Variable variable)
        {
            HashSet<Expr> result = new HashSet<Expr>();
            foreach (BigBlock bb in stmts.BigBlocks)
            {
                foreach (Expr e in GetExpressionsFromWhichVariableIsAssignedInLoop(bb, variable))
                {
                    result.Add(e);
                }
            }
            return result;
        }

        private HashSet<Expr> GetExpressionsFromWhichVariableIsAssignedInLoop(BigBlock bb, Variable variable)
        {
            HashSet<Expr> result = new HashSet<Expr>();
            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    if (assign.Lhss[0] is SimpleAssignLhs)
                    {
                        if (GPUVerifier.StripThreadIdentifier((assign.Lhss[0] as SimpleAssignLhs).AssignedVariable.Name).Equals(
                            GPUVerifier.StripThreadIdentifier(variable.Name)))
                        {
                            if (assign.Rhss[0] is NAryExpr && ((assign.Rhss[0] as NAryExpr).Fun is IfThenElse))
                            {
                                result.Add((assign.Rhss[0] as NAryExpr).Args[1]);
                            }
                            else
                            {
                                result.Add(assign.Rhss[0]);
                            }
                        }
                    }
                }
            }

            if (bb.ec is WhileCmd)
            {
                foreach (Expr e in GetExpressionsFromWhichVariableIsAssignedInLoop((bb.ec as WhileCmd).Body, variable))
                {
                    result.Add(e);
                }
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd ifCmd = bb.ec as IfCmd;

                foreach (Expr e in GetExpressionsFromWhichVariableIsAssignedInLoop(ifCmd.thn, variable))
                {
                    result.Add(e);
                }

                Debug.Assert(ifCmd.elseIf == null);

                if (ifCmd.elseBlock != null)
                {
                    foreach (Expr e in GetExpressionsFromWhichVariableIsAssignedInLoop(ifCmd.elseBlock, variable))
                    {
                        result.Add(e);
                    }
                }

            }

            return result;
        }

        private Expr InverseOfLinearFunctionOfVariable(Expr e, string v, Expr offsetExpr)
        {
            if (e is IdentifierExpr)
            {
                if (GPUVerifier.StripThreadIdentifier((e as IdentifierExpr).Name).Equals(
                    v))
                {
                    return offsetExpr;
                }
                return e;
            }

            if (e is NAryExpr)
            {
                NAryExpr nary = e as NAryExpr;
                if (nary.Fun.FunctionName.Equals("BV32_ADD"))
                {
                    if (DoesNotReferTo(nary.Args[0], v))
                    {
                        return GPUVerifier.MakeBitVectorBinaryBitVector("BV32_SUB",
                            InverseOfLinearFunctionOfVariable(nary.Args[1], v, offsetExpr),
                            nary.Args[0]);
                    }
                    else
                    {
                        Debug.Assert(DoesNotReferTo(nary.Args[1], v));
                        return GPUVerifier.MakeBitVectorBinaryBitVector("BV32_SUB",
                            InverseOfLinearFunctionOfVariable(nary.Args[0], v, offsetExpr),
                            nary.Args[1]);
                    }
                }
            }

            Debug.Assert(false);

            return null;
        }

        private Expr ExprModPow2EqualsTid(Expr expr, Expr powerOfTwoExpr)
        {
            Expr Pow2Minus1 = GPUVerifier.MakeBitVectorBinaryBitVector("BV32_SUB", powerOfTwoExpr, 
                            new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 32));

            Expr Pow2Minus1BitAndExpr =
                GPUVerifier.MakeBitVectorBinaryBitVector("BV32_AND", Pow2Minus1, expr);

            return Expr.Eq(Pow2Minus1BitAndExpr, new IdentifierExpr(Token.NoToken, GPUVerifier._X));

        }

        private bool IsLinearFunctionOfVariable(Expr e, string v)
        {
            // e is v
            if (e is IdentifierExpr)
            {
                return GPUVerifier.StripThreadIdentifier((e as IdentifierExpr).Name).Equals(v);
            }

            // e is v + f /* f only contains constants or literals */
            if (e is NAryExpr)
            {
                NAryExpr nary = e as NAryExpr;
                if (nary.Fun.FunctionName.Equals("BV32_ADD"))
                {
                    if (IsLinearFunctionOfVariable(nary.Args[0], v)
                        && DoesNotReferTo(nary.Args[1], v))
                    {
                        return true;
                    }

                    if (IsLinearFunctionOfVariable(nary.Args[1], v)
                        && DoesNotReferTo(nary.Args[0], v))
                    {
                        return true;
                    }
                }
            }

            // We can handle further cases if they prove useful

            return false;
        }

        private bool DoesNotReferTo(Expr expr, string v)
        {
            FindReferencesToNamedVariableVisitor visitor = new FindReferencesToNamedVariableVisitor(v);
            visitor.VisitExpr(expr);
            return !visitor.found;
        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(Implementation impl, WhileCmd wc, Variable v, string accessType)
        {
            foreach (Expr e in GetOffsetsAccessed(wc.Body, v, accessType))
            {
                if (e is IdentifierExpr)
                {
                    string indexVarName =
                        GPUVerifier.StripThreadIdentifier((e as IdentifierExpr).Decl.Name);

                    if (verifier.mayBeTidAnalyser.MayBe("local_id_x", impl.Name, indexVarName))
                    {
                        AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(wc, v, accessType, 1);
                        if (accessType.Equals("WRITE") || !CommandLineOptions.Symmetry)
                        {
                            AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(wc, v, accessType, 2);
                        }
                        // No point adding it multiple times
                        break;
                    }
                }
            }

        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Procedure Proc, Variable v)
        {
            AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v, "WRITE", 1);
            AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v, "WRITE", 2);
            AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v, "READ", 1);
            if (!CommandLineOptions.Symmetry)
            {
                AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v, "READ", 2);
            }
        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Procedure Proc, Variable v)
        {
            AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v, "WRITE", 1);
            AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v, "WRITE", 2);
            AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v, "READ", 1);
            if (!CommandLineOptions.Symmetry)
            {
                AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v, "READ", 2);
            }
        }

        protected abstract void AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, int Thread);

        protected abstract void AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread);

        protected abstract void AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread);

        public void AddKernelPrecondition()
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddRequiresNoPendingAccess(v);
            }
        }
        public bool AddRaceCheckingInstrumentation()
        {

            if (onlyLog1 != -1)
            {
                addedLogWrite = false;
                failedToFindSecondAccess = true;
            }
            else
            {
                addedLogWrite = true;
                failedToFindSecondAccess = false;
            }

            foreach (Declaration d in verifier.Program.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    AddRaceCheckCalls(d as Implementation);
                }
            }

            if (failedToFindSecondAccess || !addedLogWrite)
                return false;

            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddRaceCheckingDecsAndProcsForVar(v);
            }

            return true;

        }

        private void AddRaceCheckingDecsAndProcsForVar(Variable v)
        {
            IdentifierExprSeq ReadDeclsResetAtBarrier;
            IdentifierExprSeq WriteDeclsResetAtBarrier;
            IdentifierExprSeq ReadDeclsModifiedAtLogRead;
            IdentifierExprSeq WriteDeclsModifiedAtLogWrite;
                
            AddLogRaceDeclarations(v, "READ", out ReadDeclsResetAtBarrier, out ReadDeclsModifiedAtLogRead);
            AddLogRaceDeclarations(v, "WRITE", out WriteDeclsResetAtBarrier, out WriteDeclsModifiedAtLogWrite);
            AddLogAccessProcedure(v, "READ");
            AddLogAccessProcedure(v, "WRITE");

        }
        
        private StmtList AddRaceCheckCalls(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(AddRaceCheckCalls(bodyBlock));
            }
            return result;
        }

        private void AddRaceCheckCalls(Implementation impl)
        {
            impl.StructuredStmts = AddRaceCheckCalls(impl.StructuredStmts);
        }

        private bool shouldAddLogCallAndIncr()
        {
            Contract.Assert(onlyLog1 >= -1);
            int oldLogAddCount = logAddCount;
            ++logAddCount;

            if (onlyLog1 == -1)
            {
                return true;
            }

            if(onlyLog1 + onlyLog2 == oldLogAddCount)
            {
                failedToFindSecondAccess = false;
                return true;
            }

            if (onlyLog1 == oldLogAddCount)
            {
                return true;
            }

            return false;
        }

        private BigBlock AddRaceCheckCalls(BigBlock bb)
        {
            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            foreach (Cmd c in bb.simpleCmds)
            {
                result.simpleCmds.Add(c);
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    Debug.Assert(assign.Lhss.Count == 1);
                    Debug.Assert(assign.Rhss.Count == 1);
                    AssignLhs lhs = assign.Lhss[0];
                    Expr rhs = assign.Rhss[0];

                    ReadCollector rc = new ReadCollector(NonLocalStateToCheck);
                    rc.Visit(rhs);
                    if (rc.accesses.Count > 0)
                    {
                        Debug.Assert(rc.accesses.Count == 1);
                        AccessRecord ar = rc.accesses[0];

                        if (shouldAddLogCallAndIncr())
                        {

                            ExprSeq inParams = new ExprSeq();
                            if (ar.IndexZ != null)
                            {
                                inParams.Add(ar.IndexZ);
                            }
                            if (ar.IndexY != null)
                            {
                                inParams.Add(ar.IndexY);
                            }
                            if (ar.IndexX != null)
                            {
                                inParams.Add(ar.IndexX);
                            }

                            Procedure logProcedure = GetLogAccessProcedure(c.tok, "_LOG_READ_" + ar.v.Name);

                            CallCmd logAccessCallCmd = new CallCmd(c.tok, logProcedure.Name, inParams, new IdentifierExprSeq());

                            logAccessCallCmd.Proc = logProcedure;

                            result.simpleCmds.Add(logAccessCallCmd);
                            
                        }
                    }

                    WriteCollector wc = new WriteCollector(NonLocalStateToCheck);
                    wc.Visit(lhs);
                    if (wc.GetAccess() != null)
                    {
                        AccessRecord ar = wc.GetAccess();

                        if (shouldAddLogCallAndIncr())
                        {

                            ExprSeq inParams = new ExprSeq();
                            if (ar.IndexZ != null)
                            {
                                inParams.Add(ar.IndexZ);
                            }
                            if (ar.IndexY != null)
                            {
                                inParams.Add(ar.IndexY);
                            }
                            if (ar.IndexX != null)
                            {
                                inParams.Add(ar.IndexX);
                            }

                            Procedure logProcedure = GetLogAccessProcedure(c.tok, "_LOG_WRITE_" + ar.v.Name);

                            CallCmd logAccessCallCmd = new CallCmd(c.tok, logProcedure.Name, inParams, new IdentifierExprSeq());

                            logAccessCallCmd.Proc = logProcedure;

                            result.simpleCmds.Add(logAccessCallCmd);
                            
                            addedLogWrite = true;
                            
                        }
                    }



                }
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, 
                        WhileCommand.Invariants, AddRaceCheckCalls(WhileCommand.Body));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null); // We don't handle else if yet
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, AddRaceCheckCalls(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? AddRaceCheckCalls(IfCommand.elseBlock) : null);
            }
            else if (bb.ec is BreakCmd)
            {
                result.ec = bb.ec;
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }

        private Procedure GetLogAccessProcedure(IToken tok, string name)
        {
            if (logAccessProcedures.ContainsKey(name))
            {
                return logAccessProcedures[name];
            }
            Procedure newProcedure = new Procedure(tok, name, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
            logAccessProcedures[name] = newProcedure;
            return newProcedure;
        }


        protected abstract void AddLogRaceDeclarations(Variable v, String ReadOrWrite, out IdentifierExprSeq ResetAtBarrier, out IdentifierExprSeq ModifiedAtLog);

        protected abstract void AddLogAccessProcedure(Variable v, string ReadOrWrite);


        public BigBlock MakeRaceCheckingStatements(IToken tok)
        {
            BigBlock checkForRaces = new BigBlock(tok, "__CheckForRaces", new CmdSeq(), null, null);
            if (!CommandLineOptions.Eager)
            {
                foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
                {
                    CheckForRaces(checkForRaces, v, false);
                }
            }

            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                SetNoAccessOccurred(tok, checkForRaces, v);
            }
            return checkForRaces;
        }

        private void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v)
        {
            SetNoAccessOccurred(tok, bb, v, "READ");
            SetNoAccessOccurred(tok, bb, v, "WRITE");
        }

        protected abstract void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v, string AccessType);

        public abstract void CheckForRaces(BigBlock bb, Variable v, bool ReadWriteOnly);

        protected void MakeLogAccessProcedureHeader(Variable v, string ReadOrWrite, out Variable XParameterVariable, out Variable YParameterVariable, out Variable ZParameterVariable, out Procedure LogReadOrWriteProcedure)
        {
            VariableSeq inParams = new VariableSeq();
            XParameterVariable = null;
            YParameterVariable = null;
            ZParameterVariable = null;

            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);

                XParameterVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "_X_index", mt.Arguments[0]));
                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(GPUVerifier.IsIntOrBv32(mt2.Arguments[0]));
                    YParameterVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "_Y_index", mt2.Arguments[0]));
                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(GPUVerifier.IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));
                        ZParameterVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "_Z_index", mt3.Arguments[0]));
                    }
                }
            }

            if (ZParameterVariable != null)
            {
                inParams.Add(ZParameterVariable);
            }

            if (YParameterVariable != null)
            {
                inParams.Add(YParameterVariable);
            }

            if (XParameterVariable != null)
            {
                inParams.Add(XParameterVariable);
            }

            string LogProcedureName = "_LOG_" + ReadOrWrite + "_" + v.Name;

            LogReadOrWriteProcedure = GetLogAccessProcedure(v.tok, LogProcedureName);

            LogReadOrWriteProcedure.InParams = inParams;

            if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
            {
                verifier.HalfDualisedProcedureNames.Add(LogReadOrWriteProcedure.Name);
            }

            LogReadOrWriteProcedure.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

        }

        public void AddRaceCheckingCandidateRequires(Procedure Proc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateRequires(Proc, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v);
            }
        }

        public void AddRaceCheckingCandidateEnsures(Procedure Proc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateEnsures(Proc, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v);
            }
        }

        private void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateRequires(Proc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        private void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateEnsures(Proc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        protected abstract Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwo);


        public void AddNoRaceContract(Procedure proc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                proc.Requires.Add(new Requires(false, Expr.Not(GenerateRaceCondition(v, "WRITE", "WRITE"))));
                proc.Requires.Add(new Requires(false, Expr.Not(GenerateRaceCondition(v, "READ", "WRITE"))));
                if (!CommandLineOptions.Symmetry)
                {
                    proc.Requires.Add(new Requires(false, Expr.Not(GenerateRaceCondition(v, "WRITE", "READ"))));
                }

                proc.Ensures.Add(new Ensures(false, Expr.Not(GenerateRaceCondition(v, "WRITE", "WRITE"))));
                proc.Ensures.Add(new Ensures(false, Expr.Not(GenerateRaceCondition(v, "READ", "WRITE"))));
                if (!CommandLineOptions.Symmetry)
                {
                    proc.Ensures.Add(new Ensures(false, Expr.Not(GenerateRaceCondition(v, "WRITE", "READ"))));
                }
            
            }
        }

        public void AddNoRaceInvariants(Implementation impl)
        {
            AddNoRaceInvariants(impl.StructuredStmts);
        }

        private void AddNoRaceInvariants(StmtList stmtList)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                AddNoRaceInvariants(bb);
            }
        }

        private void AddNoRaceInvariants(BigBlock bb)
        {
            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;
                foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
                {
                    wc.Invariants.Add(new AssertCmd(v.tok, Expr.Not(GenerateRaceCondition(v, "WRITE", "WRITE"))));
                    wc.Invariants.Add(new AssertCmd(v.tok, Expr.Not(GenerateRaceCondition(v, "READ", "WRITE"))));
                    if (!CommandLineOptions.Symmetry)
                    {
                        wc.Invariants.Add(new AssertCmd(v.tok, Expr.Not(GenerateRaceCondition(v, "WRITE", "READ"))));
                    }
                }

                AddNoRaceInvariants(wc.Body);

            }
            else if (bb.ec is IfCmd)
            {
                AddNoRaceInvariants((bb.ec as IfCmd).thn);
                if ((bb.ec as IfCmd).elseBlock != null)
                {
                    AddNoRaceInvariants((bb.ec as IfCmd).elseBlock);
                }
            }
            else if (bb.ec is BreakCmd)
            {
                // Do nothing
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }
        }


        protected abstract Expr GenerateRaceCondition(Variable v, string FirstAccessType, string SecondAccessType);


        private HashSet<Expr> GetOffsetsAccessed(StmtList stmts, Variable v, string AccessType)
        {
            HashSet<Expr> result = new HashSet<Expr> ();
            foreach (BigBlock bb in stmts.BigBlocks)
            {
                foreach (Expr e in GetOffsetsAccessed(bb, v, AccessType))
                {
                    result.Add(e);
                }
            }
            return result;
        }

        private HashSet<Expr> GetOffsetsAccessed(BigBlock bb, Variable v, string AccessType)
        {
            HashSet<Expr> result = new HashSet<Expr>();

            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is CallCmd)
                {
                    CallCmd call = c as CallCmd;

                    if (call.callee == "_LOG_" + AccessType + "_" + v.Name)
                    {
                        // Ins[0] is thread 1's predicate,
                        // Ins[1] is the offset to be read
                        // Ins[1] has the form BV32_ADD(offset#construct...(P), offset)
                        // We are looking for the second parameter to this BV32_ADD
                        Expr offset = call.Ins[1];
                        Debug.Assert(offset is NAryExpr);
                        Debug.Assert((offset as NAryExpr).Fun.FunctionName == "BV32_ADD");
                        result.Add((offset as NAryExpr).Args[1]);
                    }

                }

            }

            if (bb.ec is WhileCmd)
            {
                HashSet<Expr> bodyResult = GetOffsetsAccessed((bb.ec as WhileCmd).Body, v, AccessType);
                foreach (Expr e in bodyResult)
                {
                    result.Add(e);
                }
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd ifCmd = bb.ec as IfCmd;

                HashSet<Expr> thenResult = GetOffsetsAccessed(ifCmd.thn, v, AccessType);
                foreach (Expr e in thenResult)
                {
                    result.Add(e);
                }

                Debug.Assert(ifCmd.elseIf == null);
                
                if(ifCmd.elseBlock != null)
                {
                    HashSet<Expr> elseResult = GetOffsetsAccessed(ifCmd.elseBlock, v, AccessType);
                    foreach (Expr e in elseResult)
                    {
                        result.Add(e);
                    }
                }
            }

            return result;
        }

    }


    class FindReferencesToNamedVariableVisitor : StandardVisitor
    {
        internal bool found = false;
        private string name;

        internal FindReferencesToNamedVariableVisitor(string name)
        {
            this.name = name;
        }

        public override Variable VisitVariable(Variable node)
        {
            if (GPUVerifier.StripThreadIdentifier(node.Name).Equals(name))
            {
                found = true;
            }
            return base.VisitVariable(node);
        }
    }

}
