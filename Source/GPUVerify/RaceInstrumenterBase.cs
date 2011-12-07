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
            AddNoReadOrWriteCandidateInvariant(wc, v, "READ", "1");
            AddNoReadOrWriteCandidateInvariant(wc, v, "WRITE", "1");
            if (!CommandLineOptions.Symmetry)
            {
                AddNoReadOrWriteCandidateInvariant(wc, v, "READ", "2");
            }
            AddNoReadOrWriteCandidateInvariant(wc, v, "WRITE", "2");
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

        public void AddRaceCheckingCandidateInvariants(WhileCmd wc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateInvariants(wc, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(wc, v);
            }
        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(WhileCmd wc, Variable v)
        {
            AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(wc, v, "WRITE", 1);
            AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(wc, v, "WRITE", 2);
            AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(wc, v, "READ", 1);
            if (!CommandLineOptions.Symmetry)
            {
                AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(wc, v, "READ", 2);
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

            HashSet<string> MayCallBarrier = verifier.GetProceduresThatIndirectlyCallProcedure(verifier.BarrierProcedure.Name);

            verifier.ExtendModifiesSetOfProcedures(ReadDeclsResetAtBarrier, MayCallBarrier);
            verifier.ExtendModifiesSetOfProcedures(WriteDeclsResetAtBarrier, MayCallBarrier);

            HashSet<string> MayCallLogRead = verifier.GetProceduresThatIndirectlyCallProcedure("_LOG_READ_" + v.Name);
            HashSet<string> MayCallLogWrite = verifier.GetProceduresThatIndirectlyCallProcedure("_LOG_WRITE_" + v.Name);

            verifier.ExtendModifiesSetOfProcedures(ReadDeclsModifiedAtLogRead, MayCallLogRead);
            verifier.ExtendModifiesSetOfProcedures(WriteDeclsModifiedAtLogWrite, MayCallLogWrite);

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

                            result.simpleCmds.Add(new CallCmd(c.tok, "_LOG_READ_" + ar.v.Name, inParams, new IdentifierExprSeq()));
                            
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

                            result.simpleCmds.Add(new CallCmd(c.tok, "_LOG_WRITE_" + ar.v.Name, inParams, new IdentifierExprSeq()));
                            addedLogWrite = true;
                            
                        }
                    }



                }
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, AddRaceCheckCalls(WhileCommand.Body));
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


        protected abstract void AddLogRaceDeclarations(Variable v, String ReadOrWrite, out IdentifierExprSeq ResetAtBarrier, out IdentifierExprSeq ModifiedAtLog);

        protected abstract void AddLogAccessProcedure(Variable v, string ReadOrWrite);


        public BigBlock MakeRaceCheckingStatements(IToken tok)
        {
            BigBlock checkForRaces = new BigBlock(tok, "__CheckForRaces", new CmdSeq(), null, null);
            if (!CommandLineOptions.Eager)
            {
                foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
                {
                    CheckForRaces(tok, checkForRaces, v, false);
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

        public abstract void CheckForRaces(IToken tok, BigBlock bb, Variable v, bool ReadWriteOnly);

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
                Debug.Assert(GPUVerifier.IsIntOrBv32(mt.Arguments[0]));

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

            LogReadOrWriteProcedure = new Procedure(v.tok, "_LOG_" + ReadOrWrite + "_" + v.Name, new TypeVariableSeq(), inParams, new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());

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



    }
}
