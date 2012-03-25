using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Diagnostics;

namespace GPUVerify
{
    class LoopInvariantGenerator
    {
        private GPUVerifier verifier;
        private Implementation Impl;

        public LoopInvariantGenerator(GPUVerifier verifier, Implementation Impl)
        {
            this.verifier = verifier;
            this.Impl = Impl;
        }

        internal void instrument(List<Expr> UserSuppliedInvariants)
        {
                HashSet<Variable> LocalVars = new HashSet<Variable>();
                foreach (Variable v in Impl.LocVars)
                {
                    LocalVars.Add(v);
                }
                foreach (Variable v in Impl.InParams)
                {
                    LocalVars.Add(v);
                }
                foreach (Variable v in Impl.OutParams)
                {
                    LocalVars.Add(v);
                }

                AddCandidateInvariants(Impl.StructuredStmts, LocalVars, UserSuppliedInvariants, Impl);

        }

        private void AddEqualityCandidateInvariant(WhileCmd wc, string LoopPredicate, Variable v)
        {
            verifier.AddCandidateInvariant(wc,
                Expr.Eq(
                    new IdentifierExpr(wc.tok, new VariableDualiser(1, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(wc.tok, new VariableDualiser(2, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable))
            ));
        }

        private void AddPredicatedEqualityCandidateInvariant(WhileCmd wc, string LoopPredicate, Variable v)
        {
            verifier.AddCandidateInvariant(wc, Expr.Imp(
                Expr.And(
                    new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, LoopPredicate + "$1", Microsoft.Boogie.Type.Int))),
                    new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, LoopPredicate + "$2", Microsoft.Boogie.Type.Int)))
                ),
                Expr.Eq(
                    new IdentifierExpr(wc.tok, new VariableDualiser(1, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(wc.tok, new VariableDualiser(2, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable))
            )));
        }


        private void AddBarrierDivergenceCandidates(HashSet<Variable> LocalVars, Implementation Impl, WhileCmd wc)
        {

            if (CommandLineOptions.AddDivergenceCandidatesOnlyToBarrierLoops)
            {
                if (!ContainsBarrierCall(wc.Body))
                {
                    return;
                }
            }

            if (verifier.uniformityAnalyser.IsUniform(Impl.Name, wc.Guard))
            {
                return;
            }

            Debug.Assert(wc.Guard is NAryExpr);
            Debug.Assert((wc.Guard as NAryExpr).Args.Length == 2);
            Debug.Assert((wc.Guard as NAryExpr).Args[0] is IdentifierExpr);
            string LoopPredicate = ((wc.Guard as NAryExpr).Args[0] as IdentifierExpr).Name;

            LoopPredicate = LoopPredicate.Substring(0, LoopPredicate.IndexOf('$'));

            verifier.AddCandidateInvariant(wc, Expr.Eq(
                // Int type used here, but it doesn't matter as we will print and then re-parse the program
                new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, LoopPredicate + "$1", Microsoft.Boogie.Type.Int))),
                new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, LoopPredicate + "$2", Microsoft.Boogie.Type.Int)))
            ));

            foreach (Variable v in LocalVars)
            {

                if (verifier.uniformityAnalyser.IsUniform(Impl.Name, v.Name))
                {
                    continue;
                }

                string lv = GPUVerifier.StripThreadIdentifier(v.Name);

                if (GPUVerifier.IsPredicateOrTemp(lv))
                {
                    continue;
                }

                if (CommandLineOptions.AddDivergenceCandidatesOnlyIfModified)
                {
                    if (!verifier.ContainsNamedVariable(GetModifiedVariables(wc.Body), 
                        GPUVerifier.StripThreadIdentifier(v.Name)))
                    {
                        continue;
                    }
                }

                AddEqualityCandidateInvariant(wc, LoopPredicate, new LocalVariable(wc.tok, new TypedIdent(wc.tok, lv, Microsoft.Boogie.Type.Int)));

                if (Impl != verifier.KernelImplementation)
                {
                    AddPredicatedEqualityCandidateInvariant(wc, LoopPredicate, new LocalVariable(wc.tok, new TypedIdent(wc.tok, lv, Microsoft.Boogie.Type.Int)));
                }
            }

            if (!CommandLineOptions.FullAbstraction && CommandLineOptions.ArrayEqualities)
            {
                foreach (Variable v in verifier.NonLocalState.getAllNonLocalVariables())
                {
                    AddEqualityCandidateInvariant(wc, LoopPredicate, v);
                }
            }
        }

        private void AddCandidateInvariants(StmtList stmtList, HashSet<Variable> LocalVars, List<Expr> UserSuppliedInvariants, Implementation Impl)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                AddCandidateInvariants(bb, LocalVars, UserSuppliedInvariants, Impl);
            }
        }

        private void AddCandidateInvariants(BigBlock bb, HashSet<Variable> LocalVars, List<Expr> UserSuppliedInvariants, Implementation Impl)
        {
            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;

                AddBarrierDivergenceCandidates(LocalVars, Impl, wc);

                AddLoopVariableBoundsCandidateInvariants(Impl, wc);

                AddPowerOfTwoCandidateInvariants(Impl, wc);

                verifier.RaceInstrumenter.AddRaceCheckingCandidateInvariants(wc);

                AddUserSuppliedInvariants(wc, UserSuppliedInvariants, Impl);

                AddCandidateInvariants(wc.Body, LocalVars, UserSuppliedInvariants, Impl);
            }
            else if (bb.ec is IfCmd)
            {
                // We should have done predicated execution by now, so we won't have any if statements
                Debug.Assert(false);
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }
        }

        private void AddPowerOfTwoCandidateInvariants(Implementation Impl, WhileCmd wc)
        {
            foreach (Variable v in Impl.LocVars)
            {
                string basicName = GPUVerifier.StripThreadIdentifier(v.Name);
                if (verifier.uniformityAnalyser.IsUniform(Impl.Name, basicName))
                {
                    if (verifier.mayBePowerOfTwoAnalyser.MayBePowerOfTwo(Impl.Name, basicName))
                    {
                        if (verifier.ContainsNamedVariable(GetModifiedVariables(wc.Body), basicName))
                        {
                            verifier.AddCandidateInvariant(wc, MakePowerOfTwoExpr(v));
                            for (int i = (1 << 30); i > 0; i >>= 1)
                            {
                                verifier.AddCandidateInvariant(wc, 
                                    GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LT",
                                    new IdentifierExpr(v.tok, v),
                                    new LiteralExpr(v.tok, BigNum.FromInt(i), 32)));
                            }
                        }
                    }
                }
            }
        }

        private Expr MakePowerOfTwoExpr(Variable v)
        {
            Expr result = null;
            for (int i = 1 << 30; i > 0; i >>= 1)
            {
                Expr eq = Expr.Eq(new IdentifierExpr(v.tok, v), new LiteralExpr(v.tok, BigNum.FromInt(i), 32));
                result = (result == null ? eq : Expr.Or(eq, result));
            }

            return Expr.Or(Expr.Eq(new IdentifierExpr(v.tok, v), new LiteralExpr(v.tok, BigNum.FromInt(0), 32)), result);
        }

        private void AddLoopVariableBoundsCandidateInvariants(Implementation Impl, WhileCmd wc)
        {
            if (verifier.uniformityAnalyser.IsUniform(Impl.Name, wc.Guard))
            {
                VariablesOccurringInExpressionVisitor visitor = new VariablesOccurringInExpressionVisitor();
                visitor.VisitExpr(wc.Guard);
                foreach (Variable v in visitor.GetVariables())
                {
                    if (!verifier.ContainsNamedVariable(GetModifiedVariables(wc.Body), v.Name))
                    {
                        continue;
                    }

                    if (IsBVType (v.TypedIdent.Type))
                    {
                        int BVWidth = (v.TypedIdent.Type as BvType).Bits;

                        verifier.AddCandidateInvariant(wc,
                                GPUVerifier.MakeBitVectorBinaryBoolean("BV" + BVWidth + "_GEQ",
                                new IdentifierExpr(v.tok, v),
                                new LiteralExpr(v.tok, BigNum.FromInt(0), BVWidth)));
                    }
                }
            }
        }

        private bool IsBVType(Microsoft.Boogie.Type type)
        {
            return type.Equals(Microsoft.Boogie.Type.GetBvType(32))
                || type.Equals(Microsoft.Boogie.Type.GetBvType(16))
                || type.Equals(Microsoft.Boogie.Type.GetBvType(8));
        }

        private void AddUserSuppliedInvariants(WhileCmd wc, List<Expr> UserSuppliedInvariants, Implementation Impl)
        {
            foreach (Expr e in UserSuppliedInvariants)
            {
                wc.Invariants.Add(new AssertCmd(wc.tok, e));
                bool OK = verifier.ProgramIsOK(Impl);
                wc.Invariants.RemoveAt(wc.Invariants.Count - 1);
                if (OK)
                {
                    verifier.AddCandidateInvariant(wc, e);
                }
            }
        }

        private HashSet<Variable> GetModifiedVariables(StmtList stmtList)
        {
            HashSet<Variable> result = new HashSet<Variable>();

            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                HashSet<Variable> resultForBlock = GetModifiedVariables(bb);
                foreach (Variable v in resultForBlock)
                {
                    result.Add(v);
                }
            }

            return result;
        }

        private HashSet<Variable> GetModifiedVariables(BigBlock bb)
        {
            HashSet<Variable> result = new HashSet<Variable>();

            foreach (Cmd c in bb.simpleCmds)
            {
                VariableSeq vars = new VariableSeq();
                c.AddAssignedVariables(vars);
                foreach (Variable v in vars)
                {
                    result.Add(v);
                }
            }

            if (bb.ec is WhileCmd)
            {
                HashSet<Variable> modifiedByLoop = GetModifiedVariables((bb.ec as WhileCmd).Body);
                foreach (Variable v in modifiedByLoop)
                {
                    result.Add(v);
                }
            }
            else if (bb.ec is IfCmd)
            {
                HashSet<Variable> modifiedByThen = GetModifiedVariables((bb.ec as IfCmd).thn);
                foreach (Variable v in modifiedByThen)
                {
                    result.Add(v);
                }

                if ((bb.ec as IfCmd).elseBlock != null)
                {
                    HashSet<Variable> modifiedByElse = GetModifiedVariables((bb.ec as IfCmd).elseBlock);
                    foreach (Variable v in modifiedByElse)
                    {
                        result.Add(v);
                    }
                }

                Debug.Assert((bb.ec as IfCmd).elseIf == null);
            }

            return result;
        }

        private bool ContainsBarrierCall(StmtList stmtList)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                if (ContainsBarrierCall(bb))
                {
                    return true;
                }
            }
            return false;
        }

        private bool ContainsBarrierCall(BigBlock bb)
        {
            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is CallCmd && ((c as CallCmd).Proc == verifier.BarrierProcedure))
                {
                    return true;
                }
            }

            if (bb.ec is WhileCmd)
            {
                return ContainsBarrierCall((bb.ec as WhileCmd).Body);
            }

            Debug.Assert(bb.ec == null || bb.ec is BreakCmd);

            return false;
        }


    }
}
