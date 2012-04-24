using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Diagnostics;

using GPUVerify.InvariantGenerationRules;

namespace GPUVerify
{
    class LoopInvariantGenerator
    {
        private GPUVerifier verifier;
        private Implementation Impl;

        private List<InvariantGenerationRule> invariantGenerationRules;

        public LoopInvariantGenerator(GPUVerifier verifier, Implementation Impl)
        {
            this.verifier = verifier;
            this.Impl = Impl;

            invariantGenerationRules = new List<InvariantGenerationRule>();
            invariantGenerationRules.Add(new PowerOfTwoInvariantGenerator(verifier));
            invariantGenerationRules.Add(new LoopVariableBoundsInvariantGenerator(verifier));
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
            ), "equality");
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
            )), "predicated equality");
        }


        private void AddBarrierDivergenceCandidates(HashSet<Variable> LocalVars, Implementation Impl, WhileCmd wc)
        {

            if (CommandLineOptions.AddDivergenceCandidatesOnlyToBarrierLoops)
            {
                if (!verifier.ContainsBarrierCall(wc.Body))
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
            ), "loop predicate equality");

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

            if (CommandLineOptions.ArrayEqualities)
            {
                foreach (Variable v in verifier.NonLocalState.getAllNonLocalVariables())
                {
                    if (!verifier.ArrayModelledAdversarially(v))
                    {
                        AddEqualityCandidateInvariant(wc, LoopPredicate, v);
                    }
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

                foreach (InvariantGenerationRule r in invariantGenerationRules)
                {
                    r.GenerateCandidates(Impl, wc);
                }

                AddBarrierDivergenceCandidates(LocalVars, Impl, wc);

                verifier.RaceInstrumenter.AddRaceCheckingCandidateInvariants(Impl, wc);

                AddUserSuppliedInvariants(wc, UserSuppliedInvariants, Impl);

                AddCandidateInvariants(wc.Body, LocalVars, UserSuppliedInvariants, Impl);
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd ifCmd = bb.ec as IfCmd;
                AddCandidateInvariants(ifCmd.thn, LocalVars, UserSuppliedInvariants, Impl);
                if (ifCmd.elseBlock != null)
                {
                    AddCandidateInvariants(ifCmd.elseBlock, LocalVars, UserSuppliedInvariants, Impl);
                }

            }
            else
            {
                Debug.Assert(bb.ec == null);
            }
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
                    verifier.AddCandidateInvariant(wc, e, "user supplied");
                }
            }
        }

        internal static HashSet<Variable> GetModifiedVariables(StmtList stmtList)
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

        private static HashSet<Variable> GetModifiedVariables(BigBlock bb)
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

    }
}
