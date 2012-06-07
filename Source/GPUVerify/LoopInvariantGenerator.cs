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

                AddCandidateInvariants(verifier.RootRegion(Impl), LocalVars, UserSuppliedInvariants, Impl);

        }

        private void AddEqualityCandidateInvariant(IRegion region, string LoopPredicate, Variable v)
        {
            verifier.AddCandidateInvariant(region,
                Expr.Eq(
                    new IdentifierExpr(Token.NoToken, new VariableDualiser(1, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(Token.NoToken, new VariableDualiser(2, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable))
            ), "equality");
        }

        private void AddPredicatedEqualityCandidateInvariant(IRegion region, string LoopPredicate, Variable v)
        {
            verifier.AddCandidateInvariant(region, Expr.Imp(
                Expr.And(
                    new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, LoopPredicate + "$1", Microsoft.Boogie.Type.Int))),
                    new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, LoopPredicate + "$2", Microsoft.Boogie.Type.Int)))
                ),
                Expr.Eq(
                    new IdentifierExpr(Token.NoToken, new VariableDualiser(1, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(Token.NoToken, new VariableDualiser(2, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable))
            )), "predicated equality");
        }


        private void AddBarrierDivergenceCandidates(HashSet<Variable> LocalVars, Implementation Impl, IRegion region)
        {

            if (CommandLineOptions.AddDivergenceCandidatesOnlyToBarrierLoops)
            {
                if (!verifier.ContainsBarrierCall(region))
                {
                    return;
                }
            }

            Expr guard = region.Guard();
            if (verifier.uniformityAnalyser.IsUniform(Impl.Name, guard))
            {
                return;
            }

            if (guard is NAryExpr &&
                (guard as NAryExpr).Args.Length == 2 &&
                (guard as NAryExpr).Args[0] is IdentifierExpr)
            {
                string LoopPredicate = ((guard as NAryExpr).Args[0] as IdentifierExpr).Name;

                LoopPredicate = LoopPredicate.Substring(0, LoopPredicate.IndexOf('$'));

                verifier.AddCandidateInvariant(region, Expr.Eq(
                    // Int type used here, but it doesn't matter as we will print and then re-parse the program
                    new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, LoopPredicate + "$1", Microsoft.Boogie.Type.Int))),
                    new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, LoopPredicate + "$2", Microsoft.Boogie.Type.Int)))
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
                        if (!verifier.ContainsNamedVariable(GetModifiedVariables(region),
                            GPUVerifier.StripThreadIdentifier(v.Name)))
                        {
                            continue;
                        }
                    }

                    AddEqualityCandidateInvariant(region, LoopPredicate, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, lv, Microsoft.Boogie.Type.Int)));

                    if (Impl != verifier.KernelImplementation)
                    {
                        AddPredicatedEqualityCandidateInvariant(region, LoopPredicate, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, lv, Microsoft.Boogie.Type.Int)));
                    }
                }

                if (CommandLineOptions.ArrayEqualities)
                {
                    foreach (Variable v in verifier.NonLocalState.getAllNonLocalVariables())
                    {
                        if (!verifier.ArrayModelledAdversarially(v))
                        {
                            AddEqualityCandidateInvariant(region, LoopPredicate, v);
                        }
                    }
                }
            }
        }

        private void AddCandidateInvariants(IRegion region, HashSet<Variable> LocalVars, List<Expr> UserSuppliedInvariants, Implementation Impl)
        {
            foreach (IRegion subregion in region.SubRegions())
            {
                foreach (InvariantGenerationRule r in invariantGenerationRules)
                {
                    r.GenerateCandidates(Impl, subregion);
                }

                AddBarrierDivergenceCandidates(LocalVars, Impl, subregion);

                verifier.RaceInstrumenter.AddRaceCheckingCandidateInvariants(Impl, subregion);

                AddUserSuppliedInvariants(subregion, UserSuppliedInvariants, Impl);
            }
        }

        private void AddUserSuppliedInvariants(IRegion region, List<Expr> UserSuppliedInvariants, Implementation Impl)
        {
            foreach (Expr e in UserSuppliedInvariants)
            {
              /*
                wc.Invariants.Add(new AssertCmd(wc.tok, e));
                bool OK = verifier.ProgramIsOK(Impl);
                wc.Invariants.RemoveAt(wc.Invariants.Count - 1);
                if (OK)
                {
                    verifier.AddCandidateInvariant(wc, e, "user supplied");
                }
              */
                verifier.AddCandidateInvariant(region, e, "user supplied");
            }
        }

        internal static HashSet<Variable> GetModifiedVariables(IRegion region)
        {
            HashSet<Variable> result = new HashSet<Variable>();

            foreach (Cmd c in region.Cmds())
            {
                VariableSeq vars = new VariableSeq();
                c.AddAssignedVariables(vars);
                foreach (Variable v in vars)
                {
                    result.Add(v);
                }
            }

            return result;
        }

    }
}
