using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Diagnostics;

using GPUVerify.InvariantGenerationRules;

namespace GPUVerify {
  class LoopInvariantGenerator {
    private GPUVerifier verifier;
    private Implementation Impl;

    private List<InvariantGenerationRule> invariantGenerationRules;

    LoopInvariantGenerator(GPUVerifier verifier, Implementation Impl) {
      this.verifier = verifier;
      this.Impl = Impl;

      invariantGenerationRules = new List<InvariantGenerationRule>();
      invariantGenerationRules.Add(new PowerOfTwoInvariantGenerator(verifier));
      invariantGenerationRules.Add(new LoopVariableBoundsInvariantGenerator(verifier));
    }

    public static void PreInstrument(GPUVerifier verifier, Implementation impl) {
      foreach (var region in verifier.RootRegion(impl).SubRegions()) {
        GenerateCandidateForReducedStrengthStrideVariables(verifier, impl, region);
      }
    }

    private static void GenerateCandidateForReducedStrengthStrideVariables(GPUVerifier verifier, Implementation impl, IRegion region) {
      var rsa = verifier.reducedStrengthAnalyses[impl];
      foreach (string lc in rsa.StridedLoopCounters(region.Identifier())) {
        var sc = rsa.GetStrideConstraint(lc);
        Variable lcVariable = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, lc,
                Microsoft.Boogie.Type.GetBvType(32)));
        var lcExpr = new IdentifierExpr(Token.NoToken, lcVariable);
        var lcPred = sc.MaybeBuildPredicate(verifier, lcExpr);

        if (lcPred != null) {
          verifier.AddCandidateInvariant(region, lcPred, "variable " + lc + " is strided");
        }
      }
    }

    public static void PostInstrument(GPUVerifier verifier, Implementation Impl, List<Expr> UserSuppliedInvariants) {
      new LoopInvariantGenerator(verifier, Impl).PostInstrument(UserSuppliedInvariants);
    }

    internal void PostInstrument(List<Expr> UserSuppliedInvariants) {
      HashSet<Variable> LocalVars = new HashSet<Variable>();
      foreach (Variable v in Impl.LocVars) {
        LocalVars.Add(v);
      }
      foreach (Variable v in Impl.InParams) {
        LocalVars.Add(v);
      }
      foreach (Variable v in Impl.OutParams) {
        LocalVars.Add(v);
      }

      AddCandidateInvariants(verifier.RootRegion(Impl), LocalVars, UserSuppliedInvariants, Impl);

    }

    private void AddEqualityCandidateInvariant(IRegion region, string LoopPredicate, Variable v) {
      verifier.AddCandidateInvariant(region,
          Expr.Eq(
              new IdentifierExpr(Token.NoToken, new VariableDualiser(1, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable)),
              new IdentifierExpr(Token.NoToken, new VariableDualiser(2, verifier.uniformityAnalyser, Impl.Name).VisitVariable(v.Clone() as Variable))
      ), "equality");
    }

    private void AddPredicatedEqualityCandidateInvariant(IRegion region, string LoopPredicate, Variable v) {
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

    private Dictionary<string, int> GetAssignmentCounts(Implementation impl) {

      Dictionary<string, int> result = new Dictionary<string, int>();

      foreach (var c in verifier.RootRegion(impl).Cmds()) {
        if (c is AssignCmd) {
          var aCmd = (AssignCmd)c;
          HashSet<string> alreadySeenInThisAssignment = new HashSet<string>();
          foreach (var a in aCmd.Lhss) {
            if (a is SimpleAssignLhs) {
              var v = GPUVerifier.StripThreadIdentifier(
                ((SimpleAssignLhs)a).AssignedVariable.Name);
              if (!alreadySeenInThisAssignment.Contains(v)) {
                if (result.ContainsKey(v)) {
                  result[v]++;
                }
                else {
                  result[v] = 1;
                }
                alreadySeenInThisAssignment.Add(v);
              }
            }
          }
        }
      }
      return result;
    }


    private void AddBarrierDivergenceCandidates(HashSet<Variable> LocalVars, Implementation Impl, IRegion region)
      {

          if (!verifier.ContainsBarrierCall(region))
          {
              return;
          }

          Expr guard = region.Guard();
          if (guard != null && verifier.uniformityAnalyser.IsUniform(Impl.Name, guard))
          {
              return;
          }

          if (IsDisjunctionOfPredicates(guard))
          {
              string LoopPredicate = ((guard as NAryExpr).Args[0] as IdentifierExpr).Name;
              LoopPredicate = LoopPredicate.Substring(0, LoopPredicate.IndexOf('$'));

              verifier.AddCandidateInvariant(region, Expr.Eq(
                  // Int type used here, but it doesn't matter as we will print and then re-parse the program
                  new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, LoopPredicate + "$1", Microsoft.Boogie.Type.Int))),
                  new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, LoopPredicate + "$2", Microsoft.Boogie.Type.Int)))
              ), "loop predicate equality");

              Dictionary<string, int> assignmentCounts = GetAssignmentCounts(Impl);

              HashSet<string> alreadyConsidered = new HashSet<String>();  

              foreach (var v in LocalVars)
              {
                string lv = GPUVerifier.StripThreadIdentifier(v.Name);
                if (alreadyConsidered.Contains(lv)) {
                  continue;
                }
                alreadyConsidered.Add(lv);

                if (verifier.uniformityAnalyser.IsUniform(Impl.Name, v.Name))
                {
                    continue;
                }

                if (GPUVerifier.IsPredicate(lv))
                {
                    continue;
                }

                if (!assignmentCounts.ContainsKey(lv) || assignmentCounts[lv] <= 1) {
                  continue;
                }

                if (!verifier.ContainsNamedVariable(
                      GetModifiedVariables(region), lv))
                {
                    continue;
                }

                AddPredicatedEqualityCandidateInvariant(region, LoopPredicate, new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, lv, Microsoft.Boogie.Type.Int)));
              }

              if (CommandLineOptions.ArrayEqualities)
              {
                  foreach (Variable v in verifier.KernelArrayInfo.getAllNonLocalArrays())
                  {
                      if (!verifier.ArrayModelledAdversarially(v))
                      {
                          AddEqualityCandidateInvariant(region, LoopPredicate, v);
                      }
                  }
              }
          }
      }

    private static bool IsDisjunctionOfPredicates(Expr guard) {
      if (!(guard is NAryExpr)) {
        return false;
      }
      NAryExpr nary = (NAryExpr)guard;
      if(nary.Args.Length != 2) {
        return false;
      }
      if(!(nary.Fun is BinaryOperator)) {
        return false;
      }
      BinaryOperator binOp = (BinaryOperator)nary.Fun;
      if(binOp.Op != BinaryOperator.Opcode.Or) {
        return false;
      }
      if(!(nary.Args[0] is IdentifierExpr && nary.Args[1] is IdentifierExpr)) {
        return false;
      }
      return GPUVerifier.IsPredicate(GPUVerifier.StripThreadIdentifier(
                ((IdentifierExpr)nary.Args[0]).Name)) &&
             GPUVerifier.IsPredicate(GPUVerifier.StripThreadIdentifier(
                ((IdentifierExpr)nary.Args[1]).Name));
    }

    private void AddCandidateInvariants(IRegion region, HashSet<Variable> LocalVars, List<Expr> UserSuppliedInvariants, Implementation Impl) {
      foreach (IRegion subregion in region.SubRegions()) {
        foreach (InvariantGenerationRule r in invariantGenerationRules) {
          r.GenerateCandidates(Impl, subregion);
        }

        AddBarrierDivergenceCandidates(LocalVars, Impl, subregion);

        verifier.RaceInstrumenter.AddRaceCheckingCandidateInvariants(Impl, subregion);

        AddUserSuppliedInvariants(subregion, UserSuppliedInvariants, Impl);
      }
    }

    private void AddUserSuppliedInvariants(IRegion region, List<Expr> UserSuppliedInvariants, Implementation Impl) {
      foreach (Expr e in UserSuppliedInvariants) {
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

    internal static HashSet<Variable> GetModifiedVariables(IRegion region) {
      HashSet<Variable> result = new HashSet<Variable>();

      foreach (Cmd c in region.Cmds()) {
        VariableSeq vars = new VariableSeq();
        c.AddAssignedVariables(vars);
        foreach (Variable v in vars) {
          result.Add(v);
        }
      }

      return result;
    }

  }
}
