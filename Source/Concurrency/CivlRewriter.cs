using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class CivlRewriter
  {
    public static void Transform(ConcurrencyOptions options, CivlTypeChecker civlTypeChecker)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      Program program = linearTypeChecker.program;

      // Store the original declarations that should be removed after desugaring below.
      var origActionDecls = program.TopLevelDeclarations.OfType<ActionDecl>();
      var origActionImpls = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(impl => impl.Proc is ActionDecl);
      var origYieldProcs = program.TopLevelDeclarations.OfType<YieldProcedureDecl>();
      var origYieldImpls = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(impl => impl.Proc is YieldProcedureDecl);
      var origYieldInvariants = program.TopLevelDeclarations.OfType<YieldInvariantDecl>();
      var originalDecls = origActionDecls.Union<Declaration>(origActionImpls).Union(origYieldProcs)
        .Union(origYieldImpls).Union(origYieldInvariants).ToHashSet();

      // Commutativity checks
      List<Declaration> decls = new List<Declaration>();
      civlTypeChecker.AtomicActions.Iter(x =>
      {
        decls.Add(x.Impl);
        decls.Add(x.Impl.Proc);
      });
      civlTypeChecker.InvariantActions.Iter(x =>
      {
        decls.Add(x.Impl);
        decls.Add(x.Impl.Proc);
      });

      if (!options.TrustMoverTypes)
      {
        MoverCheck.AddCheckers(civlTypeChecker, decls);
      }

      // Desugaring of yielding procedures
      YieldingProcChecker.AddCheckers(civlTypeChecker, decls);

      // Linear type checks
      LinearityChecker.AddCheckers(civlTypeChecker, decls);

      if (!options.TrustInductiveSequentialization)
      {
        InductiveSequentializationChecker.AddCheckers(civlTypeChecker, decls);
      }

      foreach (var action in civlTypeChecker.AtomicActions)
      {
        action.AddTriggerAssumes(program, options);
      }

      // Remove original declarations and add new checkers generated above
      program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
      program.AddTopLevelDeclarations(decls);
      
      linearTypeChecker.EraseLinearAnnotations();
    }
  }
}