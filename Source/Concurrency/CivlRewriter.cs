using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class CivlRewriter
  {
    public static void AddPendingAsyncTypes(Program program)
    {
      var pendingAsyncProcs = program.TopLevelDeclarations.OfType<ActionDecl>()
        .Where(proc => proc.actionQualifier == ActionQualifier.Async).ToList();
      var datatypeTypeCtorDecls = pendingAsyncProcs.Select(CreatePendingAsyncType);
      program.AddTopLevelDeclarations(datatypeTypeCtorDecls);
    }

    private static DatatypeTypeCtorDecl CreatePendingAsyncType(Procedure proc)
    {
      var fields = proc.InParams.Select(v => new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type)).ToList();
      var datatypeTypeCtorDecl = new DatatypeTypeCtorDecl(proc.tok, proc.Name, new List<TypeVariable>(), null);
      datatypeTypeCtorDecl.AddConstructor(proc.tok, proc.Name, fields);
      return datatypeTypeCtorDecl;
    }

    public static void Transform(ConcurrencyOptions options, CivlTypeChecker civlTypeChecker)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      Program program = linearTypeChecker.program;

      // Store the original declarations of yielding procedures, which will be removed after desugaring below.
      var origProc = program.TopLevelDeclarations.OfType<Procedure>()
        .Where(p => civlTypeChecker.procToYieldingProc.ContainsKey(p));
      var origImpl = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(i => civlTypeChecker.procToYieldingProc.ContainsKey(i.Proc));
      List<Declaration> originalDecls = Enumerable.Union<Declaration>(origProc, origImpl).ToList();

      // Commutativity checks
      List<Declaration> decls = new List<Declaration>();
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

      foreach (var action in civlTypeChecker.AllAtomicActions)
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