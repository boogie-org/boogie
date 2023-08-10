using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class YieldingProcChecker
  {
    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      Program program = civlTypeChecker.program;

      // Generate the refinement checks for every layer
      foreach (int layerNum in civlTypeChecker.AllRefinementLayers)
      {
        if (civlTypeChecker.Options.TrustLayersDownto <= layerNum ||
            layerNum <= civlTypeChecker.Options.TrustLayersUpto)
        {
          continue;
        }

        YieldingProcDuplicator duplicator = new YieldingProcDuplicator(civlTypeChecker, layerNum);

        foreach (var yieldProcedureDecl in civlTypeChecker.program.TopLevelDeclarations.OfType<YieldProcedureDecl>())
        {
          if (yieldProcedureDecl.Layer >= layerNum)
          {
            duplicator.VisitYieldProcedureDecl(yieldProcedureDecl);
          }
        }

        foreach (Implementation impl in program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
        {
          var yieldProcedureDecl = (YieldProcedureDecl)impl.Proc;
          if (yieldProcedureDecl.Layer >= layerNum)
          {
            duplicator.VisitImplementation(impl);
          }
        }

        decls.AddRange(duplicator.Collect());
      }
    }
  }
}