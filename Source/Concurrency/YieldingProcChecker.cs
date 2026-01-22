using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class YieldingProcChecker
  {
    public static void AddInvariantCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      Program program = civlTypeChecker.program;

      // Generate the invariant checks for every layer
      foreach (int layerNum in civlTypeChecker.AllRefinementLayers)
      {
        if (civlTypeChecker.Options.TrustLayersDownto <= layerNum ||
            layerNum <= civlTypeChecker.Options.TrustLayersUpto)
        {
          continue;
        }
        var duplicator = new YieldingProcDuplicator(civlTypeChecker, layerNum, false);
        foreach (var yieldProcedureDecl in civlTypeChecker.program.TopLevelDeclarations.OfType<YieldProcedureDecl>())
        {
          if (yieldProcedureDecl.Layer >= layerNum)
          {
            duplicator.VisitYieldProcedureDecl(yieldProcedureDecl);
          }
        }
        // duplicator.VisitImplementation may invoke the monomorphizer which may cause more instantiations to be generated
        // and added to program.TopLevelDeclarations; hence converting the enumeration to a new list.
        foreach (Implementation impl in program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl).ToList())
        {
          var yieldProcedureDecl = (YieldProcedureDecl)impl.Proc;
          if (yieldProcedureDecl.Layer > layerNum ||
              yieldProcedureDecl.Layer == layerNum && !yieldProcedureDecl.MoverType.HasValue)
          {
            duplicator.VisitImplementation(impl);
          }
        }
        decls.AddRange(duplicator.Collect());
      }
    }

    public static void AddRefinementCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
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
        var duplicator = new YieldingProcDuplicator(civlTypeChecker, layerNum, true);
        foreach (var yieldProcedureDecl in civlTypeChecker.program.TopLevelDeclarations.OfType<YieldProcedureDecl>())
        {
          if (yieldProcedureDecl.Layer == layerNum)
          {
            duplicator.VisitYieldProcedureDecl(yieldProcedureDecl);
          }
        }
        // duplicator.VisitImplementation may invoke the monomorphizer which may cause more instantiations to be generated
        // and added to program.TopLevelDeclarations; hence converting the enumeration to a new list.
        foreach (Implementation impl in program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl).ToList())
        {
          var yieldProcedureDecl = (YieldProcedureDecl)impl.Proc;
          if (yieldProcedureDecl.Layer == layerNum)
          {
            duplicator.VisitImplementation(impl);
          }
        }
        decls.AddRange(duplicator.Collect());
      }
    }
  }
}