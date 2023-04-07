using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class YieldingProcChecker
  {
    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      Program program = civlTypeChecker.program;

      // Generate the refinement checks for every layer
      foreach (int layerNum in civlTypeChecker.allRefinementLayers)
      {
        if (civlTypeChecker.Options.TrustLayersDownto <= layerNum ||
            layerNum <= civlTypeChecker.Options.TrustLayersUpto)
        {
          continue;
        }

        YieldingProcDuplicator duplicator = new YieldingProcDuplicator(civlTypeChecker, layerNum);

        foreach (var procToYieldingProc in civlTypeChecker.procToYieldingProc)
        {
          if (procToYieldingProc.Value.Layer >= layerNum)
          {
            duplicator.VisitProcedure(procToYieldingProc.Key);
          }
        }

        foreach (Implementation impl in program.Implementations)
        {
          if (civlTypeChecker.procToYieldingProc.TryGetValue(impl.Proc, out var yieldingProc) &&
              yieldingProc.Layer >= layerNum)
          {
            duplicator.VisitImplementation(impl);
          }
        }

        decls.AddRange(duplicator.Collect());
      }
    }
  }
}