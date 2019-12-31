using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    public class YieldingProcChecker
    {
        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            Program program = linearTypeChecker.program;

            // Generate the refinement checks for every layer
            foreach (int layerNum in civlTypeChecker.allRefinementLayers)
            {
                if (CommandLineOptions.Clo.TrustLayersDownto <= layerNum || layerNum <= CommandLineOptions.Clo.TrustLayersUpto) continue;

                YieldingProcDuplicator duplicator = new YieldingProcDuplicator(civlTypeChecker, linearTypeChecker, layerNum);

                // We can not simply call VisitProgram, because it does some resolving of calls
                // that is not necessary here (and actually fails).
                foreach (Procedure proc in program.Procedures)
                {
                    duplicator.VisitProcedure(proc);
                }
                foreach (Implementation impl in program.Implementations)
                {
                    duplicator.VisitImplementation(impl);
                }
                decls.AddRange(duplicator.Collect());
            }
        }
    }
}
