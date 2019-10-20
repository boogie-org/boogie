using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    public class YieldingProcChecker
    {
        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            Program program = linearTypeChecker.program;

            // Skip procedures do not completely disappear (because of output parameters).
            // We create dummy implementations with empty body.
            Dictionary<Procedure, Procedure> procToSkipProcDummy = new Dictionary<Procedure, Procedure>();
            foreach(SkipProc skipProc in civlTypeChecker.procToYieldingProc.Values.OfType<SkipProc>())
            {
                Procedure proc = (Procedure)skipProc.proc.Clone();
                proc.Name = $"skip_dummy_{proc.Name}";
                proc.Requires = new List<Requires>();
                proc.Ensures = new List<Ensures>();
                proc.Modifies = new List<IdentifierExpr>();
                Block newInitBlock = new Block(Token.NoToken, "_init", new List<Cmd>(), new ReturnCmd(Token.NoToken));
                List<Block> newBlocks = new List<Block> { newInitBlock };
                Implementation impl = new Implementation(Token.NoToken, proc.Name, proc.TypeParameters, proc.InParams, proc.OutParams, new List<Variable>(), newBlocks);
                impl.Proc = proc;
                CivlUtil.AddInlineAttribute(proc);
                CivlUtil.AddInlineAttribute(impl);
                decls.Add(proc);
                decls.Add(impl);
                procToSkipProcDummy.Add(skipProc.proc, proc);
            }

            // Generate the refinement checks for every layer
            foreach (int layerNum in civlTypeChecker.allRefinementLayers)
            {
                if (CommandLineOptions.Clo.TrustLayersDownto <= layerNum || layerNum <= CommandLineOptions.Clo.TrustLayersUpto) continue;

                YieldingProcDuplicator duplicator = new YieldingProcDuplicator(civlTypeChecker, linearTypeChecker, layerNum, procToSkipProcDummy);

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
