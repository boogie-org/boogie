using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie
{
    public class CivlVCGeneration
    {
        public static void Transform(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker)
        {
            Program program = linearTypeChecker.program;

            // Store the original declarations of yielding procedures, which will be removed after desugaring below.
            var origProc = program.TopLevelDeclarations.OfType<Procedure>().Where(p => civlTypeChecker.procToActionInfo.ContainsKey(p));
            var origImpl = program.TopLevelDeclarations.OfType<Implementation>().Where(i => civlTypeChecker.procToActionInfo.ContainsKey(i.Proc));
            List<Declaration> originalDecls = Enumerable.Union<Declaration>(origProc, origImpl).ToList();

            // Commutativity checks
            List<Declaration> decls = new List<Declaration>();
            if (!CommandLineOptions.Clo.TrustAtomicityTypes)
            {
                MoverCheck.AddCheckers(linearTypeChecker, civlTypeChecker, decls);
            }

            // Desugaring of yielding procedures
            CivlRefinement.AddCheckers(linearTypeChecker, civlTypeChecker, decls);

            // Trigger functions for existential vairables in transition relations
            decls.AddRange(civlTypeChecker.procToActionInfo.Values.OfType<AtomicActionInfo>().SelectMany(a => a.triggerFuns.Values));
            
            // Remove original declarations and add new checkers generated above
            program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
            program.AddTopLevelDeclarations(decls);
        }
    }
}
