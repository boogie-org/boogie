using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie
{
    public class Concurrency
    {
        public static void Transform(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker)
        {
            List<Declaration> originalDecls = new List<Declaration>();
            Program program = linearTypeChecker.program;
            foreach (var decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc != null && moverTypeChecker.procToActionInfo.ContainsKey(proc))
                {
                    originalDecls.Add(proc);
                    continue;
                }
                Implementation impl = decl as Implementation;
                if (impl != null && moverTypeChecker.procToActionInfo.ContainsKey(impl.Proc))
                {
                    originalDecls.Add(impl);
                }
            }

            List<Declaration> decls = new List<Declaration>();
            OwickiGries.AddCheckers(linearTypeChecker, moverTypeChecker, decls);
            if (!CommandLineOptions.Clo.TrustAtomicityTypes)
            {
                MoverCheck.AddCheckers(linearTypeChecker, moverTypeChecker, decls);
            }
            foreach (Declaration decl in decls)
            {
                decl.Attributes = OwickiGries.RemoveYieldsAttribute(decl.Attributes);
            }
            program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
            program.AddTopLevelDeclarations(decls);
        }

    }
}
