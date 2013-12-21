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
            // The order in which originalDecls are computed and then *.AddCheckers are called is 
            // apparently important.  The MyDuplicator code currently does not duplicate Attributes.
            // Consequently, all the yield attributes are eliminated by the AddCheckers code.

            List<Declaration> originalDecls = new List<Declaration>();
            Program program = linearTypeChecker.program;
            foreach (var decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc != null && QKeyValue.FindBoolAttribute(proc.Attributes, "yields"))
                {
                    originalDecls.Add(proc);
                    continue;
                }
                Implementation impl = decl as Implementation;
                if (impl != null && QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "yields"))
                {
                    originalDecls.Add(impl);
                }
            }

            List<Declaration> decls = new List<Declaration>();
            OwickiGries.AddCheckers(linearTypeChecker, moverTypeChecker, decls);
            MoverCheck.AddCheckers(linearTypeChecker, moverTypeChecker, decls);
            RefinementCheck.AddCheckers(linearTypeChecker, moverTypeChecker, decls);

            program.TopLevelDeclarations.RemoveAll(x => originalDecls.Contains(x));
            program.TopLevelDeclarations.AddRange(decls);
        }

    }
}
