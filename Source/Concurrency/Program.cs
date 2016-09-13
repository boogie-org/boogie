using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie
{
    public class Concurrency
    {
        public static void Transform(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker)
        {
            List<Declaration> originalDecls = new List<Declaration>();
            Program program = linearTypeChecker.program;
            foreach (var decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc != null && civlTypeChecker.procToActionInfo.ContainsKey(proc))
                {
                    originalDecls.Add(proc);
                    continue;
                }
                Implementation impl = decl as Implementation;
                if (impl != null && civlTypeChecker.procToActionInfo.ContainsKey(impl.Proc))
                {
                    originalDecls.Add(impl);
                }
            }

            List<Declaration> decls = new List<Declaration>();
            if (!CommandLineOptions.Clo.TrustAtomicityTypes)
            {
                MoverCheck.AddCheckers(linearTypeChecker, civlTypeChecker, decls);
            } 
            CivlRefinement.AddCheckers(linearTypeChecker, civlTypeChecker, decls);
            foreach (AtomicActionInfo info in civlTypeChecker.procToActionInfo.Values.Where(x => x is AtomicActionInfo))
            {
                decls.AddRange(info.triggerFuns.Values);
            }
            foreach (Declaration decl in decls)
            {
                decl.Attributes = RemoveYieldsAttribute(decl.Attributes);
            }
            program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
            program.AddTopLevelDeclarations(decls);
        }

        public static QKeyValue RemoveYieldsAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveYieldsAttribute(iter.Next);
            return (iter.Key == "yields") ? iter.Next : iter;
        }

        public static QKeyValue RemoveMoverAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveMoverAttribute(iter.Next);
            if (iter.Key == "atomic" || iter.Key == "right" || iter.Key == "left" || iter.Key == "both")
                return iter.Next;
            else
                return iter;
        }

        public static QKeyValue RemoveLayerAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveLayerAttribute(iter.Next);
            return (iter.Key == "layer") ? iter.Next : iter;
        }

        public static QKeyValue RemoveLinearAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveLinearAttribute(iter.Next);
            return (iter.Key == "linear" || iter.Key == "linear_in" || iter.Key == "linear_out") ? iter.Next : iter;
        }
    }
}
