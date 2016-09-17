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
                RemoveYieldsAttribute(decl);
            }
            program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
            program.AddTopLevelDeclarations(decls);
        }

        public static bool RemoveAttribute(ICarriesAttributes obj, Func<QKeyValue, bool> cond)
        {
            QKeyValue curr = obj.Attributes;
            bool removed = false;

            while (curr != null && cond (curr)) {
                curr = curr.Next;
                removed = true;
            }
            obj.Attributes = curr;
            while (curr != null) {
                QKeyValue next = curr.Next;
                while (next != null && cond (next)) {
                    next = next.Next;
                    removed = true;
                }
                curr.Next = next;
                curr = next;
            }

            return removed;
        }

        public static void RemoveYieldsAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj, kv => kv.Key == "yields");
        }

        public static void RemoveMoverAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute (obj,
                kv => kv.Key == "atomic" || kv.Key == "right" || kv.Key == "left" || kv.Key == "both");
        }

        public static void RemoveLayerAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj, kv => kv.Key == "layer");
        }

        public static void RemoveLinearAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj, 
                kv => kv.Key == "linear" || kv.Key == "linear_in" || kv.Key == "linear_out");
        }

        public static void DesugarYieldAssert (Program program) {
            foreach (var proc in program.Procedures) {
                if (RemoveAttribute(proc, kv => kv.Key == "yield_assert")) {
                    proc.AddAttribute("yields");
                    foreach (var requires in proc.Requires) {
                        var ensures = new Ensures(false, requires.Condition);
                        ensures.Attributes = requires.Attributes;
                        proc.Ensures.Add(ensures);
                    }
                }
            }
        }
    }
}
