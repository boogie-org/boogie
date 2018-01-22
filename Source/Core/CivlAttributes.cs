using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Boogie
{
    public static class CivlAttributes
    {
        public const string LAYER = "layer";

        public const string YIELDS = "yields";
        public const string YIELD_ASSERT = "yield_assert";

        public const string ATOMIC = "atomic";
        public const string LEFT = "left";
        public const string RIGHT = "right";
        public const string BOTH = "both";

        public static string REFINES = "refines";

        public const string TERMINATES = "terminates";

        public const string LINEAR = "linear";
        public const string LINEAR_IN = "linear_in";
        public const string LINEAR_OUT = "linear_out";

        public const string PURE = "pure";

        public static bool RemoveAttribute(ICarriesAttributes obj, Func<QKeyValue, bool> cond)
        {
            QKeyValue curr = obj.Attributes;
            bool removed = false;

            while (curr != null && cond(curr))
            {
                curr = curr.Next;
                removed = true;
            }
            obj.Attributes = curr;
            while (curr != null)
            {
                QKeyValue next = curr.Next;
                while (next != null && cond(next))
                {
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
            RemoveAttribute(obj, kv => kv.Key == YIELDS);
        }

        public static void RemoveMoverAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj,
                kv => kv.Key == ATOMIC || kv.Key == LEFT || kv.Key == RIGHT || kv.Key == BOTH);
        }

        public static void RemoveLayerAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj, kv => kv.Key == LAYER);
        }

        public static void RemoveLinearAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj,
                kv => kv.Key == LINEAR || kv.Key == LINEAR_IN || kv.Key == LINEAR_OUT);
        }

        public static void RemoveRefinesAttribute(ICarriesAttributes obj)
        {
            RemoveAttribute(obj, kv => kv.Key == REFINES);
        }

        public static void DesugarYieldAssert(Program program)
        {
            foreach (var proc in program.Procedures)
            {
                if (RemoveAttribute(proc, kv => kv.Key == YIELD_ASSERT))
                {
                    proc.AddAttribute(YIELDS);
                    foreach (var requires in proc.Requires)
                    {
                        var ensures = new Ensures(false, requires.Condition);
                        ensures.Attributes = requires.Attributes;
                        proc.Ensures.Add(ensures);
                    }
                }
            }

            foreach (var impl in program.Implementations)
            {
                RemoveAttribute(impl, kv => kv.Key == YIELD_ASSERT);
            }
        }
    }
}
