using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Diagnostics;

namespace GPUVerify
{




    class ReadCollector : AccessCollector
    {

        public List<AccessRecord> accesses = new List<AccessRecord>();

        public ReadCollector(IKernelArrayInfo NonLocalState)
            : base(NonLocalState)
        {
        }

        public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
        {
            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is MapSelect)
            {
                if ((node.Fun as MapSelect).Arity > 1)
                {
                    MultiDimensionalMapError();
                }

                Debug.Assert(node.Args[0] is IdentifierExpr);
                var ReadVariable = (node.Args[0] as IdentifierExpr).Decl;
                var Index = node.Args[1];
                this.VisitExpr(node.Args[1]);

                if (NonLocalState.Contains(ReadVariable))
                {
                    accesses.Add(new AccessRecord(ReadVariable, Index));
                }

                return node;
            }
            else
            {
                return base.VisitNAryExpr(node);
            }
        }


    }
}
