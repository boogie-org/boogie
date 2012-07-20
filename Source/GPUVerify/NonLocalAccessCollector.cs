using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;


namespace GPUVerify
{
    class NonLocalAccessCollector : StandardVisitor
    {
        public HashSet<Expr> Accesses = new HashSet<Expr>();

        private IKernelArrayInfo NonLocalState;

        public NonLocalAccessCollector(IKernelArrayInfo NonLocalState)
        {
            this.NonLocalState = NonLocalState;
        }

        public static bool IsNonLocalAccess(Expr n, IKernelArrayInfo NonLocalState)
        {
            if (n is NAryExpr)
            {
                NAryExpr node = n as NAryExpr;
                if (node.Fun is MapSelect)
                {
                    Expr temp = node;
                    while (temp is NAryExpr && (temp as NAryExpr).Fun is MapSelect)
                    {
                        temp = (temp as NAryExpr).Args[0];
                    }
                    Debug.Assert(temp is IdentifierExpr);

                    Variable v = (temp as IdentifierExpr).Decl;

                    return (NonLocalState.Contains(v));
                }
            }

            if (n is IdentifierExpr)
            {
                IdentifierExpr node = n as IdentifierExpr;
                return NonLocalState.Contains(node.Decl);
            }

            return false;
        }

        public static bool ContainsNonLocalAccess(AssignLhs lhs, IKernelArrayInfo NonLocalState)
        {
            NonLocalAccessCollector collector = new NonLocalAccessCollector(NonLocalState);
            if (lhs is SimpleAssignLhs)
            {
                collector.VisitSimpleAssignLhs(lhs as SimpleAssignLhs);
            }
            else
            {
                Debug.Assert(lhs is MapAssignLhs);
                collector.VisitMapAssignLhs(lhs as MapAssignLhs);
            }
            return collector.Accesses.Count > 0;
        }

        public static bool ContainsNonLocalAccess(Expr rhs, IKernelArrayInfo NonLocalState)
        {
            NonLocalAccessCollector collector = new NonLocalAccessCollector(NonLocalState);
            collector.VisitExpr(rhs);
            return collector.Accesses.Count > 0;
        }


        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (IsNonLocalAccess(node, NonLocalState))
            {
                Accesses.Add(node);
                return node;
            }
            return base.VisitNAryExpr(node);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (IsNonLocalAccess(node, NonLocalState))
            {
                Accesses.Add(node);
                return node;
            }
            return base.VisitIdentifierExpr(node);
        }

    }
}
