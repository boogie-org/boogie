using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class NonLocalAccessExtractor : StandardVisitor
    {
        private int TempId;
        public AssignCmd Assignment = null;
        public LocalVariable Declaration = null;
        public bool done = false;

        private ICollection<Variable> GlobalVariables;
        private ICollection<Variable> TileStaticVariables;

        public NonLocalAccessExtractor(int TempId, ICollection<Variable> GlobalVariables, ICollection<Variable> TileStaticVariables)
        {
            this.TempId = TempId;
            this.GlobalVariables = GlobalVariables;
            this.TileStaticVariables = TileStaticVariables;
        }


        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (done)
            {
                return node;
            }

            if (!NonLocalAccessCollector.IsNonLocalAccess(node, GlobalVariables, TileStaticVariables))
            {
                return base.VisitNAryExpr(node);
            }

            Expr temp = node;
            while (temp is NAryExpr && (temp as NAryExpr).Fun is MapSelect)
            {
                Debug.Assert((temp as NAryExpr).Args.Length == 2);

                if (NonLocalAccessCollector.ContainsNonLocalAccess((temp as NAryExpr).Args[1], GlobalVariables, TileStaticVariables))
                {
                    return VisitExpr((temp as NAryExpr).Args[1]);
                }
                temp = (temp as NAryExpr).Args[0];
            }

            // If we get here, we've established that the node contains no non-local accessing sub-expressions
            Debug.Assert(temp is IdentifierExpr);
            done = true;

            Declaration = new LocalVariable(node.tok, new TypedIdent(node.tok, "_temp" + TempId, node.Type));

            SimpleAssignLhs lhs = new SimpleAssignLhs(node.tok, new IdentifierExpr(node.tok, Declaration));
            Expr rhs = node;

            List<AssignLhs> lhss = new List<AssignLhs>();
            lhss.Add(lhs);

            List<Expr> rhss = new List<Expr>();
            rhss.Add(rhs);

            Assignment = new AssignCmd(node.tok, lhss, rhss);

            return new IdentifierExpr(node.tok, Declaration);
        
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (done)
            {
                return node;
            }

            if (NonLocalAccessCollector.IsNonLocalAccess(node, GlobalVariables, TileStaticVariables))
            {
                done = true;
                Declaration = new LocalVariable(node.tok, new TypedIdent(node.tok, "_temp" + TempId, node.Decl.TypedIdent.Type));
                
                SimpleAssignLhs lhs = new SimpleAssignLhs(node.tok, new IdentifierExpr(node.tok, Declaration));
                Expr rhs = node;

                List<AssignLhs> lhss = new List<AssignLhs>();
                lhss.Add(lhs);

                List<Expr> rhss = new List<Expr>();
                rhss.Add(rhs);

                Assignment = new AssignCmd(node.tok, lhss, rhss);

                return new IdentifierExpr(node.tok, Declaration);
            }
            return base.VisitIdentifierExpr(node);
        }


    }
}
