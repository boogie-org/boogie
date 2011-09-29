using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

using System.Diagnostics;

namespace GPUVerify
{
    class VariableDualiser : Duplicator
    {
        private int id;

        public VariableDualiser(int id)
        {
            this.id = id;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (!(node.Decl is Constant))
            {
                return new IdentifierExpr(node.tok, new LocalVariable(node.tok, new TypedIdent(node.tok, node.Decl.Name + "$" + id, node.Decl.TypedIdent.Type)));
            }

            return node;
        }


        public override Variable VisitVariable(Variable node)
        {
            if (!(node is Constant))
            {
                node.TypedIdent = new TypedIdent(node.tok, node.Name + "$" + id, node.TypedIdent.Type);
                node.Name = node.Name + "$" + id;
                return node;
            }

            return base.VisitVariable(node);
        }


    }

}
