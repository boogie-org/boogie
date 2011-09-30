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
                return new IdentifierExpr(node.tok, new LocalVariable(node.tok, DualiseTypedIdent(node.Decl)));
            }

            if (GPUVerifier.IsThreadLocalIdConstant(node.Decl))
            {
                return new IdentifierExpr(node.tok, new Constant(node.tok, DualiseTypedIdent(node.Decl)));
            }

            return node;
        }

        private TypedIdent DualiseTypedIdent(Variable v)
        {
            return new TypedIdent(v.tok, v.Name + "$" + id, v.TypedIdent.Type);
        }

        public override Variable VisitVariable(Variable node)
        {
            if (!(node is Constant) || GPUVerifier.IsThreadLocalIdConstant(node))
            {
                node.TypedIdent = DualiseTypedIdent(node);
                node.Name = node.Name + "$" + id;
                return node;
            }

            return base.VisitVariable(node);
        }

    }

}
