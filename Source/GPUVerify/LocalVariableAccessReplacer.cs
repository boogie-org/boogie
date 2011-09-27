using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class LocalVariableAccessReplacer : StandardVisitor
    {

        GPUVerifierAsynchronous verifier;

        public LocalVariableAccessReplacer(GPUVerifierAsynchronous verifier)
        {
            this.verifier = verifier;
        }


        public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
        {
            if (verifier.GetThreadLocalVariables().Contains(node.AssignedVariable.Decl))
            {
                List<Expr> indexes = new List<Expr>();
                indexes.Add(verifier.MakeThreadIdExpr(node.tok));
                return new MapAssignLhs(node.tok, node, indexes);
            }
            return node;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (verifier.GetThreadLocalVariables().Contains(node.Decl))
            {
                ExprSeq MapNameAndThreadID = new ExprSeq();
                MapNameAndThreadID.Add(new IdentifierExpr(node.tok, node.Decl));
                MapNameAndThreadID.Add(verifier.MakeThreadIdExpr(node.tok));

                return new NAryExpr(node.tok, new MapSelect(node.tok, 1), MapNameAndThreadID);

            }

            return node;
        }


    }
}
