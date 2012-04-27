using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    class AsymmetricExpressionFinder : StandardVisitor
    {
        private bool found = false;

        internal bool foundAsymmetricExpr()
        {
            return found;
        }

        public override Variable VisitVariable(Variable node)
        {
            if (node.TypedIdent.Name.Contains("_READ_HAS_OCCURRED") ||
                node.TypedIdent.Name.Contains("_READ_OFFSET") ||
                node.TypedIdent.Name.Contains("_WRITE_HAS_OCCURRED") ||
                node.TypedIdent.Name.Contains("_WRITE_OFFSET"))
            {
                found = true;
            }
            return node;
        }

    }
}
