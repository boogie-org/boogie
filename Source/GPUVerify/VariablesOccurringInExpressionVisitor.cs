using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class VariablesOccurringInExpressionVisitor : StandardVisitor
    {
        private HashSet<Variable> variables = new HashSet<Variable>();

        internal IEnumerable<Microsoft.Boogie.Variable> GetVariables()
        {
            return variables;
        }

        public override Variable VisitVariable(Variable node)
        {
            variables.Add(node);
            return base.VisitVariable(node);
        }

    }
}
