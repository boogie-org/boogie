using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    class UniformExpressionAnalysisVisitor : StandardVisitor
    {

        private bool isUniform = true;
        private Dictionary<string, bool> uniformityInfo;

        public UniformExpressionAnalysisVisitor(Dictionary<string, bool> uniformityInfo)
        {
            this.uniformityInfo = uniformityInfo;
        }

        public override Variable VisitVariable(Variable v)
        {
            if (uniformityInfo.ContainsKey(v.Name))
            {
                if (!uniformityInfo[v.Name])
                {
                    isUniform = false;
                }
            }

            return v;
        }

        internal bool IsUniform()
        {
            return isUniform;
        }
    }
}
