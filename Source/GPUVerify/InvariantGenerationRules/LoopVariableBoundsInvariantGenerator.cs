using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify.InvariantGenerationRules
{
    class LoopVariableBoundsInvariantGenerator : InvariantGenerationRule
    {

        public LoopVariableBoundsInvariantGenerator(GPUVerifier verifier)
            : base(verifier)
        {

        }

        public override void GenerateCandidates(Implementation Impl, IRegion region)
        {
            if (verifier.uniformityAnalyser.IsUniform(Impl.Name, region.Guard()))
            {
                VariablesOccurringInExpressionVisitor visitor = new VariablesOccurringInExpressionVisitor();
                visitor.VisitExpr(region.Guard());
                foreach (Variable v in visitor.GetVariables())
                {
                    if (!verifier.ContainsNamedVariable(LoopInvariantGenerator.GetModifiedVariables(region), v.Name))
                    {
                        continue;
                    }

                    if (IsBVType (v.TypedIdent.Type))
                    {
                        int BVWidth = (v.TypedIdent.Type as BvType).Bits;

                        verifier.AddCandidateInvariant(region,
                                verifier.MakeBVSge(
                                new IdentifierExpr(v.tok, v),
                                new LiteralExpr(v.tok, BigNum.FromInt(0), BVWidth)), "loop guard variable non-negative");
                    }
                }
            }
        }

        private bool IsBVType(Microsoft.Boogie.Type type)
        {
            return type.Equals(Microsoft.Boogie.Type.GetBvType(32))
                || type.Equals(Microsoft.Boogie.Type.GetBvType(16))
                || type.Equals(Microsoft.Boogie.Type.GetBvType(8));
        }

    }
}
