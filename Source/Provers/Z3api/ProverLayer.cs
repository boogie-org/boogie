using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Diagnostics;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.Z3;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.Simplify;

using TypeAst = System.IntPtr;
using TermAst = System.IntPtr;
using ConstDeclAst = System.IntPtr;
using ConstAst = System.IntPtr;
using Value = System.IntPtr;
using PatternAst = System.IntPtr;

namespace Microsoft.Boogie.Z3
{
    public class Z3apiProcessTheoremProver : ApiProverInterface
    {
        public Z3apiProcessTheoremProver(Z3InstanceOptions opts, DeclFreeProverContext ctxt)
        {
            this.options = opts;
            this.context = (Z3apiProverContext) ctxt;
            this.numAxiomsPushed = 0;
        }

        private Z3InstanceOptions options;

        private Z3apiProverContext context;
        public override ProverContext Context
        {
            get { return context; }
        }

        public override VCExpressionGenerator VCExprGen
        {
            get { return context.ExprGen; }
        }

        private int numAxiomsPushed;

        public override void Close()
        {
            base.Close();
            context.CloseLog();
            context.z3.Dispose();
            context.config.Dispose();
        }

        public void PushAxiom(VCExpr axiom)
        {
            context.CreateBacktrackPoint();
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            context.AddAxiom(axiom, linOptions);
        }

        private void PushConjecture(VCExpr conjecture)
        {
            context.CreateBacktrackPoint();
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            context.AddConjecture(conjecture, linOptions);
        }

        public override void PushVCExpression(VCExpr vc)
        {
            PushAxiom(vc);
            numAxiomsPushed++;
        }

        public void CreateBacktrackPoint()
        {
            context.CreateBacktrackPoint();
        }

        public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            Push();
            context.AddAxiom(context.Axioms, linOptions);
            context.AddConjecture(vc, linOptions);
            outcome = context.Check(out z3LabelModels);
            Pop();
        }
  
        public override void Check()
        {
            outcome = context.Check(out z3LabelModels);
        }

        public override void CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore)
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            outcome = context.CheckAssumptions(assumptions, linOptions, out z3LabelModels, out unsatCore);
        }

        public override void Push()
        {
            context.CreateBacktrackPoint();
        }

        public override void Pop()
        {
            context.Backtrack();
        }

        public override void Assert(VCExpr vc, bool polarity)
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            if (polarity)
                context.AddAxiom(vc, linOptions);
            else
                context.AddConjecture(vc, linOptions);
        }

        public override void AssertAxioms()
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            context.AddAxiom(context.Axioms, linOptions);
        }

        // Number of axioms pushed since the last call to FlushAxioms
        public override int NumAxiomsPushed()
        {
            return numAxiomsPushed;
        }

        public override int FlushAxiomsToTheoremProver()
        {
            var ret = numAxiomsPushed;
            numAxiomsPushed = 0;
            return ret;
        }

        private Outcome outcome;
        private List<Z3ErrorModelAndLabels> z3LabelModels = new List<Z3ErrorModelAndLabels>();

        [NoDefaultContract]
        public override Outcome CheckOutcome(ErrorHandler handler)
        {
            if (outcome == Outcome.Invalid)
            {
                foreach (Z3ErrorModelAndLabels z3LabelModel in z3LabelModels)
                {
                    List<string> unprefixedLabels = RemovePrefixes(z3LabelModel.RelevantLabels);
                    handler.OnModel(unprefixedLabels, z3LabelModel.ErrorModel);
                }
            }
            return outcome;
        }

        private List<string> RemovePrefixes(List<string> labels)
        {
            List<string> result = new List<string>();
            foreach (string label in labels)
            {
                if (label.StartsWith("+"))
                {
                    result.Add(label.Substring(1));
                }
                else if (label.StartsWith("|"))
                {
                    result.Add(label.Substring(1));
                }
                else if (label.StartsWith("@"))
                {
                    result.Add(label.Substring(1));
                }
                else
                    throw new Exception("Unknown prefix in label " + label);
            }
            return result;
        }
    }
}

namespace Microsoft.Boogie.Z3api
{
    public class Factory : ProverFactory
    {
        public override object SpawnProver(ProverOptions options, object ctxt)
        {
            return new Z3apiProcessTheoremProver((Z3InstanceOptions) options, (Z3apiProverContext) ctxt);
        }

        public override object NewProverContext(ProverOptions opts)
        {
            if (CommandLineOptions.Clo.BracketIdsInVC < 0)
            {
                CommandLineOptions.Clo.BracketIdsInVC = 0;
            }

            VCExpressionGenerator gen = new VCExpressionGenerator();
            return new Z3apiProverContext((Z3InstanceOptions)opts, gen);
        }

        public override ProverOptions BlankProverOptions()
        {
            return new Z3InstanceOptions();
        }
    }
}