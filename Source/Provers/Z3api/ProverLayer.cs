using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Diagnostics;
using Microsoft.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.Z3;
using Microsoft.Z3;
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
            Z3SafeContext cm = context.cm;
            cm.z3.Dispose();
            cm.config.Config.Dispose();
            cm.CloseLog();
        }

        public void PushAxiom(VCExpr axiom)
        {
            Z3SafeContext cm = context.cm;
            cm.CreateBacktrackPoint();
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            cm.AddAxiom(axiom, linOptions);
            
        }

        private void PushConjecture(VCExpr conjecture)
        {
            Z3SafeContext cm = context.cm;
            cm.CreateBacktrackPoint();
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            cm.AddConjecture(conjecture, linOptions);
        }

        public override void PushVCExpression(VCExpr vc)
        {
            PushAxiom(vc);
            numAxiomsPushed++;
        }

        public void CreateBacktrackPoint()
        {
            Z3SafeContext cm = context.cm;
            cm.CreateBacktrackPoint();
        }

        public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            Z3SafeContext cm = context.cm;
            Push();
            cm.AddAxiom(context.Axioms, linOptions);
            cm.AddConjecture(vc, linOptions);
            outcome = cm.Check(out z3LabelModels);
            Pop();
        }
  
        public override void Check()
        {
            Z3SafeContext cm = context.cm;
            outcome = cm.Check(out z3LabelModels);
        }

        public override void CheckAssumptions(List<VCExpr> assumptions)
        {
            Z3SafeContext cm = context.cm;
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            outcome = cm.CheckAssumptions(assumptions, linOptions, out z3LabelModels);
        }

        public override void Push()
        {
            Z3SafeContext cm = context.cm;
            cm.CreateBacktrackPoint();
        }

        public override void Pop()
        {
            Z3SafeContext cm = context.cm;
            cm.Backtrack();
        }

        public override void Assert(VCExpr vc, bool polarity)
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            Z3SafeContext cm = context.cm;
            if (polarity)
                cm.AddAxiom(vc, linOptions);
            else
                cm.AddConjecture(vc, linOptions);
        }

        public override void AssertAxioms()
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            Z3SafeContext cm = context.cm;
            cm.AddAxiom(context.Axioms, linOptions);
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

    public class Z3apiProverContext : DeclFreeProverContext
    {
        public Z3SafeContext cm;
        
        public Z3apiProverContext(Z3InstanceOptions opts, VCExpressionGenerator gen)
            : base(gen, new VCGenerationOptions(new List<string>()))
        {
            Z3Config config = BuildConfig(opts.Timeout, true);
            this.cm = new Z3SafeContext(this, config, gen);
        }
        private static Z3Config BuildConfig(int timeout, bool nativeBv)
        {
            Z3Config config = new Z3Config();
            config.SetModelCompletion(false);
            config.SetModel(true);

            if (0 <= CommandLineOptions.Clo.ProverCCLimit)
            {
                config.SetCounterExample(CommandLineOptions.Clo.ProverCCLimit);
            }

            if (0 <= timeout)
            {
                config.SetSoftTimeout(timeout.ToString());
            }

            if (CommandLineOptions.Clo.SimplifyLogFilePath != null)
            {
                config.SetLogFilename(CommandLineOptions.Clo.SimplifyLogFilePath);
            }

            config.SetTypeCheck(true);
            return config;
        }

        public override void DeclareType(TypeCtorDecl t, string attributes)
        {
            base.DeclareType(t, attributes);
            cm.DeclareType(t.Name);
        }

        public override void DeclareConstant(Constant c, bool uniq, string attributes)
        {
            base.DeclareConstant(c, uniq, attributes);
            cm.DeclareConstant(c.Name, c.TypedIdent.Type);
        }

        public override void DeclareFunction(Function f, string attributes)
        {
            base.DeclareFunction(f, attributes);
            List<Type> domain = new List<Type>();
            foreach (Variable v in f.InParams)
            {
                domain.Add(v.TypedIdent.Type);
            }
            if (f.OutParams.Length != 1)
                throw new Exception("Cannot handle functions with " + f.OutParams + " out parameters.");
            Type range = f.OutParams[0].TypedIdent.Type;

            cm.DeclareFunction(f.Name, domain, range);
        }

        public override void DeclareGlobalVariable(GlobalVariable v, string attributes)
        {
            base.DeclareGlobalVariable(v, attributes);
            cm.DeclareConstant(v.Name, v.TypedIdent.Type);
        }

        public override string Lookup(VCExprVar var)
        {
            return cm.Namer.Lookup(var);
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