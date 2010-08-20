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

using TypeAst = System.IntPtr;
using TermAst = System.IntPtr;
using ConstDeclAst = System.IntPtr;
using ConstAst = System.IntPtr;
using Value = System.IntPtr;
using PatternAst = System.IntPtr;

namespace Microsoft.Boogie.Z3
{
    public class Z3ThreadTheoremProver : ProverInterface
    {
        protected DeclFreeProverContext ctx;
        protected VCExpressionGenerator gen;
        public override ProverContext Context
        {
            get { return this.ctx; }
        }
        public override VCExpressionGenerator VCExprGen
        {
            get { return this.gen; }
        }

        private int timeout;
        private Z3Context cm;

        public Z3ThreadTheoremProver(Z3InstanceOptions proverOptions)
            : base()
        {
            gen = new VCExpressionGenerator();

            string codebaseString = Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
            string backgroundPredicates;

            // Initialize '_backgroundPredicates'
            string univBackPredPath = Path.Combine(codebaseString,
                // yes, using .NeedsTypes here is an ugly hack...
                "Z3API_UnivBackPred.smt");
            using (StreamReader reader = new System.IO.StreamReader(univBackPredPath))
            {
                backgroundPredicates = reader.ReadToEnd();
            }

            Z3Config config = BuildConfig(timeout, true);
            Z3Context cm = Z3ContextFactory.BuildZ3Context(config, gen);
            Z3ThreadProverContext ctx = new Z3ThreadProverContext(gen, cm);

            this.cm = cm;
            cm.AddSmtlibString(backgroundPredicates);
            this.z3ContextIsUsed = false;
        }

        private static Z3Config BuildConfig(int timeout, bool nativeBv)
        {
            Z3Config config = new Z3Config();
            config.SetPartialModels(true);
            config.SetModelCompletion(false);
            config.SetHideUnusedPartitions(false);
            config.SetModel(true);

            if (0 <= CommandLineOptions.Clo.ProverCCLimit)
            {
                config.SetCounterExample(CommandLineOptions.Clo.ProverCCLimit);
            }

            if (0 <= timeout)
            {
                config.SetSoftTimeout(timeout.ToString());
            }

            config.SetTypeCheck(true);
            if (nativeBv)
                config.SetReflectBvOps(true);

            return config;
        }

        private bool z3ContextIsUsed;

        public void PushAxiom(VCExpr axiom)
        {
            cm.CreateBacktrackPoint();
            cm.AddAxiom((VCExpr)axiom);
        }
        private void PushConjecture(VCExpr conjecture)
        {
            cm.CreateBacktrackPoint();
            cm.AddConjecture((VCExpr)conjecture);
        }

        public void PrepareCheck(string descriptiveName, VCExpr vc)
        {
            PushAxiom(ctx.Axioms);
            PushConjecture(vc);
        }

        public void BeginPreparedCheck()
        {
            outcome = Outcome.Undetermined;
            outcome = cm.Check(out z3LabelModels);
        }

        public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
        {
            if (z3ContextIsUsed)
            {
                cm.Backtrack();
            }
            else
            {
                cm.AddAxiom((VCExpr)ctx.Axioms);
                z3ContextIsUsed = true;
            }

            cm.CreateBacktrackPoint();
            cm.AddConjecture((VCExpr)vc);

            BeginPreparedCheck();
        }

        private Outcome outcome;
        private List<Z3ErrorModelAndLabels> z3LabelModels = new List<Z3ErrorModelAndLabels>();
        private UnexpectedProverOutputException proverException = null;

        [NoDefaultContract]
        public override Outcome CheckOutcome(ErrorHandler handler)
        {
            if (outcome == Outcome.Invalid)
            {
                foreach (Z3ErrorModelAndLabels z3LabelModel in z3LabelModels)
                {
                    List<string> unprefixedLabels = RemovePreffixes(z3LabelModel.RelevantLabels);
                    handler.OnModel(unprefixedLabels, z3LabelModel.ErrorModel);
                }
            }
            return outcome;
        }

        public void CreateBacktrackPoint()
        {
            cm.CreateBacktrackPoint();
        }
        override public void Pop()
        {
            cm.Backtrack();
        }

        private List<string> RemovePreffixes(List<string> labels)
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
                    throw new Exception("Unknown preffix in label " + label);
            }
            return result;
        }

    }

    public class Z3ThreadProverContext : DeclFreeProverContext
    {

        private Z3Context cm;

        public Z3ThreadProverContext(VCExpressionGenerator gen, Z3Context cm)
            : base(gen, null)
        {
            this.cm = cm;
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
    }
}

namespace Microsoft.Boogie.Z3api
{

    public class Factory : ProverFactory
    {
        public override object SpawnProver(ProverOptions popts, object ctxt)
        {
            Z3InstanceOptions options = (Z3InstanceOptions) popts;
            if (CommandLineOptions.Clo.BracketIdsInVC < 0)
            {
                CommandLineOptions.Clo.BracketIdsInVC = 0;
            }

            return new Z3ThreadTheoremProver(options);
        }

        public override object NewProverContext(ProverOptions options)
        {
            throw new NotImplementedException();
        }
    }
}