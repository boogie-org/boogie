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
using System.Diagnostics.Contracts;

using TypeAst = System.IntPtr;
using TermAst = System.IntPtr;
using ConstDeclAst = System.IntPtr;
using ConstAst = System.IntPtr;
using Value = System.IntPtr;
using PatternAst = System.IntPtr;

namespace Microsoft.Boogie.Z3
{
  public class Z3InstanceOptions : ProverOptions {
    public int Timeout { get { return TimeLimit / 1000; } }
    public int Lets {
      get {
        Contract.Ensures(0 <= Contract.Result<int>() && Contract.Result<int>() < 4);
        return CommandLineOptions.Clo.Z3lets;
      }
    }
    public bool DistZ3 = false;
    public string ExeName = "z3.exe";
    public bool InverseImplies = false;
    public string Inspector = null;
    public bool OptimizeForBv = false;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(ExeName != null);
    }

    protected override bool Parse(string opt) {
      //Contract.Requires(opt!=null);
      return ParseBool(opt, "REVERSE_IMPLIES", ref InverseImplies) ||
             ParseString(opt, "INSPECTOR", ref Inspector) ||
             ParseBool(opt, "DIST", ref DistZ3) ||
             ParseBool(opt, "OPTIMIZE_FOR_BV", ref OptimizeForBv) ||
             base.Parse(opt);
    }

    public override void PostParse() {
      base.PostParse();

      if (DistZ3) {
        ExeName = "z3-dist.exe";
        CommandLineOptions.Clo.RestartProverPerVC = true;
      }
    }

    public override string Help {
      get {
        return
@"
Z3-specific options:
~~~~~~~~~~~~~~~~~~~~
INSPECTOR=<string>        Use the specified Z3Inspector binary.
OPTIMIZE_FOR_BV=<bool>    Optimize Z3 options for bitvector reasoning, and not quantifier instantiation. Defaults to false.

Obscure options:
~~~~~~~~~~~~~~~~
DIST=<bool>               Use z3-dist.exe binary.
REVERSE_IMPLIES=<bool>    Encode P==>Q as Q||!P.

" + base.Help;
        // DIST requires non-public binaries
      }
    }
  }

  public class Z3LineariserOptions : LineariserOptions {
    private readonly Z3InstanceOptions opts;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(opts != null);
    }


    public Z3LineariserOptions(bool asTerm, Z3InstanceOptions opts, List<VCExprVar/*!>!*/> letVariables)
      : base(asTerm) {
      Contract.Requires(opts != null);
      Contract.Requires(cce.NonNullElements(letVariables));

      this.opts = opts;
      this.LetVariablesAttr = letVariables;
    }

    public override bool UseWeights {
      get {
        return true;
      }
    }

    public override bool UseTypes {
      get {
        return true;
      }
    }

    public override bool QuantifierIds {
      get {
        return true;
      }
    }

    public override bool InverseImplies {
      get {
        return opts.InverseImplies;
      }
    }

    public override LineariserOptions SetAsTerm(bool newVal) {
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      if (newVal == AsTerm)
        return this;
      return new Z3LineariserOptions(newVal, opts, LetVariables);
    }

    // variables representing formulas in let-bindings have to be
    // printed in a different way than other variables
    private readonly List<VCExprVar/*!>!*/> LetVariablesAttr;
    public override List<VCExprVar/*!>!*/> LetVariables {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));

        return LetVariablesAttr;
      }
    }

    public override LineariserOptions AddLetVariable(VCExprVar furtherVar) {
      //Contract.Requires(furtherVar != null);
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      List<VCExprVar/*!>!*/> allVars = new List<VCExprVar/*!*/>();
      allVars.AddRange(LetVariables);
      allVars.Add(furtherVar);
      return new Z3LineariserOptions(AsTerm, opts, allVars);
    }

    public override LineariserOptions AddLetVariables(List<VCExprVar/*!>!*/> furtherVars) {
      //Contract.Requires(furtherVars != null);
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      List<VCExprVar/*!>!*/> allVars = new List<VCExprVar/*!*/>();
      allVars.AddRange(LetVariables);
      allVars.AddRange(furtherVars);
      return new Z3LineariserOptions(AsTerm, opts, allVars);
    }
  }

    public class Z3apiProcessTheoremProver : ProverInterface
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

        public override ProverInterface.Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore, ErrorHandler handler)
        {
            LineariserOptions linOptions = new Z3LineariserOptions(false, (Z3InstanceOptions)this.options, new List<VCExprVar>());
            return context.CheckAssumptions(assumptions, linOptions, out z3LabelModels, out unsatCore);
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
                    handler.OnModel(unprefixedLabels, z3LabelModel.Model);
                }
            }
            return outcome;
        }

        public override Outcome CheckOutcomeCore(ErrorHandler handler) {
          if (outcome == Outcome.Invalid) {
            foreach (Z3ErrorModelAndLabels z3LabelModel in z3LabelModels) {
              List<string> unprefixedLabels = RemovePrefixes(z3LabelModel.RelevantLabels);
              handler.OnModel(unprefixedLabels, z3LabelModel.Model);
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