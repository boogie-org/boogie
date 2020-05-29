using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.SMTLib
{

  public class OptionValue
  {
    public readonly string Option;
    public readonly string Value;
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Option != null);
      Contract.Invariant(Value != null);
    }

    public OptionValue(string option, string value)
    {
      Contract.Requires(option != null);
      Contract.Requires(value != null);
      Option = option;
      Value = value;
    }
  }

  public enum SolverKind { Z3, CVC4, YICES2 };

  public class SMTLibProverOptions : ProverOptions
  {
    public bool UseWeights = true;
    public bool SupportsLabels => Solver == SolverKind.Z3;
    public bool UseTickleBool => Solver == SolverKind.Z3;
    public SolverKind Solver = SolverKind.Z3;
    public List<OptionValue> SmtOptions = new List<OptionValue>();
    public List<string> SolverArguments = new List<string>();
    public string Logic = null;

    // Z3 specific (at the moment; some of them make sense also for other provers)
    public string Inspector = null;

    public bool ProduceModel() {
      return CommandLineOptions.Clo.ExplainHoudini || CommandLineOptions.Clo.UseProverEvaluate || ExpectingModel();
    }

    public bool ExpectingModel()
    {
        return CommandLineOptions.Clo.PrintErrorModel >= 1 ||
               CommandLineOptions.Clo.EnhancedErrorMessages == 1 ||
               CommandLineOptions.Clo.ModelViewFile != null ||
               (CommandLineOptions.Clo.StratifiedInlining > 0 && !CommandLineOptions.Clo.StratifiedInliningWithoutModels);
    }

    public void AddSolverArgument(string s)
    {
      SolverArguments.Add(s);
    }

    public void AddSmtOption(string name, string val)
    {
      SmtOptions.Add(new OptionValue(name, val));
    }

    public void AddWeakSmtOption(string name, string val)
    {
      if (!SmtOptions.Any(o => o.Option == name))
        SmtOptions.Add(new OptionValue(name, val));
    }

    public void AddSmtOption(string opt)
    {
      var idx = opt.IndexOf('=');
      if (idx <= 0 || idx == opt.Length - 1)
        ReportError("Options to be passed to the prover should have the format: <name>=<value>, got '" + opt + "'");
      AddSmtOption(opt.Substring(0, idx), opt.Substring(idx + 1));
    }

    protected override bool Parse(string opt)
    {
      if (opt.StartsWith("O:")) {
        AddSmtOption(opt.Substring(2));
        return true;
      }

      if (opt.StartsWith("C:")) {
        AddSolverArgument(opt.Substring(2));
        return true;
      }

      string SolverStr = null;
      if (ParseString(opt, "SOLVER", ref SolverStr)) {
        switch (SolverStr.ToLower()) {
          case "z3":
            Solver = SolverKind.Z3; break;
          case "cvc4":
            Solver = SolverKind.CVC4; break;
          case "yices2":
            Solver = SolverKind.YICES2; break;
          default:
            ReportError("Invalid SOLVER value; must be 'Z3' or 'CVC4' or 'Yices2'");
            return false;
        }
        return true;
      }

      return
        ParseBool(opt, "USE_WEIGHTS", ref UseWeights) ||
        ParseString(opt, "INSPECTOR", ref Inspector) ||
        ParseString(opt, "LOGIC", ref Logic) ||
        base.Parse(opt);
    }

    public override void PostParse()
    {
      base.PostParse();

      switch (Solver) {
        case SolverKind.Z3:
          Z3.SetDefaultOptions(this);
          SolverArguments.Add("-smt2 -in");
          break;
        case SolverKind.CVC4:
          SolverArguments.Add("--lang=smt --no-strict-parsing --no-condense-function-values --incremental --produce-models");
          if (Logic == null) Logic = "ALL_SUPPORTED";
          break;
        case SolverKind.YICES2:
          SolverArguments.Add("--incremental");
          if (Logic == null) Logic = "ALL";
          break;
      }

      if (ProverName == null)
          ProverName = Solver.ToString().ToLower();
    }

    public override string Help
    {
      get
      {
        return
base.Help +
@"
SMT-specific options:
~~~~~~~~~~~~~~~~~~~~~
SOLVER=<string>           Use the given SMT solver (z3, cvc4, yices2; default: z3)
LOGIC=<string>            Pass (set-logic <string>) to the prover (default: empty, 'ALL_SUPPORTED' for CVC4)
USE_WEIGHTS=<bool>        Pass :weight annotations on quantified formulas (default: true)
VERBOSITY=<int>           1 - print prover output (default: 0)
O:<name>=<value>          Pass (set-option :<name> <value>) to the SMT solver.
C:<string>                Pass <string> to the SMT solver on the command line.

Z3-specific options:
~~~~~~~~~~~~~~~~~~~~
INSPECTOR=<string>        Use the specified Z3Inspector binary.
";
      }
    }
  }
}
