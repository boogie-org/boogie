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

  public class SMTLibProverOptions : ProverOptions
  {
    public bool UseWeights = true;
    public bool UseLabels { get { return UseZ3; } }
    public List<OptionValue> SmtOptions = new List<OptionValue>();
    public List<string> SolverArguments = new List<string>();
    public bool MultiTraces = false;
    public string Logic = "";

    // Z3 specific (at the moment; some of them make sense also for other provers)
    public bool UseZ3 = true;
    public string Inspector = null;
    public bool OptimizeForBv = false;

    public bool ExpectingModel()
    {
      return CommandLineOptions.Clo.PrintErrorModel >= 1 ||
             CommandLineOptions.Clo.EnhancedErrorMessages == 1 ||
             CommandLineOptions.Clo.ModelViewFile != null ||
             CommandLineOptions.Clo.ContractInfer ||
             CommandLineOptions.Clo.LazyInlining > 0 ||
             CommandLineOptions.Clo.StratifiedInlining > 0;
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
        ReportError("Options to be passed to the prover should have the format: O:<name>=<value>, got '" + opt + "'");
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

      return
        ParseBool(opt, "MULTI_TRACES", ref MultiTraces) ||
        ParseBool(opt, "USE_WEIGHTS", ref UseWeights) ||
        ParseBool(opt, "USE_Z3", ref UseZ3) ||
        ParseString(opt, "INSPECTOR", ref Inspector) ||
        ParseBool(opt, "OPTIMIZE_FOR_BV", ref OptimizeForBv) ||
        ParseString(opt, "LOGIC", ref Logic) ||
        base.Parse(opt);
    }

    public override void PostParse()
    {
      base.PostParse();
      if (UseZ3)
        Z3.SetupOptions(this);
    }

    public override string Help
    {
      get
      {
        return
@"
SMT-specific options:
~~~~~~~~~~~~~~~~~~~~~
USE_WEIGHTS=<bool>        Pass :weight annotations on quantified formulas (default: true)
VERBOSITY=<int>           1 - print prover output (default: 0)
O:<name>=<value>          Pass (set-option :<name> <value>) to the SMT solver.
C:<string>                Pass <string> to the SMT on the command line. 
LOGIC=<string>            Pass (set-logic <string>) to the prover (default: empty)

Z3-specific options:
~~~~~~~~~~~~~~~~~~~~
MULTI_TRACES=<bool>       Report errors with multiple paths leading to the same assertion.
INSPECTOR=<string>        Use the specified Z3Inspector binary.
OPTIMIZE_FOR_BV=<bool>    Optimize Z3 options for bitvector reasoning, and not quantifier instantiation. Defaults to false.
USE_Z3=<bool>             Use z3.exe as the prover, and use Z3 extensions (default: true)
" + base.Help;
      }
    }
  }
}
