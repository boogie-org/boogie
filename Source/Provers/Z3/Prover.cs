//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

// #define RECENT_Z3 // 2.20 or newer

using System;
using System.IO;
using System.Diagnostics;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Text;
//using util;
using Microsoft.Boogie;
using Microsoft.Boogie.Simplify;
using Microsoft.Basetypes;

// Simplified interface to an external prover like Simplify or the z3 process, taken from Bird.
namespace Microsoft.Boogie.Z3
{
  internal class Z3ProverProcess : ProverProcess
  {
    [Peer]
    private Z3InstanceOptions opts;
    [Peer]
    private readonly Inspector/*?*/ inspector;
    private readonly bool expectingModel = false;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(opts != null);
      Contract.Invariant(cce.NonNullElements(parameterSettings));
    }

    class OptionValue
    {
      public readonly string Option;
      public readonly string Value;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Option != null);
        Contract.Invariant(Value != null);
      }

      public OptionValue(string option, string value) { Contract.Requires(option != null); Contract.Requires(value != null); Option = option; Value = value; }
    }

    static void AddOption(List<OptionValue> parms, string option, string value)
      //modifies parms.*; TODO:
    {
      Contract.Requires(option != null);
      Contract.Requires(value != null);
      Contract.Requires(cce.NonNullElements(parms));
      OptionValue ov = new OptionValue(option, value);
      cce.Owner.AssignSame(ov, cce.Owner.ElementProxy(parms));
      parms.Add(ov);
    }

    private List<OptionValue/*!>!*/> parameterSettings;

    static void AppendCmdLineOption(StringBuilder cmdLineBldr, string name, object value) {
      cmdLineBldr.Append(' ').Append(OptionChar()).Append(name).Append(':').Append(value);
    }

    static void AppendCmdLineOption(StringBuilder cmdLineBldr, string name) {
      cmdLineBldr.Append(' ').Append(OptionChar()).Append(name);
    }

    static bool ExpectingModel()
    {
      return CommandLineOptions.Clo.PrintErrorModel >= 1 ||
             CommandLineOptions.Clo.EnhancedErrorMessages == 1 ||
             CommandLineOptions.Clo.ModelViewFile != null ||
             CommandLineOptions.Clo.ContractInfer ||
             CommandLineOptions.Clo.LazyInlining > 0 ||
             CommandLineOptions.Clo.StratifiedInlining > 0;
    }

    static string/*!*/ CreateCommandLineArgsForOptions(Z3InstanceOptions opts)
    {
      StringBuilder cmdLineArgsBldr = new StringBuilder();
      AppendCmdLineOption(cmdLineArgsBldr, "si");

      if (CommandLineOptions.Clo.LazyInlining == 2) 
        AppendCmdLineOption(cmdLineArgsBldr, "nw");

      if (CommandLineOptions.Clo.z3AtFlag)
        AppendCmdLineOption(cmdLineArgsBldr, "@");

      if (0 <= CommandLineOptions.Clo.ProverCCLimit)
        AppendCmdLineOption(cmdLineArgsBldr, "cex", CommandLineOptions.Clo.ProverCCLimit);

      if (0 <= opts.Timeout)
        AppendCmdLineOption(cmdLineArgsBldr, "t", opts.Timeout);

      if (ExpectingModel())
        AppendCmdLineOption(cmdLineArgsBldr, "m");

      foreach (string opt in CommandLineOptions.Clo.Z3Options) {
        Contract.Assert(opt != null);
        cmdLineArgsBldr.Append(" \"").Append(opt).Append('\"');
      }

      return cmdLineArgsBldr.ToString();
    }

    static List<OptionValue/*!*/>/*!*/ CreateParameterListForOptions(Z3InstanceOptions opts, Inspector inspector)
    {
      List<OptionValue/*!*/>/*!*/ result = new List<OptionValue/*!*/>();

      AddOption(result, "MODEL_PARTIAL", "true");
      
      AddOption(result, "MODEL_HIDE_UNUSED_PARTITIONS", "false");
      AddOption(result, "MODEL_V1", "true");
      AddOption(result, "ASYNC_COMMANDS", "false");

#if RECENT_Z3
      AddOption(result, "AUTO_CONFIG", "false");
      AddOption(result, "MBQI", "false");
#else
      AddOption(result, "MODEL_VALUE_COMPLETION", "false");
#endif

      if (!opts.OptimizeForBv) {
        // Phase selection means to always try the negative literal polarity first, seems to be good for Boogie.
        // The restart parameters change the restart behavior to match Z3 v1, which also seems to be good.
        AddOption(result, "PHASE_SELECTION", "0");
        AddOption(result, "RESTART_STRATEGY", "0");
        AddOption(result, "RESTART_FACTOR", "|1.5|");

        // Make the integer model more diverse by default, speeds up some benchmarks a lot.
        AddOption(result, "ARITH_RANDOM_INITIAL_VALUE", "true");

        // The left-to-right structural case-splitting strategy.
#if !RECENT_Z3
        AddOption(result, "SORT_AND_OR", "false");
#endif
        AddOption(result, "CASE_SPLIT", "3");

        // In addition delay adding unit conflicts.
        AddOption(result, "DELAY_UNITS", "true");
        AddOption(result, "DELAY_UNITS_THRESHOLD", "16");
      }

      // This is used by VCC, but could be also useful for others, if sk_hack(foo(x)) is included as trigger,
      // the foo(x0) will be activated for e-matching when x is skolemized to x0.
      AddOption(result, "NNF_SK_HACK", "true");

      // More or less like MAM=0.
      AddOption(result, "QI_EAGER_THRESHOLD", "100");
      // Complex proof attempts in VCC (and likely elsewhere) require matching depth of 20 or more.

      // the following will make the :weight option more usable
      AddOption(result, "QI_COST", "|\"(+ weight generation)\"|");

      if (opts.Inspector != null)
        AddOption(result, "PROGRESS_SAMPLING_FREQ", "100");

      if (opts.Typed) {
        AddOption(result, "TYPE_CHECK", "true");
        if (opts.BitVectors == CommandLineOptions.BvHandling.Z3Native)
            AddOption(result, "BV_REFLECT", "true");
      }

      if (CommandLineOptions.Clo.LazyInlining == 2)
        AddOption(result, "MACRO_EXPANSION", "true");
      
      foreach (string opt in CommandLineOptions.Clo.Z3Options) {
        Contract.Assert(opt != null);
        int eq = opt.IndexOf("=");
        // we add them both to command line and the input file:
        //    - allow for overriding default options
        //    - some options (like TRACE) work only from command line
        // Also options with spaces do not work with (SETPARAMETER ...)
        if (eq > 0 && opt.IndexOf(" ") < 0 && 'A' <= opt[0] && opt[0] <= 'Z') {
          AddOption(result, opt.Substring(0, eq), opt.Substring(eq + 1));
        }
      }

      return result;
    }

    //[NotDelayed]
    [Captured]
    public Z3ProverProcess(Z3InstanceOptions opts, Inspector inspector)
      : base(ComputeProcessStartInfo(opts), opts.ExeName) { // throws ProverException
      Contract.Requires(opts != null);
      Contract.Requires(inspector == null || cce.Owner.Same(opts, inspector));
      this.parameterSettings = CreateParameterListForOptions(opts, inspector);
      cce.Owner.AssignSame(this, opts);
      this.opts = opts;
      this.inspector = inspector;
      this.expectingModel = ExpectingModel();
    }

    private static ProcessStartInfo ComputeProcessStartInfo(Z3InstanceOptions opts)
    {
      return new ProcessStartInfo(opts.ExeName, CreateCommandLineArgsForOptions(opts))
               {
                 CreateNoWindow = true,
                 UseShellExecute = false,
                 RedirectStandardInput = true,
                 RedirectStandardOutput = true,
                 RedirectStandardError = true
               };
    }

    public override string OptionComments() {
      Contract.Ensures(Contract.Result<string>() != null);

      StringBuilder sb = new StringBuilder();
      sb.AppendFormat("Z3 command line: {0} {1}\nUser supplied Z3 options:",
                      opts.ExeName, this.simplify.StartInfo.Arguments);
      Contract.Assume(cce.IsPeerConsistent(CommandLineOptions.Clo));
      foreach (string opt in CommandLineOptions.Clo.Z3Options) {
        Contract.Assert(opt != null);
        sb.Append(" ").Append(opt);
      }
      sb.AppendFormat("\nProver options: {0}\n", opts.ToString());
      return sb.ToString();
    }

    //[Pure(false)]
    public override IEnumerable<string/*!>!*/> ParameterSettings {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<string>>()));
        foreach (OptionValue opt in parameterSettings) {
          yield return "(SETPARAMETER " + opt.Option + " " + opt.Value + ")";
        }
      }
    }

    // z3 uses different magic characters for options on linux/unix and on windows
    private static string OptionChar() {
      Contract.Ensures(Contract.Result<string>() != null);

      Contract.Assume(Environment.OSVersion != null);
      switch (Environment.OSVersion.Platform) {
        case PlatformID.Unix:
          return "-";
        default:
          return "/";
      }
    }

    protected override void DoBeginCheck(string descriptiveName, string formula) {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(formula != null);
      ToWriteLine(formula);
      ToWriteLine(String.Format(";   END OF FORMULA {0} - {1}", NumFormulasChecked.ToString(), descriptiveName));
      ToFlush();
    }

    protected int TimedFromReadChar() {
      if (opts.Timeout > 0)
        return FromReadChar((opts.Timeout + 1) * 1000);
      else
        return FromReadChar();
    }

    private void Trace(string msg) {
      Contract.Requires(msg != null);
      Console.WriteLine("Z3: " + msg);
    }

    public override ProverOutcome CheckOutcome(Microsoft.Boogie.ProverInterface.ErrorHandler handler) {
      //Contract.Requires(handler != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      //ProverOutcome outcome;
      bool isInvalid = false;

      if (this.simplify == null) {
        return ProverOutcome.Inconclusive;
      }


      while (true) {
        int ch = TimedFromReadChar();
        if (ch == -1 && this.readTimedOut) {
          handler.OnResourceExceeded("timeout (forced)");
          return ProverOutcome.TimeOut;
        }

        if (ch == -1)
            throw new UnexpectedProverOutputException("z3 crashed and produced no output");          
        
        string line = new string((char)ch, 1) + FromReadLine();

        if (line.StartsWith("STATS ")) {
          if (inspector != null) {
            inspector.StatsLine(line);
          }
          continue;
        }

        if (opts.Verbosity > 2) {
          Trace("INPUT: " + line);
        }

        if (line.StartsWith("WARNING: Out of allocated virtual memory.")) {
          handler.OnResourceExceeded("memory");
          return ProverOutcome.OutOfMemory;
        }


        if (line.StartsWith("WARNING: ")) {
          string w = line.Substring(9);
          handler.OnProverWarning(w);
          continue;
        }

        if (line.ToUpper().StartsWith("ERROR")) {
          Console.WriteLine("Z3 returns the following error:");
          Console.WriteLine("    " + line);
          return ProverOutcome.Inconclusive;
        }

        int beg = 0;
        while (beg < line.Length && '0' <= line[beg] && line[beg] <= '9') {
          cce.LoopInvariant(beg <= line.Length);
          beg++;
        }

        if (beg > 0 && line.Substring(beg).StartsWith(": ")) {
          string status = line.Substring(beg + 2);

          if (status.StartsWith("Valid")) {
            return ProverOutcome.Valid;
          }

          if (status.StartsWith("Timeout")) {
            handler.OnResourceExceeded("timeout");
            return ProverOutcome.TimeOut;
          }

          if (status.StartsWith("Inconclusive")) {
            return ProverOutcome.Inconclusive;
          }

          if (status.StartsWith("Memout")) {
            handler.OnResourceExceeded("memory");
            return ProverOutcome.OutOfMemory;
          }

          if (status.StartsWith("Invalid")) {
            isInvalid = true;
            continue;
          }
        }

        if (isInvalid && line == ".") {
          return ProverOutcome.NotValid;
        }

        if (isInvalid && line.StartsWith("labels: (")) {
          List<string/*!*/>/*!*/ l = ParseLabels(line);
          Contract.Assert(cce.NonNullElements(l));
          Z3ErrorModel errModel = null;
          if (expectingModel) {
            if (opts.Verbosity > 2) {
              Trace("waiting for model");
            }
            line = FromReadLine();
            if (line.StartsWith("partitions:")) {
              line = ParseModel(out errModel);
              if (opts.Verbosity > 2) {
                Trace("model parsed, final line " + line);
              }
              // Z3 always ends the model with END_OF_MODEL, not with labels: or .
              Contract.Assume(line == "END_OF_MODEL");
            } else {
              throw new UnexpectedProverOutputException(string.Format("evil input from z3 (expecting partitions): '{0}'", line));
            }
          }
          handler.OnModel(l, errModel);
          continue;
        }

        throw new UnexpectedProverOutputException(string.Format("evil input from z3: '{0}'", line));
      }
    }

    /* ----------------------------------------------------------------------------
    BNF Grammar to parse Z3 output, including the model generated when using the /m /si switch:

    Output  ::= VC*
    VC      ::= number ": " "Valid." | number ": " "Inconclusive" | VCI
    VCI     ::= number ": " "Invalid"
                ("labels: " "(" ID* ")"
                [MODEL] "END_OF_MODEL")+
                "."
    MODEL   ::= MBOOL MFUNC
    MBOOL   ::= "boolean assignment:"
                "partitions:"
                MAPPING*
    MAPPING ::= ZID ["{" ID+"}"] ["->" "(" (number | false | true | BITVECTOR) ")"]
    BITVECTOR ::= ulong ":bv" int
    MFUNC   ::= "function interpretations:"
                F*
    F       ::= Id "->" "{"
                MAPLET*
                "else" "->" ZID
                "}"
    MAPLET  ::= ZID* "->" ZID

    -----------------------------------------------------------------------------*/
    private string ParseModel(out Z3ErrorModel errModel)
      //modifies this.*;
      //throws UnexpectedProverOutputException;
    {
      Contract.Ensures(Contract.Result<string>() == "." || Contract.Result<string>().StartsWith("labels: (") || Contract.Result<string>() == "END_OF_MODEL");
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      //Format in the grammar:
      // ZID ["{" ID+"}"] ["->" "(" (number | false | true) ")"]
      // storing the model:
      // map each ID (a string) to the corresping ZID (an integer) in a dictionary:
      Dictionary<string/*!*/, int> identifierToPartition = new Dictionary<string/*!*/, int>();
      // map each ZID to the set (in list form) of IDs belonging to it (possibly empty):
      List<List<string/*!*/>> partitionToIdentifiers = new List<List<string/*!*/>>();
      // map each ZID to the number or boolean given, if any:
      List<Object> partitionToValue = new List<Object>();
      // map each value (number or boolean) to the ZID, reverse map of partitionToValue
      Dictionary<Object, int> valueToPartition = new Dictionary<Object, int>();
      cce.Owner.AssignSame(cce.Owner.ElementProxy(partitionToValue), cce.Owner.ElementProxy(valueToPartition));

      int ch;

      // read the MAPPING
      for (int zID = 0; true; zID++) {
        ch = FromReadChar();
        if (ch == 'f') {
          break;
        }
        ParseModelMapping(zID, identifierToPartition, partitionToIdentifiers, partitionToValue, valueToPartition);
      }// end MAPPING

      // add the fake partition for the 'else -> #undefined' clause
      List<string/*!*/> emptyList = new List<string/*!*/>();
      cce.Owner.AssignSame(emptyList, cce.Owner.ElementProxy(partitionToIdentifiers));
      partitionToIdentifiers.Add(emptyList);
      partitionToValue.Add(null);

      // continue in ParseModelFunctions, which breaks up this long method and enables its verification
      return ParseModelFunctions(ch, out errModel, identifierToPartition, partitionToIdentifiers, partitionToValue, valueToPartition);
    }

    private void ParseModelMapping(int zID,
        Dictionary<string/*!*/, int>/*!*/ identifierToPartition,
        List<List<string/*!*/>>/*!*/ partitionToIdentifiers,
        List<Object>/*!*/ partitionToValue,
        Dictionary<Object, int>/*!*/ valueToPartition)
      //modifies this.*, identifierToPartition.*, partitionToIdentifiers.*, partitionToValue.*, valueToPartition.*;
    {
      Contract.Requires(partitionToValue != null);
      Contract.Requires(valueToPartition != null);
      Contract.Requires(identifierToPartition != null);
      Contract.Requires(cce.NonNullElements(partitionToIdentifiers));
      Contract.Requires(cce.Owner.Same(cce.Owner.ElementProxy(partitionToValue), cce.Owner.ElementProxy(valueToPartition)));
      string s = FromReadLine();
      {
        // sanity check
        int pos = s.IndexOf(' ');
        string n = s;
        int k;
        if (pos >= 0) {
          n = s.Substring(0, pos);
        }
        if (!(int.TryParse(n, out k) && zID == k)) {
          System.Console.WriteLine("mismatch: {0}!={1} '{2}'", zID, k, s);
          Contract.Assume(false);
        }
      }

      int j = ParseModelZidAndIdentifiers(zID, s, identifierToPartition, partitionToIdentifiers);

      j = s.IndexOf(" -> ", j);
      if (0 <= j) {
        j += 4;
      }
      Contract.Assume(j == -1 || j < s.Length);  // if ' -> ' is present, then more should remain of the line
      if (j == -1) {
        // no "-> " found, end of this line, store that there is no value:
        partitionToValue.Add(null);
        int idForNull;
        if (identifierToPartition.TryGetValue("nullObject", out idForNull) && idForNull == zID) {
          Contract.Assume(!valueToPartition.ContainsKey("nullObject"));  // a RHS value should occur only once in the Z3 output
          valueToPartition.Add("nullObject", zID);
          // In this case partitionToValue (as the reverse of valueToPartition) should include
          // a map from zID -> "nullObject", but doing that breaks printing out the model as 
          // it is printed out by Z3. Also, that information is not required, valueToPartition
          // works well enough by itself.
        }

      } else if (s[j] == 't'/*rue*/) {
        partitionToValue.Add(true);
        object boxedTrue = true;
        Contract.Assume(!valueToPartition.ContainsKey(boxedTrue));  // a RHS value should occur only once in the Z3 output
        valueToPartition.Add(boxedTrue, zID);
      } else if (s[j] == 'f'/*alse*/) {
        object boxedFalse = false;
        cce.Owner.AssignSame(boxedFalse, cce.Owner.ElementProxy(partitionToValue));
        partitionToValue.Add(boxedFalse);
        Contract.Assume(!valueToPartition.ContainsKey(boxedFalse));  // a RHS value should occur only once in the Z3 output
        valueToPartition.Add(boxedFalse, zID);
      } else if (s[j] == 'v') {
        // -> val!..., i.e. no value
        partitionToValue.Add(null);
      } else if (s[j] == '{') {
        // array
        List<List<int>/*!*/> arrayModel = new List<List<int>/*!*/>();
        Contract.Assert(Contract.ForAll(arrayModel, a => a != null));
        string array = s.Substring(j + 1);
        int index1, index2;
        string from, to;
        List<int> tuple = new List<int>();
        while (0 <= array.IndexOf(';')) {
          index1 = array.IndexOf('*') + 1;
          index2 = array.IndexOf(' ');
          from = array.Substring(index1, index2 - index1);
          tuple.Add(int.Parse(from));
          array = array.Substring(index2);
          index1 = array.IndexOf('*') + 1;
          index2 = array.IndexOf(';');
          to = array.Substring(index1, index2 - index1);
          array = array.Substring(index2 + 2);
          tuple.Add(int.Parse(to));
          arrayModel.Add(tuple);
          tuple = new List<int>();
        }
        Contract.Assert(array.StartsWith("else ->"));
        index1 = array.IndexOf('*') + 1;
        index2 = array.IndexOf('}');
        to = array.Substring(index1, index2 - index1);
        tuple.Add(int.Parse(to));
        arrayModel.Add(tuple);
        partitionToValue.Add(arrayModel);
      } else {
        string numberOrBv = s.Substring(j);
        // make number an int, then store it:
        BigNum bvVal;
        int bvSize;
        string number, type;

        int l = numberOrBv.IndexOf(':', 0);
        if (0 <= l) {
          number = numberOrBv.Substring(0, l);
          type = numberOrBv.Substring(l + 1);
        } else {
          l = numberOrBv.IndexOf('[', 0);
          if (0 <= l) {
            number = numberOrBv.Substring(2, l - 2);
            int closingBracePosition = numberOrBv.IndexOf(']', l);
            if (l < closingBracePosition)
              type = "bv" + numberOrBv.Substring(l + 1, closingBracePosition - l - 1);
            else type = "int";
          } else {
            number = numberOrBv;
            type = "int";
          }
        }

        if (type == "int") {
          object boxedN = BigNum.FromString(number);
          Contract.Assume(cce.Owner.None(boxedN));
          cce.Owner.AssignSame(boxedN, cce.Owner.ElementProxy(partitionToValue));
          partitionToValue.Add(boxedN);
          Contract.Assume(!valueToPartition.ContainsKey(boxedN));  // a RHS value should occur only once in the Z3 output
          valueToPartition.Add(boxedN, zID);
        } else if (type.StartsWith("bv") && BigNum.TryParse(number, out bvVal) && int.TryParse(type.Substring(2), out bvSize)) {
          BvConst bitV = new BvConst(bvVal, bvSize);
          cce.Owner.AssignSame(bitV, cce.Owner.ElementProxy(partitionToValue));
          partitionToValue.Add(bitV);
          Contract.Assume(!valueToPartition.ContainsKey(bitV));  // a RHS value should occur only once in the Z3 output
          valueToPartition.Add(bitV, zID);
        } else {
          System.Console.WriteLine("cannot parse type: '{0}':'{1}'", number, type);
          Contract.Assume(false);
        }

      }
    }

    private static int ParseModelZidAndIdentifiers(int zID, string s,
        Dictionary<string/*!*/, int>/*!*/ identifierToPartition,
        List<List<string/*!*/>>/*!*/ partitionToIdentifiers)
      //modifies identifierToPartition.*, partitionToIdentifiers.*;
    {
      Contract.Requires(identifierToPartition != null && cce.NonNullElements(identifierToPartition.Keys));
      Contract.Requires(partitionToIdentifiers != null && Contract.ForAll(partitionToIdentifiers, identifier => cce.NonNullElements(identifier)));
      Contract.Requires(s != null);
      Contract.Ensures(0 <= Contract.Result<int>() && Contract.Result<int>() <= s.Length);

      List<string/*!*/> identifiers = new List<string/*!*/>();
      int arrowIndex = s.IndexOf('>');
      Contract.Assert(0 < arrowIndex);
      int j = s.IndexOf('{', 0) + 1;  // skip the '{', if present, and set j to 0 otherwise
      if (1 <= j && j < arrowIndex) {
        // There is a list of ID's.
        Contract.Assume(j < s.Length);  // there should be more characters; the ending '}', for one
        //ID*
        while (true) {
          cce.LoopInvariant(cce.IsPeerConsistent(identifiers) && cce.IsPeerConsistent(identifierToPartition) && cce.IsPeerConsistent(partitionToIdentifiers));
          cce.LoopInvariant(0 <= j && j < s.Length);
          int k = s.IndexOfAny(new char[] { ' ', '}' }, j);
          Contract.Assume(j <= k);
          string id = s.Substring(j, k - j);
          j = k + 1;
          Contract.Assume(!identifierToPartition.ContainsKey(id));  // an ID is listed only once in this list, and an ID can only belong to one ZID equivalence class
          identifierToPartition.Add(id, zID);
          identifiers.Add(id);
          if (s[k] == '}') {
            // end of reading ID*
            break;
          }
          Contract.Assume(j < s.Length);  // there should be more characters; the ending '}', for one
        }//end ID*
      } else {
        j = 0;
      }
      cce.Owner.AssignSame(identifiers, cce.Owner.ElementProxy(partitionToIdentifiers));
      partitionToIdentifiers.Add(identifiers);
      return j;
    }

    private string ParseModelFunctions(int ch, out Z3ErrorModel errModel,
      Dictionary<string/*!*/, int>/*!*/ identifierToPartition,
      List<List<string/*!*/>>/*!*/ partitionToIdentifiers,
      List<Object>/*!*/ partitionToValue,
      Dictionary<Object, int>/*!*/ valueToPartition
    )
      //modifies this.*;
    {
      Contract.Requires(identifierToPartition != null && cce.NonNullElements(identifierToPartition.Keys));
      Contract.Requires(partitionToIdentifiers != null && Contract.ForAll(partitionToIdentifiers, identifier => cce.NonNullElements(identifier)));
      Contract.Requires(partitionToValue != null);
      Contract.Requires(valueToPartition != null);
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Ensures(Contract.Result<string>() == "." || Contract.Result<string>().StartsWith("labels: (") || Contract.Result<string>() == "END_OF_MODEL");
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      // read the function F
      Expect(ch, "function interpretations:");
      FromReadLine();

      // mapping of function names to function definitions
      Dictionary<string/*!*/, List<List<int>>/*!*/> definedFunctions = new Dictionary<string/*!*/, List<List<int>>/*!*/>();
      // function definition given as list of 'pointwise definitions' in the form of the arguments and result
      // the last element here will always be a list with just one entry which corresponds to the else case
      List<List<int>> functionDefinition = new List<List<int>>();
      // list of arguments, followed by the result, the last element of this list is always the result
      List<int> argumentsAndResult = new List<int>();

      // read F
      while (true) {
        functionDefinition = new List<List<int>>();
        string s = FromReadLine();
        // end of F, "END_OF_MODEL" ends model, '.' ends whole VC, 'l' starts a new set of labels and model
        //           whenever there is a model this will end with "END_OF_MODEL", the other cases can only
        //           happen when there is no model printed!
        if (s == "." || s.StartsWith("labels: (") || s == "END_OF_MODEL") {
          errModel = new Z3ErrorModel(identifierToPartition, partitionToIdentifiers, partitionToValue, valueToPartition, definedFunctions);
          return s;
        }
        int j = s.IndexOf(' ', 0);
        Contract.Assume(0 <= j);
        string id = s.Substring(0, j);
        // id is stored into definedFunctions once the function definition for it has 
        // been completely parsed. 

        if (s.IndexOf("-> {") < 0) {
          // This function was a macro and we are not parsing its definition currently.
          // Just move on to the next function.
          while (true) {
            s = FromReadLine();
            if (0 <= s.IndexOf("{" + id + "}"))
              break;
          }
          continue;
        }

        // just ignore the "-> {" by dropping string s
        string zIDstring;

        // MAPLET
        while (true) {
          argumentsAndResult = new List<int>();
          // remove the 2 spaces that are here
          FromReadChar();
          FromReadChar();
          s = FromReadLine();
          if (s.StartsWith("else ->")) break;
          j = 0;

          //ZID*
          while (true) {
            cce.LoopInvariant(0 <= j && j <= s.Length);

            j = s.IndexOfAny(new Char[] { '*', '-' }, j);
            // true because this always ends with a "->":
            Contract.Assume(0 <= j);

            // reading -> means end of ZID*
            if (s[j] == '-'/*>*/) break;

            // start reading the ZID* with the number, not the *
            j = j + 1;
            // by input string format:
            Contract.Assume(j < s.Length);
            int k = s.IndexOf(' ', j);
            // by input string format:
            Contract.Assume(j <= k);
            zIDstring = s.Substring(j, k - j);
            // add the arguments
            argumentsAndResult.Add(int.Parse(zIDstring));
            j = k;
          }// end ZID*

          // j is the beginning of "-> *", we want the first character after this
          j = j + 4;
          // by input string format:
          Contract.Assume(j <= s.Length);
          zIDstring = s.Substring(j);
          // add the result
          argumentsAndResult.Add(int.Parse(zIDstring));
          // add the input line as another 'pointwise defined' element to the functions definition
          functionDefinition.Add(argumentsAndResult);
        }// end MAPLET

        // this is the 'else -> #unspecified' case
        // by input string format:
        Contract.Assume(s.IndexOf("#unspec") >= 0);
        // this stores the else line as another argumentsAndResult list
        argumentsAndResult = new List<int>();
        argumentsAndResult.Add(partitionToIdentifiers.Count - 1); // use the fake partition we have created before
        // which is then added to the function definition, which is now complete
        cce.Owner.AssignSame(argumentsAndResult, cce.Owner.ElementProxy(functionDefinition));
        functionDefinition.Add(argumentsAndResult);

        /*
            // this is the 'else -> *' case, that string is already in s
            j = s.IndexOf('*', 0) + 1;
            // by input string format:
            assume 0 < j && j < s.Length;
            zIDstring = s.Substring(j);
            // this stores the else line as another argumentsAndResult list
            argumentsAndResult = new List<int>();
            argumentsAndResult.Add(int.Parse(zIDstring));
            // which is then added to the function definition, which is now complete
            functionDefinition.Add(argumentsAndResult); */

        // and therefore added to the map of defined functions, together with the name 'id'
        // which had been extracted before
        Contract.Assume(!definedFunctions.ContainsKey(id));  // each function name in the model is listed only once
        definedFunctions.Add(id, functionDefinition);

        // read the line with "}"
        ch = FromReadChar();
        Expect(ch, "}");
        FromReadLine();
      }// end F
    }

  }


  public class Z3ErrorModel : ErrorModel
  {
    public Z3ErrorModel(Dictionary<string/*!*/, int>/*!*/ identifierToPartition,
      List<List<string/*!*/>>/*!*/ partitionToIdentifiers,
    List<Object>/*!*/ partitionToValue,
    Dictionary<object, int>/*!*/ valueToPartition,
    Dictionary<string/*!*/, List<List<int>>/*!*/>/*!*/ definedFunctions)
      : base(identifierToPartition, partitionToIdentifiers, partitionToValue, valueToPartition, definedFunctions) {
      Contract.Requires(identifierToPartition != null && cce.NonNullElements(identifierToPartition.Keys));
      Contract.Requires(partitionToIdentifiers != null && Contract.ForAll(partitionToIdentifiers, x => cce.NonNullElements(x)));
      Contract.Requires(partitionToValue != null);
      Contract.Requires(valueToPartition != null);
      Contract.Requires(definedFunctions != null && cce.NonNullElements(definedFunctions.Keys) && cce.NonNullElements(definedFunctions.Values));

      this.partitionNames = new string/*?*/[partitionToIdentifiers.Count];
      this.prevPartitionNames = new string/*?*/[partitionToIdentifiers.Count];
    }

    private string/*?*/[]/*!*/ partitionNames;
    private string/*?*/[]/*!*/ prevPartitionNames;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(partitionNames != null);
      Contract.Invariant(prevPartitionNames != null);
    }


    private void SetNames() {
      int len = partitionToIdentifiers.Count;
      for (int i = 0; i < 3; ++i) { // let the names stabilize a bit
        prevPartitionNames = partitionNames;
        partitionNames = new string[len];
        for (int pos = 0; pos < len; ++pos)
          GetPartitionName(pos);
      }
    }

    private int NameBadness(string name) {
      Contract.Requires(name != null);
      int badness = name.Length;
      if (name.StartsWith("call") && name.IndexOf("formal@") > 0)
        badness += 1000;
      if (name.IndexOf("(") > 0)
        badness += 500;
      return badness;
    }

    private string GetPartitionName(int pos) {
      Contract.Ensures(Contract.Result<string>() != null);

      string name = partitionNames[pos];
      if (name != null) {
        return name;
      }

      object tmp = partitionToValue[pos];
      if (tmp != null) {
        partitionNames[pos] = tmp is BvConst ? ((BvConst)tmp).ToReadableString() : tmp.ToString();
      } else {
        List<string/*!*/>/*!*/ possible_names = new List<string/*!*/>();
        List<string/*!*/> pti = partitionToIdentifiers[pos];
        Contract.Assert(cce.NonNullElements(pti));

        // make sure we're not called recursively
        string prevName = prevPartitionNames[pos];
        if (prevName == null) prevName = "*" + pos;
        partitionNames[pos] = prevName;

        if (pti != null && pti.Count > 0) {
          // add identifiers
          foreach (string n in pti) {
            Contract.Assert(n != null);
            possible_names.Add(n);
          }
        }

        // Then also look for functions,
        // and then collect possible functional definitions
        foreach (KeyValuePair<string/*!*/, List<List<int>>/*!*/> kv in definedFunctions) {
          Contract.Assert(kv.Key != null);
          Contract.Assert(kv.Value != null);
          foreach (List<int> parms in kv.Value) {
            if (parms.Count > 1 && parms[parms.Count - 1] == pos) {
              string s = kv.Key + "(";
              for (int i = 0; i < parms.Count - 1; ++i) {
                if (i != 0) s += ", ";
                s += GetPartitionName(parms[i]);
              }
              s += ")";
              possible_names.Add(s);
            }
          }
        }

        // choose the shortest possible name
        if (possible_names.Count > 0) {
          string best = possible_names[0];
          foreach (string s in possible_names) {
            Contract.Assert(s != null);
            if (NameBadness(s) < NameBadness(best)) best = s;
          }
          if (best.Length < 120)
            partitionNames[pos] = best;
        }
      }

      return cce.NonNull(partitionNames[pos]);
    }

    private void PrintReadableModel(TextWriter writer) {
      Contract.Requires(writer != null);
      writer.WriteLine("Z3 error model: ");
      SetNames();
      writer.WriteLine("partitions:");
      Contract.Assert(partitionToIdentifiers.Count == partitionToValue.Count);
      for (int i = 0; i < partitionToIdentifiers.Count; i++) {
        writer.Write("{0,5}: {1}  ", "*" + i, GetPartitionName(i));
        List<string/*!*/> pti = partitionToIdentifiers[i];
        Contract.Assert(cce.NonNullElements(pti));
        if (pti != null && (pti.Count > 1 || (pti.Count == 1 && partitionToValue[i] != null))) {
          writer.Write("{");
          for (int k = 0; k < pti.Count - 1; k++) {
            writer.Write(pti[k] + " ");
          }
          //extra work to make sure no " " is at the end of the list of identifiers
          if (pti.Count != 0) {
            writer.Write(pti[pti.Count - 1]);
          }
          writer.Write("}");
        }
        writer.WriteLine();
      }

      writer.WriteLine();
      writer.WriteLine("function interpretations:");
      List<string> funNames = new List<string>(definedFunctions.Keys);
      funNames.Sort();
      foreach (string name in funNames) {
        Contract.Assert(name != null);
        if (definedFunctions[name].Count == 1) continue; // skip functions with only the else-> clause
        foreach (List<int> parms in definedFunctions[name]) {
          Contract.Assert(parms != null);
          string s = name + "(";
          if (parms.Count == 1) {
            continue;
            // s += "*";
          } else {
            for (int i = 0; i < parms.Count - 1; ++i) {
              if (i != 0) s += ", ";
              s += GetPartitionName(parms[i]);
            }
          }
          s += ")";
          string res = GetPartitionName(parms[parms.Count - 1]);
          if (res == s)
            res = "*" + parms[parms.Count - 1] + " (SELF)";
          writer.WriteLine("{0} = {1}", s, res);
        }
        writer.WriteLine();
      }
      writer.WriteLine("The end.");
      writer.WriteLine();
    }

    public override void Print(TextWriter writer) {
      //Contract.Requires(writer != null);
      if (CommandLineOptions.Clo.PrintErrorModel == 4) {
        PrintReadableModel(writer);
      } else {
        base.Print(writer);
      }
    }
  }
}


