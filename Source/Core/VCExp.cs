//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Reflection;
using System.Text;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
namespace Microsoft.Boogie {

  public class ProverOptions {
    public class OptionException : Exception {
      public OptionException(string msg)
        : base(msg) {
        Contract.Requires(msg != null);
      }
    }

    public string/*?*/ LogFilename = null;
    public bool AppendLogFile = false;
    public bool SeparateLogFiles = false;
    // Say (DBG_WAS_VALID) or (DBG_WAS_INVALID) after query
    public bool ForceLogStatus = false;
    public int TimeLimit = 0;
    public int ResourceLimit = 0;
    public int MemoryLimit = 0;
    public int Verbosity = 0;
    public string ProverPath;

    private string/*!*/ stringRepr = "";
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(stringRepr != null);
    }


    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return stringRepr;
    }

    // The usual thing to override.
    protected virtual bool Parse(string opt) {
      Contract.Requires(opt != null);
      return ParseString(opt, "LOG_FILE", ref LogFilename) ||
             ParseBool(opt, "APPEND_LOG_FILE", ref AppendLogFile) ||
             ParseBool(opt, "FORCE_LOG_STATUS", ref ForceLogStatus) ||
             ParseInt(opt, "MEMORY_LIMIT", ref MemoryLimit) ||
             ParseInt(opt, "VERBOSITY", ref Verbosity) ||
             ParseInt(opt, "TIME_LIMIT", ref TimeLimit) || 
             ParseString(opt, "PROVER_PATH", ref ProverPath);
      // || base.Parse(opt)
    }

    public virtual string Help
    {
      get
      {
        return
@"
Generic prover options :
~~~~~~~~~~~~~~~~~~~~~~~
LOG_FILE=<string>         Log input for the theorem prover. The string @PROC@ in the filename
                          causes there to be one prover log file per verification condition, 
                          and is expanded to the name of the procedure that the verification 
                          condition is for.
APPEND_LOG_FILE=<bool>    Append, rather than overwrite the log file.
MEMORY_LIMIT=<int>        Memory limit of the prover in megabytes.
VERBOSITY=<int>           The higher, the more verbose.
TIME_LIMIT=<int>          Time limit per verification condition in miliseconds.
PROVER_PATH=<string>      Path to the prover to use.

The generic options may or may not be used by the prover plugin.
";

      }
    }

    public virtual void Parse(IEnumerable<string/*!*/>/*!*/ opts) {
      Contract.Requires(cce.NonNullElements(opts));
      StringBuilder sb = new StringBuilder(stringRepr);
      Contract.Assert(sb != null);
      foreach (string/*!*/ opt in opts) {
        Contract.Assert(opt != null);
        if (!Parse(opt)) {
          ReportError("Unrecognised prover option: " + opt);
        }
        sb.Append(opt).Append(" ");
      }
      stringRepr = sb.ToString();
      PostParse();
    }

    public virtual void PostParse() {
      if (LogFilename != null && LogFilename.Contains("@PROC@")) {
        SeparateLogFiles = true;
      }
    }

    protected void ReportError(string msg) {
      Contract.Requires(msg != null);
      throw new OptionException(msg + "\n\n" + Help);
    }

    protected virtual bool ParseString(string opt, string name, ref string field) {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      if (opt.Length >= name.Length && opt.StartsWith(name)) {
        if (opt.Length == name.Length) {
          field = "";
          return true;
        } else if (opt[name.Length] == '=' || opt[name.Length] == ':') {
          field = opt.Substring(name.Length + 1);
          return true;
        }
      }
      return false;
    }

    protected virtual bool ParseBool(string opt, string name, ref bool field) {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      string tmp = null;
      if (ParseString(opt, name, ref tmp))
        switch (cce.NonNull(tmp).ToLower()) {
          case "1":
          case "true":
          case "":
            field = true;
            return true;
          case "0":
          case "false":
            field = false;
            return true;
          default:
            ReportError("Invalid Boolean option \"" + opt + "\"");
            return false;
        }
      return false;
    }

    protected virtual bool ParseInt(string opt, string name, ref int field) {
      Contract.Requires(name != null);
      Contract.Requires(opt != null);
      string tmp = null;
      int t2;
      if (ParseString(opt, name, ref tmp)) {
        if (int.TryParse(cce.NonNull(tmp), out t2)) {
          field = t2;
          return true;
        } else {
          ReportError("Invalid integer option \"" + opt + "\"");
        }
      }
      return false;
    }

    public virtual TextWriter OpenLog(string/*?*/ descName) {
      if (LogFilename != null) {
        string filename = LogFilename;
        Contract.Assert(filename != null);
        if (descName != null)
          filename = Helpers.SubstituteAtPROC(descName, filename);
        return new StreamWriter(filename, AppendLogFile);
      } else {
        return null;
      }
    }
  }

  [ContractClass(typeof(ProverFactoryContracts))]
  public abstract class ProverFactory {
    // Really returns ProverInterface.
    //public abstract object! SpawnProver(ProverOptions! options, object! ctxt);
    public abstract object SpawnProver(ProverOptions options, object ctxt);

    // Really returns ProverContext
    public abstract object/*!*/ NewProverContext(ProverOptions/*!*/ options);

    public virtual ProverOptions BlankProverOptions() {
      Contract.Ensures(Contract.Result<ProverOptions>() != null);
      return new ProverOptions();
    }

    // return true if the prover supports DAG AST as opposed to LET AST
    public virtual bool SupportsDags {
      get {
        return false;
      }
    }

    public virtual CommandLineOptions.VCVariety DefaultVCVariety {
      get {
        Contract.Ensures(Contract.Result<CommandLineOptions.VCVariety>() != CommandLineOptions.VCVariety.Unspecified);
        return CommandLineOptions.VCVariety.DagIterative;
      }
    }

    public virtual bool SupportsLabels(ProverOptions options) {
      return true;
    }

    public virtual void Close() {
    }

    public static ProverFactory Load(string proverName) {
      Contract.Requires(proverName != null);
      Contract.Ensures(Contract.Result<ProverFactory>() != null);
      Contract.Ensures(cce.IsNew(Contract.Result<ProverFactory>()) && cce.Owner.New(Contract.Result<ProverFactory>()));
      string/*!*/ path;
      if (proverName.IndexOf("/") > 0 || proverName.IndexOf("\\") > 0) {
        path = proverName;
      } else {
        string codebase = cce.NonNull(System.IO.Path.GetDirectoryName(
                                 cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
        path = System.IO.Path.Combine(codebase, "Provers." + proverName + ".dll");
      }
      Assembly asm = cce.NonNull(Assembly.LoadFrom(path));
      string name = cce.NonNull(asm.GetName().Name);
      System.Type factoryType = cce.NonNull(asm.GetType("Microsoft.Boogie." + name.Replace("Provers.", "") + ".Factory"));
      return cce.NonNull((ProverFactory/*!*/)Activator.CreateInstance(factoryType));
    }
  }
  [ContractClassFor(typeof(ProverFactory))]
  public abstract class ProverFactoryContracts : ProverFactory {
    public override object NewProverContext(ProverOptions options) {
      Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      throw new NotImplementedException();
    }
  }
}
