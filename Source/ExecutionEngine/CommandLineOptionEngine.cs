using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie;

public class CommandLineOptionEngine
{
  public readonly string ToolName;
  public readonly string DescriptiveToolName;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(ToolName != null);
    Contract.Invariant(DescriptiveToolName != null);
    Contract.Invariant(this._environment != null);
    Contract.Invariant(cce.NonNullElements(this._files));
    Contract.Invariant(this._fileTimestamp != null);
  }

  private string /*!*/
    _environment = "";

  public string Environment
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this._environment;
    }
    set
    {
      Contract.Requires(value != null);
      this._environment = value;
    }
  }

  private readonly List<string /*!*/> /*!*/
    _files = new List<string /*!*/>();

  public IList<string /*!*/> /*!*/ Files
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<IList<string>>()));
      Contract.Ensures(Contract.Result<IList<string>>().IsReadOnly);
      return this._files.AsReadOnly();
    }
  }

  public bool VersionRequested = false;
  public bool HelpRequested = false;
  public bool AttributeHelpRequested = false;

  public CommandLineOptionEngine(string toolName, string descriptiveName)
  {
    Contract.Requires(toolName != null);
    Contract.Requires(descriptiveName != null);
    ToolName = toolName;
    DescriptiveToolName = descriptiveName;
  }

  public virtual string /*!*/ VersionNumber
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return cce.NonNull(cce
        .NonNull(System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly()
          .Location)).FileVersion);
    }
  }

  public virtual string /*!*/ VersionSuffix
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return " version " + VersionNumber + ", Copyright (c) 2003-2014, Microsoft.";
    }
  }

  public virtual string /*!*/ Version
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return DescriptiveToolName + VersionSuffix;
    }
  }

  private string /*!*/
    _fileTimestamp = cce.NonNull(DateTime.Now.ToString("o")).Replace(':', '.');

  public string FileTimestamp
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this._fileTimestamp;
    }
    set
    {
      Contract.Requires(value != null);
      this._fileTimestamp = value;
    }
  }

  public void ExpandFilename(ref string pattern, string logPrefix, string fileTimestamp)
  {
    if (pattern != null)
    {
      pattern = pattern.Replace("@PREFIX@", logPrefix).Replace("@TIME@", fileTimestamp);
      string fn = Files.Count == 0 ? "" : Files[Files.Count - 1];
      fn = Util.EscapeFilename(fn);
      pattern = pattern.Replace("@FILE@", fn);
    }
  }

  /// <summary>
  /// Process the option and modify "ps" accordingly.
  /// Return true if the option is one that is recognized.
  /// </summary>
  protected virtual bool ParseOption(string name, CommandLineParseState ps)
  {
    Contract.Requires(name != null);
    Contract.Requires(ps != null);

    if (ps.CheckBooleanFlag("version", ref VersionRequested) ||
        ps.CheckBooleanFlag("help", ref HelpRequested) ||
        ps.CheckBooleanFlag("?", ref HelpRequested) ||
        ps.CheckBooleanFlag("attrHelp", ref AttributeHelpRequested))
    {
      return true;
    }

    return false; // unrecognized option
  }

  protected class CommandLineParseState
  {
    public string s;
    public bool hasColonArgument;

    public readonly string[] /*!*/
      args;

    public int i;
    public int nextIndex;
    public bool EncounteredErrors;
    public readonly string ToolName;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(args != null);
      Contract.Invariant(0 <= i && i <= args.Length);
      Contract.Invariant(0 <= nextIndex && nextIndex <= args.Length);
    }


    public CommandLineParseState(string[] args, string toolName)
    {
      Contract.Requires(args != null);
      Contract.Requires(Contract.ForAll(0, args.Length, i => args[i] != null));
      Contract.Requires(toolName != null);
      Contract.Ensures(this.args == args);
      this.ToolName = toolName;
      this.s = null; // set later by client
      this.hasColonArgument = false; // set later by client
      this.args = args;
      this.i = 0;
      this.nextIndex = 0; // set later by client
      this.EncounteredErrors = false;
    }

    public bool CheckBooleanFlag(string flagName, ref bool flag, bool valueWhenPresent)
    {
      Contract.Requires(flagName != null);
      //modifies nextIndex, encounteredErrors, Console.Error.*;
      bool flagPresent = false;

      if ((s == "/" + flagName || s == "-" + flagName) && ConfirmArgumentCount(0))
      {
        flag = valueWhenPresent;
        flagPresent = true;
      }

      return flagPresent;
    }

    public bool CheckBooleanFlag(string flagName, ref bool flag)
    {
      Contract.Requires(flagName != null);
      //modifies nextIndex, encounteredErrors, Console.Error.*;
      return CheckBooleanFlag(flagName, ref flag, true);
    }

    /// <summary>
    /// If there is one argument and it is a non-negative integer, then set "arg" to that number and return "true".
    /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
    /// </summary>
    public bool GetNumericArgument(ref bool arg)
    {
      int intArg = 0;
      var result = GetNumericArgument(ref intArg, x => x < 2);
      if (result) {
        arg = intArg != 0;
      }
      return result;
    }
      
    /// <summary>
    /// If there is one argument and it is a non-negative integer, then set "arg" to that number and return "true".
    /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
    /// </summary>
    public bool GetNumericArgument(ref int arg)
    {
      //modifies nextIndex, encounteredErrors, Console.Error.*;
      return GetNumericArgument(ref arg, a => 0 <= a);
    }

    public bool GetUnsignedNumericArgument(ref uint arg, Predicate<uint> filter)
    {
      if (this.ConfirmArgumentCount(1))
      {
        try
        {
          Contract.Assume(args[i] != null);
          Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
          uint d = Convert.ToUInt32(this.args[this.i]);
          if (filter == null || filter(d))
          {
            arg = d;
            return true;
          }
        }
        catch (System.FormatException)
        {
        }
        catch (System.OverflowException)
        {
        }
      }
      else
      {
        return false;
      }

      Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
      return false;
    }

    /// <summary>
    /// If there is one argument and the filtering predicate holds, then set "arg" to that number and return "true".
    /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
    /// </summary>
    public bool GetNumericArgument(ref int arg, Predicate<int> filter)
    {
      Contract.Requires(filter != null);

      if (this.ConfirmArgumentCount(1))
      {
        try
        {
          Contract.Assume(args[i] != null);
          Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
          int d = Convert.ToInt32(this.args[this.i]);
          if (filter == null || filter(d))
          {
            arg = d;
            return true;
          }
        }
        catch (System.FormatException)
        {
        }
        catch (System.OverflowException)
        {
        }
      }
      else
      {
        return false;
      }

      Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
      return false;
    }

    /// <summary>
    /// If there is one argument and it is a non-negative integer less than "limit",
    /// then set "arg" to that number and return "true".
    /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
    /// </summary>
    public bool GetNumericArgument(ref int arg, int limit)
    {
      Contract.Requires(this.i < args.Length);
      Contract.Ensures(Math.Min(arg, 0) <= Contract.ValueAtReturn(out arg) &&
                       Contract.ValueAtReturn(out arg) < limit);
      //modifies nextIndex, encounteredErrors, Console.Error.*;
      int a = arg;
      if (!GetNumericArgument(ref a))
      {
        return false;
      }
      else if (a < limit)
      {
        arg = a;
        return true;
      }
      else
      {
        Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
        return false;
      }
    }

    /// <summary>
    /// If there is one argument and it is a non-negative real, then set "arg" to that number and return "true".
    /// Otherwise, emit an error message, leave "arg" unchanged, and return "false".
    /// </summary>
    public bool GetNumericArgument(ref double arg)
    {
      Contract.Ensures(Contract.ValueAtReturn(out arg) >= 0);
      //modifies nextIndex, encounteredErrors, Console.Error.*;
      if (this.ConfirmArgumentCount(1))
      {
        try
        {
          Contract.Assume(args[i] != null);
          Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
          double d = Convert.ToDouble(this.args[this.i]);
          if (0 <= d)
          {
            arg = d;
            return true;
          }
        }
        catch (System.FormatException)
        {
        }
        catch (System.OverflowException)
        {
        }
      }
      else
      {
        return false;
      }

      Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
      return false;
    }

    public bool ConfirmArgumentCount(int argCount)
    {
      Contract.Requires(0 <= argCount);
      //modifies nextIndex, encounteredErrors, Console.Error.*;
      Contract.Ensures(Contract.Result<bool>() ==
                       (!(hasColonArgument && argCount != 1) && !(args.Length < i + argCount)));
      if (hasColonArgument && argCount != 1)
      {
        Error("\"{0}\" cannot take a colon argument", s);
        nextIndex = args.Length;
        return false;
      }
      else if (args.Length < i + argCount)
      {
        Error("\"{0}\" expects {1} argument{2}", s, argCount.ToString(), (string) (argCount == 1 ? "" : "s"));
        nextIndex = args.Length;
        return false;
      }
      else
      {
        nextIndex = i + argCount;
        return true;
      }
    }

    public void Error(string message, params string[] args)
    {
      Contract.Requires(args != null);
      Contract.Requires(message != null);
      //modifies encounteredErrors, Console.Error.*;
      Console.Error.WriteLine("{0}: Error: {1}", ToolName, String.Format(message, args));
      EncounteredErrors = true;
    }
  }

  public virtual string Help =>
    $"Usage: {ToolName} [ option ... ] [ filename ... ]" + @"

  ---- General options -------------------------------------------------------

  /version      print the " + ToolName + @" version number
  /help         print this message
  /attrHelp     print a message about supported declaration attributes";

  public virtual string AttributeHelp => "";

  /// <summary>
  /// This method is called after all parsing is done, if no parse errors were encountered.
  /// </summary>
  public virtual void ApplyDefaultOptions()
  {
  }

  public virtual bool ProcessInfoFlags()
  {
    if (VersionRequested)
    {
      Console.WriteLine(Version);
      return true;
    }
    if (HelpRequested)
    {
      Console.WriteLine(Help);
      return true;
    }
    if (AttributeHelpRequested)
    {
      Console.WriteLine(AttributeHelp);
      return true;
    }
    return false;
  }

  /// <summary>
  /// Parses the command-line arguments "args" into the global flag variables.  Returns true
  /// if there were no errors.
  /// </summary>
  /// <param name="args">Consumed ("captured" and possibly modified) by the method.</param>
  public bool Parse([Captured] string[] /*!*/ args)
  {
    Contract.Requires(cce.NonNullElements(args));

    // save the command line options for the log files
    Environment += "Command Line Options: " + args.Concat(" ");
    args = cce.NonNull((string[]) args.Clone()); // the operations performed may mutate the array, so make a copy
    var ps = new CommandLineParseState(args, ToolName);

    while (ps.i < args.Length)
    {
      cce.LoopInvariant(ps.args == args);
      string arg = args[ps.i];
      Contract.Assert(arg != null);
      ps.s = arg.Trim();

      bool isOption = ps.s.StartsWith("-") || ps.s.StartsWith("/");
      int colonIndex = ps.s.IndexOf(':');
      if (0 <= colonIndex && isOption)
      {
        ps.hasColonArgument = true;
        args[ps.i] = ps.s.Substring(colonIndex + 1);
        ps.s = ps.s.Substring(0, colonIndex);
      }
      else
      {
        ps.i++;
        ps.hasColonArgument = false;
      }

      ps.nextIndex = ps.i;

      if (isOption)
      {
        if (!ParseOption(ps.s.Substring(1), ps))
        {
          if (Path.DirectorySeparatorChar == '/' && ps.s.StartsWith("/"))
          {
            this._files.Add(arg);
          }
          else
          {
            ps.Error("unknown switch: {0}", ps.s);
          }
        }
      }
      else
      {
        this._files.Add(arg);
      }

      ps.i = ps.nextIndex;
    }

    if (ps.EncounteredErrors)
    {
      Console.Error.WriteLine("Use /help for available options");
      return false;
    }
    else
    {
      this.ApplyDefaultOptions();
      return true;
    }
  }
}