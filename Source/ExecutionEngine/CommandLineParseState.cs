using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class CommandLineParseState
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

  public bool CheckBooleanFlag(string flagName, Action<bool> setFlag, bool valueWhenPresent = true)
  {
    Contract.Requires(flagName != null);
    //modifies nextIndex, encounteredErrors, Console.Error.*;
    bool flagPresent = false;

    if ((s == "/" + flagName || s == "-" + flagName) && ConfirmArgumentCount(0))
    {
      setFlag(valueWhenPresent);
      flagPresent = true;
    }

    return flagPresent;
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
  /// If there is one argument and it is a non-negative integer,
  /// then call "setArg" with that number mapped to a boolean and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetIntArgument(Action<bool> setArg)
  {
    int intArg = 0;
    var result = GetIntArgument(ref intArg, x => x < 2);
    if (result) {
      setArg(intArg != 0);
    }
    return result;
  }

  /// <summary>
  /// If there is one argument and it is a non-negative integer, then set "arg" to that number and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetIntArgument(ref bool arg)
  {
    int intArg = 0;
    var result = GetIntArgument(ref intArg, x => x < 2);
    if (result) {
      arg = intArg != 0;
    }
    return result;
  }

  /// <summary>
  /// If there is one argument and it is a non-negative integer, then call "setArg" with that number and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetIntArgument(Action<int> setArg, Predicate<int> filter = null)
  {
    filter ??= a => 0 <= a;

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
          setArg(d);
          return true;
        }
      }
      catch (FormatException)
      {
      }
      catch (OverflowException)
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
  /// If there is one argument and it is a non-negative integer, then set "arg" to that number and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetIntArgument(ref int arg)
  {
    //modifies nextIndex, encounteredErrors, Console.Error.*;
    return GetIntArgument(ref arg, a => 0 <= a);
  }

  public bool GetUnsignedNumericArgument(Action<uint> setArg, Predicate<uint> filter = null)
  {
    if (ConfirmArgumentCount(1))
    {
      try
      {
        Contract.Assume(args[i] != null);
        Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
        uint d = Convert.ToUInt32(this.args[this.i]);
        if (filter == null || filter(d))
        {
          setArg(d);
          return true;
        }
      }
      catch (FormatException)
      {
      }
      catch (OverflowException)
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
  public bool GetIntArgument(ref int arg, Predicate<int> filter)
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
  /// then call "setArg" with that number and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetIntArgument(Action<int> setArg, int limit)
  {
    Contract.Requires(this.i < args.Length);
    int a = 0;
    if (!GetIntArgument(x => a = x))
    {
      return false;
    }

    if (a < limit) {
      setArg(a);
      return true;
    }

    Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
    return false;
  }

  /// <summary>
  /// If there is one argument and it is a non-negative integer less than "limit",
  /// then set "arg" to that number and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetIntArgument(ref int arg, int limit)
  {
    Contract.Requires(this.i < args.Length);
    Contract.Ensures(Math.Min(arg, 0) <= Contract.ValueAtReturn(out arg) &&
                     Contract.ValueAtReturn(out arg) < limit);
    //modifies nextIndex, encounteredErrors, Console.Error.*;
    int a = arg;
    if (!GetIntArgument(ref a))
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
  /// If there is one argument and it is a non-negative real,
  /// then call "setArg" with that number and return "true".
  /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
  /// </summary>
  public bool GetDoubleArgument(Action<double> setArg)
  {
    //modifies nextIndex, encounteredErrors, Console.Error.*;
    if (this.ConfirmArgumentCount(1))
    {
      try
      {
        Contract.Assume(args[i] != null);
        Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
        double d = Convert.ToDouble(this.args[this.i]);
        if (0 <= d) {
          setArg(d);
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