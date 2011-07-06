//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie.SMTLib
{
  class Z3
  {
    static string _proverPath;

    static string CodebaseString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location));
    }

    public static string ExecutablePath()
    {
      if (_proverPath == null)
        FindExecutable();
      return _proverPath;
    }

    static void FindExecutable()
    // throws ProverException, System.IO.FileNotFoundException;
    {      
      Contract.Ensures(_proverPath != null);

      var proverExe = "z3.exe";

      if (_proverPath == null) {
        // Initialize '_proverPath'
        _proverPath = Path.Combine(CodebaseString(), proverExe);
        string firstTry = _proverPath;

        if (File.Exists(firstTry))
          return;

        string programFiles = Environment.GetEnvironmentVariable("ProgramFiles");
        Contract.Assert(programFiles != null);
        string programFilesX86 = Environment.GetEnvironmentVariable("ProgramFiles(x86)");
        if (programFiles.Equals(programFilesX86)) {
          // If both %ProgramFiles% and %ProgramFiles(x86)% point to "ProgramFiles (x86)", use %ProgramW6432% instead.
          programFiles = Environment.GetEnvironmentVariable("ProgramW6432");
        }


        List<string> z3Dirs = new List<string>();
        if (Directory.Exists(programFiles + @"\Microsoft Research\")) {
          string msrDir = programFiles + @"\Microsoft Research\";
          z3Dirs.AddRange(Directory.GetDirectories(msrDir, "Z3-*"));
        }
        if (Directory.Exists(programFilesX86 + @"\Microsoft Research\")) {
          string msrDir = programFilesX86 + @"\Microsoft Research\";
          z3Dirs.AddRange(Directory.GetDirectories(msrDir, "Z3-*"));
        }

        // Look for the most recent version of Z3.
        int minor = 0, major = 0;
        string winner = null;
        Regex r = new Regex(@"^Z3-(\d+)\.(\d+)$");
        foreach (string d in z3Dirs) {
          string name = new DirectoryInfo(d).Name;
          foreach (Match m in r.Matches(name)) {
            int ma, mi;
            ma = int.Parse(m.Groups[1].ToString());
            mi = int.Parse(m.Groups[2].ToString());
            if (major < ma || (major == ma && minor < mi)) {
              major = ma;
              minor = mi;
              winner = d;
            }
          }
        }

        if (major == 0 && minor == 0) {
          throw new ProverException("Cannot find executable: " + firstTry);
        }
        Contract.Assert(winner != null);

        _proverPath = Path.Combine(Path.Combine(winner, "bin"), proverExe);
        if (!File.Exists(_proverPath)) {
          throw new ProverException("Cannot find prover: " + _proverPath);
        }

        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("[TRACE] Using prover: " + _proverPath);
        }
      }
    }

    // options that work only on the command line
    static string[] commandLineOnly = { "TRACE", "PROOF_MODE" };

    public static void SetupOptions(SMTLibProverOptions options)
    {
      // don't bother with auto-config - it would disable explicit settings for eager threshold and so on
      options.AddWeakSmtOption("AUTO_CONFIG", "false");

      //options.AddWeakSmtOption("MODEL_PARTIAL", "true");
      //options.WeakAddSmtOption("MODEL_VALUE_COMPLETION", "false");
      options.AddWeakSmtOption("MODEL_HIDE_UNUSED_PARTITIONS", "false");
      options.AddWeakSmtOption("MODEL_V2", "true");
      options.AddWeakSmtOption("ASYNC_COMMANDS", "false");

      if (!options.OptimizeForBv) {
        // Phase selection means to always try the negative literal polarity first, seems to be good for Boogie.
        // The restart parameters change the restart behavior to match Z3 v1, which also seems to be good.
        options.AddWeakSmtOption("PHASE_SELECTION", "0");
        options.AddWeakSmtOption("RESTART_STRATEGY", "0");
        options.AddWeakSmtOption("RESTART_FACTOR", "|1.5|");

        // Make the integer model more diverse by default, speeds up some benchmarks a lot.
        options.AddWeakSmtOption("ARITH_RANDOM_INITIAL_VALUE", "true");

        // The left-to-right structural case-splitting strategy.
        //options.AddWeakSmtOption("SORT_AND_OR", "false"); // always false now
        options.AddWeakSmtOption("CASE_SPLIT", "3");

        // In addition delay adding unit conflicts.
        options.AddWeakSmtOption("DELAY_UNITS", "true");
        options.AddWeakSmtOption("DELAY_UNITS_THRESHOLD", "16");
      }

      // This is used by VCC, but could be also useful for others, if sk_hack(foo(x)) is included as trigger,
      // the foo(x0) will be activated for e-matching when x is skolemized to x0.
      options.AddWeakSmtOption("NNF_SK_HACK", "true");

      // don't use model-based quantifier instantiation; it never finishes on non-trivial Boogie problems
      options.AddWeakSmtOption("MBQI", "false");      

      // More or less like MAM=0.
      options.AddWeakSmtOption("QI_EAGER_THRESHOLD", "100");
      // Complex proof attempts in VCC (and likely elsewhere) require matching depth of 20 or more.

      // the following will make the :weight option more usable
      options.AddWeakSmtOption("QI_COST", "|\"(+ weight generation)\"|");

      //if (options.Inspector != null)
      //  options.WeakAddSmtOption("PROGRESS_SAMPLING_FREQ", "100");

      options.AddWeakSmtOption("TYPE_CHECK", "true");
      options.AddWeakSmtOption("BV_REFLECT", "true");

      if (CommandLineOptions.Clo.LazyInlining == 2) {
        options.AddWeakSmtOption("MACRO_EXPANSION", "true");
        options.AddWeakSmtOption("WARNING", "false");
      }

      if (options.TimeLimit > 0) {
        options.AddWeakSmtOption("SOFT_TIMEOUT", options.TimeLimit.ToString());
        options.AddSolverArgument("/T:" + (options.TimeLimit + 1000) / 1000);
      }

      // legacy option handling
      if (!CommandLineOptions.Clo.z3AtFlag)
        options.MultiTraces = true;

      foreach (string opt in CommandLineOptions.Clo.Z3Options) {
        Contract.Assert(opt != null);
        int eq = opt.IndexOf("=");
        if (eq > 0 && 'A' <= opt[0] && opt[0] <= 'Z' && !commandLineOnly.Contains(opt.Substring(0, eq))) {
          options.AddSmtOption(opt.Substring(0, eq), opt.Substring(eq + 1));
        } else {
          options.AddSolverArgument(opt);
        }
      }
    }


  }
}
