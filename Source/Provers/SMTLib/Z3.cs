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
        // throws ProverException, System.IO.FileNotFoundException;
        {
            if (_proverPath == null)
                FindExecutable();
            return _proverPath;
        }

        static void FindExecutable()
        // throws ProverException, System.IO.FileNotFoundException;
        {
            Contract.Ensures(_proverPath != null);

            // Command line option 'z3exe' always has priority if set 
            if (CommandLineOptions.Clo.Z3ExecutablePath != null)
            {
                _proverPath = CommandLineOptions.Clo.Z3ExecutablePath;
                if (!File.Exists(_proverPath))
                {
                    throw new ProverException("Cannot find prover specified with z3exe: " + _proverPath);
                }
                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                }
                return;
            }

            var proverExe = CommandLineOptions.Clo.Z3ExecutableName; 
            proverExe = proverExe == null ? "z3.exe" : proverExe;

            if (_proverPath == null)
            {
                // Initialize '_proverPath'
                _proverPath = Path.Combine(CodebaseString(), proverExe);
                string firstTry = _proverPath;

                if (File.Exists(firstTry))
                {
                    if (CommandLineOptions.Clo.Trace)
                    {
                        Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                    }
                    return;
                }

                List<string> z3Dirs = new List<string>();
                var msrDir = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ProgramFiles), @"Microsoft Research\");
                if (Directory.Exists(msrDir))
                {
                  z3Dirs.AddRange(Directory.GetDirectories(msrDir, "Z3-*"));
                }
                var msrDirX86 = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ProgramFilesX86), @"Microsoft Research\");
                if (Directory.Exists(msrDirX86))
                {
                  z3Dirs.AddRange(Directory.GetDirectories(msrDirX86, "Z3-*"));
                }

                int minMajor = 3, minMinor = 2;

                // Look for the most recent version of Z3.
                int minor = 0, major = 0;
                string winner = null;
                Regex r = new Regex(@"^Z3-(\d+)\.(\d+)$");
                foreach (string d in z3Dirs)
                {
                    string name = new DirectoryInfo(d).Name;
                    foreach (Match m in r.Matches(name))
                    {
                        int ma, mi;
                        ma = int.Parse(m.Groups[1].ToString());
                        mi = int.Parse(m.Groups[2].ToString());
                        if (major < ma || (major == ma && minor < mi))
                        {
                            major = ma;
                            minor = mi;
                            winner = d;
                        }
                    }
                }

                if (major == 0 && minor == 0)
                {
                    throw new ProverException("Cannot find executable: " + firstTry);
                }

                Contract.Assert(winner != null);

                _proverPath = Path.Combine(Path.Combine(winner, "bin"), proverExe);
                if (!File.Exists(_proverPath))
                {
                    throw new ProverException("Cannot find prover: " + _proverPath);
                }

                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                }

                if (major < minMajor || (major == minMajor && minor < minMinor))
                {
                    throw new ProverException(string.Format("Found version {0}.{1} of Z3. Please install version {2}.{3} or later. " +
                                                            "(More conservative users might opt to supply -prover:Z3 option instead to get the historic Simplify back-end)",
                                                            major, minor, minMajor, minMinor));
                }
            }
        }


        static int Z3MajorVersion = 0;
        static int Z3MinorVersion = 0;
        static bool Z3VersionObtained = false;

        public static void GetVersion(out int major, out int minor)
        {
            if (!Z3VersionObtained)
            {
                var proc = new System.Diagnostics.Process();
                proc.StartInfo.FileName = _proverPath;
                proc.StartInfo.Arguments = "--version";
                proc.StartInfo.RedirectStandardOutput = true;
                proc.StartInfo.RedirectStandardError = true;
                proc.StartInfo.UseShellExecute = false;
                proc.StartInfo.CreateNoWindow = true;
                proc.Start();
                string answer = proc.StandardOutput.ReadToEnd();
                proc.WaitForExit();
                if (proc.ExitCode == 0)
                {                    
                    var firstdot = answer.IndexOf('.');
                    if (firstdot >= 0)
                    {
                        var seconddot = answer.IndexOf('.', firstdot + 1);
                        if (seconddot >= firstdot + 1)
                        {
                            var spacebeforefirstdot = answer.LastIndexOf(' ', firstdot);
                            if (spacebeforefirstdot >= 0)
                            {
                                var majorstr = answer.Substring(spacebeforefirstdot, firstdot - spacebeforefirstdot);
                                var minorstr = answer.Substring(firstdot + 1, seconddot - firstdot - 1);
                                Z3MajorVersion = Convert.ToInt32(majorstr);
                                Z3MinorVersion = Convert.ToInt32(minorstr);
                            }
                        }
                    }
                }
                Z3VersionObtained = true;
            }
            major = Z3MajorVersion;
            minor = Z3MinorVersion;
        }

        public static string SetTimeoutOption()
        {
            int major, minor;
            GetVersion(out major, out minor);
            if (major > 4 || major == 4 && minor >= 3)
                return "TIMEOUT";
            else
                return "SOFT_TIMEOUT";
        }

        public static string SetRlimitOption()
        {
            int major, minor;
            GetVersion(out major, out minor);
            if (major > 4 || major == 4 && minor >= 3)
                return "RLIMIT";
            else
                // not sure what is for "rlimit" in earlier versions.
                return "";
        }

        // options that work only on the command line
        static string[] commandLineOnly = { "TRACE", "PROOF_MODE" };


        public static void SetupOptions(SMTLibProverOptions options)
        // throws ProverException, System.IO.FileNotFoundException;
        {
          FindExecutable();
          int major, minor;
          GetVersion(out major, out minor);
          if (major > 4 || major == 4 && minor >= 3)
          {

            bool fp = false; // CommandLineOptions.Clo.FixedPointEngine != null;

            // don't bother with auto-config - it would disable explicit settings for eager threshold and so on
            if(!fp) options.AddWeakSmtOption("AUTO_CONFIG", "false");

            //options.AddWeakSmtOption("MODEL_PARTIAL", "true");
            //options.WeakAddSmtOption("MODEL_VALUE_COMPLETION", "false");

            // options.AddWeakSmtOption("MODEL_HIDE_UNUSED_PARTITIONS", "false"); TODO: what does this do?

            // Make sure we get something that is parsable as a bitvector
            options.AddWeakSmtOption("pp.bv_literals", "false");
            if (!CommandLineOptions.Clo.UseSmtOutputFormat)
            {
              options.AddWeakSmtOption("MODEL.V2", "true");
            }
            //options.AddWeakSmtOption("ASYNC_COMMANDS", "false"); TODO: is this needed?

            if (!options.OptimizeForBv)
            {
              // Phase selection means to always try the negative literal polarity first, seems to be good for Boogie.
              // The restart parameters change the restart behavior to match Z3 v1, which also seems to be good.
              options.AddWeakSmtOption("smt.PHASE_SELECTION", "0");
              options.AddWeakSmtOption("smt.RESTART_STRATEGY", "0");
              options.AddWeakSmtOption("smt.RESTART_FACTOR", "|1.5|");

              // Make the integer model more diverse by default, speeds up some benchmarks a lot.
              options.AddWeakSmtOption("smt.ARITH.RANDOM_INITIAL_VALUE", "true");

              // The left-to-right structural case-splitting strategy.
              //options.AddWeakSmtOption("SORT_AND_OR", "false"); // always false now

              if (!fp) options.AddWeakSmtOption("smt.CASE_SPLIT", "3");

              // In addition delay adding unit conflicts.
              options.AddWeakSmtOption("smt.DELAY_UNITS", "true");
              //options.AddWeakSmtOption("DELAY_UNITS_THRESHOLD", "16"); TODO: what?
            }

            // This is used by VCC, but could be also useful for others, if sk_hack(foo(x)) is included as trigger,
            // the foo(x0) will be activated for e-matching when x is skolemized to x0.
            options.AddWeakSmtOption("NNF.SK_HACK", "true");

            // don't use model-based quantifier instantiation; it never finishes on non-trivial Boogie problems
            options.AddWeakSmtOption("smt.MBQI", "false");

            // More or less like MAM=0.
            options.AddWeakSmtOption("smt.QI.EAGER_THRESHOLD", "100");
            // Complex proof attempts in VCC (and likely elsewhere) require matching depth of 20 or more.

            // the following will make the :weight option more usable
              // KLM: this QI cost function is the default
            // if (!fp) options.AddWeakSmtOption("smt.QI.COST", "|(+ weight generation)|"); // TODO: this doesn't seem to work

            //if (options.Inspector != null)
            //  options.WeakAddSmtOption("PROGRESS_SAMPLING_FREQ", "100");

            options.AddWeakSmtOption("TYPE_CHECK", "true");
            options.AddWeakSmtOption("smt.BV.REFLECT", "true");

            if (major > 4 || (major == 4 && minor >= 8)) {
              // {:captureState} does not work with compressed models
              options.AddWeakSmtOption("model_compress", "false");
            }

            if (options.TimeLimit > 0)
            {
              options.AddWeakSmtOption("TIMEOUT", options.TimeLimit.ToString());
              if (major == 4 && minor < 8)
              {
                 options.AddWeakSmtOption("fixedpoint.TIMEOUT", options.TimeLimit.ToString());
              }
              // This kills the Z3 *instance* after the specified time, not a particular query, so we cannot use it.
              // options.AddSolverArgument("/T:" + (options.TimeLimit + 1000) / 1000);
            }

            if (options.ResourceLimit > 0) 
            {
              options.AddWeakSmtOption("RLIMIT", options.ResourceLimit.ToString());
            }

            if (options.Inspector != null)
              options.AddWeakSmtOption("PROGRESS_SAMPLING_FREQ", "200");

            if (CommandLineOptions.Clo.WeakArrayTheory)
            {
              options.AddWeakSmtOption("smt.array.weak", "true");
              options.AddWeakSmtOption("smt.array.extensional", "false");
            }

            if (CommandLineOptions.Clo.PrintConjectures != null && major == 4 && minor < 8)
            {
                options.AddWeakSmtOption("fixedpoint.conjecture_file", CommandLineOptions.Clo.PrintConjectures + ".tmp");
            }
          }
          else
          {
            // don't bother with auto-config - it would disable explicit settings for eager threshold and so on
            options.AddWeakSmtOption("AUTO_CONFIG", "false");

            //options.AddWeakSmtOption("MODEL_PARTIAL", "true");
            //options.WeakAddSmtOption("MODEL_VALUE_COMPLETION", "false");
            options.AddWeakSmtOption("MODEL_HIDE_UNUSED_PARTITIONS", "false");
            options.AddWeakSmtOption("ASYNC_COMMANDS", "false");

            if (CommandLineOptions.Clo.UseSmtOutputFormat)
            {
              options.AddWeakSmtOption("pp-bv-literals", "false"); ;
            }
            else
            {
              options.AddWeakSmtOption("MODEL_V2", "true");
            }

            if (!options.OptimizeForBv)
            {
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

            if (options.TimeLimit > 0)
            {
              options.AddWeakSmtOption("SOFT_TIMEOUT", options.TimeLimit.ToString());
              // This kills the Z3 *instance* after the specified time, not a particular query, so we cannot use it.
              // options.AddSolverArgument("/T:" + (options.TimeLimit + 1000) / 1000);
            }

            if (options.Inspector != null)
              options.AddWeakSmtOption("PROGRESS_SAMPLING_FREQ", "200");

            if (CommandLineOptions.Clo.WeakArrayTheory)
            {
              options.AddWeakSmtOption("ARRAY_WEAK", "true");
              options.AddWeakSmtOption("ARRAY_EXTENSIONAL", "false");
            }

            options.AddWeakSmtOption("MODEL_ON_TIMEOUT", "true");

          }

          // KLM: don't add Z3 options here. The options are different in different Z3 versions.
          // Add options in the above condition for the appropriate version.

          // legacy option handling
          if (!CommandLineOptions.Clo.z3AtFlag)
            options.MultiTraces = true;


          foreach (string opt in CommandLineOptions.Clo.Z3Options)
          {
            Contract.Assert(opt != null);
            int eq = opt.IndexOf("=");
            if (eq > 0 && 'A' <= opt[0] && opt[0] <= 'Z' && !commandLineOnly.Contains(opt.Substring(0, eq)))
            {
              options.AddSmtOption(opt.Substring(0, eq), opt.Substring(eq + 1));
            }
            else
            {
              options.AddSolverArgument(opt);
            }
          }
        }


    }
}
