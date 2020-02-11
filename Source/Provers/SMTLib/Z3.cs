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

                var exePaths = Environment.GetEnvironmentVariable("PATH");
                foreach (var exePath in exePaths.Split(Path.PathSeparator))
                {
                    var exes = new string[] { proverExe, Path.GetFileNameWithoutExtension(proverExe) };
                    foreach (var exe in exes) {
                        var path = Path.Combine(exePath, exe);
                        if (File.Exists(path)) {
                            _proverPath = path;

                            if (CommandLineOptions.Clo.Trace)
                            {
                                Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                            }
                            return;
                        }
                    }
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
        static int Z3PatchVersion = 0;
        static bool Z3VersionObtained = false;

        public static void GetVersion(out int major, out int minor, out int patch)
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
                                var spaceafterseconddot = answer.IndexOf(' ', seconddot + 1);
                                if (spaceafterseconddot >= 0) {

                                    var majorstr = answer.Substring(spacebeforefirstdot, firstdot - spacebeforefirstdot);
                                    var minorstr = answer.Substring(firstdot + 1, seconddot - firstdot - 1);
                                    var patchstr = answer.Substring(seconddot + 1, spaceafterseconddot - seconddot - 1);
                                    Z3MajorVersion = Convert.ToInt32(majorstr);
                                    Z3MinorVersion = Convert.ToInt32(minorstr);
                                    Z3PatchVersion = Convert.ToInt32(patchstr);
                                }
                            }
                        }
                    }
                }
                Z3VersionObtained = true;
            }
            major = Z3MajorVersion;
            minor = Z3MinorVersion;
            patch = Z3PatchVersion;
        }

        public static string SetTimeoutOption()
        {
            int major, minor, patch;
            GetVersion(out major, out minor, out patch);
            if (major > 4 || major == 4 && minor >= 3)
                return "TIMEOUT";
            else
                return "SOFT_TIMEOUT";
        }

        public static string SetRlimitOption()
        {
            int major, minor, patch;
            GetVersion(out major, out minor, out patch);
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
          int major, minor, patch;
          GetVersion(out major, out minor, out patch);

          // {:captureState} does not work with compressed models
          options.AddWeakSmtOption("model.compact", "false");  // default: false
          options.AddWeakSmtOption("model.v2", "true");        // default: false

          // Make sure we get something that is parsable as a bitvector
          options.AddWeakSmtOption("pp.bv_literals", "false"); // default: true

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
