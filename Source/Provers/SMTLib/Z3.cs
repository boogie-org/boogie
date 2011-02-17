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

    public static string Z3ExecutablePath()
    {
      if (_proverPath == null)
        FindZ3Executable();
      return _proverPath;
    }

    static void FindZ3Executable()
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


  }
}
