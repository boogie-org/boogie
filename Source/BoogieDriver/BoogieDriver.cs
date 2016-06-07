//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// OnlyBoogie OnlyBoogie.ssc
//       - main program for taking a BPL program and verifying it
//---------------------------------------------------------------------------------------------

namespace Microsoft.Boogie {
  using System;
  using System.IO;
  using System.Collections.Generic;
  using System.Diagnostics.Contracts;

  /*
    The following assemblies are referenced because they are needed at runtime, not at compile time:
      BaseTypes
      Provers.Z3
      System.Compiler.Framework
  */

  public class OnlyBoogie
  {

    public static int Main(string[] args)
    {
      Contract.Requires(cce.NonNullElements(args));

      ExecutionEngine.printer = new ConsolePrinter();

      CommandLineOptions.Install(new CommandLineOptions());

      CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
      if (!CommandLineOptions.Clo.Parse(args)) {
        goto END;
      }
      if (CommandLineOptions.Clo.Files.Count == 0) {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: No input files were specified.");
        goto END;
      }
      if (CommandLineOptions.Clo.XmlSink != null) {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null) {
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: " + errMsg);
          goto END;
        }
      }
      if (!CommandLineOptions.Clo.DontShowLogo) {
        Console.WriteLine(CommandLineOptions.Clo.Version);
      }
      if (CommandLineOptions.Clo.ShowEnv == CommandLineOptions.ShowEnvironment.Always) {
        Console.WriteLine("---Command arguments");
        foreach (string arg in args) {
          Contract.Assert(arg != null);
          Console.WriteLine(arg);
        }

        Console.WriteLine("--------------------");
      }

      Helpers.ExtraTraceInformation("Becoming sentient");

      List<string> fileList = new List<string>();
      foreach (string file in CommandLineOptions.Clo.Files) {
        string extension = Path.GetExtension(file);
        if (extension != null) {
          extension = extension.ToLower();
        }
        if (extension == ".txt") {
          StreamReader stream = new StreamReader(file);
          string s = stream.ReadToEnd();
          fileList.AddRange(s.Split(new char[3] {' ', '\n', '\r'}, StringSplitOptions.RemoveEmptyEntries));
        }
        else {
          fileList.Add(file);
        }
      }
      foreach (string file in fileList) {
        Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) {
          extension = extension.ToLower();
        }
        if (extension != ".bpl") {
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be BoogiePL programs (.bpl).", file,
              extension == null ? "" : extension);
          goto END;
        }
      }
      ExecutionEngine.ProcessFiles(fileList);
      return 0;

    END:
      if (CommandLineOptions.Clo.XmlSink != null) {
        CommandLineOptions.Clo.XmlSink.Close();
      }
      if (CommandLineOptions.Clo.Wait) {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }
      return 1;
    }
  }
}
