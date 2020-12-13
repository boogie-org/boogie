using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie
{
  public class OnlyBoogie
  {
    public static int Main(string[] args)
    {
      Contract.Requires(cce.NonNullElements(args));

      ExecutionEngine.printer = new ConsolePrinter();

      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;

      if (!CommandLineOptions.Clo.Parse(args))
      {
        return 1;
      }
      
      if (CommandLineOptions.Clo.ProcessInfoFlags())
      {
        return 0;
      }

      if (CommandLineOptions.Clo.Files.Count == 0)
      {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: No input files were specified.");
        return 1;
      }

      List<string> fileList = GetFileList();
      if (fileList == null)
      {
        return 1;
      }

      if (CommandLineOptions.Clo.XmlSink != null)
      {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null)
        {
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: " + errMsg);
          return 1;
        }
      }

      if (CommandLineOptions.Clo.ShowEnv == CommandLineOptions.ShowEnvironment.Always)
      {
        Console.WriteLine("---Command arguments");
        foreach (string arg in args)
        {
          Contract.Assert(arg != null);
          Console.WriteLine(arg);
        }

        Console.WriteLine("--------------------");
      }

      Helpers.ExtraTraceInformation("Becoming sentient");

      ExecutionEngine.ProcessFiles(fileList);

      if (CommandLineOptions.Clo.XmlSink != null)
      {
        CommandLineOptions.Clo.XmlSink.Close();
      }

      if (CommandLineOptions.Clo.Wait)
      {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }

      return 0;
    }

    private static List<string> GetFileList()
    {
      List<string> fileList = new List<string>();
      foreach (string file in CommandLineOptions.Clo.Files)
      {
        string extension = Path.GetExtension(file);
        if (extension != null)
        {
          extension = extension.ToLower();
        }

        if (extension == ".txt")
        {
          StreamReader stream = new StreamReader(file);
          string s = stream.ReadToEnd();
          fileList.AddRange(s.Split(new char[3] { ' ', '\n', '\r' }, StringSplitOptions.RemoveEmptyEntries));
        }
        else
        {
          fileList.Add(file);
        }
      }

      foreach (string file in fileList)
      {
        Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null)
        {
          extension = extension.ToLower();
        }

        if (extension != ".bpl")
        {
          ExecutionEngine.printer.ErrorWriteLine(
            Console.Out,
            "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be BoogiePL programs (.bpl).",
            file,
            extension == null ? string.Empty : extension);
          return null;
        }
      }

      return fileList;
    }
  }
}
