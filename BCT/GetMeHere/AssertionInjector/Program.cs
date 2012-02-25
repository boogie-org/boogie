//-----------------------------------------------------------------------------
//
// Copyright (c) Microsoft. All rights reserved.
// This code is licensed under the Microsoft Public License.
// THIS CODE IS PROVIDED *AS IS* WITHOUT WARRANTY OF
// ANY KIND, EITHER EXPRESS OR IMPLIED, INCLUDING ANY
// IMPLIED WARRANTIES OF FITNESS FOR A PARTICULAR
// PURPOSE, MERCHANTABILITY, OR NON-INFRINGEMENT.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.Serialization; // needed for defining exception .ctors
using Microsoft.Cci;
using Microsoft.Cci.MutableCodeModel;
using Bpl = Microsoft.Boogie;
using System.Diagnostics;

namespace AssertionInjector {

  class Program {
    const int errorValue = -1;
    static int Main(string[] args) {
      if (args == null || args.Length < 4) {
        Console.WriteLine("Usage: AssertionInjector <assembly> <filename+extension> <line number> <column number> [<outputPath>]");
        return errorValue;
      }

      int lineNumber;
      if (!Int32.TryParse(args[2], out lineNumber)) {
        Console.WriteLine("Error: couldn't parse '{0}' as an integer to use as a line number", args[2]);
        return errorValue;
      }
      int columnNumber;
      if (!Int32.TryParse(args[3], out columnNumber)) {
        Console.WriteLine("Error: couldn't parse '{0}' as an integer to use as a column number", args[3]);
        return errorValue;
      }

      return InjectAssertionInBpl(args[0], args[1], lineNumber, columnNumber);
    }

    static int InjectAssertionInBpl(string bplFileName, string fileName, int lineNumber, int columnNumber) {
      Bpl.CommandLineOptions.Install(new Bpl.CommandLineOptions());
      Bpl.CommandLineOptions.Clo.DoModSetAnalysis = true;
      var returnValue = errorValue; 
      Bpl.Program program;
      Bpl.Parser.Parse(bplFileName, new List<string>(), out program);
      int errorCount = program.Resolve();
      if (errorCount != 0) {
        Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, bplFileName);
        return returnValue;
      }
      errorCount = program.Typecheck();
      if (errorCount != 0) {
        Console.WriteLine("{0} type checking errors detected in {1}", errorCount, bplFileName);
        return returnValue;
      }

      GetMeHereBplInjector bplInjector = new GetMeHereBplInjector(fileName, lineNumber, columnNumber);
      bplInjector.Visit(program);
      using (Bpl.TokenTextWriter writer = new Bpl.TokenTextWriter(bplFileName)) {
        Bpl.CommandLineOptions.Clo.PrintInstrumented = true;
        program.Emit(writer);
      }
      return returnValue;
    }
  }

  public class GetMeHereBplInjector : Bpl.StandardVisitor {
    string fileName;
    int lineNumber;
    int columnNumber;

    public GetMeHereBplInjector(string fileName, int lineNumber, int columnNumber) {
      this.fileName = fileName;
      this.lineNumber = lineNumber;
      this.columnNumber = columnNumber;
    }

    public override Bpl.CmdSeq VisitCmdSeq(Bpl.CmdSeq cmdSeq) {
      Bpl.CmdSeq newCmdSeq = new Bpl.CmdSeq();
      for (int i = 0; i < cmdSeq.Length; i++) {
        Bpl.Cmd cmd = cmdSeq[i];
        if (IsRelevant(cmd))
          newCmdSeq.Add(new Bpl.AssertCmd(cmd.tok, Bpl.Expr.False));
        newCmdSeq.Add(cmd);
      }
      return newCmdSeq;
    }

    private bool IsRelevant(Bpl.Cmd cmd) {
      Bpl.AssertCmd assertCmd = cmd as Bpl.AssertCmd;
      if (assertCmd == null)
        return false;
      string sourceFile = Bpl.QKeyValue.FindStringAttribute(assertCmd.Attributes, "sourceFile");
      if (sourceFile == null)
        return false;
      string[] ds = sourceFile.Split('\\');
      if (sourceFile != fileName && ds[ds.Length - 1] != fileName)
        return false;
      int sourceLine = Bpl.QKeyValue.FindIntAttribute(assertCmd.Attributes, "sourceLine", -1);
      Debug.Assert(sourceLine != -1);
      if (sourceLine != lineNumber)
        return false;
      return true;
    }
  }

}
