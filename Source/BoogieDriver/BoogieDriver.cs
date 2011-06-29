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
  using System.Collections;
  using System.Collections.Generic;
  using PureCollections;
  using Microsoft.Boogie;
  using Microsoft.Boogie.AbstractInterpretation;
  using System.Diagnostics.Contracts;
  using System.Diagnostics;
  using VC;
  using AI = Microsoft.AbstractInterpretationFramework;
  using BoogiePL = Microsoft.Boogie;

  /* 
    The following assemblies are referenced because they are needed at runtime, not at compile time:
      BaseTypes
      Provers.Z3
      System.Compiler.Framework
  */

  public class OnlyBoogie {
    // ------------------------------------------------------------------------
    // Main

    public static void Main(string[] args) {
      Contract.Requires(cce.NonNullElements(args));
      CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
      if (CommandLineOptions.Clo.Parse(args) != 1) {
        goto END;
      }
      if (CommandLineOptions.Clo.Files.Count == 0) {
        ErrorWriteLine("*** Error: No input files were specified.");
        goto END;
      }
      if (CommandLineOptions.Clo.XmlSink != null) {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null) {
          ErrorWriteLine("*** Error: " + errMsg);
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

      foreach (string file in CommandLineOptions.Clo.Files) {
        Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) {
          extension = extension.ToLower();
        }
        if (extension != ".bpl") {
          ErrorWriteLine("*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be BoogiePL programs (.bpl).", file,
              extension == null ? "" : extension);
          goto END;
        }
      }
      CommandLineOptions.Clo.RunningBoogieOnSsc = false;
      ProcessFiles(CommandLineOptions.Clo.Files);

    END:
      if (CommandLineOptions.Clo.XmlSink != null) {
        CommandLineOptions.Clo.XmlSink.Close();
      }
      if (CommandLineOptions.Clo.Wait) {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }
    }

    public static void ErrorWriteLine(string s) {
      Contract.Requires(s != null);
      if (!s.Contains("Error: ") && !s.Contains("Error BP")) {
        Console.WriteLine(s);
        return;
      }

      // split the string up into its first line and the remaining lines
      string remaining = null;
      int i = s.IndexOf('\r');
      if (0 <= i) {
        remaining = s.Substring(i + 1);
        if (remaining.StartsWith("\n")) {
          remaining = remaining.Substring(1);
        }
        s = s.Substring(0, i);
      }

      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Red;
      Console.WriteLine(s);
      Console.ForegroundColor = col;

      if (remaining != null) {
        Console.WriteLine(remaining);
      }
    }

    public static void ErrorWriteLine(string format, params object[] args) {
      Contract.Requires(format != null);
      string s = string.Format(format, args);
      ErrorWriteLine(s);
    }

    public static void AdvisoryWriteLine(string format, params object[] args) {
      Contract.Requires(format != null);
      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Yellow;
      Console.WriteLine(format, args);
      Console.ForegroundColor = col;
    }

    enum FileType {
      Unknown,
      Cil,
      Bpl,
      Dafny
    };

    static void ProcessFiles(List<string> fileNames) {
      Contract.Requires(cce.NonNullElements(fileNames));
      using (XmlFileScope xf = new XmlFileScope(CommandLineOptions.Clo.XmlSink, fileNames[fileNames.Count - 1])) {
        //BoogiePL.Errors.count = 0;
        Program program = ParseBoogieProgram(fileNames, false);
        if (program == null)
          return;
        if (CommandLineOptions.Clo.PrintFile != null) {
          PrintBplFile(CommandLineOptions.Clo.PrintFile, program, false);
        }

        PipelineOutcome oc = ResolveAndTypecheck(program, fileNames[fileNames.Count - 1]);
        if (oc != PipelineOutcome.ResolvedAndTypeChecked)
          return;
        //BoogiePL.Errors.count = 0;

        oc = EliminateDeadVariablesAndInline(program);
        //BoogiePL.Errors.count = 0;

        int errorCount, verified, inconclusives, timeOuts, outOfMemories;
        oc = InferAndVerify(program, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);
        switch (oc) {
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            WriteTrailer(verified, errorCount, inconclusives, timeOuts, outOfMemories);
            break;
          default:
            break;
        }
      }
    }


    static void PrintBplFile(string filename, Program program, bool allowPrintDesugaring) {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = CommandLineOptions.Clo.PrintDesugarings;
      if (!allowPrintDesugaring) {
        CommandLineOptions.Clo.PrintDesugarings = false;
      }
      using (TokenTextWriter writer = filename == "-" ?
                                      new TokenTextWriter("<console>", Console.Out) :
                                      new TokenTextWriter(filename)) {
        if (CommandLineOptions.Clo.ShowEnv != CommandLineOptions.ShowEnvironment.Never) {
          writer.WriteLine("// " + CommandLineOptions.Clo.Version);
          writer.WriteLine("// " + CommandLineOptions.Clo.Environment);
        }
        writer.WriteLine();
        program.Emit(writer);
      }
      CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaring;
    }


    static bool ProgramHasDebugInfo(Program program) {
      Contract.Requires(program != null);
      // We inspect the last declaration because the first comes from the prelude and therefore always has source context.
      return program.TopLevelDeclarations.Count > 0 &&
          ((cce.NonNull(program.TopLevelDeclarations)[program.TopLevelDeclarations.Count - 1]).tok.IsValid);
    }


    /// <summary>
    /// Inform the user about something and proceed with translation normally.
    /// Print newline after the message.
    /// </summary>
    public static void Inform(string s) {
      if (!CommandLineOptions.Clo.Trace) {
        return;
      }
      Console.WriteLine(s);
    }

    static void WriteTrailer(int verified, int errors, int inconclusives, int timeOuts, int outOfMemories) {
      Contract.Requires(0 <= errors && 0 <= inconclusives && 0 <= timeOuts && 0 <= outOfMemories);
      Console.WriteLine();
      if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
        Console.Write("{0} finished with {1} credible, {2} doomed{3}", CommandLineOptions.Clo.ToolName, verified, errors, errors == 1 ? "" : "s");
      } else {
        Console.Write("{0} finished with {1} verified, {2} error{3}", CommandLineOptions.Clo.ToolName, verified, errors, errors == 1 ? "" : "s");
      }
      if (inconclusives != 0) {
        Console.Write(", {0} inconclusive{1}", inconclusives, inconclusives == 1 ? "" : "s");
      }
      if (timeOuts != 0) {
        Console.Write(", {0} time out{1}", timeOuts, timeOuts == 1 ? "" : "s");
      }
      if (outOfMemories != 0) {
        Console.Write(", {0} out of memory", outOfMemories);
      }
      Console.WriteLine();
      Console.Out.Flush();
    }



    static void ReportBplError(Absy node, string message, bool error, bool showBplLocation) {
      Contract.Requires(message != null);
      Contract.Requires(node != null);
      IToken tok = node.tok;
      string s;
      if (tok != null && showBplLocation) {
        s = string.Format("{0}({1},{2}): {3}", tok.filename, tok.line, tok.col, message);
      } else {
        s = message;
      }
      if (error) {
        ErrorWriteLine(s);
      } else {
        Console.WriteLine(s);
      }
    }

    /// <summary>
    /// Parse the given files into one Boogie program.  If an I/O or parse error occurs, an error will be printed
    /// and null will be returned.  On success, a non-null program is returned.
    /// </summary>
    static Program ParseBoogieProgram(List<string> fileNames, bool suppressTraceOutput) {
      Contract.Requires(cce.NonNullElements(fileNames));
      //BoogiePL.Errors.count = 0;
      Program program = null;
      bool okay = true;
      for (int fileId = 0; fileId < fileNames.Count; fileId++) {
        string bplFileName = fileNames[fileId];
        if (!suppressTraceOutput) {
          if (CommandLineOptions.Clo.XmlSink != null) {
            CommandLineOptions.Clo.XmlSink.WriteFileFragment(bplFileName);
          }
          if (CommandLineOptions.Clo.Trace) {
            Console.WriteLine("Parsing " + bplFileName);
          }
        }

        Program programSnippet;
        int errorCount;
        try {
          var defines = new List<string>() { "FILE_" + fileId };
          errorCount = BoogiePL.Parser.Parse(bplFileName, defines, out programSnippet);
          if (programSnippet == null || errorCount != 0) {
            Console.WriteLine("{0} parse errors detected in {1}", errorCount, bplFileName);
            okay = false;
            continue;
          }
        } catch (IOException e) {
          ErrorWriteLine("Error opening file \"{0}\": {1}", bplFileName, e.Message);
          okay = false;
          continue;
        }
        if (program == null) {
          program = programSnippet;
        } else if (programSnippet != null) {
          program.TopLevelDeclarations.AddRange(programSnippet.TopLevelDeclarations);
        }
      }
      if (!okay) {
        return null;
      } else if (program == null) {
        return new Program();
      } else {
        return program;
      }
    }


    enum PipelineOutcome {
      Done,
      ResolutionError,
      TypeCheckingError,
      ResolvedAndTypeChecked,
      FatalError,
      VerificationCompleted
    }

    /// <summary>
    /// Resolves and type checks the given Boogie program.  Any errors are reported to the
    /// console.  Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    static PipelineOutcome ResolveAndTypecheck(Program program, string bplFileName) {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);
      // ---------- Resolve ------------------------------------------------------------

      if (CommandLineOptions.Clo.NoResolve) {
        return PipelineOutcome.Done;
      }

      int errorCount = program.Resolve();
      if (errorCount != 0) {
        Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, bplFileName);
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------

      if (CommandLineOptions.Clo.NoTypecheck) {
        return PipelineOutcome.Done;
      }

      errorCount = program.Typecheck();
      if (errorCount != 0) {
        Console.WriteLine("{0} type checking errors detected in {1}", errorCount, bplFileName);
        return PipelineOutcome.TypeCheckingError;
      }

      if (CommandLineOptions.Clo.PrintFile != null && CommandLineOptions.Clo.PrintDesugarings) {
        // if PrintDesugaring option is engaged, print the file here, after resolution and type checking
        PrintBplFile(CommandLineOptions.Clo.PrintFile, program, true);
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }

    static PipelineOutcome EliminateDeadVariablesAndInline(Program program) {
      Contract.Requires(program != null);
      // Eliminate dead variables
      Microsoft.Boogie.UnusedVarEliminator.Eliminate(program);

      // Collect mod sets
      if (CommandLineOptions.Clo.DoModSetAnalysis) {
        Microsoft.Boogie.ModSetCollector.DoModSetAnalysis(program);
      }

      // Coalesce blocks
      if (CommandLineOptions.Clo.CoalesceBlocks) {
        Microsoft.Boogie.BlockCoalescer.CoalesceBlocks(program);
      }

      // Inline
      // In Spec#, there was no run-time test. The type was just List<Declaration!>
      List<Declaration> TopLevelDeclarations = cce.NonNull(program.TopLevelDeclarations);
      
      
      if (CommandLineOptions.Clo.ProcedureInlining != CommandLineOptions.Inlining.None) {
        bool inline = false;
        foreach (Declaration d in TopLevelDeclarations) {
          if (d.FindExprAttribute("inline") != null) {
            inline = true;
          }
        }
        if (inline && CommandLineOptions.Clo.LazyInlining == 0 &&
          CommandLineOptions.Clo.StratifiedInlining == 0) {
          foreach (Declaration d in TopLevelDeclarations) {
            Implementation impl = d as Implementation;
            if (impl != null) {
              impl.OriginalBlocks = impl.Blocks;
              impl.OriginalLocVars = impl.LocVars;
            }
          }
          foreach (Declaration d in TopLevelDeclarations) {
            Implementation impl = d as Implementation;
            if (impl != null && !impl.SkipVerification) {
              Inliner.ProcessImplementation(program, impl);
            }
          }
          foreach (Declaration d in TopLevelDeclarations) {
            Implementation impl = d as Implementation;
            if (impl != null) {
              impl.OriginalBlocks = null;
              impl.OriginalLocVars = null;
            }
          }
        }
      }
      return PipelineOutcome.Done;
    }

    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    static PipelineOutcome InferAndVerify(Program program,
                                           out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories) {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;

      // ---------- Infer invariants --------------------------------------------------------

      // Abstract interpretation -> Always use (at least) intervals, if not specified otherwise (e.g. with the "/noinfer" switch)
      Microsoft.Boogie.AbstractInterpretation.AbstractInterpretation.RunAbstractInterpretation(program);

      if (CommandLineOptions.Clo.LoopUnrollCount != -1) {
        program.UnrollLoops(CommandLineOptions.Clo.LoopUnrollCount);
      }

      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo = null;
      if (CommandLineOptions.Clo.ExtractLoops)
      {
          extractLoopMappingInfo = program.ExtractLoops();
      }

      if (CommandLineOptions.Clo.PrintInstrumented) {
        program.Emit(new TokenTextWriter(Console.Out));
      }

      if (CommandLineOptions.Clo.ExpandLambdas) {
        LambdaHelper.ExpandLambdas(program);
        //PrintBplFile ("-", program, true);
      }

      // ---------- Verify ------------------------------------------------------------

      if (!CommandLineOptions.Clo.Verify) {
        return PipelineOutcome.Done;
      }

      #region Verify each implementation

#if ROB_DEBUG
      string now = DateTime.Now.ToString().Replace(' ','-').Replace('/','-').Replace(':','-');
      System.IO.StreamWriter w = new System.IO.StreamWriter(@"\temp\batch_"+now+".bpl");
      program.Emit(new TokenTextWriter(w));
      w.Close();
#endif

      ConditionGeneration vcgen = null;
      try {
        if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
          vcgen = new DCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        } else if(CommandLineOptions.Clo.StratifiedInlining > 0) {
            vcgen = new StratifiedVCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        } else {
          vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        }
      } catch (ProverException e) {
        ErrorWriteLine("Fatal Error: ProverException: {0}", e);
        return PipelineOutcome.FatalError;
      }

      // operate on a stable copy, in case it gets updated while we're running
      var decls = program.TopLevelDeclarations.ToArray();
      foreach (Declaration decl in decls) {
        Contract.Assert(decl != null);
        Implementation impl = decl as Implementation;
        if (impl != null && CommandLineOptions.Clo.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) && !impl.SkipVerification) {
          List<Counterexample/*!*/>/*?*/ errors;

          DateTime start = new DateTime();  // to please compiler's definite assignment rules
          if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.XmlSink != null) {
            start = DateTime.Now;
            if (CommandLineOptions.Clo.Trace) {
              Console.WriteLine();
              Console.WriteLine("Verifying {0} ...", impl.Name);
            }
            if (CommandLineOptions.Clo.XmlSink != null) {
              CommandLineOptions.Clo.XmlSink.WriteStartMethod(impl.Name, start);
            }
          }

          VCGen.Outcome outcome;
          try {
              if (CommandLineOptions.Clo.inferLeastForUnsat != null)
              {
                  var svcgen = vcgen as VC.StratifiedVCGen;
                  Debug.Assert(svcgen != null);
                  var ss = new HashSet<string>();
                  foreach (var tdecl in program.TopLevelDeclarations)
                  {
                      var c = tdecl as Constant;
                      if (c == null || !c.Name.StartsWith(CommandLineOptions.Clo.inferLeastForUnsat)) continue;
                      ss.Add(c.Name);
                  }
                  outcome = svcgen.FindLeastToVerify(impl, program, ref ss);
                  errors = new List<Counterexample>();
                  Console.Write("Result: ");
                  foreach (var s in ss)
                  {
                      Console.Write("{0} ", s);
                  }
                  Console.WriteLine();
              }
              else
              {
                  outcome = vcgen.VerifyImplementation(impl, program, out errors);
              }
          } catch (VCGenException e) {
            ReportBplError(impl, String.Format("Error BP5010: {0}  Encountered in implementation {1}.", e.Message, impl.Name), true, true);
            errors = null;
            outcome = VCGen.Outcome.Inconclusive;
          } catch (UnexpectedProverOutputException upo) {
            AdvisoryWriteLine("Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}", impl.Name, upo.Message);
            errors = null;
            outcome = VCGen.Outcome.Inconclusive;
          }

          string timeIndication = "";

          DateTime end = DateTime.Now;
          TimeSpan elapsed = end - start;
          if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.XmlSink != null) {
            if (CommandLineOptions.Clo.Trace) {
              timeIndication = string.Format("  [{0} s]  ", elapsed.TotalSeconds);
            }
          }


          switch (outcome) {
            default:
              Contract.Assert(false);  // unexpected outcome
              throw new cce.UnreachableException();
            case VCGen.Outcome.ReachedBound:
              Inform(String.Format("{0}verified", timeIndication));
              Console.WriteLine(string.Format("Stratified Inlining: Reached recursion bound of {0}", CommandLineOptions.Clo.RecursionBound));
              verified++;
              break;
            case VCGen.Outcome.Correct:
              if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
                Inform(String.Format("{0}credible", timeIndication));
                verified++;
              } else {
                Inform(String.Format("{0}verified", timeIndication));
                verified++;
              }
              break;
            case VCGen.Outcome.TimedOut:
              timeOuts++;
              Inform(String.Format("{0}timed out", timeIndication));
              break;
            case VCGen.Outcome.OutOfMemory:
              outOfMemories++;
              Inform(String.Format("{0}out of memory", timeIndication));
              break;
            case VCGen.Outcome.Inconclusive:
              inconclusives++;
              Inform(String.Format("{0}inconclusive", timeIndication));
              break;
            case VCGen.Outcome.Errors:
              if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
                Inform(String.Format("{0}doomed", timeIndication));
                errorCount++;
              } //else {
              Contract.Assert(errors != null);  // guaranteed by postcondition of VerifyImplementation

              {
                // BP1xxx: Parsing errors
                // BP2xxx: Name resolution errors
                // BP3xxx: Typechecking errors
                // BP4xxx: Abstract interpretation errors (Is there such a thing?)
                // BP5xxx: Verification errors

                if (CommandLineOptions.Clo.ExtractLoops && (vcgen is VCGen))
                {
                    for (int i = 0; i < errors.Count; i++)
                    {
                        errors[i] = (vcgen as VCGen).extractLoopTrace(errors[i], impl.Name, program, extractLoopMappingInfo);
                    }
                }

                errors.Sort(new CounterexampleComparer());
                foreach (Counterexample error in errors) {
                  if (error is CallCounterexample) {
                    CallCounterexample err = (CallCounterexample)error;
                    if (!CommandLineOptions.Clo.ForceBplErrors && err.FailingRequires.ErrorMessage != null) {
                      ReportBplError(err.FailingRequires, err.FailingRequires.ErrorMessage, true, false);
                    } else {
                      ReportBplError(err.FailingCall, "Error BP5002: A precondition for this call might not hold.", true, true);
                      ReportBplError(err.FailingRequires, "Related location: This is the precondition that might not hold.", false, true);
                    }
                    if (CommandLineOptions.Clo.XmlSink != null) {
                      CommandLineOptions.Clo.XmlSink.WriteError("precondition violation", err.FailingCall.tok, err.FailingRequires.tok, error.Trace);
                    }
                  } else if (error is ReturnCounterexample) {
                    ReturnCounterexample err = (ReturnCounterexample)error;
                    if (!CommandLineOptions.Clo.ForceBplErrors && err.FailingEnsures.ErrorMessage != null) {
                      ReportBplError(err.FailingEnsures, err.FailingEnsures.ErrorMessage, true, false);
                    } else {
                      ReportBplError(err.FailingReturn, "Error BP5003: A postcondition might not hold on this return path.", true, true);
                      ReportBplError(err.FailingEnsures, "Related location: This is the postcondition that might not hold.", false, true);
                    }
                    if (CommandLineOptions.Clo.XmlSink != null) {
                      CommandLineOptions.Clo.XmlSink.WriteError("postcondition violation", err.FailingReturn.tok, err.FailingEnsures.tok, error.Trace);
                    }
                  } else // error is AssertCounterexample
                    {
                    AssertCounterexample err = (AssertCounterexample)error;
                    if (err.FailingAssert is LoopInitAssertCmd) {
                      ReportBplError(err.FailingAssert, "Error BP5004: This loop invariant might not hold on entry.", true, true);
                      if (CommandLineOptions.Clo.XmlSink != null) {
                        CommandLineOptions.Clo.XmlSink.WriteError("loop invariant entry violation", err.FailingAssert.tok, null, error.Trace);
                      }
                    } else if (err.FailingAssert is LoopInvMaintainedAssertCmd) {
                      // this assertion is a loop invariant which is not maintained
                      ReportBplError(err.FailingAssert, "Error BP5005: This loop invariant might not be maintained by the loop.", true, true);
                      if (CommandLineOptions.Clo.XmlSink != null) {
                        CommandLineOptions.Clo.XmlSink.WriteError("loop invariant maintenance violation", err.FailingAssert.tok, null, error.Trace);
                      }
                    } else {
                      if (!CommandLineOptions.Clo.ForceBplErrors && err.FailingAssert.ErrorMessage != null) {
                        ReportBplError(err.FailingAssert, err.FailingAssert.ErrorMessage, true, false);
                      } else if (err.FailingAssert.ErrorData is string) {
                        ReportBplError(err.FailingAssert, (string)err.FailingAssert.ErrorData, true, true);
                      } else {
                        ReportBplError(err.FailingAssert, "Error BP5001: This assertion might not hold.", true, true);
                      }
                      if (CommandLineOptions.Clo.XmlSink != null) {
                        CommandLineOptions.Clo.XmlSink.WriteError("assertion violation", err.FailingAssert.tok, null, error.Trace);
                      }
                    }
                  }
                  if (CommandLineOptions.Clo.EnhancedErrorMessages == 1) {
                    foreach (string info in error.relatedInformation) {
                      Contract.Assert(info != null);
                      Console.WriteLine("       " + info);
                    }
                  }
                  if (CommandLineOptions.Clo.ErrorTrace > 0) {
                    Console.WriteLine("Execution trace:");
                    error.Print(4);
                  }
                  if (CommandLineOptions.Clo.ModelViewFile != null) {
                    error.PrintModel();
                  }
                  errorCount++;
                }
                //}
                Inform(String.Format("{0}error{1}", timeIndication, errors.Count == 1 ? "" : "s"));
              }
              break;
          }
          if (CommandLineOptions.Clo.XmlSink != null) {
            CommandLineOptions.Clo.XmlSink.WriteEndMethod(outcome.ToString().ToLowerInvariant(), end, elapsed);
          }
          if (outcome == VCGen.Outcome.Errors || CommandLineOptions.Clo.Trace) {
            Console.Out.Flush();
          }
        }
      }
      vcgen.Close();
      cce.NonNull(CommandLineOptions.Clo.TheProverFactory).Close();


      #endregion

      return PipelineOutcome.VerificationCompleted;
    }

  }
}
