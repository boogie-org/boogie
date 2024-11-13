using System;
using System.Diagnostics.Contracts;
using System.IO;
using VCGeneration;
using VC;

namespace Microsoft.Boogie;

public class ConsolePrinter : OutputPrinter
{
  public ExecutionEngineOptions Options { get; set; }

  public virtual void ErrorWriteLine(TextWriter tw, string s)
  {
    Contract.Requires(s != null);
    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    if (!s.Contains("Error: ") && !s.Contains("Error BP"))
    {
      tw.WriteLine(s);
      return;
    }

    // split the string up into its first line and the remaining lines
    string remaining = null;
    int i = s.IndexOf('\r');
    if (i >= 0)
    {
      remaining = s.Substring(i + 1);
      if (remaining.StartsWith("\n"))
      {
        remaining = remaining.Substring(1);
      }

      s = s.Substring(0, i);
    }

    ConsoleColor col = Console.ForegroundColor;
    Console.ForegroundColor = ConsoleColor.Red;
    tw.WriteLine(s);
    Console.ForegroundColor = col;

    if (remaining != null)
    {
      tw.WriteLine(remaining);
    }
  }


  public virtual void ErrorWriteLine(TextWriter tw, string format, params object[] args)
  {
    Contract.Requires(format != null);
    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    string s = string.Format(format, args);
    ErrorWriteLine(tw, s);
  }


  public virtual void AdvisoryWriteLine(TextWriter output, string format, params object[] args)
  {
    Contract.Requires(format != null);
    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    ConsoleColor col = Console.ForegroundColor;
    Console.ForegroundColor = ConsoleColor.Yellow;
    Console.WriteLine(format, args);
    Console.ForegroundColor = col;
  }


  /// <summary>
  /// Inform the user about something and proceed with translation normally.
  /// Print newline after the message.
  /// </summary>
  public virtual void Inform(string s, TextWriter tw)
  {
    if (Options.Trace || Options.TraceProofObligations)
    {
      tw.WriteLine(s);
    }
  }


  public virtual void WriteTrailer(TextWriter textWriter, PipelineStatistics stats)
  {
    Contract.Requires(stats != null);
    Contract.Requires(0 <= stats.VerifiedCount && 0 <= stats.ErrorCount && 0 <= stats.InconclusiveCount &&
                      0 <= stats.TimeoutCount && 0 <= stats.OutOfMemoryCount);

    if (Options.Verbosity <= CoreOptions.VerbosityLevel.Quiet) {
      return;
    }

    textWriter.WriteLine();
    if (Options.ShowVerifiedProcedureCount)
    {
      textWriter.Write("{0} finished with {1} verified, {2} error{3}", Options.DescriptiveToolName,
        stats.VerifiedCount, stats.ErrorCount, stats.ErrorCount == 1 ? "" : "s");
    }
    else
    {
      textWriter.Write("{0} finished with {1} error{2}", Options.DescriptiveToolName, stats.ErrorCount,
        stats.ErrorCount == 1 ? "" : "s");
    }

    if (stats.InconclusiveCount != 0)
    {
      textWriter.Write(", {0} inconclusive{1}", stats.InconclusiveCount, stats.InconclusiveCount == 1 ? "" : "s");
    }

    if (stats.TimeoutCount != 0)
    {
      textWriter.Write(", {0} time out{1}", stats.TimeoutCount, stats.TimeoutCount == 1 ? "" : "s");
    }

    if (stats.OutOfMemoryCount != 0)
    {
      textWriter.Write(", {0} out of memory", stats.OutOfMemoryCount);
    }

    if (stats.OutOfResourceCount != 0)
    {
      textWriter.Write(", {0} out of resource", stats.OutOfResourceCount);
    }

    if (stats.SolverExceptionCount != 0)
    {
      textWriter.Write(", {0} solver exceptions", stats.SolverExceptionCount);
    }

    textWriter.WriteLine();
    textWriter.Flush();
  }


  public virtual void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
  {
    Contract.Requires(errorInfo != null);

    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    ReportBplError(errorInfo.Tok, errorInfo.FullMsg, true, tw);

    foreach (var e in errorInfo.Aux)
    {
      if (!(skipExecutionTrace && e.Category != null && e.Category.Contains("Execution trace")))
      {
        ReportBplError(e.Tok, e.FullMsg, false, tw);
      }
    }

    tw.Write(errorInfo.Out.ToString());
    tw.Write(errorInfo.ModelWriter.ToString());
    tw.Flush();
  }


  public virtual void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
  {
    Contract.Requires(message != null);

    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    if (category != null)
    {
      message = $"{category}: {message}";
    }

    var s = tok != null
      ? string.Format("{0}({1},{2}): {3}", ExecutionEngine.GetFileNameForConsole(Options, tok.filename), tok.line,
        tok.col, message)
      : message;

    if (error)
    {
      ErrorWriteLine(tw, s);
    }
    else
    {
      tw.WriteLine(s);
    }
  }

  public virtual void ReportImplementationsBeforeVerification(Implementation[] implementations) {
    // Do not print anything to console
  }

  public virtual void ReportStartVerifyImplementation(Implementation implementation) {
    // Do not print anything to console
  }

  public virtual void ReportEndVerifyImplementation(Implementation implementation, ImplementationRunResult result) {
    // Do not print anything to console
  }

  public virtual void ReportSplitResult(Split split, VerificationRunResult splitResult) {
    // Do not print anything to console
  }
}
