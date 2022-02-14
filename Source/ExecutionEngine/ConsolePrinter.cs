using System;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie;

public class ConsolePrinter : OutputPrinter
{
  private ExecutionEngineOptions options;

  public ConsolePrinter(ExecutionEngineOptions options)
  {
    this.options = options;
  }

  public void ErrorWriteLine(TextWriter tw, string s)
  {
    Contract.Requires(s != null);
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


  public void ErrorWriteLine(TextWriter tw, string format, params object[] args)
  {
    Contract.Requires(format != null);
    string s = string.Format(format, args);
    ErrorWriteLine(tw, s);
  }


  public void AdvisoryWriteLine(string format, params object[] args)
  {
    Contract.Requires(format != null);
    ConsoleColor col = Console.ForegroundColor;
    Console.ForegroundColor = ConsoleColor.Yellow;
    Console.WriteLine(format, args);
    Console.ForegroundColor = col;
  }


  /// <summary>
  /// Inform the user about something and proceed with translation normally.
  /// Print newline after the message.
  /// </summary>
  public void Inform(string s, TextWriter tw)
  {
    if (options.Trace || options.TraceProofObligations)
    {
      tw.WriteLine(s);
    }
  }


  public void WriteTrailer(PipelineStatistics stats)
  {
    Contract.Requires(stats != null);
    Contract.Requires(0 <= stats.VerifiedCount && 0 <= stats.ErrorCount && 0 <= stats.InconclusiveCount &&
                      0 <= stats.TimeoutCount && 0 <= stats.OutOfMemoryCount);

    Console.WriteLine();
    if (options.ShowVerifiedProcedureCount)
    {
      Console.Write("{0} finished with {1} verified, {2} error{3}", options.DescriptiveToolName,
        stats.VerifiedCount, stats.ErrorCount, stats.ErrorCount == 1 ? "" : "s");
    }
    else
    {
      Console.Write("{0} finished with {1} error{2}", options.DescriptiveToolName, stats.ErrorCount,
        stats.ErrorCount == 1 ? "" : "s");
    }

    if (stats.InconclusiveCount != 0)
    {
      Console.Write(", {0} inconclusive{1}", stats.InconclusiveCount, stats.InconclusiveCount == 1 ? "" : "s");
    }

    if (stats.TimeoutCount != 0)
    {
      Console.Write(", {0} time out{1}", stats.TimeoutCount, stats.TimeoutCount == 1 ? "" : "s");
    }

    if (stats.OutOfMemoryCount != 0)
    {
      Console.Write(", {0} out of memory", stats.OutOfMemoryCount);
    }

    if (stats.OutOfResourceCount != 0)
    {
      Console.Write(", {0} out of resource", stats.OutOfResourceCount);
    }

    if (stats.SolverExceptionCount != 0)
    {
      Console.Write(", {0} solver exceptions", stats.SolverExceptionCount);
    }

    Console.WriteLine();
    Console.Out.Flush();
  }


  public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
  {
    Contract.Requires(errorInfo != null);

    ReportBplError(errorInfo.Tok, errorInfo.FullMsg, true, tw);

    foreach (var e in errorInfo.Aux)
    {
      if (!(skipExecutionTrace && e.Category != null && e.Category.Contains("Execution trace")))
      {
        ReportBplError(e.Tok, e.FullMsg, false, tw);
      }
    }

    tw.Write(errorInfo.Out.ToString());
    tw.Write(errorInfo.Model.ToString());
    tw.Flush();
  }


  public virtual void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
  {
    Contract.Requires(message != null);

    if (category != null)
    {
      message = string.Format("{0}: {1}", category, message);
    }

    string s;
    if (tok != null)
    {
      s = string.Format("{0}({1},{2}): {3}", ExecutionEngine.GetFileNameForConsole(options, tok.filename), tok.line, tok.col,
        message);
    }
    else
    {
      s = message;
    }

    if (error)
    {
      ErrorWriteLine(tw, s);
    }
    else
    {
      tw.WriteLine(s);
    }
  }
}