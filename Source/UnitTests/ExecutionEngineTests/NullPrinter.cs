using System;
using System.IO;
using Microsoft.Boogie;
using VCGeneration;

namespace ExecutionEngineTests;

public class NullPrinter : OutputPrinter {

  public ExecutionEngineOptions Options { get; set; }

  public void ErrorWriteLine(TextWriter tw, string s) {
  }

  public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
  }

  public void AdvisoryWriteLine(TextWriter output, string format, params object[] args) {
  }

  public void Inform(string s, TextWriter tw) {
  }

  public void WriteTrailer(TextWriter textWriter, PipelineStatistics stats) {
  }

  public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
  }

  public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null) {
  }

  public void ReportEndVerifyImplementation(Implementation implementation, VerificationResult result)
  {
  }
}
