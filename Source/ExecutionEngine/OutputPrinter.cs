using System.IO;
using VC;
using VCGeneration;

namespace Microsoft.Boogie;

public interface OutputPrinter
{
  ExecutionEngineOptions Options { get; set; }
  void ErrorWriteLine(TextWriter tw, string s);
  void ErrorWriteLine(TextWriter tw, string format, params object[] args);
  void AdvisoryWriteLine(TextWriter output, string format, params object[] args);
  void Inform(string s, TextWriter tw);
  void WriteTrailer(TextWriter textWriter, PipelineStatistics stats);
  void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true);
  void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null);
}
