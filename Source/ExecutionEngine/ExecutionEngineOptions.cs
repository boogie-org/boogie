using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie;

public interface ExecutionEngineOptions : HoudiniOptions, ConcurrencyOptions
{
  public new OutputPrinter Printer { get; }
  bool ShowVerifiedProcedureCount { get; }
  string DescriptiveToolName { get; }
  bool TraceProofObligations { get; }
  string PrintFile { get; }
  string PrintCFGPrefix { get; }
  string CivlDesugaredFile { get; }
  bool CoalesceBlocks { get; }
  ShowEnvironment ShowEnv { get; }
  string Version { get; }
  string Environment { get; }
  bool UseBaseNameForFileName { get; }
  HashSet<string> Libraries { get; set; }
  bool Monomorphize { get; set; }
  bool NoResolve { get; }
  bool NoTypecheck { get; }

  List<string> ProcsToCheck { get; }
  List<string> ProcsToIgnore { get; }
  int PrintErrorModel { get; }
  int EnhancedErrorMessages { get; }
  bool ForceBplErrors { get; }
  bool PrintAssignment { get; }
  bool ExtractLoops { get; }
  TextWriter ModelWriter { get; }
  bool ExpandLambdas { get; }
  bool PrintLambdaLifting { get; }
  bool UseAbstractInterpretation { get; }
  int LoopUnrollCount { get; }
  bool SoundLoopUnrolling { get; }
  bool Verify { get; }
  bool ContractInfer { get; }

  public enum ShowEnvironment
  {
    Never,
    DuringPrint,
    Always
  }

  public bool UserWantsToCheckRoutine(string methodFullname)
  {
    Contract.Requires(methodFullname != null);
    Func<string, bool> match = s => Regex.IsMatch(methodFullname, "^" + Regex.Escape(s).Replace(@"\*", ".*") + "$");
    return (ProcsToCheck.Count == 0 || ProcsToCheck.Any(match)) && !ProcsToIgnore.Any(match);
  }
}