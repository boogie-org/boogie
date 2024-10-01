using System.Collections.Generic;
using System.Diagnostics.Contracts;
using VC;

namespace Microsoft.Boogie;

public class ReturnCounterexample : Counterexample
{
  public TransferCmd FailingReturn;
  public Ensures FailingEnsures;
  public AssertEnsuresCmd FailingAssert;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(FailingEnsures != null);
    Contract.Invariant(FailingReturn != null);
  }


  public ReturnCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertEnsuresCmd assertEnsuresCmd, TransferCmd failingReturn, Model model,
    VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun, byte[] checksum)
    : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun)
  {
    var failingEnsures = assertEnsuresCmd.Ensures;
    Contract.Requires(trace != null);
    Contract.Requires(context != null);
    Contract.Requires(failingReturn != null);
    Contract.Requires(failingEnsures != null);
    Contract.Requires(!failingEnsures.Free);
    this.FailingReturn = failingReturn;
    this.FailingEnsures = failingEnsures;
    this.FailingAssert = assertEnsuresCmd;
    this.checksum = checksum;
  }

  protected override Cmd ModelFailingCommand => null;

  public override int GetLocation()
  {
    return FailingReturn.tok.line * 1000 + FailingReturn.tok.col;
  }

  byte[] checksum;

  /// <summary>
  /// Returns the checksum of the corresponding assertion.
  /// </summary>
  public override byte[] Checksum
  {
    get { return checksum; }
  }

  public override Counterexample Clone()
  {
    var ret = new ReturnCounterexample(options, Trace, AugmentedTrace, FailingAssert, FailingReturn, Model, MvInfo, Context, ProofRun, checksum);
    ret.calleeCounterexamples = calleeCounterexamples;
    return ret;
  }
}