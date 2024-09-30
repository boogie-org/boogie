using System.Collections.Generic;
using System.Diagnostics.Contracts;
using VC;

namespace Microsoft.Boogie;

public class CallCounterexample : Counterexample
{
  public CallCmd FailingCall;
  public Requires FailingRequires;
  public AssertRequiresCmd FailingAssert;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(FailingCall != null);
    Contract.Invariant(FailingRequires != null);
  }


  public CallCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertRequiresCmd assertRequiresCmd, Model model,
    VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun, byte[] checksum = null)
    : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun)
  {
    var failingRequires = assertRequiresCmd.Requires;
    var failingCall = assertRequiresCmd.Call;
    Contract.Requires(!failingRequires.Free);
    Contract.Requires(trace != null);
    Contract.Requires(context != null);
    Contract.Requires(failingCall != null);
    Contract.Requires(failingRequires != null);
    this.FailingCall = failingCall;
    this.FailingRequires = failingRequires;
    this.FailingAssert = assertRequiresCmd;
    this.checksum = checksum;
    this.SugaredCmdChecksum = failingCall.Checksum;
  }

  protected override Cmd ModelFailingCommand => FailingCall;

  public override int GetLocation()
  {
    return FailingCall.tok.line * 1000 + FailingCall.tok.col;
  }

  byte[] checksum;

  public override byte[] Checksum
  {
    get { return checksum; }
  }

  public override Counterexample Clone()
  {
    var ret = new CallCounterexample(options, Trace, AugmentedTrace, FailingAssert, Model, MvInfo, Context, ProofRun, Checksum);
    ret.calleeCounterexamples = calleeCounterexamples;
    return ret;
  }
}