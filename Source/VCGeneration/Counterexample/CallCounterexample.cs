using System.Collections.Generic;
using System.Diagnostics.Contracts;
using VC;

namespace Microsoft.Boogie;

public class CallCounterexample : Counterexample
{
  public readonly CallCmd FailingCall;
  public readonly Requires FailingRequires;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(FailingCall != null);
    Contract.Invariant(FailingRequires != null);
  }


  public CallCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertRequiresCmd failingAssertRequires, Model model,
    VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun, byte[] checksum = null)
    : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun, failingAssertRequires)
  {
    var failingRequires = failingAssertRequires.Requires;
    var failingCall = failingAssertRequires.Call;
    Contract.Requires(!failingRequires.Free);
    Contract.Requires(trace != null);
    Contract.Requires(context != null);
    Contract.Requires(failingCall != null);
    Contract.Requires(failingRequires != null);
    this.FailingCall = failingCall;
    this.FailingRequires = failingRequires;
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
    var ret = new CallCounterexample(Options, Trace, AugmentedTrace, (AssertRequiresCmd)FailingAssert, Model, MvInfo, Context, ProofRun, Checksum);
    ret.CalleeCounterexamples = CalleeCounterexamples;
    return ret;
  }
}