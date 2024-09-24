using System.Collections.Generic;
using System.Diagnostics.Contracts;
using VC;

namespace Microsoft.Boogie;

public class AssertCounterexample : Counterexample
{
  [Peer] public readonly AssertCmd FailingAssert;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(FailingAssert != null);
  }


  public AssertCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertCmd failingAssert, Model model, VC.ModelViewInfo mvInfo,
    ProverContext context, ProofRun proofRun)
    : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun, failingAssert)
  {
    Contract.Requires(trace != null);
    Contract.Requires(failingAssert != null);
    Contract.Requires(context != null);
    this.FailingAssert = failingAssert;
  }

  protected override Cmd ModelFailingCommand => FailingAssert;

  public override int GetLocation()
  {
    return FailingAssert.tok.line * 1000 + FailingAssert.tok.col;
  }

  public override byte[] Checksum
  {
    get { return FailingAssert.Checksum; }
  }

  public override Counterexample Clone()
  {
    var ret = new AssertCounterexample(Options, Trace, AugmentedTrace, FailingAssert, Model, MvInfo, Context, ProofRun);
    ret.CalleeCounterexamples = CalleeCounterexamples;
    return ret;
  }
}