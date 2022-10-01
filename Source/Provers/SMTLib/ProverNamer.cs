using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.SMTLib;

public class ProverNamer : UniqueNamer {
  private readonly SMTLibProcessTheoremProver prover;

  public ProverNamer(SMTLibProcessTheoremProver prover) {
    this.prover = prover;
  }

  public string Lookup(object thingie) {
    return BackingNamer.Lookup(thingie);
  }

  public UniqueNamer BackingNamer => prover.Namer;

  public string GetName(object thing, string name) {
    return BackingNamer.GetName(thing, name);
  }

  public void PopScope() {
    BackingNamer.PopScope();
  }

  public void PushScope() {
    BackingNamer.PushScope();
  }

  public string GetLocalName(object thing, string name) {
    return BackingNamer.GetLocalName(thing, name);
  }

  public string GetOriginalName(string newName) {
    return BackingNamer.GetOriginalName(newName);
  }

  public UniqueNamer Clone() {
    return BackingNamer.Clone();
  }
}
