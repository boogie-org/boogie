#nullable enable
using System.Collections.Generic;

namespace Microsoft.Boogie;

public class ChangeScope : Cmd {
  public bool Push { get; }

  public ChangeScope(IToken tok, bool push) : base(tok) {
    Push = push;
  }

  public override void Resolve(ResolutionContext rc) {
  }

  public override void Typecheck(TypecheckingContext tc) {
  }

  public override void Emit(TokenTextWriter stream, int level) {
  }

  public override void AddAssignedVariables(List<Variable> vars) {
  }

  public override Absy StdDispatch(StandardVisitor visitor) {
    return this;
  }
}