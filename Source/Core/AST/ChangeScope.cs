#nullable enable
using System.Collections.Generic;

namespace Microsoft.Boogie;

/// <summary>
/// Allows pushing and popping scopes inside a Boogie implementation.
/// 
/// Right now these scopes only affect the state of what functions are hidden and revealed using the hide and reveal keywords.
/// However, in the future these scopes should also allow lexical scoping and variable shadowing.
/// </summary>
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