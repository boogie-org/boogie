#nullable enable
using System.Collections.Generic;

namespace Microsoft.Boogie;

/// <summary>
/// Can be used to hide or reveal a specific function, or all functions
/// If pruning is turned on, a hidden function will be pruned despite being referenced in a Boogie implementation.
/// The function is only partially pruned though: the function definition itself is kept, and only axioms
/// that the function depends on, that are marked as hideable, are pruned.
///
/// Hide and revealing takes into account lexical scoping:
/// A popScope command will undo any hide and reveal operations that came after the last pushScope command.  
/// </summary>
public class HideRevealCmd : Cmd {
  public enum Modes { Hide, Reveal }
  public Modes Mode { get; }
  private readonly FunctionCall? functionCall;

  public HideRevealCmd(IToken tok, Modes mode) : base(tok) {
    this.Mode = mode;
  }

  public HideRevealCmd(IdentifierExpr name, Modes mode) : base(name.tok) {
    this.Mode = mode;
    this.functionCall = new FunctionCall(name);
  }

  public Function? Function => functionCall?.Func;

  public override void Resolve(ResolutionContext rc)
  {
    functionCall?.Resolve(rc, null);
  }

  public override void Typecheck(TypecheckingContext tc)
  {
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.Write(this, level, Mode == Modes.Hide ? "hide " : "reveal ");
    stream.Write(this, functionCall == null ? "*" : functionCall.FunctionName);
    stream.WriteLine(";");
  }

  public override void AddAssignedVariables(List<Variable> vars)
  {
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    return visitor.VisitRevealCmd(this);
  }
}