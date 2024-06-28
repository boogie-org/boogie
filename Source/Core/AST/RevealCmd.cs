#nullable enable
using System.Collections.Generic;

namespace Microsoft.Boogie;

public class HideRevealCmd : Cmd {
  public bool Hide { get; }
  private readonly FunctionCall? functionCall;

  public HideRevealCmd(IToken tok, bool hide) : base(tok) {
    this.Hide = hide;
  }

  public HideRevealCmd(IdentifierExpr name, bool hide) : base(name.tok) {
    this.Hide = hide;
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
  }

  public override void AddAssignedVariables(List<Variable> vars)
  {
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    return visitor.VisitRevealCmd(this);
  }
}