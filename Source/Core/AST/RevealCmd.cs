using System.Collections.Generic;

namespace Microsoft.Boogie;

public class RevealCmd : Cmd
{
  private readonly FunctionCall functionCall;
  
  public RevealCmd(IdentifierExpr name) : base(name.tok)
  {
    this.functionCall = new FunctionCall(name);
    
  }

  public Function Function => functionCall.Func;

  public RevealCmd(IToken tok) : base(tok)
  {
  }

  public override void Resolve(ResolutionContext rc)
  {
    functionCall.Resolve(rc, null);
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