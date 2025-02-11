using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class WhileCmd : StructuredCmd
{
  [Peer] public Expr Guard;

  public List<PredicateCmd> Invariants;

  public List<CallCmd> Yields;

  public StmtList Body;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Body != null);
    Contract.Invariant(Cce.NonNullElements(Invariants));
  }

  public WhileCmd(IToken tok, [Captured] Expr guard, List<PredicateCmd> invariants, List<CallCmd> yields, StmtList body)
    : base(tok)
  {
    Contract.Requires(Cce.NonNullElements(invariants));
    Contract.Requires(body != null);
    Contract.Requires(tok != null);
    this.Guard = guard;
    this.Invariants = invariants;
    this.Yields = yields;
    this.Body = body;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.Write(level, "while (");
    if (Guard == null)
    {
      stream.Write("*");
    }
    else
    {
      Guard.Emit(stream);
    }

    stream.WriteLine(")");

    foreach (var yield in Yields)
    {
      stream.Write(level + 1, "invariant");
      yield.Emit(stream, level + 1);
    }
    foreach (var inv in Invariants)
    {
      if (inv is AssumeCmd)
      {
        stream.Write(level + 1, "free invariant ");
      }
      else
      {
        stream.Write(level + 1, "invariant ");
      }

      Cmd.EmitAttributes(stream, inv.Attributes);
      inv.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    stream.WriteLine(level, "{");
    Body.Emit(stream, level + 1);
    stream.WriteLine(level, "}");
  }
}