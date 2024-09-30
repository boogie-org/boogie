using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

/// <summary>
/// A StateCmd is like an imperative-let binding around a sequence of commands.
/// There is no user syntax for a StateCmd.  Instead, a StateCmd is only used
/// temporarily during the desugaring phase inside the VC generator.
/// </summary>
public class StateCmd : Cmd
{
  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this.locals != null);
    Contract.Invariant(this.cmds != null);
  }

  private List<Variable> locals;

  public /*readonly, except for the StandardVisitor*/ List<Variable> /*!*/ Locals
  {
    get
    {
      Contract.Ensures(Contract.Result<List<Variable>>() != null);
      return this.locals;
    }
    internal set
    {
      Contract.Requires(value != null);
      this.locals = value;
    }
  }

  private List<Cmd> cmds;

  public /*readonly, except for the StandardVisitor*/ List<Cmd> /*!*/ Cmds
  {
    get
    {
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      return this.cmds;
    }
    set
    {
      Contract.Requires(value != null);
      this.cmds = value;
    }
  }

  public StateCmd(IToken tok, List<Variable> /*!*/ locals, List<Cmd> /*!*/ cmds)
    : base(tok)
  {
    Contract.Requires(locals != null);
    Contract.Requires(cmds != null);
    Contract.Requires(tok != null);
    this.locals = locals;
    this.cmds = cmds;
  }

  public override void Resolve(ResolutionContext rc)
  {
    //Contract.Requires(rc != null);
    rc.PushVarContext();
    foreach (Variable /*!*/ v in Locals)
    {
      Contract.Assert(v != null);
      rc.AddVariable(v);
    }

    foreach (Cmd /*!*/ cmd in Cmds)
    {
      Contract.Assert(cmd != null);
      cmd.Resolve(rc);
    }

    rc.PopVarContext();
  }

  public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
    var vs = new List<IdentifierExpr>();
    foreach (Cmd cmd in Cmds)
    {
      Contract.Assert(cmd != null);
      cmd.AddAssignedIdentifiers(vs);
    }

    var localsSet = new HashSet<Variable>(this.Locals);
    foreach (var v in vs)
    {
      Debug.Assert(v.Decl != null);
      if (!localsSet.Contains(v.Decl))
      {
        vars.Add(v);
      }
    }
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    //Contract.Requires(tc != null);
    foreach (Cmd /*!*/ cmd in Cmds)
    {
      Contract.Assert(cmd != null);
      cmd.Typecheck(tc);
    }
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    //Contract.Requires(stream != null);
    stream.WriteLine(this, level, "{");
    foreach (Variable /*!*/ v in Locals)
    {
      Contract.Assert(v != null);
      v.Emit(stream, level + 1);
    }

    foreach (Cmd /*!*/ c in Cmds)
    {
      Contract.Assert(c != null);
      c.Emit(stream, level + 1);
    }

    stream.WriteLine(level, "}");
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    //Contract.Requires(visitor != null);
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitStateCmd(this);
  }
}