using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify {

class StructuredRegion : IRegion {
  Implementation impl;
  WhileCmd cmd;

  public StructuredRegion(Implementation impl) {
    this.impl = impl;
  }

  public StructuredRegion(WhileCmd cmd) {
    this.cmd = cmd;
  }

  public object Identifier() {
    if (cmd != null)
      return cmd;
    else
      return impl;
  }

  private StmtList StmtList() {
    if (cmd != null)
      return cmd.Body;
    else
      return impl.StructuredStmts;
  }

  private IEnumerable<Cmd> Cmds(StmtList stmts) {
    foreach (var bb in stmts.BigBlocks) {
      foreach (Cmd c in bb.simpleCmds)
        yield return c;

      if (bb.ec is IfCmd) {
        var ic = (IfCmd)bb.ec;
        foreach (var c in Cmds(ic.thn))
          yield return c;

        if (ic.elseBlock != null)
          foreach (var c in Cmds(ic.elseBlock))
            yield return c;
      } else if (bb.ec is WhileCmd) {
        var wc = (WhileCmd)bb.ec;
        foreach (var c in Cmds(wc.Body))
          yield return c;
      }
    }
  }

  private IEnumerable<object> CmdsChildRegions(StmtList stmts) {
    foreach (var bb in stmts.BigBlocks) {
      foreach (Cmd c in bb.simpleCmds)
        yield return c;

      if (bb.ec is IfCmd) {
        var ic = (IfCmd)bb.ec;
        foreach (var c in Cmds(ic.thn))
          yield return c;

        if (ic.elseBlock != null)
          foreach (var c in Cmds(ic.elseBlock))
            yield return c;
      } else if (bb.ec is WhileCmd) {
        var wc = (WhileCmd)bb.ec;
        yield return new StructuredRegion(wc);
      }
    }
  }

  private IEnumerable<IRegion> SubRegions(StmtList stmts) {
    foreach (var bb in stmts.BigBlocks) {
      if (bb.ec is IfCmd) {
        var ic = (IfCmd)bb.ec;
        foreach (var r in SubRegions(ic.thn))
          yield return r;

        if (ic.elseBlock != null)
          foreach (var r in SubRegions(ic.elseBlock))
            yield return r;
      } else if (bb.ec is WhileCmd) {
        var wc = (WhileCmd)bb.ec;
        yield return new StructuredRegion(wc);

        foreach (var r in SubRegions(wc.Body))
          yield return r;
      }
    }
  }

  public IEnumerable<Cmd> Cmds() {
    return Cmds(StmtList());
  }

  public IEnumerable<object> CmdsChildRegions() {
    return CmdsChildRegions(StmtList());
  }

  public IEnumerable<IRegion> SubRegions() {
    return SubRegions(StmtList());
  }

  public Expr Guard() {
    if (cmd != null)
      return cmd.Guard;
    else
      return null;
  }

  public void AddInvariant(PredicateCmd pc) {
    if (cmd != null)
      cmd.Invariants.Add(pc);
  }
}

}
