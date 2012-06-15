using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify {

class StructuredRegion : IRegion {
  WhileCmd cmd;
  StmtList stmts;

  public StructuredRegion(WhileCmd cmd) {
    this.cmd = cmd;
  }

  public StructuredRegion(StmtList stmts) {
    this.stmts = stmts;
  }

  public StructuredRegion(Implementation impl) {
    this.stmts = impl.StructuredStmts;
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
    if (cmd != null)
      return Cmds(cmd.Body);
    else
      return Cmds(stmts);
  }

  public IEnumerable<object> CmdsChildRegions() {
    if (cmd != null)
      return CmdsChildRegions(cmd.Body);
    else
      return CmdsChildRegions(stmts);
  }

  public IEnumerable<IRegion> SubRegions() {
    if (cmd != null)
      return SubRegions(cmd.Body);
    else
      return SubRegions(stmts);
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