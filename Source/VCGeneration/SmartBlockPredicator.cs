using Graphing;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie {

public class SmartBlockPredicator {

  Program prog;
  Implementation impl;
  Graph<Block> blockGraph;
  List<Tuple<Block, bool>> sortedBlocks;

  bool useProcedurePredicates = true;

  Dictionary<Block, Variable> predMap, defMap;
  Dictionary<Block, HashSet<Variable>> ownedMap;
  Dictionary<Block, PartInfo> partInfo;

  IdentifierExpr fp;
  Dictionary<Microsoft.Boogie.Type, IdentifierExpr> havocVars =
    new Dictionary<Microsoft.Boogie.Type, IdentifierExpr>();
  Dictionary<Block, Expr> blockIds = new Dictionary<Block, Expr>();
  HashSet<Block> doneBlocks = new HashSet<Block>();

  SmartBlockPredicator(Program p, Implementation i, bool upp) {
    prog = p;
    impl = i;
    useProcedurePredicates = upp;
  }

  void PredicateCmd(Expr p, List<Block> blocks, Block block, Cmd cmd, out Block nextBlock) {
    if (!useProcedurePredicates && cmd is CallCmd) {
      var trueBlock = new Block();
      blocks.Add(trueBlock);
      trueBlock.Label = block.Label + ".call.true";
      trueBlock.Cmds.Add(new AssumeCmd(Token.NoToken, p));
      trueBlock.Cmds.Add(cmd);

      var falseBlock = new Block();
      blocks.Add(falseBlock);
      falseBlock.Label = block.Label + ".call.false";
      falseBlock.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(p)));

      var contBlock = new Block();
      blocks.Add(contBlock);
      contBlock.Label = block.Label + ".call.cont";

      block.TransferCmd =
        new GotoCmd(Token.NoToken, new BlockSeq(trueBlock, falseBlock));
      trueBlock.TransferCmd = falseBlock.TransferCmd =
        new GotoCmd(Token.NoToken, new BlockSeq(contBlock));
      nextBlock = contBlock;
    } else {
      PredicateCmd(p, block.Cmds, cmd);
      nextBlock = block;
    }
  }

  void PredicateCmd(Expr p, CmdSeq cmdSeq, Cmd cmd) {
    if (p == null) {
      cmdSeq.Add(cmd);
      return;
    }

    if (cmd is AssignCmd) {
      var aCmd = (AssignCmd)cmd;
      cmdSeq.Add(new AssignCmd(Token.NoToken, aCmd.Lhss,
                   new List<Expr>(aCmd.Lhss.Zip(aCmd.Rhss, (lhs, rhs) =>
                     new NAryExpr(Token.NoToken,
                       new IfThenElse(Token.NoToken),
                       new ExprSeq(p, rhs, lhs.AsExpr))))));
    } else if (cmd is AssertCmd) {
      var aCmd = (AssertCmd)cmd;
      Expr newExpr = new EnabledReplacementVisitor(p).VisitExpr(aCmd.Expr);
      aCmd.Expr = QKeyValue.FindBoolAttribute(aCmd.Attributes, "do_not_predicate") ? newExpr : Expr.Imp(p, newExpr);
      cmdSeq.Add(aCmd);
    } else if (cmd is AssumeCmd) {
      var aCmd = (AssumeCmd)cmd;
      cmdSeq.Add(new AssumeCmd(Token.NoToken, Expr.Imp(p, aCmd.Expr)));
    } else if (cmd is HavocCmd) {
      var hCmd = (HavocCmd)cmd;
      foreach (IdentifierExpr v in hCmd.Vars) {
        Microsoft.Boogie.Type type = v.Decl.TypedIdent.Type;
        Contract.Assert(type != null);

        IdentifierExpr havocTempExpr;
        if (havocVars.ContainsKey(type)) {
          havocTempExpr = havocVars[type];
        } else {
          var havocVar = new LocalVariable(Token.NoToken,
                             new TypedIdent(Token.NoToken,
                                            "_HAVOC_" + type.ToString(), type));
          impl.LocVars.Add(havocVar);
          havocVars[type] = havocTempExpr =
            new IdentifierExpr(Token.NoToken, havocVar);
        }
        cmdSeq.Add(new HavocCmd(Token.NoToken,
                                new IdentifierExprSeq(havocTempExpr)));
        cmdSeq.Add(Cmd.SimpleAssign(Token.NoToken, v,
                                    new NAryExpr(Token.NoToken,
                                      new IfThenElse(Token.NoToken),
                                      new ExprSeq(p, havocTempExpr, v))));
      }
    } else if (cmd is CallCmd) {
      Debug.Assert(useProcedurePredicates);
      var cCmd = (CallCmd)cmd;
      cCmd.Ins.Insert(0, p);
      cmdSeq.Add(cCmd);
    }
    else if (cmd is CommentCmd) {
      // skip
    }
    else if (cmd is StateCmd) {
      var sCmd = (StateCmd)cmd;
      var newCmdSeq = new CmdSeq();
      foreach (Cmd c in sCmd.Cmds)
        PredicateCmd(p, newCmdSeq, c);
      sCmd.Cmds = newCmdSeq;
      cmdSeq.Add(sCmd);
    }
    else {
      Console.WriteLine("Unsupported cmd: " + cmd.GetType().ToString());
    }
  }

  void PredicateTransferCmd(Expr p, Block src, CmdSeq cmdSeq, TransferCmd cmd) {
    if (cmd is GotoCmd) {
      var gCmd = (GotoCmd)cmd;
      if (gCmd.labelTargets.Length == 1) {
        if (defMap.ContainsKey(gCmd.labelTargets[0]))
          PredicateCmd(p, cmdSeq,
                       Cmd.SimpleAssign(Token.NoToken,
                                        Expr.Ident(predMap[gCmd.labelTargets[0]]), Expr.True));
      } else {
        Debug.Assert(gCmd.labelTargets.Length > 1);
        Debug.Assert(gCmd.labelTargets.Cast<Block>().All(t => partInfo.ContainsKey(t)));
        foreach (Block target in gCmd.labelTargets) {
          var part = partInfo[target];
          if (defMap.ContainsKey(part.realDest))
            PredicateCmd(p, cmdSeq,
                         Cmd.SimpleAssign(Token.NoToken,
                                          Expr.Ident(predMap[part.realDest]), part.pred));
          var predsExitingLoop = new Dictionary<Block, List<Expr>>();
          foreach (Block exit in LoopsExited(src, target)) {
            List<Expr> predList;
            if (!predsExitingLoop.ContainsKey(exit))
              predList = predsExitingLoop[exit] = new List<Expr>();
            else
              predList = predsExitingLoop[exit];
            predList.Add(part.pred);
          }
          foreach (var pred in predsExitingLoop) {
            PredicateCmd(p, cmdSeq,
                         Cmd.SimpleAssign(Token.NoToken,
                                          Expr.Ident(predMap[pred.Key]),
                                          Expr.Not(pred.Value.Aggregate(Expr.Or))));
          }
        }
      }
    } else if (cmd is ReturnCmd) {
      // Blocks which end in a return will never share a predicate with a block
      // which appears after it.  Furthermore, such a block cannot be part of a
      // loop.  So it is safe to do nothing here.
    } else {
      Console.WriteLine("Unsupported cmd: " + cmd.GetType().ToString());
    }
  }

  Variable FreshPredicate(ref int predCount) {
    var pVar = new LocalVariable(Token.NoToken,
                                 new TypedIdent(Token.NoToken,
                                                "p" + predCount++,
                                                Microsoft.Boogie.Type.Bool));
    impl.LocVars.Add(pVar);
    return pVar;
  }

  void AssignPredicates(Graph<Block> blockGraph,
                        DomRelation<Block> dom,
                        DomRelation<Block> pdom,
                        IEnumerator<Tuple<Block, bool>> i,
                        Variable headPredicate,
                        ref int predCount,
                        Dictionary<Block, Variable> predMap,
                        Dictionary<Block, Variable> defMap,
                        Dictionary<Block, HashSet<Variable>> ownedMap) {
    var header = i.Current.Item1;
    var regionPreds = new List<Tuple<Block, Variable>>();
    var ownedPreds = new HashSet<Variable>();
    ownedMap[header] = ownedPreds;

    predMap[header] = headPredicate;
    defMap[header] = headPredicate;
    regionPreds.Add(new Tuple<Block, Variable>(header, headPredicate));
    if (!i.MoveNext())
      return;

    do {
      var block = i.Current;
      if (block.Item2) {
        if (block.Item1 == header)
          return;
      } else {
        if (blockGraph.Headers.Contains(block.Item1)) {
          var loopPred = FreshPredicate(ref predCount);
          ownedPreds.Add(loopPred);
          AssignPredicates(blockGraph, dom, pdom, i, loopPred, ref predCount,
                           predMap, defMap, ownedMap);
        } else {
          bool foundExisting = false;
          foreach (var regionPred in regionPreds) {
            if (dom.DominatedBy(block.Item1, regionPred.Item1) &&
                pdom.DominatedBy(regionPred.Item1, block.Item1)) {
              predMap[block.Item1] = regionPred.Item2;
              foundExisting = true;
              break;
            }
          }
          if (!foundExisting) {
            var condPred = FreshPredicate(ref predCount);
            predMap[block.Item1] = condPred;
            defMap[block.Item1] = condPred;
            ownedPreds.Add(condPred);
            regionPreds.Add(new Tuple<Block, Variable>(block.Item1, condPred));
          }
        }
      }
    } while (i.MoveNext());
  }

  void AssignPredicates(out Dictionary<Block, Variable> predMap,
                        out Dictionary<Block, Variable> defMap,
                        out Dictionary<Block, HashSet<Variable>> ownedMap) {
    DomRelation<Block> dom = blockGraph.DominatorMap;

    Graph<Block> dualGraph = blockGraph.Dual(new Block());
    DomRelation<Block> pdom = dualGraph.DominatorMap;

    var iter = sortedBlocks.GetEnumerator();
    if (!iter.MoveNext()) {
      predMap = defMap = null;
      ownedMap = null;
      return;
    }

    int predCount = 0;
    predMap = new Dictionary<Block, Variable>();
    defMap = new Dictionary<Block, Variable>();
    ownedMap = new Dictionary<Block, HashSet<Variable>>();
    AssignPredicates(blockGraph, dom, pdom, iter,
                     useProcedurePredicates ? impl.InParams[0] : null,
                     ref predCount, predMap, defMap, ownedMap);
  }

  IEnumerable<Block> LoopsExited(Block src, Block dest) {
    var i = sortedBlocks.GetEnumerator();
    while (i.MoveNext()) {
      var b = i.Current;
      if (b.Item1 == src) {
        return LoopsExitedForwardEdge(dest, i);
      } else if (b.Item1 == dest) {
        return LoopsExitedBackEdge(src, i);
      }
    }
    Debug.Assert(false);
    return null;
  }

  private IEnumerable<Block> LoopsExitedBackEdge(Block src, IEnumerator<Tuple<Block, bool>> i) {
    var headsSeen = new HashSet<Block>();
    while (i.MoveNext()) {
      var b = i.Current;
      if (!b.Item2 && blockGraph.Headers.Contains(b.Item1))
        headsSeen.Add(b.Item1);
      else if (b.Item2)
        headsSeen.Remove(b.Item1);
      if (b.Item1 == src)
        return headsSeen;
    }
    Debug.Assert(false);
    return null;
  }

  private IEnumerable<Block> LoopsExitedForwardEdge(Block dest, IEnumerator<Tuple<Block, bool>> i) {
    var headsSeen = new HashSet<Block>();
    while (i.MoveNext()) {
      var b = i.Current;
      if (b.Item1 == dest)
        yield break;
      else if (!b.Item2 && blockGraph.Headers.Contains(b.Item1))
        headsSeen.Add(b.Item1);
      else if (b.Item2 && !headsSeen.Contains(b.Item1))
        yield return b.Item1;
    }
    Debug.Assert(false);
  }

  class PartInfo {
    public PartInfo(Expr p, Block r) { pred = p; realDest = r; }
    public Expr pred;
    public Block realDest;
  }

  Dictionary<Block, PartInfo> BuildPartitionInfo() {
    var partInfo = new Dictionary<Block, PartInfo>();
    foreach (var block in blockGraph.Nodes) {
      var parts = block.Cmds.Cast<Cmd>().TakeWhile(
          c => c is AssumeCmd &&
          QKeyValue.FindBoolAttribute(((AssumeCmd)c).Attributes, "partition"));

      Expr pred = null;
      if (parts.Count() > 0) {
        pred = parts.Select(a => ((AssumeCmd)a).Expr).Aggregate(Expr.And);
        block.Cmds =
          new CmdSeq(block.Cmds.Cast<Cmd>().Skip(parts.Count()).ToArray());
      } else {
        continue;
      }

      Block realDest = block;
      if (block.Cmds.Length == 0) {
        var gc = block.TransferCmd as GotoCmd;
        if (gc != null && gc.labelTargets.Length == 1)
          realDest = gc.labelTargets[0];
      }
      partInfo[block] = new PartInfo(pred, realDest);
    }

    return partInfo;
  }

  void PredicateImplementation() {
    blockGraph = prog.ProcessLoops(impl);
    sortedBlocks = blockGraph.LoopyTopSort();

    AssignPredicates(out predMap, out defMap, out ownedMap);
    partInfo = BuildPartitionInfo();

    if (useProcedurePredicates)
      fp = Expr.Ident(impl.InParams[0]);

    var newBlocks = new List<Block>();
    Block prevBlock = null;
    foreach (var n in sortedBlocks) {
      var p = predMap[n.Item1];
      var pExpr = Expr.Ident(p);

      if (n.Item2) {
        var backedgeBlock = new Block();
        newBlocks.Add(backedgeBlock);

        backedgeBlock.Label = n.Item1.Label + ".backedge";
        backedgeBlock.Cmds = new CmdSeq(new AssumeCmd(Token.NoToken, pExpr,
          new QKeyValue(Token.NoToken, "backedge", new List<object>(), null)));
        backedgeBlock.TransferCmd = new GotoCmd(Token.NoToken,
                                                new BlockSeq(n.Item1));

        var tailBlock = new Block();
        newBlocks.Add(tailBlock);

        tailBlock.Label = n.Item1.Label + ".tail";
        tailBlock.Cmds = new CmdSeq(new AssumeCmd(Token.NoToken,
                                             Expr.Not(pExpr)));

        if (prevBlock != null)
          prevBlock.TransferCmd = new GotoCmd(Token.NoToken,
                                        new BlockSeq(backedgeBlock, tailBlock));
        prevBlock = tailBlock;
      } else {
        var runBlock = n.Item1;
        var oldCmdSeq = runBlock.Cmds;
        runBlock.Cmds = new CmdSeq();
        newBlocks.Add(runBlock);
        if (prevBlock != null)
          prevBlock.TransferCmd = new GotoCmd(Token.NoToken,
                                              new BlockSeq(runBlock));

        var transferCmd = runBlock.TransferCmd;
        foreach (Cmd cmd in oldCmdSeq)
          PredicateCmd(pExpr, newBlocks, runBlock, cmd, out runBlock);

        if (ownedMap.ContainsKey(n.Item1)) {
          var owned = ownedMap[n.Item1];
          foreach (var v in owned)
            runBlock.Cmds.Add(Cmd.SimpleAssign(Token.NoToken, Expr.Ident(v), Expr.False));
        }

        PredicateTransferCmd(pExpr, runBlock, runBlock.Cmds, transferCmd);

        prevBlock = runBlock;
        doneBlocks.Add(runBlock);
      }
    }

    prevBlock.TransferCmd = new ReturnCmd(Token.NoToken);
    impl.Blocks = newBlocks;
  }

  private Expr CreateIfFPThenElse(Expr then, Expr eElse) {
    if (useProcedurePredicates) {
      return new NAryExpr(Token.NoToken,
                 new IfThenElse(Token.NoToken),
                 new ExprSeq(fp, then, eElse));
    } else {
      return then;
    }
  }

  public static void Predicate(Program p,
                               bool useProcedurePredicates = true) {
    foreach (var decl in p.TopLevelDeclarations.ToList()) {
      if (useProcedurePredicates && decl is DeclWithFormals && !(decl is Function)) {
        var dwf = (DeclWithFormals)decl;
        var fpVar = new Formal(Token.NoToken,
                               new TypedIdent(Token.NoToken, "_P",
                                              Microsoft.Boogie.Type.Bool),
                               /*incoming=*/true);
        dwf.InParams = new VariableSeq(
          (new Variable[] {fpVar}.Concat(dwf.InParams.Cast<Variable>()))
            .ToArray());

        if (dwf is Procedure)
        {
            var proc = (Procedure)dwf;
            var newRequires = new RequiresSeq();
            foreach (Requires r in proc.Requires)
            {
                newRequires.Add(new Requires(r.Free,
                    new EnabledReplacementVisitor(new IdentifierExpr(Token.NoToken, fpVar)).VisitExpr(r.Condition)));
            }
            var newEnsures = new EnsuresSeq();
            foreach (Ensures e in proc.Ensures)
            {
                newEnsures.Add(new Ensures(e.Free,
                    new EnabledReplacementVisitor(new IdentifierExpr(Token.NoToken, fpVar)).VisitExpr(e.Condition)));
            }
        }

      }

      try {
        var impl = decl as Implementation;
        if (impl != null)
          new SmartBlockPredicator(p, impl, useProcedurePredicates).PredicateImplementation();
      }
      catch (Program.IrreducibleLoopException) { }
    }
  }

  public static void Predicate(Program p, Implementation impl) {
    try {
      new SmartBlockPredicator(p, impl, false).PredicateImplementation();
    }
    catch (Program.IrreducibleLoopException) { }
  }

}

}
