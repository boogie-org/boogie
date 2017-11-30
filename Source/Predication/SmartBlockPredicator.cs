using Microsoft.Boogie.GraphUtil;
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

  Func<Procedure, bool> useProcedurePredicates;

  Dictionary<Block, Variable> predMap, defMap;
  Dictionary<Block, HashSet<Variable>> ownedMap;
  Dictionary<Block, Block> parentMap;
  Dictionary<Block, PartInfo> partInfo;

  IdentifierExpr fp;
  Dictionary<Microsoft.Boogie.Type, IdentifierExpr> havocVars =
    new Dictionary<Microsoft.Boogie.Type, IdentifierExpr>();
  HashSet<Block> doneBlocks = new HashSet<Block>();
  bool myUseProcedurePredicates;
  UniformityAnalyser uni;

  SmartBlockPredicator(Program p, Implementation i, Func<Procedure, bool> upp, UniformityAnalyser u) {
    prog = p;
    impl = i;
    useProcedurePredicates = upp;
    myUseProcedurePredicates = useProcedurePredicates(i.Proc);
    uni = u;
  }

  void PredicateCmd(Expr p, Expr pDom, List<Block> blocks, Block block, Cmd cmd, out Block nextBlock) {
    var cCmd = cmd as CallCmd;
    if (cCmd != null && !useProcedurePredicates(cCmd.Proc)) {
      if (p == null) {
        block.Cmds.Add(cmd);
        nextBlock = block;
        return;
      }

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
        new GotoCmd(Token.NoToken, new List<Block> { trueBlock, falseBlock });
      trueBlock.TransferCmd = falseBlock.TransferCmd =
        new GotoCmd(Token.NoToken, new List<Block> { contBlock });
      nextBlock = contBlock;
    } else {
      PredicateCmd(p, pDom, block.Cmds, cmd);
      nextBlock = block;
    }
  }

  void PredicateCmd(Expr p, Expr pDom, List<Cmd> cmdSeq, Cmd cmd) {
    if (cmd is CallCmd) {
      var cCmd = (CallCmd)cmd;
      Debug.Assert(useProcedurePredicates(cCmd.Proc));
      foreach (IdentifierExpr e in cCmd.Outs) {
        cCmd.Ins.Add(e);
      }
      cCmd.Ins.Insert(0, p != null ? p : Expr.True);
      cmdSeq.Add(cCmd);
    } else if (p == null) {
      new EnabledReplacementVisitor(Expr.True, pDom).Visit(cmd);
      cmdSeq.Add(cmd);
    } else if (cmd is AssignCmd) {
      var aCmd = (AssignCmd)cmd;
      cmdSeq.Add(new AssignCmd(Token.NoToken, aCmd.Lhss,
                   new List<Expr>(aCmd.Lhss.Zip(aCmd.Rhss, (lhs, rhs) =>
                     new NAryExpr(Token.NoToken,
                       new IfThenElse(Token.NoToken),
                       new List<Expr> { p, rhs, lhs.AsExpr })))));
    } else if (cmd is AssertCmd) {
      var aCmd = (AssertCmd)cmd;
      Expr newExpr = new EnabledReplacementVisitor(p, pDom).VisitExpr(aCmd.Expr);
      aCmd.Expr = QKeyValue.FindBoolAttribute(aCmd.Attributes, "do_not_predicate") ? newExpr : Expr.Imp(p, newExpr);
      cmdSeq.Add(aCmd);
    } else if (cmd is AssumeCmd) {
      var aCmd = (AssumeCmd)cmd;
      Expr newExpr = new EnabledReplacementVisitor(p, pDom).VisitExpr(aCmd.Expr);
      aCmd.Expr = QKeyValue.FindBoolAttribute(aCmd.Attributes, "do_not_predicate") ? newExpr : Expr.Imp(p, newExpr);
      cmdSeq.Add(aCmd);
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
                                new List<IdentifierExpr> { havocTempExpr }));
        cmdSeq.Add(Cmd.SimpleAssign(Token.NoToken, v,
                                    new NAryExpr(Token.NoToken,
                                      new IfThenElse(Token.NoToken),
                                      new List<Expr> { p, havocTempExpr, v })));
      }
    } else if (cmd is CommentCmd) {
      // skip
    } else if (cmd is StateCmd) {
      var sCmd = (StateCmd)cmd;
      var newCmdSeq = new List<Cmd>();
      foreach (Cmd c in sCmd.Cmds)
        PredicateCmd(p, pDom, newCmdSeq, c);
      sCmd.Cmds = newCmdSeq;
      cmdSeq.Add(sCmd);
    } else {
      Console.WriteLine("Unsupported cmd: " + cmd.GetType().ToString());
    }
  }

  // hasPredicatedRegion is true iff the block or its targets are predicated
  // (i.e. we enter, stay within or exit a predicated region).
  void PredicateTransferCmd(Expr p, Block src, List<Cmd> cmdSeq, TransferCmd cmd, out bool hasPredicatedRegion) {
    hasPredicatedRegion = predMap.ContainsKey(src);

    if (cmd is GotoCmd) {
      var gCmd = (GotoCmd)cmd;

      hasPredicatedRegion = hasPredicatedRegion ||
        gCmd.labelTargets.Cast<Block>().Any(b => predMap.ContainsKey(b));

      if (gCmd.labelTargets.Count == 1) {
        if (defMap.ContainsKey(gCmd.labelTargets[0])) {
          PredicateCmd(p, Expr.True, cmdSeq,
                       Cmd.SimpleAssign(Token.NoToken,
                                        Expr.Ident(predMap[gCmd.labelTargets[0]]), Expr.True));
        }
      } else {
        Debug.Assert(gCmd.labelTargets.Count > 1);
        Debug.Assert(gCmd.labelTargets.Cast<Block>().All(t => uni.IsUniform(impl.Name, t) ||
                                                              partInfo.ContainsKey(t)));
        foreach (Block target in gCmd.labelTargets) {
          if (!partInfo.ContainsKey(target))
            continue;

          // In this case we not only predicate with the current predicate p,
          // but also with the "part predicate"; this ensures that we do not
          // update a predicate twice when it occurs in both parts.
          var part = partInfo[target];
          if (defMap.ContainsKey(part.realDest)) {
            PredicateCmd(p == null ? part.pred : Expr.And(p, part.pred), Expr.True, cmdSeq,
                         Cmd.SimpleAssign(Token.NoToken,
                                          Expr.Ident(predMap[part.realDest]), part.pred));
          }
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
            PredicateCmd(p == null ? part.pred : Expr.And(p, part.pred), Expr.True, cmdSeq,
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
                        IEnumerable<Block> headerDominance,
                        IEnumerator<Tuple<Block, bool>> i,
                        Variable headPredicate,
                        ref int predCount) {
    var header = i.Current.Item1;
    var regionPreds = new List<Tuple<Block, Variable>>();
    var ownedPreds = new HashSet<Variable>();
    ownedMap[header] = ownedPreds;

    if (headPredicate != null) {
      predMap[header] = headPredicate;
      defMap[header] = headPredicate;
      regionPreds.Add(new Tuple<Block, Variable>(header, headPredicate));
    }

    while (i.MoveNext()) {
      var block = i.Current;

      if (block.Item2) {
        if (block.Item1 == header) {
          return;
        }
      }

      if (uni != null && uni.IsUniform(impl.Name, block.Item1)) {
        if (blockGraph.Headers.Contains(block.Item1)) {
          parentMap[block.Item1] = header;
          AssignPredicates(blockGraph, dom, pdom, headerDominance, i, headPredicate, ref predCount);
        }
        continue;
      }

      if (!block.Item2) {
        if (blockGraph.Headers.Contains(block.Item1)) {
          parentMap[block.Item1] = header;
          var loopPred = FreshPredicate(ref predCount);
          ownedPreds.Add(loopPred);
          AssignPredicates(blockGraph, dom, pdom, headerDominance, i, loopPred, ref predCount);
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
            var headerIterator = headerDominance.GetEnumerator();
            // Add the predicate to the loop header H that dominates the node (if one
            // exists) such that H does not dominate another header which also dominates
            // the node. Since predicates are owned by loop headers (or the program entry
            // node), this is the block 'closest' to block to which we are assigning a
            // that can be made to own the predicate.
            Block node = null;
            while (headerIterator.MoveNext()) {
              var current = headerIterator.Current;
              if (dom.DominatedBy(block.Item1, current)) {
                node = current;
                break;
              }
            }
            if (node != null) {
              ownedMap[node].Add(condPred);
            } else {
               // In this case the header is the program entry node.
              ownedPreds.Add(condPred);
            }
            regionPreds.Add(new Tuple<Block, Variable>(block.Item1, condPred));
          }
        }
      }
    }
  }

  void AssignPredicates() {
    DomRelation<Block> dom = blockGraph.DominatorMap;

    Graph<Block> dualGraph = blockGraph.Dual(new Block());
    DomRelation<Block> pdom = dualGraph.DominatorMap;
    IEnumerable<Block> headerDominance = blockGraph.SortHeadersByDominance();

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
    parentMap = new Dictionary<Block, Block>();
    AssignPredicates(blockGraph, dom, pdom, headerDominance, iter,
                     myUseProcedurePredicates ? impl.InParams[0] : null,
                     ref predCount);
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
      if (uni.IsUniform(impl.Name, block))
        continue;

      var parts = block.Cmds.Cast<Cmd>().TakeWhile(
          c => c is AssumeCmd &&
          QKeyValue.FindBoolAttribute(((AssumeCmd)c).Attributes, "partition"));

      Expr pred = null;
      if (parts.Count() > 0) {
        pred = parts.Select(a => ((AssumeCmd)a).Expr).Aggregate(Expr.And);
        block.Cmds =
          new List<Cmd>(block.Cmds.Cast<Cmd>().Skip(parts.Count()).ToArray());
      } else {
        continue;
      }

      Block realDest = block;
      if (block.Cmds.Count == 0) {
        var gc = block.TransferCmd as GotoCmd;
        if (gc != null && gc.labelTargets.Count == 1)
          realDest = gc.labelTargets[0];
      }
      partInfo[block] = new PartInfo(pred, realDest);
    }

    return partInfo;
  }

  Block FindImmediateDominator(Block block) {
    Block predecessor = null;
    foreach(var pred in blockGraph.Predecessors(block)) {
      if (!blockGraph.DominatorMap.DominatedBy(pred, block)) {
        if (predecessor == null)
          predecessor = pred;
        else
          predecessor = blockGraph.DominatorMap.LeastCommonAncestor(pred, predecessor);
      }
    }
    return predecessor;
  }

  void PredicateImplementation() {
    blockGraph = prog.ProcessLoops(impl);
    sortedBlocks = blockGraph.LoopyTopSort();

    AssignPredicates();
    partInfo = BuildPartitionInfo();

    if (myUseProcedurePredicates)
      fp = Expr.Ident(impl.InParams[0]);

    var newBlocks = new List<Block>();
    Block prevBlock = null;
    foreach (var n in sortedBlocks) {
      if (predMap.ContainsKey(n.Item1)) {
        var p = predMap[n.Item1];
        var pExpr = Expr.Ident(p);

        if (n.Item2) {
          var dominator = FindImmediateDominator(n.Item1);
          if (dominator != null && predMap.ContainsKey(dominator)) {
            AssumeCmd aCmd = new AssumeCmd(Token.NoToken, Expr.True);
            aCmd.Attributes = new QKeyValue(Token.NoToken, "dominator_predicate", new List<object>() { predMap[dominator].ToString() }, aCmd.Attributes);
            aCmd.Attributes = new QKeyValue(Token.NoToken, "predicate", new List<object>() { predMap[n.Item1].ToString() }, aCmd.Attributes);
            n.Item1.Cmds.Insert(0, aCmd);
          }

          var backedgeBlock = new Block();
          newBlocks.Add(backedgeBlock);

          backedgeBlock.Label = n.Item1.Label + ".backedge";
          backedgeBlock.Cmds = new List<Cmd> { new AssumeCmd(Token.NoToken, pExpr,
            new QKeyValue(Token.NoToken, "backedge", new List<object>(), null)) };
          backedgeBlock.TransferCmd = new GotoCmd(Token.NoToken,
                                                  new List<Block> { n.Item1 });

          var tailBlock = new Block();
          newBlocks.Add(tailBlock);

          tailBlock.Label = n.Item1.Label + ".tail";
          tailBlock.Cmds = new List<Cmd> { new AssumeCmd(Token.NoToken,
                                               Expr.Not(pExpr)) };

          if (uni != null && !uni.IsUniform(impl.Name, n.Item1)) {
            uni.AddNonUniform(impl.Name, backedgeBlock);
            uni.AddNonUniform(impl.Name, tailBlock);
          }

          if (prevBlock != null)
            prevBlock.TransferCmd = new GotoCmd(Token.NoToken,
                                          new List<Block> { backedgeBlock, tailBlock });
          prevBlock = tailBlock;
        } else {
          PredicateBlock(pExpr, n.Item1, newBlocks, ref prevBlock);
        }
      } else {
        if (!n.Item2) {
          PredicateBlock(null, n.Item1, newBlocks, ref prevBlock);
        }
      }
    }

    if (prevBlock != null)
      prevBlock.TransferCmd = new ReturnCmd(Token.NoToken);

    impl.Blocks = newBlocks;
  }

  private void PredicateBlock(Expr pExpr, Block block, List<Block> newBlocks, ref Block prevBlock) {
    var firstBlock = block;

    var oldCmdSeq = block.Cmds;
    block.Cmds = new List<Cmd>();
    newBlocks.Add(block);
    if (prevBlock != null && !((prevBlock.TransferCmd is ReturnCmd) && uni != null && uni.IsUniform(impl.Name, block))) {
      prevBlock.TransferCmd = new GotoCmd(Token.NoToken, new List<Block> { block });
    }

    Block currentBlock = block;
    Expr pCurrentExpr = pExpr;
    while (parentMap.ContainsKey(currentBlock)) {
      Block parent = parentMap[currentBlock];
      Expr pParentExpr = null;
      if (predMap.ContainsKey(parent)) {
        var parentPred = predMap[parent];
        if (parentPred != null) {
          pParentExpr = Expr.Ident(parentPred);
          block.Cmds.Add(new AssertCmd(Token.NoToken,
                                          pCurrentExpr != null ? (Expr)Expr.Imp(pCurrentExpr, pParentExpr)
                                                               : pParentExpr));
        }
      }
      currentBlock = parent;
      pCurrentExpr = pParentExpr;
    }

    Block dominator = FindImmediateDominator(block);
    Expr pDomExpr = Expr.True;
    if (dominator != null && predMap.ContainsKey(dominator))
      pDomExpr = new IdentifierExpr(Token.NoToken, predMap[dominator]);
    var transferCmd = block.TransferCmd;
    foreach (Cmd cmd in oldCmdSeq)
      PredicateCmd(pExpr, pDomExpr, newBlocks, block, cmd, out block);

    if (ownedMap.ContainsKey(firstBlock)) {
      var owned = ownedMap[firstBlock];
      foreach (var v in owned)
        block.Cmds.Add(Cmd.SimpleAssign(Token.NoToken, Expr.Ident(v), Expr.False));
    }

    bool hasPredicatedRegion;
    PredicateTransferCmd(pExpr, block, block.Cmds, transferCmd, out hasPredicatedRegion);

    if (hasPredicatedRegion)
      prevBlock = block;
    else
      prevBlock = null;

    doneBlocks.Add(block);
  }

  private Expr CreateIfFPThenElse(Expr then, Expr eElse) {
    if (myUseProcedurePredicates) {
      return new NAryExpr(Token.NoToken,
                 new IfThenElse(Token.NoToken),
                 new List<Expr> { fp, then, eElse });
    } else {
      return then;
    }
  }

  public static void Predicate(Program p,
                               Func<Procedure, bool> useProcedurePredicates = null,
                               UniformityAnalyser uni = null) {
    useProcedurePredicates = useProcedurePredicates ?? (proc => false);
    if (uni != null) {
      var oldUPP = useProcedurePredicates;
      useProcedurePredicates = proc => oldUPP(proc) && !uni.IsUniform(proc.Name);
    }

    foreach (var decl in p.TopLevelDeclarations.ToList()) {
      if (decl is Procedure || decl is Implementation) {
        var proc = decl as Procedure;
        Implementation impl = null;
        if (proc == null) {
          impl = (Implementation)decl;
          proc = impl.Proc;
        }

        bool upp = useProcedurePredicates(proc);
        if (upp) {
          var dwf = (DeclWithFormals)decl;
          // Copy InParams, as the list is shared between impl and proc
          var inParams = new List<Variable>(dwf.InParams);

          var fpVar = new Formal(Token.NoToken,
                                 new TypedIdent(Token.NoToken, "_P",
                                                Microsoft.Boogie.Type.Bool),
                                 /*incoming=*/true);
          inParams.Insert(0, fpVar);
          var fpIdentifierExpr = new IdentifierExpr(Token.NoToken, fpVar);

          // Add in-parameters for all out-parameters. These new in-parameters
          // are used to ensure we preserve the value of the variable assigned
          // to when the passed predicate value is false.
          var newEqParamExprs = new List<Expr>();
          var newAssignCmds = new List<Cmd>();
          foreach (Variable outV in dwf.OutParams) {
            var inV = new Formal(Token.NoToken,
                                 new TypedIdent(Token.NoToken, "_V" + outV.TypedIdent.Name,
                                     outV.TypedIdent.Type),
                                 /*incoming=*/true);
            inParams.Add(inV);

            var inVExpr = new IdentifierExpr(Token.NoToken, inV);
            var outVExpr = new IdentifierExpr(Token.NoToken, outV);
            newEqParamExprs.Add(Expr.Imp(Expr.Not(fpIdentifierExpr), Expr.Eq(inVExpr, outVExpr)));
            newAssignCmds.Add(new AssignCmd(Token.NoToken,
                                            new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, outVExpr) },
                                            new List<Expr> { new NAryExpr(Token.NoToken,
                                                             new IfThenElse(Token.NoToken),
                                                             new List<Expr> { fpIdentifierExpr, outVExpr, inVExpr })}));
          }
          dwf.InParams = inParams;

          if (impl == null) {
            foreach (Requires r in proc.Requires) {
              new EnabledReplacementVisitor(fpIdentifierExpr, Expr.True).VisitExpr(r.Condition);
              if (!QKeyValue.FindBoolAttribute(r.Attributes, "do_not_predicate")) {
                r.Condition = Expr.Imp(fpIdentifierExpr, r.Condition);
              }
            }
            foreach (Ensures e in proc.Ensures) {
              new EnabledReplacementVisitor(new IdentifierExpr(Token.NoToken, fpVar), Expr.True).VisitExpr(e.Condition);
              if (!QKeyValue.FindBoolAttribute(e.Attributes, "do_not_predicate")) {
                e.Condition = Expr.Imp(fpIdentifierExpr, e.Condition);
              }
            }
            foreach (Expr e in newEqParamExprs) {
              proc.Ensures.Add(new Ensures(false, e));
            }
          } else {
            try {
              new SmartBlockPredicator(p, impl, useProcedurePredicates, uni).PredicateImplementation();
              foreach (AssignCmd c in newAssignCmds) {
                impl.Blocks.First().Cmds.Insert(0, c);
              }
            } catch (Program.IrreducibleLoopException) { }
          }
        } else {
          if (impl == null) {
            foreach (Requires r in proc.Requires) {
              new EnabledReplacementVisitor(Expr.True, Expr.True).VisitExpr(r.Condition);
            }
            foreach (Ensures e in proc.Ensures) {
              new EnabledReplacementVisitor(Expr.True, Expr.True).VisitExpr(e.Condition);
            }
          } else {
            try {
              new SmartBlockPredicator(p, impl, useProcedurePredicates, uni).PredicateImplementation();
            } catch (Program.IrreducibleLoopException) { }
          }
        }
      }
    }
  }

  public static void Predicate(Program p, Implementation impl) {
    try {
      new SmartBlockPredicator(p, impl, proc => false, null).PredicateImplementation();
    }
    catch (Program.IrreducibleLoopException) { }
  }

}

class EnabledReplacementVisitor : StandardVisitor
{
    private Expr pExpr;
    private Expr pDomExpr;

    internal EnabledReplacementVisitor(Expr pExpr, Expr pDomExpr)
    {
        this.pExpr = pExpr;
        this.pDomExpr = pDomExpr;
    }

    public override Expr VisitExpr(Expr node)
    {
        if (node is IdentifierExpr)
        {
            IdentifierExpr iExpr = node as IdentifierExpr;
            if (iExpr.Decl is Constant && QKeyValue.FindBoolAttribute(iExpr.Decl.Attributes, "__enabled"))
            {
                return pExpr;
            } else if (iExpr.Decl is Constant && QKeyValue.FindBoolAttribute(iExpr.Decl.Attributes, "__dominator_enabled"))
            {
                return pDomExpr;
            }
        }
        return base.VisitExpr(node);
    }
}

}
