using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public class Prune {
    public class DependencyEvaluator : ReadOnlyVisitor
    {
      // For each declaration, we compute incoming and outgoing dependents.
      // Incoming dependents are functions or constants that the declaration may help the solver with.
      // Most incoming dependents correspond to exactly one function or constant, but some of them are tuples.
      // For example, consider an axiom of the form:
      //                        axiom forall x, y :: {P(x, y), Q(y)} {R(x)} P(x, y) ==> R(x)
      // The axiom may (only) be triggerd by a declaration/implementation that either mentions
      // both P and Q or mentions function R.
      // Thus, it has two incoming dependents:
      // 1) the tuple (P, Q) and 2) the function R. I store tuples in the variable incomingTuples.
      // Outgoing dependents consist of functions and constants that a declaration mentions.
      // For the axiom above, there are 2 outgoing dependents: P and R.
      // (notice that Q is excluded because the axiom itself does not mention it.)
      // Now, a declaration A depends on B, if the outgoing dependents of A match
      // with some incoming dependent of B (see method depends).

      public readonly Declaration node; // a node could either be a function or an axiom.
      public HashSet<Declaration> outgoing; // an edge can either be a function or a constant.
      public HashSet<Declaration> incoming;
      public List<HashSet<Declaration>> incomingTuples;
      public HashSet<Type> types;

      public DependencyEvaluator(Declaration d)
      {
        node = d;
        incoming = new HashSet<Declaration>();
        incomingTuples = new List<HashSet<Declaration>>();
        outgoing = new HashSet<Declaration>();
        types = new HashSet<Type>();
      }
      // returns true if there is an edge from a to b
      public static bool depends(DependencyEvaluator a, DependencyEvaluator b)
      {
        return b.incoming.Intersect(a.outgoing).Any() ||
                b.incomingTuples.Where(s => s.IsSubsetOf(a.outgoing)).Any();
      }
    }

    private class FunctionVisitor : DependencyEvaluator
    {
      public FunctionVisitor(Function func) : base(func)
      {
        incoming.Add(func);
      }

      public override Expr VisitExpr(Expr node)
      {
        if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c)
        {
          outgoing.Add(c);
        }
        else if (node is NAryExpr e && e.Fun is FunctionCall f)
        {
          outgoing.Add(f.Func);
        }
        return base.VisitExpr(node);
      }
      public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type node)
      {
        types.Add(node);
        return base.VisitType(node);
      }
    }

    private class AxiomVisitor : DependencyEvaluator
    {
      public AxiomVisitor (Axiom a) : base(a) {}

      private void VisitTriggerCustom(Trigger t) {
        var incomingOld = new HashSet<Declaration>(incoming);
        incoming = new HashSet<Declaration>();
        var triggerList = t.Tr.ToList();
        triggerList.ForEach(e => e.pos = Expr.Position.Neither);
        triggerList.ForEach(e => VisitExpr(e));
        if (incoming.Count() > 1) {
          incomingTuples.Add(new HashSet<Declaration>(incoming));
          incoming = incomingOld;
        } else {
          incoming.UnionWith(incomingOld);
        }
      }

      public override Expr VisitExpr(Expr node) {
        if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c) {
          incoming.Add(c);
          outgoing.Add(c);
        } else if (node is NAryExpr e && e.Fun is FunctionCall f) {
          incoming.Add(f.Func);
          outgoing.Add(f.Func);
        } else if (node is NAryExpr n) {
          var appliable = n.Fun;
          if (appliable is UnaryOperator op) {
            Contract.Assert(op.Op == UnaryOperator.Opcode.Neg || op.Op == UnaryOperator.Opcode.Not);
            Contract.Assert(n.Args.Count() == 1);
            n.Args[0].pos = Expr.NegatePosition(n.Args[0].pos);
          } else if (appliable is BinaryOperator bin) {
            Contract.Assert(n.Args.Count() == 2);
            if (bin.Op == BinaryOperator.Opcode.And
                || bin.Op == BinaryOperator.Opcode.Or) {
            } else if (bin.Op == BinaryOperator.Opcode.Imp) {
              n.Args[0].pos = Expr.NegatePosition(n.Args[0].pos);
            } else {
              n.Args.ToList().ForEach(a => a.pos = Expr.Position.Neither);
            }
          } else {
            n.Args.ToList().ForEach(a => a.pos = Expr.Position.Neither);
          }
        } else if (node is BinderExpr be && be is QuantifierExpr qe) {
          Trigger start = qe.Triggers;
          while(start != null) {
            VisitTriggerCustom(start);
            start = start.Next;
          }
          var discardBodyIncoming = (qe is ForallExpr fa && fa.pos == Expr.Position.Pos && qe.Triggers != null)
                                    || qe is ExistsExpr ee && ee.pos == Expr.Position.Neg;
          be.Body.pos = Expr.Position.Neither;
          var incomingOld = new HashSet<Declaration>(incoming);
          VisitExpr(be.Body); // this will still edit the outgoing edges and types
          incoming = discardBodyIncoming ? incomingOld : incoming;
          return null;
        } else if (node is OldExpr o) {
          o.Expr.pos = Expr.Position.Neither;
        } else if (node is CodeExpr) {
          // no blocks in axioms
          Contract.Assert(false);
        } else if (node is BvExtractExpr bve) {
          bve.Bitvector.pos = Expr.Position.Neither;
        } else if (node is BvConcatExpr bvc) {
          bvc.E0.pos = Expr.Position.Neither;
          bvc.E1.pos = Expr.Position.Neither;
        } else if (node is BinderExpr bexp) {
          bexp.Body.pos = Expr.Position.Neither;
        } else if (node is LetExpr l){
          l.Body.pos = Expr.Position.Neither;
        } else {
          if(node is LiteralExpr || node is IdentifierExpr) {

          } else {
            Console.WriteLine(node);
            Contract.Assert(false);
          }
        }
        return base.VisitExpr(node);
      }

      public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type node)
      {
        types.Add(node);
        return base.VisitType(node);
      }
    }

    private class AssumeVisitor : ReadOnlyVisitor
    {
      public AssumeCmd ac;
      public HashSet<Variable> RelVars;

      public AssumeVisitor(AssumeCmd assumeCmd) : base(null)
      {
        this.ac = assumeCmd;
        this.RelVars = new HashSet<Variable>();
      }

      public override Variable VisitVariable(Variable v) {
        RelVars.Add(v);
        return base.VisitVariable(v);
      }
    }

    private class BlocksVisitor : DependencyEvaluator
    {
      public List<Block> Blocks;
      public HashSet<Variable> RelVars;

      public BlocksVisitor(List<Block> blocks) : base(null)
      {
        Blocks = blocks;
        RelVars = new HashSet<Variable>();
      }

      public override Variable VisitVariable(Variable v) {
        RelVars.Add(v);
        return base.VisitVariable(v);
      }

      public override Expr VisitExpr(Expr node)
      {
        if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c) {
          outgoing.Add(c);
        } else if (node is NAryExpr e && e.Fun is FunctionCall f) {
          outgoing.Add(f.Func);
        }
        return base.VisitExpr(node);
      }

      public override Cmd VisitAssumeCmd(AssumeCmd ac) {
        if (GetWhereVariable(ac) != null) {
          var cacheVars = new HashSet<Variable> (RelVars);
          var ex = base.VisitAssumeCmd(ac);
          this.RelVars = cacheVars;
          return ex;
        } else {
          return base.VisitAssumeCmd(ac);
        }
      }

      public override Microsoft.Boogie.Type VisitType(Microsoft.Boogie.Type node)
      {
        types.Add(node);
        return base.VisitType(node);
      }
    }

    private static bool ExcludeDep(Declaration d)
    {
      return d.Attributes != null &&
              QKeyValue.FindBoolAttribute(d.Attributes, "exclude_dep");
    }

    public static Dictionary<DependencyEvaluator, List<DependencyEvaluator>> InitializeEdges(Program p)
    {
      if (!CommandLineOptions.Clo.PruneFunctionsAndAxioms)
      {
        return null;
      }
      var nodes = p.Axioms.Select(ax => (DependencyEvaluator)new AxiomVisitor(ax)).ToList();
      nodes.ForEach(axv => ((AxiomVisitor)axv).Visit(axv.node));
      var functionNodes = p.Functions.Select(f => (DependencyEvaluator)new FunctionVisitor(f)).ToList();
      functionNodes.ForEach(fv => ((FunctionVisitor)fv).Visit(fv.node));
      nodes.AddRange(functionNodes);
      nodes.ForEach(u => u.incoming = u.incoming.Where(i => u.node == i || !ExcludeDep(i)).ToHashSet());
      nodes.ForEach(u => u.incoming.ToList().ForEach(f => Console.WriteLine(f)));
      nodes.ForEach(u => u.outgoing = u.outgoing.Where(i => !ExcludeDep(i)).ToHashSet());
      var edges = new Dictionary<DependencyEvaluator, List<DependencyEvaluator>>();
      nodes.ForEach(u => edges[u] = nodes.Where(v => DependencyEvaluator.depends(u, v)).ToList());
      return edges;
    }

    private static Variable GetWhereVariable(Cmd c) {
      if (c is AssumeCmd ac)
      {
        var attr = QKeyValue.FindAttribute(ac.Attributes, qkv => qkv.Key == "where" && qkv.Params.Count == 1);
        if (attr != null)
        {
          var ie = (IdentifierExpr) attr.Params[0];
          return ie.Decl;
        }
      }
      return null;
    }

    public static void TrimWhereAssumes(List<Block> blocks, HashSet<Variable> liveVars) {
      var whereAssumes = new Dictionary<Variable, AssumeVisitor> ();
      foreach (var blk in blocks)
      {
        foreach(var cmd in blk.Cmds)
        {
          var v = GetWhereVariable(cmd);
          if (v != null)
          {
            var ac = cmd as AssumeCmd;
            whereAssumes[v] = new AssumeVisitor(ac);
            whereAssumes[v].Visit(ac);
          }
        }
      }

      var todo = new Stack<Variable> (liveVars);
      while (todo.Any())
      {
        var t = todo.Pop();
        if (whereAssumes.Keys.Contains(t)) {
          whereAssumes[t].RelVars.Where(v => !liveVars.Contains(v)).ToList().ForEach(v => todo.Push(v));
        }
        liveVars.Add(t);
      }

      bool DeadWhereAssumption(Cmd c)
      {
        var v = GetWhereVariable(c);
        return v != null && !liveVars.Contains(v);
      }

      blocks.ForEach(blk => blk.Cmds = blk.Cmds.Where(c => !DeadWhereAssumption(c)).ToList());
    }

    public static IEnumerable<Declaration> PruneDecl(Program p, List<Block> blocks)
    {
      if (p.edges == null || blocks == null || !CommandLineOptions.Clo.PruneFunctionsAndAxioms)
      {
        return p.TopLevelDeclarations;
      }

      var edges = p.edges;
      // an implementation only has outgoing edges.
      BlocksVisitor bnode = new BlocksVisitor(blocks);
      bnode.Blocks.ForEach(blk => bnode.Visit(blk));
      TrimWhereAssumes(blocks, bnode.RelVars);
      var implHooks = edges.Keys.Where(m => DependencyEvaluator.depends(bnode, m));

      IEnumerable<Declaration> ComputeReachability (IEnumerable<DependencyEvaluator> implHooks)
      {
        var todo = new Stack<DependencyEvaluator>(implHooks);
        var visited = new HashSet<DependencyEvaluator>();
        while(todo.Any())
        {
          var d = todo.Pop();
          foreach (var x in edges[d].Where(t => !visited.Contains(t)))
          {
            todo.Push(x);
          }
          visited.Add(d);
        }
        return visited.Select(a => (Declaration) a.node);
      }

      var s = ComputeReachability(implHooks);
      bool PruneDecl(Declaration d)
      {
        return (d is Axiom || d is Function) && !s.Contains(d);
      }

      return p.TopLevelDeclarations.Where(d => !PruneDecl(d));
    }
  }
}