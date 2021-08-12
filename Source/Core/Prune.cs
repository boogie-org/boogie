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
          var discardBodyIncoming = qe is ForallExpr fa && fa.pos == Expr.Position.Pos
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

    private class ImplVisitor : DependencyEvaluator
    {
      public Implementation impl;

      public ImplVisitor(Implementation i) : base(null)
      {
        impl = i;
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
      nodes.ForEach(u => u.outgoing = u.outgoing.Where(i => !ExcludeDep(i)).ToHashSet());
      var edges = new Dictionary<DependencyEvaluator, List<DependencyEvaluator>>();
      nodes.ForEach(u => edges[u] = nodes.Where(v => DependencyEvaluator.depends(u, v)).ToList());
      return edges;
    }

    public static IEnumerable<Declaration> GetSuccinctDecl(Program p, Implementation impl)
    {
      if (p.edges == null || impl == null || !CommandLineOptions.Clo.PruneFunctionsAndAxioms)
      {
        return p.TopLevelDeclarations;
      }

      var edges = p.edges;
      // an implementation only has outgoing edges.
      DependencyEvaluator implNode = new ImplVisitor(impl);
      implNode.Visit(impl);
      var implHooks = edges.Keys.Where(m => DependencyEvaluator.depends(implNode, m));

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