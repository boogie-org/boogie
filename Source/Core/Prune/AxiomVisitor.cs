using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie
{
  internal class AxiomVisitor : DependencyEvaluator
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

    public override Boogie.Type VisitType(Boogie.Type node)
    {
      types.Add(node);
      return base.VisitType(node);
    }
  }
}