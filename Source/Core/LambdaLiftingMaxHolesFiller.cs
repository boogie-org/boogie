using System.Collections.Generic;
using Microsoft.Boogie;

namespace Core {

/// <summary>
/// Traverses an expression, replacing all holes with bound variables taken from the <see cref="_replDummies"/>
/// queue.
/// </summary>
class LambdaLiftingMaxHolesFiller : StandardVisitor {
        private readonly List<Absy> _holes;
        private readonly QKeyValue _lambdaAttrs;
        private readonly Queue<Variable> _replDummies;

        private LambdaLiftingMaxHolesFiller(List<Absy> holes, IEnumerable<Variable> replDummies, QKeyValue lambdaAttrs) {
          _holes = holes;
          _lambdaAttrs = lambdaAttrs;
          _replDummies = new Queue<Variable>(replDummies);
        }

        public static Expr Fill(List<Absy> holes,
          List<Variable> replDummies,
          Expr expr, QKeyValue lambdaAttrs) {
          return new LambdaLiftingMaxHolesFiller(holes, replDummies, lambdaAttrs).VisitExpr(expr);
        }

        private bool ShouldBeReplaced(Absy node) {
          return _holes.Contains(node);
        }
        
        private bool GetReplacementVariable(Absy node, out Variable variable) {
          if (_replDummies.Count > 0 && ShouldBeReplaced(node)) {
            variable = _replDummies.Dequeue();
            return true;
          }
          variable = null;
          return false;
        }

        public override Expr VisitLambdaExpr(LambdaExpr node) {
          var attributes =_lambdaAttrs == null ? null : VisitQKeyValue(_lambdaAttrs);
          var body = VisitExpr(node.Body);
          return new LambdaExpr(node.tok, node.TypeParameters, node.Dummies, attributes, body);
        }

        public override Variable VisitVariable(Variable node) {
          if (GetReplacementVariable(new IdentifierExpr(node.tok, node), out var variable)) return variable;
          return base.VisitVariable(node);
        }

        public override Expr VisitExistsExpr(ExistsExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitExistsExpr(node);
        }

        public override Expr VisitForallExpr(ForallExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitForallExpr(node);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitIdentifierExpr(node);
        }

        public override Expr VisitLetExpr(LetExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitLetExpr(node);
        }

        public override Expr VisitLiteralExpr(LiteralExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitLiteralExpr(node);
        }

        public override Expr VisitNAryExpr(NAryExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitNAryExpr(node);
        }

        public override Expr VisitOldExpr(OldExpr node) {
          if (GetReplacementVariable(node, out var variable)) return new IdentifierExpr(variable.tok, variable);
          return base.VisitOldExpr(node);
        }
      }
}