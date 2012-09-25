using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

using System.Diagnostics;

namespace GPUVerify
{
    class VariableDualiser : Duplicator
    {
      static internal HashSet<string> otherFunctionNames =
        new HashSet<string>(new string[] { "__other_bool", "__other_bv32", "__other_arrayId" });

        private int id;
        private UniformityAnalyser uniformityAnalyser;
        private string procName;

        public VariableDualiser(int id, UniformityAnalyser uniformityAnalyser, string procName)
        {
            Debug.Assert((uniformityAnalyser == null && procName == null)
                || (uniformityAnalyser != null && procName != null));

            this.id = id;
            this.uniformityAnalyser = uniformityAnalyser;
            this.procName = procName;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
          if (node.Decl is Formal) {
            return new IdentifierExpr(node.tok, new Formal(node.tok, DualiseTypedIdent(node.Decl),
              (node.Decl as Formal).InComing));
          }

          if (!(node.Decl is Constant))
          {
              return new IdentifierExpr(node.tok, new LocalVariable(node.tok, DualiseTypedIdent(node.Decl)));
          }

          if (GPUVerifier.IsThreadLocalIdConstant(node.Decl))
          {
              return new IdentifierExpr(node.tok, new Constant(node.tok, DualiseTypedIdent(node.Decl)));
          }

          if (GPUVerifier.IsGroupIdConstant(node.Decl))
          {
              return new IdentifierExpr(node.tok, new Constant(node.tok, DualiseTypedIdent(node.Decl)));
          }

          return node;
        }

        private TypedIdent DualiseTypedIdent(Variable v)
        {
          if (QKeyValue.FindBoolAttribute(v.Attributes, "global") ||
              QKeyValue.FindBoolAttribute(v.Attributes, "group_shared")) {
            return new TypedIdent(v.tok, v.Name, v.TypedIdent.Type);
          }

          if (uniformityAnalyser != null && uniformityAnalyser.IsUniform(procName, v.Name))
          {
            return new TypedIdent(v.tok, v.Name, v.TypedIdent.Type);
          }

          return new TypedIdent(v.tok, v.Name + "$" + id, v.TypedIdent.Type);

        }

        public override Variable VisitVariable(Variable node)
        {
            if (!(node is Constant) || GPUVerifier.IsThreadLocalIdConstant(node) ||
                GPUVerifier.IsGroupIdConstant(node))
            {
                node.TypedIdent = DualiseTypedIdent(node);
                node.Name = node.Name + "$" + id;
                return node;
            }

            return base.VisitVariable(node);
        }


        public override Expr VisitNAryExpr(NAryExpr node)
        {
          if (node.Fun is MapSelect) {
            Debug.Assert((node.Fun as MapSelect).Arity == 1);
            Debug.Assert(node.Args[0] is IdentifierExpr);
            var v = (node.Args[0] as IdentifierExpr).Decl;
            if (QKeyValue.FindBoolAttribute(v.Attributes, "group_shared")) {
              return new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                new ExprSeq(new Expr[] { new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), 
                  new ExprSeq(new Expr[] { node.Args[0], GPUVerifier.GroupSharedIndexingExpr(id) })), 
                  VisitExpr(node.Args[1]) }));
            }
          }

          if (node.Fun is FunctionCall)
          {
            FunctionCall call = node.Fun as FunctionCall;

            // Alternate dualisation for "other thread" functions
            if (otherFunctionNames.Contains(call.Func.Name))
            {
              Debug.Assert(id == 1 || id == 2);
              int otherId = id == 1 ? 2 : 1;
              return new VariableDualiser(otherId, uniformityAnalyser, procName).VisitExpr(
                  node.Args[0]);
            }

          }

          return base.VisitNAryExpr(node);
        }


        public override AssignLhs VisitMapAssignLhs(MapAssignLhs node) {

          var v = node.DeepAssignedVariable;
          if(QKeyValue.FindBoolAttribute(v.Attributes, "group_shared")) {
            return new MapAssignLhs(Token.NoToken, new MapAssignLhs(Token.NoToken, node.Map,
              new List<Expr>(new Expr[] { GPUVerifier.GroupSharedIndexingExpr(id) })), 
              node.Indexes.Select(idx => this.VisitExpr(idx)).ToList());

          }
          return base.VisitMapAssignLhs(node);
        }

    }

}
