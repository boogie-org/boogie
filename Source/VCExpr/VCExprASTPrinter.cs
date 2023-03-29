using System.IO;
using System.Collections;
using System.Diagnostics.Contracts;

// A simple visitor for turning a VCExpr into a human-readable string
// (S-expr syntax)

namespace Microsoft.Boogie.VCExprAST {
  public class VCExprPrinter : IVCExprVisitor<bool, TextWriter /*!*/> {
    private VCExprOpPrinter OpPrinterVar = null;
    public PrintOptions Options { get; }

    public VCExprPrinter(PrintOptions options) {
      Options = options;
    }

    private VCExprOpPrinter /*!*/ OpPrinter {
      get {
        Contract.Ensures(Contract.Result<VCExprOpPrinter>() != null);

        if (OpPrinterVar == null) {
          OpPrinterVar = new VCExprOpPrinter(this);
        }

        return OpPrinterVar;
      }
    }

    public void Print(VCExpr expr, TextWriter wr) {
      Contract.Requires(wr != null);
      Contract.Requires(expr != null);
      expr.Accept<bool, TextWriter /*!*/>(this, wr);
    }

    public bool Visit(VCExprLiteral node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      if (node == VCExpressionGenerator.True) {
        wr.Write("true");
      } else if (node == VCExpressionGenerator.False) {
        wr.Write("false");
      } else if (node is VCExprIntLit) {
        wr.Write(((VCExprIntLit)node).Val);
      } else if (node is VCExprStringLit stringLit) {
        wr.Write(stringLit.Val);
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }

      return true;
    }

    public DynamicStack<bool> Visit(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      VCExprOp /*!*/
        op = node.Op;
      Contract.Assert(op != null);

      if (op.Equals(VCExpressionGenerator.AndOp) ||
          op.Equals(VCExpressionGenerator.OrOp)) {
        // handle these operators without recursion

        wr.Write("({0}",
          op.Equals(VCExpressionGenerator.AndOp) ? "And" : "Or");
        IEnumerator /*!*/
          enumerator = new VCExprNAryUniformOpEnumerator(node);
        Contract.Assert(enumerator != null);
        while (enumerator.MoveNext()) {
          VCExprNAry naryExpr = enumerator.Current as VCExprNAry;
          if (naryExpr == null || !naryExpr.Op.Equals(op)) {
            wr.Write(" ");
            Print(cce.NonNull((VCExpr /*!*/)enumerator.Current), wr);
          }
        }

        wr.Write(")");

        return DynamicStack.FromResult(true);
      }

      return node.Accept<bool, TextWriter /*!*/>(OpPrinter, wr);
    }

    public bool Visit(VCExprVar node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      wr.Write(node.Name);
      return true;
    }

    public DynamicStack<bool> Visit(VCExprQuantifier node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      string /*!*/
        quan = node.Quan == Quantifier.ALL ? "Forall" : "Exists";
      Contract.Assert(quan != null);

      wr.Write("({0} ", quan);

      if (node.TypeParameters.Count > 0) {
        wr.Write("<");
        string /*!*/
          sep = "";
        foreach (TypeVariable /*!*/ v in node.TypeParameters) {
          Contract.Assert(v != null);
          wr.Write(sep);
          sep = ", ";
          wr.Write("{0}", v.Name);
        }

        wr.Write("> ");
      }

      if (node.BoundVars.Count > 0) {
        string /*!*/
          sep = "";
        foreach (VCExprVar /*!*/ v in node.BoundVars) {
          Contract.Assert(v != null);
          wr.Write(sep);
          sep = ", ";
          Print(v, wr);
        }

        wr.Write(" ");
      }

      wr.Write(":: ");

      if (node.Triggers.Count > 0) {
        wr.Write("{0} ", "{");
        string /*!*/
          sep = "";
        foreach (VCTrigger /*!*/ t in node.Triggers) {
          Contract.Assert(t != null);
          wr.Write(sep);
          sep = ", ";
          string /*!*/
            sep2 = "";
          foreach (VCExpr /*!*/ e in t.Exprs) {
            Contract.Assert(e != null);
            wr.Write(sep2);
            sep2 = "+";
            Print(e, wr);
          }
        }

        wr.Write(" {0} ", "}");
      }

      Print(node.Body, wr);
      wr.Write(")");
      return DynamicStack.FromResult(true);
    }

    public DynamicStack<bool> Visit(VCExprLet node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      wr.Write("(Let ");

      string /*!*/
        sep = "";
      foreach (VCExprLetBinding /*!*/ b in node) {
        Contract.Assert(b != null);
        wr.Write(sep);
        sep = ", ";
        Print(b.V, wr);
        wr.Write(" = ");
        Print(b.E, wr);
      }

      wr.Write(" ");

      Print(node.Body, wr);
      wr.Write(")");
      return DynamicStack.FromResult(true);
    }
  }

  public class VCExprOpPrinter : IVCExprOpVisitor<bool, TextWriter /*!*/> {
    private VCExprPrinter /*!*/ ExprPrinter;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(ExprPrinter != null);
    }


    public VCExprOpPrinter(VCExprPrinter exprPrinter) {
      Contract.Requires(exprPrinter != null);
      this.ExprPrinter = exprPrinter;
    }

    private DynamicStack<bool> PrintNAry(string op, VCExprNAry node, TextWriter wr) {
      Contract.Requires(wr != null);
      Contract.Requires(node != null);
      Contract.Requires(op != null);
      wr.Write("({0}", op);
      foreach (VCExpr /*!*/ arg in node.Arguments) {
        Contract.Assert(arg != null);
        wr.Write(" ");
        ExprPrinter.Print(arg, wr);
      }

      wr.Write(")");
      return DynamicStack.FromResult(true);
    }

    public DynamicStack<bool> VisitNotOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("!", node, wr);
    }

    public DynamicStack<bool> VisitEqOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("==", node, wr);
    }

    public DynamicStack<bool> VisitNeqOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("!=", node, wr);
    }

    public DynamicStack<bool> VisitAndOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    public DynamicStack<bool> VisitOrOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    public DynamicStack<bool> VisitImpliesOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("Implies", node, wr);
    }

    public DynamicStack<bool> VisitDistinctOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("Distinct", node, wr);
    }

    public DynamicStack<bool> VisitFieldAccessOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("FieldAccess", node, wr);
    }

    public DynamicStack<bool> VisitIsConstructorOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("IsConstructor", node, wr);
    }

    public DynamicStack<bool> VisitSelectOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("Select", node, wr);
    }

    public DynamicStack<bool> VisitStoreOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("Store", node, wr);
    }

    public DynamicStack<bool> VisitFloatAddOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.add", node, wr);
    }

    public DynamicStack<bool> VisitFloatSubOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.sub", node, wr);
    }

    public DynamicStack<bool> VisitFloatMulOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.mul", node, wr);
    }

    public DynamicStack<bool> VisitFloatDivOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.div", node, wr);
    }

    public DynamicStack<bool> VisitFloatLeqOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.leq", node, wr);
    }

    public DynamicStack<bool> VisitFloatLtOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.lt", node, wr);
    }

    public DynamicStack<bool> VisitFloatGeqOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.geq", node, wr);
    }

    public DynamicStack<bool> VisitFloatGtOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.gt", node, wr);
    }

    public DynamicStack<bool> VisitFloatEqOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("fp.eq", node, wr);
    }

    public async DynamicStack<bool> VisitFloatNeqOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      bool toReturn = await PrintNAry("not (fp.eq", node, wr);
      wr.Write(")"); // A bit hacky, but it works
      return toReturn;
    }

    public DynamicStack<bool> VisitBvOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("Bv", node, wr);
    }

    public DynamicStack<bool> VisitBvExtractOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("BvExtract", node, wr);
    }

    public DynamicStack<bool> VisitBvConcatOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("BvConcat", node, wr);
    }

    public DynamicStack<bool> VisitIfThenElseOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("if-then-else", node, wr);
    }

    public DynamicStack<bool> VisitCustomOp(VCExprNAry node /*!*/, TextWriter wr /*!*/) {
      //Contract.Requires(node!=null);
      //Contract.Requires(wr != null);
      VCExprCustomOp op = (VCExprCustomOp)node.Op;
      return PrintNAry(op.Name, node, wr);
    }

    public DynamicStack<bool> VisitAddOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      if (ExprPrinter.Options.ReflectAdd) {
        return PrintNAry("Reflect$Add", node, wr);
      } else {
        return PrintNAry("+", node, wr);
      }
    }

    public DynamicStack<bool> VisitSubOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("-", node, wr);
    }

    public DynamicStack<bool> VisitMulOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("*", node, wr);
    }

    public DynamicStack<bool> VisitDivOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("div", node, wr);
    }

    public DynamicStack<bool> VisitModOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("mod", node, wr);
    }

    public DynamicStack<bool> VisitRealDivOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("/", node, wr);
    }

    public DynamicStack<bool> VisitPowOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("**", node, wr);
    }

    public DynamicStack<bool> VisitLtOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("<", node, wr);
    }

    public DynamicStack<bool> VisitLeOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("<=", node, wr);
    }

    public DynamicStack<bool> VisitGtOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry(">", node, wr);
    }

    public DynamicStack<bool> VisitGeOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry(">=", node, wr);
    }

    public DynamicStack<bool> VisitSubtypeOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("<:", node, wr);
    }

    public DynamicStack<bool> VisitSubtype3Op(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("<::", node, wr);
    }

    public DynamicStack<bool> VisitToIntOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("int", node, wr);
    }

    public DynamicStack<bool> VisitToRealOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      return PrintNAry("real", node, wr);
    }

    public DynamicStack<bool> VisitBoogieFunctionOp(VCExprNAry node, TextWriter wr) {
      //Contract.Requires(wr != null);
      //Contract.Requires(node != null);
      VCExprBoogieFunctionOp /*!*/
        op = (VCExprBoogieFunctionOp)node.Op;
      Contract.Assert(op != null);
      return PrintNAry(op.Func.Name, node, wr);
    }
  }
}