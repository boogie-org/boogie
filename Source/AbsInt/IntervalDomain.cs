using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;

namespace Microsoft.Boogie.AbstractInterpretation
{
  class NativeIntervallDomain : NativeLattice
  {
    abstract class E_Common : NativeLattice.Element { }
    class E_Bottom : E_Common
    {
      public override Expr ToExpr() {
        return Expr.False;
      }
    }
    class E : E_Common
    {
      public readonly Node N;
      public E() { }
      public E(Node n) {
        N = n;
      }

      public override Expr ToExpr() {
        Expr expr = Expr.True;
        for (var n = N; n != null; n = n.Next) {
          expr = BplAnd(expr, n.ToExpr());
        }
        return expr;
      }
    }
    public class Node
    {
      public readonly Variable V;  // variable has type bool or int
      // For an integer variable (Lo,Hi) indicates Lo <= V < Hi, where Lo==null means no lower bound and Hi==null means no upper bound.
      // For a real variable (Lo,Hi) indicates Lo <= V <= Hi, where Lo==null means no lower bound and Hi==null means no upper bound.
      // For a boolean variable, (Lo,Hi) is one of: (null,null) for {false,true}, (null,1) for {false}, and (1,null) for {true}.
      public readonly BigInteger? Lo;
      public readonly BigInteger? Hi;
      public Node Next;  // always sorted according to StrictlyBefore; readonly after full initialization
      [Pure]
      public static bool StrictlyBefore(Variable a, Variable b) {
        Contract.Assert(a.UniqueId != b.UniqueId || a == b);
        return a.UniqueId < b.UniqueId;
      }

      Node(Variable v, BigInteger? lo, BigInteger? hi, Node next) {
        Contract.Requires(lo != null || hi != null);  // don't accept empty constraints
        Contract.Requires(next == null || StrictlyBefore(v, next.V));
        V = v;
        Lo = lo;
        Hi = hi;
        Next = next;
      }

      /// <summary>
      /// This constructor leaves Next as null, allowing the caller to fill in Next to finish off the construction.
      /// </summary>
      public Node(Variable v, BigInteger? lo, BigInteger? hi) {
        Contract.Requires(lo != null || hi != null);  // don't accept empty constraints
        V = v;
        Lo = lo;
        Hi = hi;
      }

      /// <summary>
      /// Returns a Node that has the constraints head.{V,Lo,Hi} plus
      /// all the constraints entailed by Nodes reachable from tail.
      /// Requires that "head" sorts no later than anything in "tail".
      /// Create either returns "head" itself or returns a new Node.
      /// </summary>
      public static Node Create(Node head, Node tail) {
        Contract.Requires(head != null);
        Contract.Requires(tail == null || !StrictlyBefore(tail.V, head.V));
        Contract.Requires(head != tail);

        if (head.Next == tail) {
          return head;
        } else if (tail != null && head.V == tail.V) {
          // incorporate both constraints into one Node
          return new Node(head.V, Max(head.Lo, tail.Lo, true), Min(head.Lo, tail.Lo, true), tail.Next);
        } else {
          return new Node(head.V, head.Lo, head.Hi, tail);
        }
      }

      public static void GetBounds(Node n, Variable v, out BigInteger? lo, out BigInteger? hi) {
        for (; n != null; n = n.Next) {
          if (n.V == v) {
            lo = n.Lo;
            hi = n.Hi;
            return;
          } else if (StrictlyBefore(v, n.V)) {
            break;
          }
        }
        lo = null;
        hi = null;
      }

      /// <summary>
      /// Return the minimum of "a" and "b".  If treatNullAsUnit==true, then "null" is
      /// interpreted as positive infinity (the unit element of min); otherwise, it is
      /// treated as negative infinity (the zero element of min).
      /// </summary>
      public static BigInteger? Min(BigInteger? a, BigInteger? b, bool treatNullAsUnit) {
        if (a == null) {
          return treatNullAsUnit ? b : a;
        } else if (b == null) {
          return treatNullAsUnit ? a : b;
        } else {
          return BigInteger.Min((BigInteger)a, (BigInteger)b);
        }
      }

      /// <summary>
      /// Return the maximum of "a" and "b".  If treatNullAsUnit==true, then "null" is
      /// interpreted as negative infinity (the unit element of max); otherwise, it is
      /// treated as positive infinity (the zero element of max).
      /// </summary>
      public static BigInteger? Max(BigInteger? a, BigInteger? b, bool treatNullAsUnit) {
        if (a == null) {
          return treatNullAsUnit ? b : a;
        } else if (b == null) {
          return treatNullAsUnit ? a : b;
        } else {
          return BigInteger.Max((BigInteger)a, (BigInteger)b);
        }
      }

      public static IEnumerable<Tuple<Node, Node>> Merge(Node a, Node b) {
        while (true) {
          if (a == null && b == null) {
            yield break;
          } else if (a == null || b == null) {
            yield return new Tuple<Node, Node>(a, b);
            if (a != null) { a = a.Next; } else { b = b.Next; }
          } else if (a.V == b.V) {
            yield return new Tuple<Node, Node>(a, b);
            a = a.Next; b = b.Next;
          } else if (StrictlyBefore(a.V, b.V)) {
            yield return new Tuple<Node, Node>(a, null);
            a = a.Next;
          } else {
            yield return new Tuple<Node, Node>(null, b);
            b = b.Next;
          }
        }
      }

      public Expr ToExpr() {
        if (!V.IsMutable && CommandLineOptions.Clo.InstrumentInfer != CommandLineOptions.InstrumentationPlaces.Everywhere) {
          // omit invariants about readonly variables
          return Expr.True;
        } else if (V.TypedIdent.Type.IsBool) {
          if (Lo == null && Hi == null) {
            return Expr.True;
          } else {
            Contract.Assert((Lo == null && (BigInteger)Hi == 1) || (Hi == null && (BigInteger)Lo == 1));
            var ide = new IdentifierExpr(Token.NoToken, V);
            return Hi == null ? ide : Expr.Not(ide);
          }
        } else if (V.TypedIdent.Type.IsInt) {
          Expr e = Expr.True;
          if (Lo != null && Hi != null && Lo + 1 == Hi) {
            // produce an equality
            var ide = new IdentifierExpr(Token.NoToken, V);
            e = Expr.And(e, BplEq(ide, NumberToExpr((BigInteger)Lo, V.TypedIdent.Type)));
          } else {
            // produce a (possibly empty) conjunction of inequalities
            if (Lo != null) {
              var ide = new IdentifierExpr(Token.NoToken, V);
              e = Expr.And(e, BplLe(NumberToExpr((BigInteger)Lo, V.TypedIdent.Type), ide));
            }
            if (Hi != null) {
              var ide = new IdentifierExpr(Token.NoToken, V);
              e = Expr.And(e, BplLt(ide, NumberToExpr((BigInteger)Hi, V.TypedIdent.Type)));
            }
          }
          return e;
        } else if (V.TypedIdent.Type.IsReal){
          Expr e = Expr.True;
          if (Lo != null && Hi != null && Lo == Hi) {
            // produce an equality
            var ide = new IdentifierExpr(Token.NoToken, V);
            e = Expr.And(e, BplEq(ide, NumberToExpr((BigInteger)Lo, V.TypedIdent.Type)));
          } else {
            // produce a (possibly empty) conjunction of inequalities
            if (Lo != null) {
              var ide = new IdentifierExpr(Token.NoToken, V);
              e = Expr.And(e, BplLe(NumberToExpr((BigInteger)Lo, V.TypedIdent.Type), ide));
            }
            if (Hi != null) {
              var ide = new IdentifierExpr(Token.NoToken, V);
              e = Expr.And(e, BplLe(ide, NumberToExpr((BigInteger)Hi, V.TypedIdent.Type)));
            }
          }
          return e;
        } else {
          Contract.Assert(V.TypedIdent.Type.IsFloat);
          Expr e = Expr.True;
          if (Lo != null && Hi != null && Lo == Hi)
          {
            // produce an equality
            var ide = new IdentifierExpr(Token.NoToken, V);
            e = Expr.And(e, BplEq(ide, NumberToExpr((BigInteger)Lo, V.TypedIdent.Type)));
          }
          else
          {
            // produce a (possibly empty) conjunction of inequalities
            if (Lo != null)
            {
              var ide = new IdentifierExpr(Token.NoToken, V);
              e = Expr.And(e, BplLe(NumberToExpr((BigInteger)Lo, V.TypedIdent.Type), ide));
            }
            if (Hi != null)
            {
              var ide = new IdentifierExpr(Token.NoToken, V);
              e = Expr.And(e, BplLe(ide, NumberToExpr((BigInteger)Hi, V.TypedIdent.Type)));
            }
          }
          return e;
        }
      }
    }

    static Expr NumberToExpr(BigInteger n, Type ty) {
      if (n == null) {
        return null;
      } else if (ty.IsReal) {
        return Expr.Literal(Basetypes.BigDec.FromBigInt(n));
      } else if (ty.IsFloat) {
        return Expr.Literal(Basetypes.BigFloat.FromBigInt(n, ty.FloatExponent, ty.FloatSignificand));
      } else {
        Contract.Assume(ty.IsInt);
        return Expr.Literal(Basetypes.BigNum.FromBigInt(n));
      }
    }

    List<BigInteger> upThresholds;  // invariant: thresholds are sorted
    List<BigInteger> downThresholds;  // invariant: thresholds are sorted

    /// <summary>
    /// Requires "thresholds" to be sorted.
    /// </summary>
    public NativeIntervallDomain() {
      upThresholds = new List<BigInteger>();
      downThresholds = new List<BigInteger>();
    }

    public override void Specialize(Implementation impl) {
      if (impl == null) {
        // remove thresholds
        upThresholds = new List<BigInteger>();
        downThresholds = new List<BigInteger>();
      } else {
        var tf = new ThresholdFinder(impl);
        tf.Find(out downThresholds, out upThresholds);
#if DEBUG_PRINT
        Console.Write("DEBUG: for implementation '{0}', setting downs to [", impl.Name);
        foreach (var i in downThresholds) {
          Console.Write(" {0}", i);
        }
        Console.Write(" ] and ups to [");
        foreach (var i in upThresholds) {
          Console.Write(" {0}", i);
        }
        Console.WriteLine(" ]");
#endif
      }
      base.Specialize(impl);
    }

    private E_Common top = new E();
    private E_Common bottom = new E_Bottom();

    public override Element Top { get { return top; } }
    public override Element Bottom { get { return bottom; } }

    public override bool IsTop(Element element) {
      var e = element as E;
      return e != null && e.N == null;
    }
    public override bool IsBottom(Element element) {
      return element is E_Bottom;
    }

    public override bool Below(Element a, Element b) {
      if (a is E_Bottom) {
        return true;
      } else if (b is E_Bottom) {
        return false;
      } else {
        var aa = (E)a;
        var bb = (E)b;
        // check if every constraint in 'bb' is implied by constraints in 'aa'
        foreach (var t in Node.Merge(aa.N, bb.N)) {
          var x = t.Item1;
          var y = t.Item2;
          if (x == null) {
            // bb constrains a variable that aa does not
            return false;
          } else if (y == null) {
            // aa constrains a variable that bb does not; that's fine
          } else if (y.Lo != null && (x.Lo == null || x.Lo < y.Lo)) {
            // bb has a Lo constraint, and either aa has no Lo constraint or it has a weaker Lo constraint
            return false;
          } else if (y.Hi != null && (x.Hi == null || y.Hi < x.Hi)) {
            // bb has a Hi o constraint, and either aa has no Hi constraint or it has a weaker Hi constraint
            return false;
          }
        }
        return true;
      }
    }

    public override Element Meet(Element a, Element b) {
      if (a is E_Bottom) {
        return a;
      } else if (b is E_Bottom) {
        return b;
      } else {
        var aa = (E)a;
        var bb = (E)b;
        Node head = null;
        Node prev = null;
        foreach (var t in Node.Merge(aa.N, bb.N)) {
          var x = t.Item1;
          var y = t.Item2;
          Node n;
          if (x == null) {
            n = new Node(y.V, y.Lo, y.Hi);
          } else if (y == null) {
            n = new Node(x.V, x.Lo, x.Hi);
          } else {
            var lo = Node.Max(x.Lo, y.Lo, true);
            var hi = Node.Min(x.Hi, y.Hi, true);
            // if hi<=lo (or hi<lo for reals), then we're overconstrained
            if (lo != null && hi != null && (x.V.TypedIdent.Type.IsReal ? hi < lo : hi <= lo)) {
              return bottom;
            }
            n = new Node(x.V, lo, hi);
          }
          if (head == null) {
            head = n;
          } else {
            prev.Next = n;
          }
          prev = n;
        }
        return new E(head);
      }
    }

    public override Element Join(Element a, Element b) {
      if (a is E_Bottom) {
        return b;
      } else if (b is E_Bottom) {
        return a;
      } else {
        var aa = (E)a;
        var bb = (E)b;
        // for each variable, take the weaker of the constraints
        Node head = null;
        Node prev = null;
        foreach (var t in Node.Merge(aa.N, bb.N)) {
          if (t.Item1 != null && t.Item2 != null) {
            var lo = Node.Min(t.Item1.Lo, t.Item2.Lo, false);
            var hi = Node.Max(t.Item1.Hi, t.Item2.Hi, false);
            if (lo != null || hi != null) {
              var n = new Node(t.Item1.V, lo, hi);
              if (head == null) {
                head = n;
              } else {
                prev.Next = n;
              }
              prev = n;
            }
          }
        }
        return new E(head);
      }
    }

    public override Element Widen(Element a, Element b) {
      if (a is E_Bottom) {
        return b;  // since this is done just once, we maintain the ascending chains property
      } else if (b is E_Bottom) {
        return a;
      } else {
        var aa = (E)a;
        var bb = (E)b;
        // return a subset of the constraints of aa, namely those that are implied by bb
        Node head = null;
        Node prev = null;
        foreach (var t in Node.Merge(aa.N, bb.N)) {
          var x = t.Item1;
          var y = t.Item2;
          if (x != null && y != null) {
            BigInteger? lo, hi;
            lo = hi = null;
            if (x.Lo != null && y.Lo != null) {
              if (x.Lo <= y.Lo) {
                // okay, we keep the lower bound
                lo = x.Lo;
              } else {
                // set "lo" to the threshold that is below (or equal) y.Lo
                lo = RoundDown((BigInteger)y.Lo);
              }
            }
            if (x.Hi != null && y.Hi != null) {
              if (y.Hi <= x.Hi) {
                // okay, we keep the upper bound
                hi = x.Hi;
              } else {
                // set "hi" to the threshold that is above (or equal) y.Hi
                hi = RoundUp((BigInteger)y.Hi);
              }
            }
            if (lo != null || hi != null) {
              var n = new Node(x.V, lo, hi);
              if (head == null) {
                head = n;
              } else {
                prev.Next = n;
              }
              prev = n;
            }
          }
        }
        return new E(head);
      }
    }

    /// <summary>
    /// For a proof of correctness of this method, see Test/dafny2/Intervals.dfy.
    /// A difference is that the this method returns:
    ///     let d = Dafny_RoundDown(k);
    ///     return d == -1 ? null : downThresholds[d];
    /// </summary>
    BigInteger? RoundDown(BigInteger k)
    {
      if (downThresholds.Count == 0 || k < downThresholds[0]) {
        return null;
      }
      var i = 0;
      var j = downThresholds.Count - 1;
      while (i < j)
      {
        var mid = i + (j - i + 1) / 2;
        if (downThresholds[mid] <= k) {
          i = mid;
        } else {
          j = mid - 1;
        }
      }
      return downThresholds[i];
    }

    /// <summary>
    /// For a proof of correctness of this method, see Test/dafny2/Intervals.dfy.
    /// A difference is that the this method returns:
    ///     let d = Dafny_RoundUp(k);
    ///     return d == thresholds.Count ? null : upThresholds[d];
    /// </summary>
    BigInteger? RoundUp(BigInteger k)
    {
      if (upThresholds.Count == 0 || upThresholds[upThresholds.Count - 1] < k) {
        return null;
      }
      var i = 0;
      var j = upThresholds.Count - 1;
      while (i < j)
      {
        var mid = i + (j - i) / 2;
        if (upThresholds[mid] < k) {
          i = mid + 1;
        } else {
          j = mid;
        }
      }
      return upThresholds[i];
    }

    public override Element Constrain(Element element, Expr expr) {
      if (element is E_Bottom) {
        return element;
      } else {
        var e = (E)element;
        var c = Constraint(expr, e.N);
        return c == null ? element : Meet(element, c);
      }
    }

    /// <summary>
    /// Returns an Element that corresponds to the constraints implied by "expr" in the
    /// state "state".
    /// Return "null" to indicate no constraints.
    /// </summary>
    E_Common Constraint(Expr expr, Node state) {
      Variable v;
      if (IsVariable(expr, out v)) {
        var n = new Node(v, BigInteger.One, null);
        return new E(n);
      } else if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        return (bool)e.Val ? null : new E_Bottom();
      } else if (expr is NAryExpr) {
        var e = (NAryExpr)expr;
        if (e.Fun is UnaryOperator) {
          if (((UnaryOperator)e.Fun).Op == UnaryOperator.Opcode.Not) {
            if (IsVariable(e.Args[0], out v)) {
              var n = new Node(v, null, BigInteger.One);
              return new E(n);
            }
          }
        } else if (e.Fun is BinaryOperator) {
          var op = ((BinaryOperator)e.Fun).Op;
          var arg0 = e.Args[0];
          var arg1 = e.Args[1];
          switch (op) {
            case BinaryOperator.Opcode.Eq:
            case BinaryOperator.Opcode.Iff: {
                E_Common c = null;
                if (IsVariable(arg0, out v)) {
                  BigInteger? lo, hi;
                  if (PartiallyEvaluate(arg1, state, out lo, out hi)) {
                    var n = new Node(v, lo, hi);
                    c = new E(n);
                  }
                }
                if (IsVariable(arg1, out v)) {
                  BigInteger? lo, hi;
                  if (PartiallyEvaluate(arg1, state, out lo, out hi)) {
                    var n = new Node(v, lo, hi);
                    c = c == null ? new E(n) : (E_Common)Meet(c, new E(n));
                  }
                }
                return c;
              }
            case BinaryOperator.Opcode.Neq: {
              E_Common c = null;
                if (IsVariable(arg0, out v)) {
                  c = ConstrainNeq(state, v, arg1);
                }
                if (IsVariable(arg1, out v)) {
                  var cc = ConstrainNeq(state, v, arg0);
                  if (cc != null) {
                    c = c == null ? cc : (E_Common)Meet(c, cc);
                  }
                }
                return c;
              }
            case BinaryOperator.Opcode.Le: {
                E_Common c = null;
                if (IsVariable(arg1, out v)) {
                  BigInteger? lo, hi;
                  PartiallyEvaluate(arg0, state, out lo, out hi);
                  if (lo != null) {
                    var n = new Node(v, lo, null);
                    c = new E(n);
                  }
                }
                if (IsVariable(arg0, out v)) {
                  BigInteger? lo, hi;
                  PartiallyEvaluate(arg1, state, out lo, out hi);
                  if (hi != null) {
                    var n = new Node(v, null, hi);
                    c = c == null ? new E(n) : (E_Common)Meet(c, new E(n));
                  }
                }
                return c;
              }
            case BinaryOperator.Opcode.Lt: {
              E_Common c = null;
                if (IsVariable(arg1, out v)) {
                  BigInteger? lo, hi;
                  PartiallyEvaluate(arg0, state, out lo, out hi);
                  if (lo != null) {
                    var n = new Node(v, v.TypedIdent.Type.IsReal ? lo : lo + 1, null);
                    c = new E(n);
                  }
                }
                if (IsVariable(arg0, out v)) {
                  BigInteger? lo, hi;
                  PartiallyEvaluate(arg1, state, out lo, out hi);
                  if (hi != null) {
                    var n = new Node(v, null, v.TypedIdent.Type.IsReal ? hi : hi - 1);
                    c = c == null ? new E(n) : (E_Common)Meet(c, new E(n));
                  }
                }
                return c;
              }
            case BinaryOperator.Opcode.Ge: {
                var tmp = arg0; arg0 = arg1; arg1 = tmp;
                goto case BinaryOperator.Opcode.Le;
              }
            case BinaryOperator.Opcode.Gt: {
                var tmp = arg0; arg0 = arg1; arg1 = tmp;
                goto case BinaryOperator.Opcode.Lt;
              }
            default:
              break;
          }
        }
      }
      return null;  // approximation
    }

    private E ConstrainNeq(Node state, Variable v, Expr arg) {
      BigInteger? lo, hi;
      if (PartiallyEvaluate(arg, state, out lo, out hi)) {
        if (!v.TypedIdent.Type.IsReal && lo != null && hi != null && lo + 1 == hi) {
          var exclude = lo;
          // If the partially evaluated arg (whose value is "exclude") is an end-point of
          // the interval known for "v", then produce a constraint that excludes that bound.
          Node.GetBounds(state, v, out lo, out hi);
          if (lo != null && lo == exclude) {
            var n = new Node(v, lo + 1, null);
            return new E(n);
          } else if (hi != null && exclude + 1 == hi) {
            var n = new Node(v, null, exclude);
            return new E(n);
          }
        }
      }
      return null;
    }

    bool IsVariable(Expr expr, out Variable v) {
      var e = expr as IdentifierExpr;
      if (e == null) {
        v = null;
        return false;
      } else {
        v = e.Decl;
        return true;
      }
    }

    public override Element Update(Element element, AssignCmd cmd) {
      if (element is E_Bottom) {
        return element;
      }
      var e = (E)element;
      var nn = e.N;
      Contract.Assert(cmd.Lhss.Count == cmd.Rhss.Count);
      for (int i = 0; i < cmd.Lhss.Count; i++) {
        var lhs = cmd.Lhss[i];
        var rhs = cmd.Rhss[i];
        BigInteger? lo;
        BigInteger? hi;
        PartiallyEvaluate(rhs, e.N, out lo, out hi);
        nn = UpdateOne(nn, lhs.DeepAssignedVariable, lo, hi);
      }
      return new E(nn);
    }

    bool PartiallyEvaluate(Expr rhs, Node node, out BigInteger? lo, out BigInteger? hi) {
      var pe = new PEVisitor(node);
      pe.VisitExpr(rhs);
      lo = pe.Lo;
      hi = pe.Hi;
      return lo != null || hi != null;
    }

    class PEVisitor : ReadOnlyVisitor
    {
      public BigInteger? Lo;
      public BigInteger? Hi;

      readonly BigInteger one = BigInteger.One;

      Node N;
      public PEVisitor(Node n) {
        N = n;
      }

      // Override visitors for all expressions that can return a boolean, integer, or real result

      public override Expr VisitExpr(Expr node) {
        Lo = Hi = null;
        return base.VisitExpr(node);
      }
      public override Expr VisitLiteralExpr(LiteralExpr node) {
        if (node.Val is BigNum) {
          var n = ((BigNum)node.Val).ToBigInteger;
          Lo = n;
          Hi = n + 1;
        } else if (node.Val is BigDec) {
          BigInteger floor, ceiling;
          ((BigDec)node.Val).FloorCeiling(out floor, out ceiling);
          Lo = floor;
          Hi = ceiling;
        } else if (node.Val is BigFloat) {
          BigInteger floor, ceiling;
          ((BigFloat)node.Val).FloorCeiling(out floor, out ceiling);
          Lo = floor;
          Hi = ceiling;
        } else if (node.Val is bool) {
          if ((bool)node.Val) {
            // true
            Lo = one;
            Hi = null;
          } else {
            // false
            Lo = null;
            Hi = one;
          }
        }
        return node;
      }
      public override Expr VisitIdentifierExpr(IdentifierExpr node) {
        if (node.Type.IsBool || node.Type.IsInt || node.Type.IsReal) {
          Node.GetBounds(N, node.Decl, out Lo, out Hi);
        }
        return node;
      }
      public override Expr VisitNAryExpr(NAryExpr node) {
        if (node.Fun is UnaryOperator) {
          var op = (UnaryOperator)node.Fun;
          Contract.Assert(node.Args.Count == 1);
          if (op.Op == UnaryOperator.Opcode.Neg) {
            BigInteger? lo, hi;
            VisitExpr(node.Args[0]);
            lo = Lo; hi = Hi;
            if (hi != null) {
              Lo = node.Type.IsReal ? -hi : 1 - hi;
            } else {
              Lo = null;
            }
            if (lo != null) {
              Hi = node.Type.IsReal ? -lo : 1 - lo;
            } else {
              Hi = null;
            }
          }
          else if (op.Op == UnaryOperator.Opcode.Not) {
            VisitExpr(node.Args[0]);
            Contract.Assert((Lo == null && Hi == null) ||
              (Lo == null && (BigInteger)Hi == 1) ||
              (Hi == null && (BigInteger)Lo == 1));
            var tmp = Lo;
            Lo = Hi;
            Hi = tmp;
          }
        } else if (node.Fun is BinaryOperator) {
          var op = (BinaryOperator)node.Fun;
          Contract.Assert(node.Args.Count == 2);
          BigInteger? lo0, hi0, lo1, hi1;
          VisitExpr(node.Args[0]);
          lo0 = Lo; hi0 = Hi;
          VisitExpr(node.Args[1]);
          lo1 = Lo; hi1 = Hi;
          Lo = Hi = null;
          var isReal = node.Args[0].Type.IsReal;
          switch (op.Op) {
            case BinaryOperator.Opcode.And:
              if (hi0 != null || hi1 != null) {
                // one operand is definitely false, thus so is the result
                Lo = null; Hi = one;
              } else if (lo0 != null && lo1 != null) {
                // both operands are definitely true, thus so is the result
                Lo = one; Hi = null;
              }
              break;
            case BinaryOperator.Opcode.Or:
              if (lo0 != null || lo1 != null) {
                // one operand is definitely true, thus so is the result
                Lo = one; Hi = null;
              } else if (hi0 != null && hi1 != null) {
                // both operands are definitely false, thus so is the result
                Lo = null; Hi = one;
              }
              break;
            case BinaryOperator.Opcode.Imp:
              if (hi0 != null || lo1 != null) {
                // either arg0 false or arg1 is true, so the result is true
                Lo = one; Hi = null;
              } else if (lo0 != null && hi1 != null) {
                // arg0 is true and arg1 is false, so the result is false
                Lo = null; Hi = one;
              }
              break;
            case BinaryOperator.Opcode.Iff:
              if (lo0 != null && lo1 != null) {
                Lo = one; Hi = null;
              } else if (hi0 != null && hi1 != null) {
                Lo = one; Hi = null;
              } else if (lo0 != null && hi1 != null) {
                Lo = null; Hi = one;
              } else if (hi0 != null && lo1 != null) {
                Lo = null; Hi = one;
              }
              if (op.Op == BinaryOperator.Opcode.Neq) {
                var tmp = Lo; Lo = Hi; Hi = tmp;
              }
              break;
            case BinaryOperator.Opcode.Eq:
            case BinaryOperator.Opcode.Neq:
              if (node.Args[0].Type.IsBool) {
                goto case BinaryOperator.Opcode.Iff;
              }
              // For Eq:
              // If the (lo0,hi0) and (lo1,hi1) ranges do not overlap, the answer is false.
              // If both ranges are the same unit range, then the answer is true.
              if (hi0 != null && lo1 != null && (isReal ? hi0 < lo1 : hi0 <= lo1)) {
                // no overlap
                Lo = null; Hi = one;
              } else if (lo0 != null && hi1 != null && (isReal ? hi1 < lo0 : hi1 <= lo0)) {
                Lo = null; Hi = one;
                // no overlaop
              } else if (lo0 != null && hi0 != null && lo1 != null && hi1 != null &&
                lo0 == lo1 && hi0 == hi1 &&  // ranges are the same
                (isReal ? lo0 == hi0 : lo0 + 1 == hi0)) {  // unit range
                // both ranges are the same unit range
                Lo = one; Hi = null;
              }
              if (op.Op == BinaryOperator.Opcode.Neq) {
                var tmp = Lo; Lo = Hi; Hi = tmp;
              }
              break;
            case BinaryOperator.Opcode.Le:
              if (isReal) {
                // If hi0 <= lo1, then the answer is true.
                // If hi1 < lo0, then the answer is false.
                if (hi0 != null && lo1 != null && hi0 <= lo1) {
                  Lo = one; Hi = null;
                } else if (hi1 != null && lo0 != null && hi1 < lo0) {
                  Lo = null; Hi = one;
                }
              } else {
                // If hi0 - 1 <= lo1, then the answer is true.
                // If hi1 <= lo0, then the answer is false.
                if (hi0 != null && lo1 != null && hi0 - 1 <= lo1) {
                  Lo = one; Hi = null;
                } else if (lo0 != null && hi1 != null && hi1 <= lo0) {
                  Lo = null; Hi = one;
                }
              }
              break;
            case BinaryOperator.Opcode.Lt:
              if (isReal) {
                // If hi0 < lo1, then the answer is true.
                // If hi1 <= lo0, then the answer is false.
                if (hi0 != null && lo1 != null && hi0 < lo1) {
                  Lo = one; Hi = null;
                } else if (hi1 != null && lo0 != null && hi1 <= lo0) {
                  Lo = null; Hi = one;
                }
              } else {
                // If hi0 <= lo1, then the answer is true.
                // If hi1 - 1 <= lo0, then the answer is false.
                if (hi0 != null && lo1 != null && hi0 <= lo1) {
                  Lo = one; Hi = null;
                } else if (lo0 != null && hi1 != null && hi1 - 1 <= lo0) {
                  Lo = null; Hi = one;
                }
              }
              break;
            case BinaryOperator.Opcode.Gt:
              // swap the operands and then continue as Lt
              {
                var tmp = lo0; lo0 = lo1; lo1 = tmp;
                tmp = hi0; hi0 = hi1; hi1 = tmp;
              }
              goto case BinaryOperator.Opcode.Lt;
            case BinaryOperator.Opcode.Ge:
              // swap the operands and then continue as Le
              {
                var tmp = lo0; lo0 = lo1; lo1 = tmp;
                tmp = hi0; hi0 = hi1; hi1 = tmp;
              }
              goto case BinaryOperator.Opcode.Le;
            case BinaryOperator.Opcode.Add:
              if (lo0 != null && lo1 != null) {
                Lo = lo0 + lo1;
              }
              if (hi0 != null && hi1 != null) {
                Hi = isReal ? hi0 + hi1 : hi0 + hi1 - 1;
              }
              break;
            case BinaryOperator.Opcode.Sub:
              if (lo0 != null && hi1 != null) {
                Lo = isReal ? lo0 - hi1 : lo0 - hi1 + 1;
              }
              if (hi0 != null && lo1 != null) {
                Hi = hi0 - lo1;
              }
              break;
            case BinaryOperator.Opcode.Mul:
              // this uses an incomplete approximation that could be tightened up
              if (lo0 != null && lo1 != null) {
                if (0 <= (BigInteger)lo0 && 0 <= (BigInteger)lo1) {
                  Lo = lo0 * lo1;
                  Hi = hi0 == null || hi1 == null ? null : isReal ? hi0 * hi1 : (hi0 - 1) * (hi1 - 1) + 1;
                } else if ((BigInteger)lo0 < 0 && (BigInteger)lo1 < 0) {
                  Lo = null;  // approximation
                  Hi = isReal ? lo0 * lo1 : lo0 * lo1 + 1;
                }
              }
              break;
            case BinaryOperator.Opcode.Div:
              // this uses an incomplete approximation that could be tightened up
              if (lo0 != null && lo1 != null && 0 <= (BigInteger)lo0 && 0 <= (BigInteger)lo1) {
                Lo = BigInteger.Zero;
                Hi = hi0;
              }
              break;
            case BinaryOperator.Opcode.Mod:
              // this uses an incomplete approximation that could be tightened up
              if (lo0 != null && lo1 != null && 0 <= (BigInteger)lo0 && 0 <= (BigInteger)lo1) {
                Lo = BigInteger.Zero;
                Hi = hi1;
                if (lo0 < lo1 && hi0 != null && hi0 < lo1) {
                  Lo = lo0;
                  Hi = hi0;
                }
              }
              break;
            case BinaryOperator.Opcode.RealDiv:
              // this uses an incomplete approximation that could be tightened up
              if (lo0 != null && lo1 != null && 0 <= (BigInteger)lo0 && 0 <= (BigInteger)lo1) {
                Lo = BigInteger.Zero;
                Hi = 1 <= (BigInteger)lo1 ? hi0 : null;
              }
              break;
            case BinaryOperator.Opcode.Pow:
              // this uses an incomplete approximation that could be tightened up
              if (lo0 != null && lo1 != null && 0 <= (BigInteger)lo0 && 0 <= (BigInteger)lo1) {
                Lo = 1 <= (BigInteger)lo1 ? BigInteger.One : BigInteger.Zero;
                Hi = hi1;
              }
              break;
            default:
              break;
          }
        } else if (node.Fun is IfThenElse) {
          var op = (IfThenElse)node.Fun;
          Contract.Assert(node.Args.Count == 3);
          BigInteger? guardLo, guardHi, lo0, hi0, lo1, hi1;
          VisitExpr(node.Args[0]);
          guardLo = Lo; guardHi = Hi;
          VisitExpr(node.Args[1]);
          lo0 = Lo; hi0 = Hi;
          VisitExpr(node.Args[2]);
          lo1 = Lo; hi1 = Hi;
          Contract.Assert(guardLo == null || guardHi == null);  // this is a consequence of the guard being boolean
          if (guardLo != null) {
            // guard is always true
            Lo = lo0; Hi = hi0;
          } else if (guardHi != null) {
            // guard is always false
            Lo = lo1; Hi = hi1;
          } else {
            // we don't know which branch will be taken, so join the information from the two branches
            Lo = Node.Min(lo0, lo1, false);
            Hi = Node.Max(hi0, hi1, false);
          }
        } else if (node.Fun is FunctionCall) {
          var call = (FunctionCall)node.Fun;
          // See if this is an identity function, which we do by checking: that the function has
          // exactly one argument and the function has been marked by the user with the attribute {:identity}
          bool claimsToBeIdentity = false;
          if (call.ArgumentCount == 1 && call.Func.CheckBooleanAttribute("identity", ref claimsToBeIdentity) && claimsToBeIdentity && node.Args[0].Type.Equals(node.Type)) {
            VisitExpr(node.Args[0]);
          }
        }
        return node;
      }
      public override BinderExpr VisitBinderExpr(BinderExpr node) {
        // don't recurse on subexpression
        return node;
      }
      public override Expr VisitOldExpr(OldExpr node) {
        // don't recurse on subexpression
        return node;
      }
      public override Expr VisitCodeExpr(CodeExpr node) {
        // don't recurse on subexpression
        return node;
      }
      public override Expr VisitBvConcatExpr(BvConcatExpr node) {
        // don't recurse on subexpression
        return node;
      }
      public override Expr VisitBvExtractExpr(BvExtractExpr node) {
        // don't recurse on subexpression
        return node;
      }
    }

    public override Element Eliminate(Element element, Variable v) {
      if (element is E_Bottom) {
        return element;
      }
      var e = (E)element;
      var nn = UpdateOne(e.N, v, null, null);
      if (nn == e.N) {
        return element;
      } else {
        return new E(nn);
      }
    }

    Node UpdateOne(Node nn, Variable v, BigInteger? lo, BigInteger? hi) {
      var orig = nn;
      Node head = null;
      Node prev = null;
      var foundV = false;
      for (; nn != null && !Node.StrictlyBefore(v, nn.V); nn = nn.Next) {
        if (nn.V == v) {
          foundV = true;
          nn = nn.Next;
          break;  // we found the place where the new node goes
        } else {
          var n = new Node(nn.V, nn.Lo, nn.Hi);  // copy this Node
          if (head == null) {
            head = n;
          } else {
            prev.Next = n;
          }
          prev = n;
        }
      }
      Node rest;
      if (lo == null && hi == null) {
        // eliminate all information about "v"
        if (!foundV) {
          return orig;
        }
        rest = nn;
      } else {
        rest = new Node(v, lo, hi);
        rest.Next = nn;
      }
      if (head == null) {
        head = rest;
      } else {
        prev.Next = rest;
      }
      return head;
    }

    /// <summary>
    /// Return a resolved/type-checked expression that represents the conjunction of a and b.
    /// Requires a and b to be resolved and type checked already.
    /// </summary>
    public static Expr BplAnd(Expr a, Expr b) {
      if (a == Expr.True) {
        return b;
      } else if (b == Expr.True) {
        return a;
      } else {
        var nary = Expr.Binary(BinaryOperator.Opcode.And, a, b);
        nary.Type = Type.Bool;
        nary.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        return nary;
      }
    }

    /// <summary>
    /// Return a resolved/type-checked expression that represents a EQUALS b.
    /// Requires a and b to be resolved and type checked already.
    /// </summary>
    public static Expr BplEq(Expr a, Expr b) {
      var e = Expr.Eq(a, b);
      e.Type = Type.Bool;
      return e;
    }

    /// <summary>
    /// Return a resolved/type-checked expression that represents a LESS-EQUAL b.
    /// Requires a and b to be resolved and type checked already.
    /// </summary>
    public static Expr BplLe(Expr a, Expr b) {
      var e = Expr.Le(a, b);
      e.Type = Type.Bool;
      return e;
    }
    /// <summary>
    /// Return a resolved/type-checked expression that represents a LESS b.
    /// Requires a and b to be resolved and type checked already.
    /// </summary>
    public static Expr BplLt(Expr a, Expr b) {
      var e = Expr.Lt(a, b);
      e.Type = Type.Bool;
      return e;
    }
  }

  public class ThresholdFinder : ReadOnlyVisitor
  {
    readonly Implementation Impl;
    public ThresholdFinder(Implementation impl) {
      Contract.Requires(impl != null);
      Impl = impl;
    }
    HashSet<BigInteger> downs = new HashSet<BigInteger>();
    HashSet<BigInteger> ups = new HashSet<BigInteger>();
    public void Find(out List<BigInteger> downThresholds, out List<BigInteger> upThresholds) {
      // always include -1, 0, 1 as down-thresholds
      downs.Clear();
      downs.Add(-1);
      downs.Add(0);
      downs.Add(1);
      // always include 0 and 1 as up-thresholds
      ups.Clear();
      ups.Add(0);
      ups.Add(1);

      foreach (Requires p in Impl.Proc.Requires) {
        Visit(p.Condition);
      }
      foreach (Ensures p in Impl.Proc.Ensures) {
        Visit(p.Condition);
      }
      foreach (var b in Impl.Blocks) {
        foreach (Cmd c in b.Cmds) {
          Visit(c);
        }
      }

      // convert the HashSets to sorted Lists and return
      downThresholds = new List<BigInteger>();
      foreach (var i in downs) {
        downThresholds.Add(i);
      }
      downThresholds.Sort();
      upThresholds = new List<BigInteger>();
      foreach (var i in ups) {
        upThresholds.Add(i);
      }
      upThresholds.Sort();
    }

    public override Expr VisitNAryExpr(NAryExpr node) {
      if (node.Fun is BinaryOperator) {
        var op = (BinaryOperator)node.Fun;
        Contract.Assert(node.Args.Count == 2);
        var arg0 = node.Args[0];
        var arg1 = node.Args[1];
        var offset = arg0.Type.IsReal ? 0 : 1;
        BigInteger? k;
        switch (op.Op) {
          case BinaryOperator.Opcode.Eq:
          case BinaryOperator.Opcode.Neq:
            k = AsIntLiteral(arg0);
            if (k != null) {
              var i = (BigInteger)k;
              downs.Add(i - 1);
              downs.Add(i);
              ups.Add(i + 1);
              ups.Add(i + 2);
            }
            k = AsIntLiteral(arg1);
            if (k != null) {
              var i = (BigInteger)k;
              downs.Add(i - 1);
              downs.Add(i);
              ups.Add(i + 1);
              ups.Add(i + 2);
            }
            break;
          case BinaryOperator.Opcode.Le:
            k = AsIntLiteral(arg0);
            if (k != null) {
              var i = (BigInteger)k;
              downs.Add(i - 1);
              downs.Add(i);
            }
            k = AsIntLiteral(arg1);
            if (k != null) {
              var i = (BigInteger)k;
              ups.Add(i + offset);
              ups.Add(i + 1 + offset);
            }
            break;
          case BinaryOperator.Opcode.Lt:
            k = AsIntLiteral(arg0);
            if (k != null) {
              var i = (BigInteger)k;
              downs.Add(i );
              downs.Add(i + 1);
            }
            k = AsIntLiteral(arg1);
            if (k != null) {
              var i = (BigInteger)k;
              ups.Add(i - 1 + offset);
              ups.Add(i + offset);
            }
            break;
          case BinaryOperator.Opcode.Ge:
            { var tmp = arg0; arg0 = arg1; arg1 = tmp; }
            goto case BinaryOperator.Opcode.Le;
          case BinaryOperator.Opcode.Gt:
            { var tmp = arg0; arg0 = arg1; arg1 = tmp; }
            goto case BinaryOperator.Opcode.Lt;
          default:
            break;
        }
      }
      return base.VisitNAryExpr(node);
    }

    BigInteger? AsIntLiteral(Expr e) {
      var lit = e as LiteralExpr;
      if (lit != null && lit.isBigNum) {
        BigNum bn = lit.asBigNum;
        return bn.ToBigInteger;
      }
      return null;
    }
  }

}
