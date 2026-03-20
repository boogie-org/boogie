using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class FunctionCall : IAppliable
{
  public int ContentHash => 1;

  private IdentifierExpr name;

  public Function Func;

  public FunctionCall(IdentifierExpr name)
  {
    Contract.Requires(name != null);
    this.name = name;
  }

  public FunctionCall(Function f)
  {
    Contract.Requires(f != null);
    this.Func = f;
    this.name = new IdentifierExpr(Token.NoToken, f.Name);

    // We need set the type of this IdentifierExpr so ShallowType() works
    Debug.Assert(f.OutParams.Count > 0);
    this.name.Type = f.OutParams[0].TypedIdent.Type;
  }

  public string FunctionName
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.name.Name;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(name != null);
  }

  public FunctionCall CreateUnresolvedCopy()
  {
    return new FunctionCall(new IdentifierExpr(name.tok, name.Name, name.Type));
  }

  [Pure]
  public override string ToString()
  {
    Contract.Ensures(Contract.Result<string>() != null);
    return name.Name;
  }

  [Pure]
  [Reads(ReadsAttribute.Reads.Nothing)]
  public override bool Equals(object other)
  {
    FunctionCall fc = other as FunctionCall;
    return fc != null && this.Func == fc.Func;
  }

  [Pure]
  public override int GetHashCode()
  {
    Contract.Assume(this.Func != null);
    return Func.GetHashCode();
  }

  public virtual void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
  {

    if (stream.UseForComputingChecksums && Func.OriginalLambdaExprAsString != null)
    {
      stream.Write(Func.OriginalLambdaExprAsString);
    }
    else
    {
      this.name.Emit(stream, 0xF0, false);
    }

    if (stream.UseForComputingChecksums)
    {
      var c = Func.DependencyChecksum;
      if (c != null)
      {
        stream.Write(string.Format("[dependency_checksum:{0}]", c));
      }
    }

    stream.Write("(");
    args.Emit(stream);
    stream.Write(")");
  }

  public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
  {
    if (Func != null)
    {
      // already resolved
      if (rc.TriggerMode && Func.Body != null)
      {
        CheckBodyTriggerLegality(Func, subjectForErrorReporting, rc, new HashSet<Function>());
      }
      return;
    }

    Func = rc.LookUpFunction(name.Name);
    if (Func == null)
    {
      rc.Error(this.name, "use of undeclared function: {0}", name.Name);
    }
    else
    {
      if (name.Type == null)
      {
        // We need set the type of this IdentifierExpr so ShallowType() works
        Debug.Assert(name.Type == null);
        Debug.Assert(Func.OutParams.Count > 0);
        name.Type = Func.OutParams[0].TypedIdent.Type;
      }
      if (rc.TriggerMode && Func.Body != null)
      {
        CheckBodyTriggerLegality(Func, subjectForErrorReporting, rc, new HashSet<Function>());
      }
    }
  }

  private static void CheckBodyTriggerLegality(Function func, Expr subjectForErrorReporting,
    ResolutionContext rc, HashSet<Function> visited)
  {
    if (!visited.Add(func))
    {
      return; // Already checking this function (cycle detection)
    }
    CheckExprTriggerLegality(func.Body, func.Name, subjectForErrorReporting, rc, visited);
  }

  private static void CheckExprTriggerLegality(Expr expr, string funcName, Expr subjectForErrorReporting,
    ResolutionContext rc, HashSet<Function> visited)
  {
    if (expr is NAryExpr nary)
    {
      if (nary.Fun is UnaryOperator uop && uop.Op == UnaryOperator.Opcode.Not)
      {
        rc.Error(subjectForErrorReporting,
          "trigger expression refers to the inline function '{0}' whose body contains boolean operators, which are not allowed in triggers",
          funcName);
      }
      else if (nary.Fun is BinaryOperator bop)
      {
        switch (bop.Op)
        {
          case BinaryOperator.Opcode.Eq:
            rc.Error(subjectForErrorReporting,
              "trigger expression refers to the inline function '{0}' whose body contains equality, which is not allowed in triggers",
              funcName);
            break;
          case BinaryOperator.Opcode.Gt:
          case BinaryOperator.Opcode.Ge:
          case BinaryOperator.Opcode.Lt:
          case BinaryOperator.Opcode.Le:
            rc.Error(subjectForErrorReporting,
              "trigger expression refers to the inline function '{0}' whose body contains arithmetic comparisons, which are not allowed in triggers",
              funcName);
            break;
          case BinaryOperator.Opcode.And:
          case BinaryOperator.Opcode.Or:
          case BinaryOperator.Opcode.Imp:
          case BinaryOperator.Opcode.Iff:
            rc.Error(subjectForErrorReporting,
              "trigger expression refers to the inline function '{0}' whose body contains boolean operators, which are not allowed in triggers",
              funcName);
            break;
        }
      }
      else if (nary.Fun is FunctionCall nestedFc && nestedFc.Func?.Body != null)
      {
        CheckBodyTriggerLegality(nestedFc.Func, subjectForErrorReporting, rc, visited);
      }
      foreach (var arg in nary.Args)
      {
        CheckExprTriggerLegality(arg, funcName, subjectForErrorReporting, rc, visited);
      }
    }
  }

  public virtual int ArgumentCount
  {
    get
    {
      Contract.Assume(Func != null); // ArgumentCount requires object to be properly resolved.
      return Func.InParams.Count;
    }
  }

  public virtual Type Typecheck(IList<Expr> actuals, out TypeParamInstantiation tpInstantiation,
    TypecheckingContext tc)
  {
    Contract.Ensures(Contract.ValueAtReturn(out actuals) != null);
    Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
    Contract.Assume(this.Func != null);
    Contract.Assume(actuals.Count == Func.InParams.Count);
    Contract.Assume(Func.OutParams.Count == 1);

    List<Type> actualResultType =
      Type.CheckArgumentTypes(Func.TypeParameters,
        out var resultingTypeArgs,
        Func.InParams.Select(Item => Item.TypedIdent.Type).ToList(),
        actuals,
        Func.OutParams.Select(Item => Item.TypedIdent.Type).ToList(),
        null,
        // we need some token to report a possibly wrong number of
        // arguments
        actuals.Count > 0 ? Cce.NonNull(actuals[0]).tok : Token.NoToken,
        "application of " + name.Name,
        tc);

    if (actualResultType == null)
    {
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      return null;
    }
    else
    {
      Contract.Assert(actualResultType.Count == 1);
      tpInstantiation =
        SimpleTypeParamInstantiation.From(Func.TypeParameters, resultingTypeArgs);
      return actualResultType[0];
    }
  }

  public Type ShallowType(IList<Expr> args)
  {
    Contract.Ensures(Contract.Result<Type>() != null);
    Contract.Assume(name.Type != null);
    return name.Type;
  }

  public virtual T Dispatch<T>(IAppliableVisitor<T> visitor)
  {
    return visitor.Visit(this);
  }
}