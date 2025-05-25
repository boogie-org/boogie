using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class NAryExpr : Expr
{
  public override int ContentHash =>
    Args.Select(a => a.ContentHash).Aggregate(Util.GetHashCode(98765939, Fun.ContentHash), Util.GetHashCode);
    
  [Additive] [Peer] private IAppliable _Fun;

  public IAppliable Fun
  {
    get => _Fun;
    set
    {
      if (Immutable)
      {
        throw new InvalidOperationException("Cannot change Function used by Immutable NAryExpr");
      }

      _Fun = value;
    }
  }

  private List<Expr> _Args;

  public IList<Expr> Args
  {
    get
    {
      if (Immutable)
      {
        return _Args.AsReadOnly();
      }
      else
      {
        return _Args;
      }
    }
    set
    {
      if (Immutable)
      {
        throw new InvalidOperationException("Cannot change Args of Immutable NAryExpr");
      }

      _Args = value as List<Expr>;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Fun != null);
    Contract.Invariant(Args != null);
  }


  // The instantiation of type parameters that is determined during type checking.
  // Which type parameters are available depends on the IAppliable
  public TypeParamInstantiation TypeParameters = null;

  [Captured]
  public NAryExpr(IToken tok, IAppliable fun, IList<Expr> args, bool immutable = false)
    : base(tok, immutable)
  {
    Contract.Requires(tok != null);
    Contract.Requires(fun != null);
    Contract.Requires(args != null);
    _Fun = fun;
    Contract.Assert(Contract.ForAll(0, args.Count, index => args[index] != null));
    if (immutable)
    {
      // We need to make a new list because the client might be holding
      // references to the list that they gave us which could be used to
      // circumvent the immutability enforcement
      _Args = new List<Expr>(args);
      CachedHashCode = ComputeHashCode();
    }
    else
    {
      if (args is List<Expr>)
      {
        // Preserve NAryExpr's old behaviour, we take ownership of the List<Expr>.
        // We can only do this if the type matches
        _Args = args as List<Expr>;
      }
      else
      {
        // Otherwise we must make a copy
        _Args = new List<Expr>(args);
      }
    }
  }

  [Pure]
  [Reads(ReadsAttribute.Reads.Nothing)]
  public override bool Equals(object obj)
  {
    if (obj == null)
    {
      return false;
    }

    if (!(obj is NAryExpr))
    {
      return false;
    }

    NAryExpr other = (NAryExpr) obj;
    return object.Equals(this.Fun, other.Fun) && this.Args.SequenceEqual(other.Args);
  }

  [Pure]
  public override int GetHashCode()
  {
    if (Immutable)
    {
      return this.CachedHashCode;
    }
    else
    {
      return ComputeHashCode();
    }
  }

  [Pure]
  public override int ComputeHashCode()
  {
    int h = this.Fun.GetHashCode();
    // DO NOT USE Args.GetHashCode() because that uses Object.GetHashCode() which uses references
    // We want structural equality
    foreach (var arg in Args)
    {
      h = (97 * h) + arg.GetHashCode();
    }

    return h;
  }

  public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
  {
    stream.SetToken(this);
    Fun.Emit(Args, stream, contextBindingStrength, fragileContext);
  }

  public override void Resolve(ResolutionContext rc)
  {
    Fun.Resolve(rc, this);
    foreach (Expr e in Args)
    {
      Contract.Assert(e != null);
      e.Resolve(rc);
    }
  }

  public override void ComputeFreeVariables(GSet<object> /*Variable*/ freeVars)
  {
    foreach (Expr e in Args)
    {
      Contract.Assert(e != null);
      e.ComputeFreeVariables(freeVars);
    }

    // also add the free type variables
    if (TypeParameters != null)
    {
      foreach (TypeVariable var in TypeParameters.FormalTypeParams)
      {
        Contract.Assert(var != null);
        foreach (TypeVariable w in TypeParameters[var].FreeVariables)
        {
          Contract.Assert(w != null);
          freeVars.Add(w);
        }
      }
    }
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    int prevErrorCount = tc.ErrorCount;
    foreach (Expr e in Args)
    {
      Contract.Assert(e != null);
      e.Typecheck(tc);
    }

    if (Fun.ArgumentCount != Args.Count)
    {
      tc.Error(this, "wrong number of arguments to function: {0} ({1} instead of {2})",
        Fun.FunctionName, Args.Count, Fun.ArgumentCount);
    }
    else if (tc.ErrorCount == prevErrorCount &&
             // if the type parameters are set, this node has already been
             // typechecked and does not need to be checked again
             TypeParameters == null)
    {
      Type = Fun.Typecheck(Args, out var tpInsts,
        tc); // Make sure we pass Args so if this Expr is immutable it is protected
      TypeParameters = tpInsts;
    }

    IOverloadedAppliable oa = Fun as IOverloadedAppliable;
    if (oa != null)
    {
      oa.ResolveOverloading(this);
    }

    if (Type == null)
    {
      Type = Expr.ErrorType;
    }
  }

  public override Type ShallowType
  {
    get
    {
      Contract.Ensures(Contract.Result<Type>() != null);

      return Fun.ShallowType(Args);
    }
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitNAryExpr(this);
  }
}