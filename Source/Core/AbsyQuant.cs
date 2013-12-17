//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// BoogiePL - AbsyQuant.cs
//---------------------------------------------------------------------------------------------

namespace Microsoft.Boogie {
  using System;
  using System.Collections;
  using System.Diagnostics;
  using System.Collections.Generic;
  using System.Linq;
  using Microsoft.Boogie.AbstractInterpretation;
  using System.Diagnostics.Contracts;
  using Microsoft.Basetypes;

  using Set = GSet<object>;

  //---------------------------------------------------------------------
  // Quantifiers and general binders
  //---------------------------------------------------------------------

  public enum BinderKind {
    Forall,
    Exists,
    Lambda
  }
  [ContractClassFor(typeof(BinderExpr))]
  abstract class BinderExprContracts : BinderExpr {
    public override BinderKind Kind {
      get {
        throw new NotImplementedException();
      }
    }
    public BinderExprContracts():base(null,null,null,null,null){
  }

    public override Type ShallowType {
      get {
        throw new NotImplementedException();
      }
    }
  }
  [ContractClass(typeof(BinderExprContracts))]
  public abstract class BinderExpr : Expr {
    public List<TypeVariable>/*!*/ TypeParameters;
    public List<Variable>/*!*/ Dummies;
    public QKeyValue Attributes;
    public Expr/*!*/ Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TypeParameters != null);
      Contract.Invariant(Dummies != null);
      Contract.Invariant(Body != null);
    }


    public BinderExpr(IToken/*!*/ tok, List<TypeVariable>/*!*/ typeParameters,
                      List<Variable>/*!*/ dummies, QKeyValue kv, Expr/*!*/ body)
      : base(tok)
      {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParameters.Count > 0);
      TypeParameters = typeParameters;
      Dummies = dummies;
      Attributes = kv;
      Body = body;
    }

    abstract public BinderKind Kind {
      get;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is BinderExpr) ||
          this.Kind != ((BinderExpr)obj).Kind)
        return false;

      BinderExpr other = (BinderExpr)obj;
      // Note, we consider quantifiers equal modulo the Triggers.
      return object.Equals(this.TypeParameters, other.TypeParameters)
             && object.Equals(this.Dummies, other.Dummies)
             && object.Equals(this.Body, other.Body);
    }

    [Pure]
    public override int GetHashCode() {
      int h = this.Dummies.GetHashCode();
      // Note, we consider quantifiers equal modulo the Triggers.
      h ^= this.Body.GetHashCode();
      h = h * 5 + this.TypeParameters.GetHashCode();
      h *= ((int)Kind + 1);
      return h;
    }

    protected virtual void EmitTypeHint(TokenTextWriter stream) {
      Contract.Requires(stream != null);
    }

    protected virtual void EmitTriggers(TokenTextWriter stream) {
      Contract.Requires(stream != null);
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext) {
      //Contract.Requires(stream != null);
      stream.Write(this, "({0}", Kind.ToString().ToLower());
      this.EmitTypeHint(stream);
      Type.EmitOptionalTypeParams(stream, TypeParameters);
      stream.Write(this, " ");
      this.Dummies.Emit(stream, true);
      stream.Write(" :: ");
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        kv.Emit(stream);
        stream.Write(" ");
      }
      this.EmitTriggers(stream);

      this.Body.Emit(stream);
      stream.Write(")");
    }

    protected virtual void ResolveTriggers(ResolutionContext rc) {
      Contract.Requires(rc != null);
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      if (rc.TriggerMode) {
        rc.Error(this, "quantifiers are not allowed in triggers");
      }

      int previousTypeBinderState = rc.TypeBinderState;
      try {
        foreach (TypeVariable/*!*/ v in TypeParameters) {
          Contract.Assert(v != null);
          rc.AddTypeBinder(v);
        }

        rc.PushVarContext();
        foreach (Variable/*!*/ v in Dummies) {
          Contract.Assert(v != null);
          v.Register(rc);
          v.Resolve(rc);
        }
        for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
          kv.Resolve(rc);
        }
        this.ResolveTriggers(rc);
        Body.Resolve(rc);
        rc.PopVarContext();

        // establish a canonical order of the type parameters
        this.TypeParameters = Type.SortTypeParams(TypeParameters, new List<Type>(Dummies.Select(Item => Item.TypedIdent.Type).ToArray()), null);

      } finally {
        rc.TypeBinderState = previousTypeBinderState;
      }
    }

    public override void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      //Contract.Requires(freeVars != null);
      foreach (Variable/*!*/ v in Dummies) {
        Contract.Assert(v != null);
        Contract.Assert(!freeVars[v]);
      }
      Body.ComputeFreeVariables(freeVars);
      foreach (Variable/*!*/ v in Dummies) {
        Contract.Assert(v != null);
        foreach (TypeVariable/*!*/ w in v.TypedIdent.Type.FreeVariables) {
          Contract.Assert(w != null);
          freeVars.Add(w);
        }
      }
      foreach (Variable/*!*/ v in Dummies) {
        Contract.Assert(v != null);
        freeVars.Remove(v);
      }
      foreach (TypeVariable/*!*/ v in TypeParameters) {
        Contract.Assert(v != null);
        freeVars.Remove(v);
      }
    }

    protected List<TypeVariable> GetUnmentionedTypeParameters() {
      Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);
      List<TypeVariable>/*!*/ dummyParameters = Type.FreeVariablesIn(new List<Type>(Dummies.Select(Item => Item.TypedIdent.Type).ToArray()));
      Contract.Assert(dummyParameters != null);
      List<TypeVariable>/*!*/ unmentionedParameters = new List<TypeVariable>();
      foreach (TypeVariable/*!*/ var in TypeParameters) {
        Contract.Assert(var != null);
        if (!dummyParameters.Contains(var))
          unmentionedParameters.Add(var);
      }
      return unmentionedParameters;
    }
  }

  public class QKeyValue : Absy {
    public readonly string/*!*/ Key;
    public readonly List<object/*!*/>/*!*/ Params;  // each element is either a string or an Expr
    public QKeyValue Next;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Key != null);
      Contract.Invariant(cce.NonNullElements(Params));
    }


    public QKeyValue(IToken tok, string key, [Captured] List<object/*!*/>/*!*/ parameters, QKeyValue next)
      : base(tok) {
      Contract.Requires(key != null);
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(parameters));
      Key = key;
      Params = parameters;
      Next = next;
    }

    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      stream.Write("{:");
      stream.Write(Key);
      string sep = " ";
      foreach (object p in Params) {
        stream.Write(sep);
        sep = ", ";
        if (p is string) {
          stream.Write("\"");
          stream.Write((string)p);
          stream.Write("\"");
        } else {
          ((Expr)p).Emit(stream);
        }
      }
      stream.Write("}");
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      foreach (object p in Params) {
        if (p is Expr) {
          ((Expr)p).Resolve(rc);
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      foreach (object p in Params) {
        if (p is Expr) {
          ((Expr)p).Typecheck(tc);
        }
      }
    }
    public void AddLast(QKeyValue other) {
      Contract.Requires(other != null);
      QKeyValue current = this;
      while (current.Next != null) {
        current = current.Next;
      }
      current.Next = other;
    }
    // Look for {:name string} in list of attributes.
    public static string FindStringAttribute(QKeyValue kv, string name) {
      Contract.Requires(name != null);
      for (; kv != null; kv = kv.Next) {
        if (kv.Key == name) {
          if (kv.Params.Count == 1 && kv.Params[0] is string) {
            return (string)kv.Params[0];
          }
        }
      }
      return null;
    }
    // Look for {:name expr} in list of attributes.
    public static Expr FindExprAttribute(QKeyValue kv, string name) {
      Contract.Requires(name != null);
      for (; kv != null; kv = kv.Next) {
        if (kv.Key == name) {
          if (kv.Params.Count == 1 && kv.Params[0] is Expr) {
            return (Expr)kv.Params[0];
          }
        }
      }
      return null;
    }
    // Return 'true' if {:name true} or {:name} is an attribute in 'kv'
    public static bool FindBoolAttribute(QKeyValue kv, string name) {
      Contract.Requires(name != null);
      for (; kv != null; kv = kv.Next) {
        if (kv.Key == name) {
          return kv.Params.Count == 0 ||
            (kv.Params.Count == 1 && kv.Params[0] is LiteralExpr && ((LiteralExpr)kv.Params[0]).IsTrue);
        }
      }
      return false;
    }

    public static int FindIntAttribute(QKeyValue kv, string name, int defl) {
      Contract.Requires(name != null);
      Expr e = FindExprAttribute(kv, name);
      LiteralExpr l = e as LiteralExpr;
      if (l != null && l.isBigNum)
        return l.asBigNum.ToIntSafe;
      return defl;
    }

    public override Absy Clone() {
      List<object> newParams = new List<object>();
      foreach (object o in Params)
        newParams.Add(o);
      return new QKeyValue(tok, Key, newParams, (Next == null) ? null : (QKeyValue)Next.Clone());
    }
  }

  public class Trigger : Absy {
    public readonly bool Pos;
    [Rep]
    public List<Expr>/*!*/ Tr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tr != null);
      Contract.Invariant(1 <= Tr.Count);
      Contract.Invariant(Pos || Tr.Count == 1);
    }

    public Trigger Next;

    public Trigger(IToken tok, bool pos, List<Expr> tr)
      : this(tok, pos, tr, null) {
      Contract.Requires(tr != null);
      Contract.Requires(tok != null);
      Contract.Requires(1 <= tr.Count);
      Contract.Requires(pos || tr.Count == 1);
    }

    public Trigger(IToken/*!*/ tok, bool pos, List<Expr>/*!*/ tr, Trigger next)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(tr != null);
      Contract.Requires(1 <= tr.Count);
      Contract.Requires(pos || tr.Count == 1);
      this.Pos = pos;
      this.Tr = tr;
      this.Next = next;
    }

    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      stream.SetToken(this);
      Contract.Assert(this.Tr.Count >= 1);
      string/*!*/ sep = Pos ? "{ " : "{:nopats ";
      foreach (Expr/*!*/ e in this.Tr) {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }
      stream.Write(" }");
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.TriggerMode = true;
      foreach (Expr/*!*/ e in this.Tr) {
        Contract.Assert(e != null);
        e.Resolve(rc);

        // just a variable by itself is not allowed
        if (e is IdentifierExpr) {
          rc.Error(e, "a matching pattern must be more than just a variable by itself: {0}", e);
        }

        // the free-variable check is performed in the surrounding quantifier expression (because that's
        // where the bound variables are known)
      }
      rc.TriggerMode = false;
    }

    /// <summary>
    /// Add to "freeVars" the free variables in the triggering expressions.
    /// </summary>
    public void ComputeFreeVariables(Set /*Variable*/ freeVars) {
      Contract.Requires(freeVars != null);
      foreach (Expr/*!*/ e in this.Tr) {
        Contract.Assert(e != null);
        e.ComputeFreeVariables(freeVars);
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      foreach (Expr/*!*/ e in this.Tr) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }
    }

    public void AddLast(Trigger other) {
      Trigger current = this;
      while (current.Next != null) {
        current = current.Next;
      }
      current.Next = other;
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTrigger(this);
    }
  }

  public class ForallExpr : QuantifierExpr {
    public ForallExpr(IToken/*!*/ tok, List<TypeVariable>/*!*/ typeParams,
                      List<Variable>/*!*/ dummies, QKeyValue kv, Trigger triggers, Expr/*!*/ body)
      : base(tok, typeParams, dummies, kv, triggers, body) {
      Contract.Requires(tok != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParams.Count > 0);
    }
    public ForallExpr(IToken tok, List<Variable> dummies, Trigger triggers, Expr body)
      : base(tok, new List<TypeVariable>(), dummies, null, triggers, body) {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }
    public ForallExpr(IToken tok, List<Variable> dummies, Expr body)
      : base(tok, new List<TypeVariable>(), dummies, null, null, body) {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }
    public ForallExpr(IToken tok, List<TypeVariable> typeParams, List<Variable> dummies, Expr body)
      : base(tok, typeParams, dummies, null, null, body) {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count + typeParams.Count > 0);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitForallExpr(this);
    }

    public override BinderKind Kind {
      get {
        return BinderKind.Forall;
      }
    }
  }

  public class ExistsExpr : QuantifierExpr {
    public ExistsExpr(IToken/*!*/ tok, List<TypeVariable>/*!*/ typeParams, List<Variable>/*!*/ dummies,
                      QKeyValue kv, Trigger triggers, Expr/*!*/ body)
      : base(tok, typeParams, dummies, kv, triggers, body) {
      Contract.Requires(tok != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParams.Count > 0);
    }
    public ExistsExpr(IToken tok, List<Variable> dummies, Trigger triggers, Expr body)
      : base(tok, new List<TypeVariable>(), dummies, null, triggers, body) {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }
    public ExistsExpr(IToken tok, List<Variable> dummies, Expr body)
      : base(tok, new List<TypeVariable>(), dummies, null, null, body) {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitExistsExpr(this);
    }

    public override BinderKind Kind {
      get {
        return BinderKind.Exists;
      }
    }
  }

  public abstract class QuantifierExpr : BinderExpr {
    public Trigger Triggers;

    static int SkolemIds = 0;
    public static int GetNextSkolemId() {
      SkolemIds++;
      return SkolemIds;
    }

    public readonly int SkolemId;

    public QuantifierExpr(IToken/*!*/ tok, List<TypeVariable>/*!*/ typeParameters,
                          List<Variable>/*!*/ dummies, QKeyValue kv, Trigger triggers, Expr/*!*/ body)
      : base(tok, typeParameters, dummies, kv, body) {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParameters.Count > 0);

      Contract.Assert((this is ForallExpr) || (this is ExistsExpr));

      Triggers = triggers;
      SkolemId = SkolemIds++;
    }

    protected override void EmitTriggers(TokenTextWriter stream) {
      //Contract.Requires(stream != null);
      for (Trigger tr = this.Triggers; tr != null; tr = tr.Next) {
        tr.Emit(stream);
        stream.Write(" ");
      }
    }

    // if the user says ( forall x :: forall y :: { f(x,y) } ... ) we transform it to
    // (forall x, y :: { f(x,y) } ... ) otherwise the prover ignores the trigger
    private void MergeAdjecentQuantifier() {
      QuantifierExpr qbody = Body as QuantifierExpr;
      if (!(qbody != null && (qbody is ForallExpr) == (this is ForallExpr) && Triggers == null)) {
        return;
      }
      qbody.MergeAdjecentQuantifier();
      if (qbody.Triggers == null) {
        return;
      }
      Body = qbody.Body;
      TypeParameters.AddRange(qbody.TypeParameters);
      Dummies.AddRange(qbody.Dummies);
      Triggers = qbody.Triggers;
      if (qbody.Attributes != null) {
        if (Attributes == null) {
          Attributes = qbody.Attributes;
        } else {
          QKeyValue p = Attributes;
          while (p.Next != null) {
            p = p.Next;
          }
          p.Next = qbody.Attributes;
        }
      }
    }

    #region never triggers
    private class NeverTriggerCollector : StandardVisitor {
      QuantifierExpr/*!*/ parent;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(parent != null);
      }

      public NeverTriggerCollector(QuantifierExpr p) {
        Contract.Requires(p != null);
        parent = p;
      }

      public override Expr VisitNAryExpr(NAryExpr node) {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        FunctionCall fn = node.Fun as FunctionCall;
        if (fn != null && cce.NonNull(fn.Func).NeverTrigger) {
          parent.Triggers = new Trigger(fn.Func.tok, false, new List<Expr> { node} , parent.Triggers);
        }
        return base.VisitNAryExpr(node);
      }
      public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node) {
        // don't go into quantifier expression or its triggers, since the terms in there may have more bound variables
        // (note, with only the VisitBinderExpr override below, we'd still be visiting triggers, which we don't want to do)
        return node;
      }
      public override BinderExpr VisitBinderExpr(BinderExpr node) {
        // don't go into binder expression, since the terms in there may have more bound variables
        return node;
      }
    }

    private bool neverTriggerApplied;
    private void ApplyNeverTriggers() {
      if (neverTriggerApplied) {
        return;
      }
      neverTriggerApplied = true;

      for (Trigger t = Triggers; t != null; t = t.Next) {
        if (t.Pos) {
          return;
        }
      }

      NeverTriggerCollector visitor = new NeverTriggerCollector(this);
      visitor.VisitExpr(Body);
    }
    #endregion

    protected override void ResolveTriggers(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      for (Trigger tr = this.Triggers; tr != null; tr = tr.Next) {
        int prevErrorCount = rc.ErrorCount;
        tr.Resolve(rc);
        if (prevErrorCount == rc.ErrorCount) {
          // for positive triggers, make sure all bound variables are mentioned
          if (tr.Pos) {
            Set /*Variable*/ freeVars = new Set /*Variable*/ ();
            tr.ComputeFreeVariables(freeVars);
            foreach (Variable/*!*/ v in Dummies) {
              Contract.Assert(v != null);
              if (!freeVars[v]) {
                rc.Error(tr, "trigger must mention all quantified variables, but does not mention: {0}", v);
              }
            }
          }
        }
      }
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      int oldErrorCount = rc.ErrorCount;

      this.MergeAdjecentQuantifier();

      base.Resolve(rc);

      if (oldErrorCount == rc.ErrorCount) {
        this.ApplyNeverTriggers();
      }
    }


    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        kv.Typecheck(tc);
      }
      for (Trigger tr = this.Triggers; tr != null; tr = tr.Next) {
        tr.Typecheck(tc);
      }
      Body.Typecheck(tc);
      Contract.Assert(Body.Type != null);  // follows from postcondition of Expr.Typecheck
      if (!Body.Type.Unify(Type.Bool)) {
        tc.Error(this, "quantifier body must be of type bool");
      }
      this.Type = Type.Bool;

      // Check that type parameters occur in the types of the
      // dummies, or otherwise in the triggers. This can only be
      // done after typechecking
      List<TypeVariable>/*!*/ unmentionedParameters = GetUnmentionedTypeParameters();
      Contract.Assert(unmentionedParameters != null);

      if (unmentionedParameters.Count > 0) {
        // all the type parameters that do not occur in dummy types
        // have to occur in triggers

        for (Trigger tr = this.Triggers; tr != null; tr = tr.Next) {
          // for positive triggers, make sure all bound variables are mentioned
          if (tr.Pos) {
            Set /*Variable*/ freeVars = new Set /*Variable*/ ();
            tr.ComputeFreeVariables(freeVars);
            foreach (TypeVariable/*!*/ v in unmentionedParameters) {
              Contract.Assert(v != null);
              if (!freeVars[v])
                tc.Error(tr,
                         "trigger does not mention {0}, which does not occur in variables types either",
                         v);
            }
          }
        }
      }
    }
    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Type.Bool;
      }
    }

  }


  public class LambdaExpr : BinderExpr {
    public LambdaExpr(IToken/*!*/ tok, List<TypeVariable>/*!*/ typeParameters,
                      List<Variable>/*!*/ dummies, QKeyValue kv, Expr/*!*/ body)
      : base(tok, typeParameters, dummies, kv, body) {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParameters.Count > 0);
    }

    public override BinderKind Kind {
      get {
        return BinderKind.Lambda;
      }
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      base.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        kv.Typecheck(tc);
      }
      Body.Typecheck(tc);
      Contract.Assert(Body.Type != null);  // follows from postcondition of Expr.Typecheck

      List<Type>/*!*/ argTypes = new List<Type>();
      foreach (Variable/*!*/ v in Dummies) {
        Contract.Assert(v != null);
        argTypes.Add(v.TypedIdent.Type);
      }
      this.Type = new MapType(this.tok, this.TypeParameters, argTypes, Body.Type);

      // Check that type parameters occur in the types of the
      // dummies, or otherwise in the triggers. This can only be
      // done after typechecking
      List<TypeVariable>/*!*/ unmentionedParameters = GetUnmentionedTypeParameters();
      Contract.Assert(unmentionedParameters != null);

      if (unmentionedParameters.Count > 0) {
        tc.Error(this, "the type variable {0} does not occur in types of the lambda parameters", unmentionedParameters[0]);
      }
    }

    private Type mapType;
    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        if (mapType == null) {
          List<Type>/*!*/ argTypes = new List<Type>();
          foreach (Variable/*!*/ v in Dummies) {
            Contract.Assert(v != null);
            argTypes.Add(v.TypedIdent.Type);
          }
          mapType = new MapType(this.tok, this.TypeParameters, argTypes, Body.ShallowType);
        }

        return mapType;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitLambdaExpr(this);
    }

  }
}