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
  using Microsoft.Boogie.AbstractInterpretation;
  using AI = Microsoft.AbstractInterpretationFramework;
  using System.Diagnostics.Contracts;
  using Microsoft.Basetypes;


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

    public override Microsoft.AbstractInterpretationFramework.IFunctionSymbol FunctionSymbol {
      get {
        Contract.Ensures(Contract.Result<AI.IFunctionSymbol>() != null);
        throw new NotImplementedException();
      }
    }

    public override Type ShallowType {
      get {
        throw new NotImplementedException();
      }
    }

    public override Microsoft.AbstractInterpretationFramework.IExpr IExpr {
      get {
        throw new NotImplementedException();
      }
    }
  }
  [ContractClass(typeof(BinderExprContracts))]
  public abstract class BinderExpr : Expr {
    public TypeVariableSeq/*!*/ TypeParameters;
    public VariableSeq/*!*/ Dummies;
    public QKeyValue Attributes;
    public Expr/*!*/ Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TypeParameters != null);
      Contract.Invariant(Dummies != null);
      Contract.Invariant(Body != null);
    }


    public BinderExpr(IToken/*!*/ tok, TypeVariableSeq/*!*/ typeParameters,
                      VariableSeq/*!*/ dummies, QKeyValue kv, Expr/*!*/ body)
      : base(tok)//BASEMOVEA
      {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Length + typeParameters.Length > 0);
      //base(tok);
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
      this.Dummies.Emit(stream);
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
        this.TypeParameters = Type.SortTypeParams(TypeParameters, Dummies.ToTypeSeq, null);

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

    protected TypeVariableSeq GetUnmentionedTypeParameters() {
      Contract.Ensures(Contract.Result<TypeVariableSeq>() != null);
      TypeVariableSeq/*!*/ dummyParameters = Type.FreeVariablesIn(Dummies.ToTypeSeq);
      Contract.Assert(dummyParameters != null);
      TypeVariableSeq/*!*/ unmentionedParameters = new TypeVariableSeq();
      foreach (TypeVariable/*!*/ var in TypeParameters) {
        Contract.Assert(var != null);
        if (!dummyParameters.Has(var))
          unmentionedParameters.Add(var);
      }
      return unmentionedParameters;
    }


    public abstract AI.IFunctionSymbol/*!*/ FunctionSymbol {
      get;
    }

    internal sealed class AIQuantifier : AI.IFunApp {
      internal readonly AIFunctionRep/*!*/ arg;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(arg != null);
      }

      internal AIQuantifier(BinderExpr/*!*/ realQuantifier, int dummyIndex)
        : this(new AIFunctionRep(realQuantifier, dummyIndex)) {
        Contract.Requires(realQuantifier != null);
      }
      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object obj) {
        if (obj == null)
          return false;
        if (!(obj is AIQuantifier))
          return false;

        AIQuantifier other = (AIQuantifier)obj;
        return object.Equals(this.arg, other.arg);
      }
      [Pure]
      public override int GetHashCode() {
        return this.arg.GetHashCode();
      }

      private AIQuantifier(AIFunctionRep arg) {
        Contract.Requires(arg != null);
        this.arg = arg;
        // base();
      }

      [Pure]
      public object DoVisit(AI.ExprVisitor visitor) {
        //Contract.Requires(visitor != null);
        return visitor.VisitFunApp(this);
      }

      public AI.IFunctionSymbol/*!*/ FunctionSymbol {
        get {
          Contract.Ensures(Contract.Result<AI.IFunctionSymbol>() != null);
          return arg.RealQuantifier.FunctionSymbol;
        }
      }

      private IList/*?*/ argCache = null;
      public IList/*<IExpr!>*//*!*/ Arguments {

        get {
          Contract.Ensures(Contract.Result<IList>() != null);

          if (argCache == null) {
            IList a = new ArrayList(1);
            a.Add(arg);
            argCache = ArrayList.ReadOnly(a);
          }
          return argCache;
        }
      }

      public AI.IFunApp CloneWithArguments(IList/*<IExpr!>*/ args) {
        //Contract.Requires(args != null);
        Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
        Contract.Assume(args.Count == 1);

        AIFunctionRep rep = args[0] as AIFunctionRep;
        if (rep != null)
          return new AIQuantifier(rep);
        else
          throw new System.NotImplementedException();
      }

      [Pure]
      public override string ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        return string.Format("{0}({1})", FunctionSymbol, arg);
      }
    }

    internal sealed class AIFunctionRep : AI.IFunction {
      internal readonly BinderExpr/*!*/ RealQuantifier;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(RealQuantifier != null);
      }

      private readonly int dummyIndex;

      internal AIFunctionRep(BinderExpr realQuantifier, int dummyIndex) {
        Contract.Requires(realQuantifier != null);
        this.RealQuantifier = realQuantifier;
        this.dummyIndex = dummyIndex;
        Contract.Assert(realQuantifier.TypeParameters.Length == 0); // PR: don't know how to handle this yet
        // base();
      }
      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object obj) {
        if (obj == null)
          return false;
        if (!(obj is AIFunctionRep))
          return false;

        AIFunctionRep other = (AIFunctionRep)obj;
        return object.Equals(this.RealQuantifier, other.RealQuantifier) && this.dummyIndex == other.dummyIndex;
      }
      [Pure]
      public override int GetHashCode() {
        return this.RealQuantifier.GetHashCode() ^ dummyIndex;
      }

      [Pure]
      public object DoVisit(AI.ExprVisitor visitor) {
        //Contract.Requires(visitor != null);
        return visitor.VisitFunction(this);
      }

      public AI.IVariable/*!*/ Param {

        get {
          Contract.Ensures(Contract.Result<AI.IVariable>() != null);
          return cce.NonNull(RealQuantifier.Dummies[dummyIndex]);
        }
      }
      public AI.AIType/*!*/ ParamType {
        get {
          Contract.Ensures(Contract.Result<AI.AIType>() != null);
          throw new System.NotImplementedException();
        }
      }

      // We lazily convert to 1 dummy per quantifier representation for AIFramework
      private AI.IExpr/*?*/ bodyCache = null;
      public AI.IExpr/*!*/ Body {
        get {
          Contract.Ensures(Contract.Result<AI.IExpr>() != null);

          if (bodyCache == null) {
            int dummyi = dummyIndex;
            int dummylen = RealQuantifier.Dummies.Length;
            Contract.Assume(dummylen > dummyi);

            // return the actual body if there are no more dummies
            if (dummyi + 1 == dummylen)
              bodyCache = RealQuantifier.Body.IExpr;
            else {
              AIQuantifier innerquant = new AIQuantifier(RealQuantifier, dummyi + 1);
              bodyCache = innerquant;
            }
          }
          return bodyCache;
        }
      }
      public AI.IFunction CloneWithBody(AI.IExpr body) {
        //Contract.Requires(body != null);
        Contract.Ensures(Contract.Result<AI.IFunction>() != null);
        BinderExpr realquant;

        AIQuantifier innerquant = body as AIQuantifier;
        if (innerquant == null) {
          // new quantifier body, clone the real quantifier
          realquant = (BinderExpr)RealQuantifier.Clone();
          realquant.Body = BoogieFactory.IExpr2Expr(body);
        } else {
          if (innerquant.arg.dummyIndex > 0) {
            realquant = innerquant.arg.RealQuantifier;
          } else {
            realquant = (BinderExpr)RealQuantifier.Clone();
            VariableSeq/*!*/ newdummies = new VariableSeq();
            newdummies.Add(Param);
            newdummies.AddRange(innerquant.arg.RealQuantifier.Dummies);
            realquant.Dummies = newdummies;
            realquant.Body = innerquant.arg.RealQuantifier.Body;
          }
        }

        return new AIFunctionRep(realquant, dummyIndex);
      }
      [Pure]
      public override string ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        return string.Format("\\{0} :: {1}", Param, Body);
      }
    }

    private AI.IExpr aiexprCache = null;
    public override AI.IExpr/*!*/ IExpr {
      get {
        Contract.Ensures(Contract.Result<AI.IExpr>() != null);

        if (TypeParameters.Length > 0)
          return new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "anon", Type.Bool));
        if (aiexprCache == null) {
          aiexprCache = new AIQuantifier(this, 0);
        }
        return aiexprCache;
      }
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
      : base(tok) {//BASEMOVEA
      Contract.Requires(key != null);
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(parameters));
      //:base(tok);
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
  }

  public class Trigger : Absy {
    public readonly bool Pos;
    [Rep]
    public ExprSeq/*!*/ Tr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tr != null);
      Contract.Invariant(1 <= Tr.Length);
      Contract.Invariant(Pos || Tr.Length == 1);
    }


    public Trigger Next;

    public Trigger(IToken tok, bool pos, ExprSeq tr)
      : this(tok, pos, tr, null) {//BASEMOVEA
      Contract.Requires(tr != null);
      Contract.Requires(tok != null);
      Contract.Requires(1 <= tr.Length);
      Contract.Requires(pos || tr.Length == 1);
      //:this(tok, pos, tr, null);
    }

    public Trigger(IToken/*!*/ tok, bool pos, ExprSeq/*!*/ tr, Trigger next)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(tr != null);
      Contract.Requires(1 <= tr.Length);
      Contract.Requires(pos || tr.Length == 1);
      this.Pos = pos;
      this.Tr = tr;
      this.Next = next;
      // base(tok);
    }

    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      stream.SetToken(this);
      Contract.Assert(this.Tr.Length >= 1);
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
    public ForallExpr(IToken/*!*/ tok, TypeVariableSeq/*!*/ typeParams,
                      VariableSeq/*!*/ dummies, QKeyValue kv, Trigger triggers, Expr/*!*/ body)
      : base(tok, typeParams, dummies, kv, triggers, body) {//BASEMOVEA
      Contract.Requires(tok != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Length + typeParams.Length > 0);
      //:base(tok, typeParams, dummies, kv, triggers, body); // here for aesthetic reasons
    }
    public ForallExpr(IToken tok, VariableSeq dummies, Trigger triggers, Expr body)
      : base(tok, new TypeVariableSeq(), dummies, null, triggers, body) {//BASEMOVEA
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Length > 0);
      //:base(tok, new TypeVariableSeq(), dummies, null, triggers, body); // here for aesthetic reasons
    }
    public ForallExpr(IToken tok, VariableSeq dummies, Expr body)
      : base(tok, new TypeVariableSeq(), dummies, null, null, body) {//BASEMOVEA
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Length > 0);
      //:base(tok, new TypeVariableSeq(), dummies, null, null, body); // here for aesthetic reasons
    }
    public ForallExpr(IToken tok, TypeVariableSeq typeParams, VariableSeq dummies, Expr body)
      : base(tok, typeParams, dummies, null, null, body) {//BASEMOVEA
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Length + typeParams.Length > 0);
      //:base(tok, typeParams, dummies, null, null, body); // here for aesthetic reasons
    }
    public override AI.IFunctionSymbol/*!*/ FunctionSymbol {
      get {
        Contract.Ensures(Contract.Result<AI.IFunctionSymbol>() != null);

        return AI.Prop.Forall;
      }
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
    public ExistsExpr(IToken/*!*/ tok, TypeVariableSeq/*!*/ typeParams, VariableSeq/*!*/ dummies,
                      QKeyValue kv, Trigger triggers, Expr/*!*/ body)
      : base(tok, typeParams, dummies, kv, triggers, body) {//BASEMOVEA
      Contract.Requires(tok != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Length + typeParams.Length > 0);
      //:base(tok, typeParams, dummies, kv, triggers, body); // here for aesthetic reasons
    }
    public ExistsExpr(IToken tok, VariableSeq dummies, Trigger triggers, Expr body)
      : base(tok, new TypeVariableSeq(), dummies, null, triggers, body) {//BASEMOVEA
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Length > 0);
      //:base(tok, new TypeVariableSeq(), dummies, null, triggers, body); // here for aesthetic reasons
    }
    public ExistsExpr(IToken tok, VariableSeq dummies, Expr body)
      : base(tok, new TypeVariableSeq(), dummies, null, null, body) {//BASEMOVEA
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Length > 0);
      //:base(tok, new TypeVariableSeq(), dummies, null, null, body); // here for aesthetic reasons
    }
    public override AI.IFunctionSymbol/*!*/ FunctionSymbol {
      get {
        Contract.Ensures(Contract.Result<AI.IFunctionSymbol>() != null);

        return AI.Prop.Exists;
      }
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

    public QuantifierExpr(IToken/*!*/ tok, TypeVariableSeq/*!*/ typeParameters,
                          VariableSeq/*!*/ dummies, QKeyValue kv, Trigger triggers, Expr/*!*/ body)
      : base(tok, typeParameters, dummies, kv, body) {//BASEMOVEA
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Length + typeParameters.Length > 0);
      //:base(tok, typeParameters, dummies, kv, body);

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
          parent.Triggers = new Trigger(fn.Func.tok, false, new ExprSeq(node), parent.Triggers);
        }
        return base.VisitNAryExpr(node);
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
      TypeVariableSeq/*!*/ unmentionedParameters = GetUnmentionedTypeParameters();
      Contract.Assert(unmentionedParameters != null);

      if (unmentionedParameters.Length > 0) {
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
    public LambdaExpr(IToken/*!*/ tok, TypeVariableSeq/*!*/ typeParameters,
                      VariableSeq/*!*/ dummies, QKeyValue kv, Expr/*!*/ body)
      : base(tok, typeParameters, dummies, kv, body) {//BASEMOVEA
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Length + typeParameters.Length > 0);
      //:base(tok, typeParameters, dummies, kv, body);
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

      TypeSeq/*!*/ argTypes = new TypeSeq();
      foreach (Variable/*!*/ v in Dummies) {
        Contract.Assert(v != null);
        argTypes.Add(v.TypedIdent.Type);
      }
      this.Type = new MapType(this.tok, this.TypeParameters, argTypes, Body.Type);

      // Check that type parameters occur in the types of the
      // dummies, or otherwise in the triggers. This can only be
      // done after typechecking
      TypeVariableSeq/*!*/ unmentionedParameters = GetUnmentionedTypeParameters();
      Contract.Assert(unmentionedParameters != null);

      if (unmentionedParameters.Length > 0) {
        tc.Error(this, "the type variable {0} does not occur in types of the lambda parameters", unmentionedParameters[0]);
      }
    }

    private Type mapType;
    public override Type/*!*/ ShallowType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        if (mapType == null) {
          TypeSeq/*!*/ argTypes = new TypeSeq();
          foreach (Variable/*!*/ v in Dummies) {
            Contract.Assert(v != null);
            argTypes.Add(v.TypedIdent.Type);
          }
          mapType = new MapType(this.tok, this.TypeParameters, argTypes, Body.ShallowType);
        }

        return mapType;
      }
    }

    public override AI.IFunctionSymbol/*!*/ FunctionSymbol {

      get {
        Contract.Ensures(Contract.Result<AI.IFunctionSymbol>() != null);

        return AI.Prop.Lambda;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitLambdaExpr(this);
    }

  }
}