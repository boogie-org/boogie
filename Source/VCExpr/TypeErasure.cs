//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

// different classes for erasing complex types in VCExprs, replacing them
// with axioms that can be handled by theorem provers and SMT solvers

namespace Microsoft.Boogie.TypeErasure {
  using Microsoft.Boogie.VCExprAST;

  // some functionality that is needed in many places (and that should
  // really be provided by the Spec# container classes; maybe one
  // could integrate the functions in a nicer way?)
  public class HelperFuns {

    public static Function BoogieFunction(string name, List<TypeVariable/*!*/>/*!*/ typeParams, params Type[] types) {
      Contract.Requires(types != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeParams));
      Contract.Requires(types.Length > 0);
      Contract.Requires(Contract.ForAll(0, types.Length, i => types[i] != null));
      Contract.Ensures(Contract.Result<Function>() != null);

      List<Variable> args = new List<Variable>();
      for (int i = 0; i < types.Length - 1; ++i)
        args.Add(new Formal(Token.NoToken,
                             new TypedIdent(Token.NoToken, "arg" + i, cce.NonNull(types[i])),
                             true));
      Formal result = new Formal(Token.NoToken,
                                   new TypedIdent(Token.NoToken, "res",
                                                   cce.NonNull(types)[types.Length - 1]),
                                   false);
      return new Function(Token.NoToken, name, new List<TypeVariable>(typeParams), args, result);
    }

    public static Function BoogieFunction(string name, params Type[] types) {
      Contract.Requires(types != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return BoogieFunction(name, new List<TypeVariable/*!*/>(), types);
    }

    // boogie function where all arguments and the result have the same type U
    public static Function UniformBoogieFunction(string name, int arity, Type U) {
      Contract.Requires(U != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      Type[]/*!*/ types = new Type[arity + 1];
      for (int i = 0; i < arity + 1; ++i)
        types[i] = U;
      return BoogieFunction(name, types);
    }

    public static List<VCExprVar/*!*/>/*!*/ GenVarsForInParams(Function fun, VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      Contract.Requires(fun != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      List<VCExprVar/*!*/>/*!*/ arguments = new List<VCExprVar/*!*/>(fun.InParams.Count);
      foreach (Formal/*!*/ f in fun.InParams) {
        Contract.Assert(f != null);
        VCExprVar/*!*/ var = gen.Variable(f.Name, f.TypedIdent.Type);
        arguments.Add(var);
      }
      return arguments;
    }

    public static List<T/*!*/>/*!*/ ToList<T>(params T[] args) where T : class{
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<T>>()));
      return new List<T>(args);
    }

    public static List<VCExpr/*!*/>/*!*/ ToVCExprList(List<VCExprVar/*!*/>/*!*/ list) {
      Contract.Requires(cce.NonNullElements(list));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      return new List<VCExpr>(list);
    }

    public static List<VCExprVar/*!*/>/*!*/ VarVector(string baseName, int num, Type type, VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      Contract.Requires(type != null);
      Contract.Requires(baseName != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      List<VCExprVar/*!*/>/*!*/ res = new List<VCExprVar/*!*/>(num);
      for (int i = 0; i < num; ++i)
        res.Add(gen.Variable(baseName + i, type));
      return res;
    }

    public static List<VCExprVar/*!*/>/*!*/ VarVector(string baseName, List<Type/*!*/>/*!*/ types, VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      Contract.Requires(baseName != null);
      Contract.Requires(cce.NonNullElements(types));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      List<VCExprVar/*!*/>/*!*/ res = new List<VCExprVar/*!*/>(types.Count);
      for (int i = 0; i < types.Count; ++i)
        res.Add(gen.Variable(baseName + i, types[i]));
      return res;
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  internal struct TypeCtorRepr {
    // function that represents the application of the type constructor
    // to smaller types
    public readonly Function/*!*/ Ctor;
    // left-inverse functions that extract the subtypes of a compound type
    public readonly List<Function/*!*/>/*!*/ Dtors;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Ctor != null);
      Contract.Invariant(cce.NonNullElements(Dtors));
    }


    public TypeCtorRepr(Function ctor, List<Function/*!*/>/*!*/ dtors) {
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(dtors));
      Contract.Requires(ctor.InParams.Count == dtors.Count);
      this.Ctor = ctor;
      this.Dtors = dtors;
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // The class responsible for creating and keeping track of all
  // axioms related to the type system. This abstract class is made
  // concrete in two subclasses, one for type erasure with type
  // premisses in quantifiers (the semantic approach), and one for
  // type erasure with explicit type arguments of polymorphic
  // functions (the syntacted approach).
  [ContractClass(typeof(TypeAxiomBuilderContracts))]
  public abstract class TypeAxiomBuilder : ICloneable {

    protected readonly VCExpressionGenerator/*!*/ Gen;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Gen != null);
      Contract.Invariant(Ctor != null);

    }


    internal abstract MapTypeAbstractionBuilder/*!*/ MapTypeAbstracter {
      get;
    }

    ///////////////////////////////////////////////////////////////////////////
    // Type Axioms

    // list in which all typed axioms are collected
    private readonly List<VCExpr/*!*/>/*!*/ AllTypeAxioms;
    [ContractInvariantMethod]
    void AllTypeAxiomsInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(AllTypeAxioms));
    }

    // list in which type axioms are incrementally collected
    private readonly List<VCExpr/*!*/>/*!*/ IncTypeAxioms;
    [ContractInvariantMethod]
    void IncTypeAxiomsInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(IncTypeAxioms));
    }

    internal void AddTypeAxiom(VCExpr axiom) {
      Contract.Requires(axiom != null);
      AllTypeAxioms.Add(axiom);
      IncTypeAxioms.Add(axiom);
    }

    // Return all axioms that were added since the last time NewAxioms
    // was called
    public VCExpr GetNewAxioms() {
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr/*!*/ res = Gen.NAry(VCExpressionGenerator.AndOp, IncTypeAxioms);
      IncTypeAxioms.Clear();
      return res;
    }

    // mapping from a type to its constructor number/index
    private readonly Function/*!*/ Ctor;
    private BigNum CurrentCtorNum;

    private VCExpr GenCtorAssignment(VCExpr typeRepr) {
      Contract.Requires(typeRepr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (CommandLineOptions.Clo.TypeEncodingMethod
                == CommandLineOptions.TypeEncoding.None)
        return VCExpressionGenerator.True;

      VCExpr res = Gen.Eq(Gen.Function(Ctor, typeRepr),
                           Gen.Integer(CurrentCtorNum));
      CurrentCtorNum = CurrentCtorNum + BigNum.ONE;
      return res;
    }

    private VCExpr GenCtorAssignment(Function typeRepr) {
      Contract.Requires(typeRepr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (CommandLineOptions.Clo.TypeEncodingMethod
                == CommandLineOptions.TypeEncoding.None)
        return VCExpressionGenerator.True;

      List<VCExprVar/*!*/>/*!*/ quantifiedVars = HelperFuns.GenVarsForInParams(typeRepr, Gen);
      VCExpr/*!*/ eq =
        GenCtorAssignment(Gen.Function(typeRepr,
                                       HelperFuns.ToVCExprList(quantifiedVars)));

      if (typeRepr.InParams.Count == 0)
        return eq;

      return Gen.Forall(quantifiedVars, new List<VCTrigger/*!*/>(),
                        "ctor:" + typeRepr.Name, -1, eq);
    }

    // generate an axiom (forall x0, x1, ... :: invFun(fun(x0, x1, ...) == xi)
    protected VCExpr GenLeftInverseAxiom(Function fun, Function invFun, int dtorNum) {
      Contract.Requires(invFun != null);
      Contract.Requires(fun != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      List<VCExprVar/*!*/>/*!*/ quantifiedVars = HelperFuns.GenVarsForInParams(fun, Gen);
      Contract.Assert(cce.NonNullElements(quantifiedVars));

      VCExpr/*!*/ funApp = Gen.Function(fun, HelperFuns.ToVCExprList(quantifiedVars));
      VCExpr/*!*/ lhs = Gen.Function(invFun, funApp);
      VCExpr/*!*/ rhs = quantifiedVars[dtorNum];
      VCExpr/*!*/ eq = Gen.Eq(lhs, rhs);

      List<VCTrigger/*!*/>/*!*/ triggers = HelperFuns.ToList(Gen.Trigger(true, HelperFuns.ToList(funApp)));
      Contract.Assert(cce.NonNullElements(triggers));
      return Gen.Forall(quantifiedVars, triggers, "typeInv:" + invFun.Name, -1, eq);
    }

    ///////////////////////////////////////////////////////////////////////////

    // the type of everything that is not int, bool, or a type
    [ContractInvariantMethod]
    void ObjectInvariant2() {
      Contract.Invariant(UDecl != null);
      Contract.Invariant(TDecl != null);
      Contract.Invariant(U != null);
      Contract.Invariant(T != null);
    }

    private readonly TypeCtorDecl/*!*/ UDecl;
    public readonly Type/*!*/ U;

    // the type of types
    private readonly TypeCtorDecl/*!*/ TDecl;
    public readonly Type/*!*/ T;

    public abstract Type/*!*/ TypeAfterErasure(Type/*!*/ type);
    [Pure]
    public abstract bool UnchangedType(Type/*!*/ type);

    ///////////////////////////////////////////////////////////////////////////
    // Symbols for representing types

    private readonly IDictionary<Type/*!*/, VCExpr/*!*/>/*!*/ BasicTypeReprs;
    [ContractInvariantMethod]
    void BasicTypeReprsInvariantMethod() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(BasicTypeReprs));
    }

    private VCExpr GetBasicTypeRepr(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(type.IsBasic || type.IsBv || type.IsFloat);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr res;
      if (!BasicTypeReprs.TryGetValue(type, out res)) {
        res = Gen.Function(HelperFuns.BoogieFunction(type.ToString() + "Type", T));
        AddTypeAxiom(GenCtorAssignment(res));
        BasicTypeReprs.Add(type, res);
      }
      return cce.NonNull(res);
    }

    private readonly IDictionary<TypeCtorDecl/*!*/, TypeCtorRepr/*!*/>/*!*/ TypeCtorReprs;
    [ContractInvariantMethod]
    void TypeCtorReprsInvariantMethod() {
      Contract.Invariant(TypeCtorReprs != null);
    }

    internal TypeCtorRepr GetTypeCtorReprStruct(TypeCtorDecl decl) {
      Contract.Requires(decl != null);
      TypeCtorRepr reprSet;
      if (!TypeCtorReprs.TryGetValue(decl, out reprSet)) {
        Function/*!*/ ctor = HelperFuns.UniformBoogieFunction(decl.Name + "Type", decl.Arity, T);
        Contract.Assert(ctor != null);
        AddTypeAxiom(GenCtorAssignment(ctor));

        List<Function/*!*/>/*!*/ dtors = new List<Function/*!*/>(decl.Arity);
        for (int i = 0; i < decl.Arity; ++i) {
          Function/*!*/ dtor = HelperFuns.UniformBoogieFunction(decl.Name + "TypeInv" + i, 1, T);
          dtors.Add(dtor);
          AddTypeAxiom(GenLeftInverseAxiom(ctor, dtor, i));
        }

        reprSet = new TypeCtorRepr(ctor, dtors);
        TypeCtorReprs.Add(decl, reprSet);
      }

      return reprSet;
    }

    public Function GetTypeCtorRepr(TypeCtorDecl decl) {
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return GetTypeCtorReprStruct(decl).Ctor;
    }

    public Function GetTypeDtor(TypeCtorDecl decl, int num) {
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return GetTypeCtorReprStruct(decl).Dtors[num];
    }

    // mapping from free type variables to VCExpr variables
    private readonly IDictionary<TypeVariable/*!*/, VCExprVar/*!*/>/*!*/ TypeVariableMapping;
    [ContractInvariantMethod]
    void TypeVariableMappingInvariantMethod() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(TypeVariableMapping));
    }

    public VCExprVar Typed2Untyped(TypeVariable var) {
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<VCExprVar>() != null);
      VCExprVar res;
      if (!TypeVariableMapping.TryGetValue(var, out res)) {
        res = new VCExprVar(var.Name, T);
        TypeVariableMapping.Add(var, res);
      }
      return cce.NonNull(res);
    }


    ////////////////////////////////////////////////////////////////////////////
    // Symbols for representing variables and constants

    // Globally defined variables
    private readonly IDictionary<VCExprVar/*!*/, VCExprVar/*!*/>/*!*/ Typed2UntypedVariables;
    [ContractInvariantMethod]
    void Typed2UntypedVariablesInvariantMethod() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(Typed2UntypedVariables));
    }

    // This method must only be used for free (unbound) variables
    public VCExprVar Typed2Untyped(VCExprVar var) {
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<VCExprVar>() != null);
      VCExprVar res = TryTyped2Untyped(var);
      if (res == null) {
        res = Gen.Variable(var.Name, TypeAfterErasure(var.Type));
        Typed2UntypedVariables.Add(var, res);
        AddVarTypeAxiom(res, var.Type);
      }
      return cce.NonNull(res);
    }

    /// <summary>
    ///  This method is like Typed2Untyped, except in the case where the given variables
    ///  doesn't exist in the mapping.  For that case, this method returns null whereas
    ///  Typed2Untyped creates a new variable that it adds to the mapping.
    /// </summary>
    /// <param name="var"></param>
    /// <returns></returns>
    public VCExprVar TryTyped2Untyped(VCExprVar var) {
      Contract.Requires(var != null);
      VCExprVar res;
      if (Typed2UntypedVariables.TryGetValue(var, out res)) {
        return res;
      } else {
        return null;
      }
    }

    protected abstract void AddVarTypeAxiom(VCExprVar/*!*/ var, Type/*!*/ originalType);

    ///////////////////////////////////////////////////////////////////////////
    // Translation function from types to their term representation

    public VCExpr Type2Term(Type type, IDictionary<TypeVariable/*!*/, VCExpr/*!*/>/*!*/ varMapping) {
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(varMapping));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      //
      if (type.IsBasic || type.IsBv || type.IsFloat) {
        //
        return GetBasicTypeRepr(type);
        //
      } else if (type.IsCtor) {
        //
        CtorType ctype = type.AsCtor;
        Function/*!*/ repr = GetTypeCtorRepr(ctype.Decl);
        List<VCExpr/*!*/>/*!*/ args = new List<VCExpr/*!*/>(ctype.Arguments.Count);
        foreach (Type/*!*/ t in ctype.Arguments.ToArray()) {
          Contract.Assert(t != null);
          args.Add(Type2Term(t, varMapping));
        }
        return Gen.Function(repr, args);
        //
      } else if (type.IsVariable) {
        //
        VCExpr res;
        if (!varMapping.TryGetValue(type.AsVariable, out res))
          // then the variable is free and we bind it at this point to a term
          // variable
          res = Typed2Untyped(type.AsVariable);
        return cce.NonNull(res);
        //
      } else if (type.IsMap) {
        //
        return Type2Term(MapTypeAbstracter.AbstractMapType(type.AsMap), varMapping);
        //
      } else {
        System.Diagnostics.Debug.Fail("Don't know how to handle this type: " + type);
        Contract.Assert(false);
        throw new cce.UnreachableException();  // please the compiler
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    public TypeAxiomBuilder(VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      this.Gen = gen;
      AllTypeAxioms = new List<VCExpr/*!*/>();
      IncTypeAxioms = new List<VCExpr/*!*/>();
      BasicTypeReprs = new Dictionary<Type/*!*/, VCExpr/*!*/>();
      CurrentCtorNum = BigNum.ZERO;
      TypeCtorReprs = new Dictionary<TypeCtorDecl/*!*/, TypeCtorRepr>();
      TypeVariableMapping = new Dictionary<TypeVariable/*!*/, VCExprVar/*!*/>();
      Typed2UntypedVariables = new Dictionary<VCExprVar/*!*/, VCExprVar/*!*/>();

      TypeCtorDecl/*!*/ uDecl = new TypeCtorDecl(Token.NoToken, "U", 0);
      UDecl = uDecl;
      Type/*!*/ u = new CtorType(Token.NoToken, uDecl, new List<Type>());
      U = u;

      TypeCtorDecl/*!*/ tDecl = new TypeCtorDecl(Token.NoToken, "T", 0);
      TDecl = tDecl;
      Type/*!*/ t = new CtorType(Token.NoToken, tDecl, new List<Type>());
      T = t;

      Ctor = HelperFuns.BoogieFunction("Ctor", t, Type.Int);
    }

    public virtual void Setup() {
      GetBasicTypeRepr(Type.Int);
      GetBasicTypeRepr(Type.Real);
      GetBasicTypeRepr(Type.Bool);
      GetBasicTypeRepr(Type.RMode);
    }

    // constructor to allow cloning
    internal TypeAxiomBuilder(TypeAxiomBuilder builder) {
      Contract.Requires(builder != null);
      Gen = builder.Gen;
      AllTypeAxioms = new List<VCExpr/*!*/>(builder.AllTypeAxioms);
      IncTypeAxioms = new List<VCExpr/*!*/>(builder.IncTypeAxioms);

      UDecl = builder.UDecl;
      U = builder.U;

      TDecl = builder.TDecl;
      T = builder.T;

      Ctor = builder.Ctor;
      CurrentCtorNum = builder.CurrentCtorNum;

      BasicTypeReprs = new Dictionary<Type/*!*/, VCExpr/*!*/>(builder.BasicTypeReprs);
      TypeCtorReprs = new Dictionary<TypeCtorDecl/*!*/, TypeCtorRepr>(builder.TypeCtorReprs);

      TypeVariableMapping =
        new Dictionary<TypeVariable/*!*/, VCExprVar/*!*/>(builder.TypeVariableMapping);
      Typed2UntypedVariables =
        new Dictionary<VCExprVar/*!*/, VCExprVar/*!*/>(builder.Typed2UntypedVariables);
    }

    public abstract Object/*!*/ Clone();
  }

  [ContractClassFor(typeof(TypeAxiomBuilder))]
  public abstract class TypeAxiomBuilderContracts : TypeAxiomBuilder {
    public TypeAxiomBuilderContracts()
      : base((VCExpressionGenerator)null) {
    }
    internal override MapTypeAbstractionBuilder MapTypeAbstracter {
      get {
        Contract.Ensures(Contract.Result<MapTypeAbstractionBuilder>() != null);
        throw new NotImplementedException();
      }
    }

    public override Type TypeAfterErasure(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public override bool UnchangedType(Type type) {
      Contract.Requires(type != null);
      throw new NotImplementedException();
    }

    protected override void AddVarTypeAxiom(VCExprVar var, Type originalType) {
      Contract.Requires(var != null);
      Contract.Requires(originalType != null);
      throw new NotImplementedException();
    }

    public override object Clone() {
      Contract.Ensures(Contract.Result<object>() != null);

      throw new NotImplementedException();
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // Subclass of the TypeAxiomBuilder that provides all functionality
  // to deal with native sorts of a theorem prover (that are the only
  // types left after erasing all other types). Currently, these are:
  //
  //  U ... sort of all individuals/objects/values
  //  T ... sort of all types
  //  int ... integers
  //  bool ... booleans

  [ContractClass(typeof(TypeAxiomBuilderIntBoolUContracts))]
  public abstract class TypeAxiomBuilderIntBoolU : TypeAxiomBuilder {

    public TypeAxiomBuilderIntBoolU(VCExpressionGenerator gen)
      : base(gen) {
      Contract.Requires(gen != null);

      TypeCasts = new Dictionary<Type/*!*/, TypeCastSet>();
    }

    // constructor to allow cloning
    internal TypeAxiomBuilderIntBoolU(TypeAxiomBuilderIntBoolU builder)
      : base(builder) {
      Contract.Requires(builder != null);

      TypeCasts = new Dictionary<Type/*!*/, TypeCastSet>(builder.TypeCasts);
    }

    public override void Setup() {
      base.Setup();

      GetTypeCasts(Type.Int);
      GetTypeCasts(Type.Real);
      GetTypeCasts(Type.Bool);
      GetTypeCasts(Type.RMode);

    }

    // generate inverse axioms for casts (castToU(castFromU(x)) = x, under certain premisses)
    protected abstract VCExpr/*!*/ GenReverseCastAxiom(Function/*!*/ castToU, Function/*!*/ castFromU);

    protected VCExpr GenReverseCastEq(Function castToU, Function castFromU, out VCExprVar var, out List<VCTrigger/*!*/>/*!*/ triggers) {
      Contract.Requires((castFromU != null));
      Contract.Requires((castToU != null));
      Contract.Ensures((cce.NonNullElements(Contract.ValueAtReturn(out triggers))));
      Contract.Ensures(Contract.ValueAtReturn(out var) != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      var = Gen.Variable("x", U);

      VCExpr inner = Gen.Function(castFromU, var);
      VCExpr lhs = Gen.Function(castToU, inner);
      triggers = HelperFuns.ToList(Gen.Trigger(true, HelperFuns.ToList(inner)));

      return Gen.Eq(lhs, var);
    }

    protected abstract VCExpr/*!*/ GenCastTypeAxioms(Function/*!*/ castToU, Function/*!*/ castFromU);

    ///////////////////////////////////////////////////////////////////////////
    // storage of type casts for types that are supposed to be left over in the
    // VCs (like int, bool, bitvectors)

    private readonly IDictionary<Type/*!*/, TypeCastSet/*!*/>/*!*/ TypeCasts;
    [ContractInvariantMethod]
    void TypeCastsInvariantMethod() {
      Contract.Invariant(TypeCasts != null);
    }

    private TypeCastSet GetTypeCasts(Type type) {
      Contract.Requires(type != null);
      TypeCastSet res;
      if (!TypeCasts.TryGetValue(type, out res)) {
        Function/*!*/ castToU = HelperFuns.BoogieFunction(type.ToString() + "_2_U", type, U);
        Function/*!*/ castFromU = HelperFuns.BoogieFunction("U_2_" + type.ToString(), U, type);

        AddTypeAxiom(GenLeftInverseAxiom(castToU, castFromU, 0));
        AddTypeAxiom(GenReverseCastAxiom(castToU, castFromU));
        AddTypeAxiom(GenCastTypeAxioms(castToU, castFromU));

        res = new TypeCastSet(castToU, castFromU);
        TypeCasts.Add(type, res);
      }
      return res;
    }
    [Pure]
    public Function CastTo(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(UnchangedType(type));
      Contract.Ensures(Contract.Result<Function>() != null);
      return GetTypeCasts(type).CastFromU;
    }

    public Function CastFrom(Type type) {
      Contract.Requires(type != null);
      Contract.Requires((UnchangedType(type)));
      Contract.Ensures(Contract.Result<Function>() != null);
      return GetTypeCasts(type).CastToU;
    }

    private struct TypeCastSet {
      public readonly Function/*!*/ CastToU;
      public readonly Function/*!*/ CastFromU;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(CastToU != null);
        Contract.Invariant(CastFromU != null);
      }


      public TypeCastSet(Function castToU, Function castFromU) {
        Contract.Requires(castFromU != null);
        Contract.Requires(castToU != null);
        CastToU = castToU;
        CastFromU = castFromU;
      }
    }

    public bool IsCast(Function fun) {
      Contract.Requires(fun != null);
      if (fun.InParams.Count != 1)
        return false;
      Type/*!*/ inType = cce.NonNull(fun.InParams[0]).TypedIdent.Type;
      if (inType.Equals(U)) {
        Type/*!*/ outType = cce.NonNull(fun.OutParams[0]).TypedIdent.Type;
        if (!TypeCasts.ContainsKey(outType))
          return false;
        return fun.Equals(CastTo(outType));
      } else {
        if (!TypeCasts.ContainsKey(inType))
          return false;
        Type/*!*/ outType = cce.NonNull(fun.OutParams[0]).TypedIdent.Type;
        if (!outType.Equals(U))
          return false;
        return fun.Equals(CastFrom(inType));
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    // the only types that we allow in "untyped" expressions are U,
    // Type.Int, Type.Real, Type.Bool, and Type.RMode

    public override Type TypeAfterErasure(Type type) {
      //Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      if (UnchangedType(type))
        // these types are kept
        return type;
      else
        // all other types are replaced by U
        return U;
    }

    [Pure]
    public override bool UnchangedType(Type type) {
      //Contract.Requires(type != null);
      return type.IsInt || type.IsReal || type.IsBool || type.IsBv || type.IsFloat || type.IsRMode || (type.IsMap && CommandLineOptions.Clo.MonomorphicArrays);
    }

    public VCExpr Cast(VCExpr expr, Type toType) {
      Contract.Requires(toType != null);
      Contract.Requires(expr != null);
      Contract.Requires((expr.Type.Equals(U) || UnchangedType(expr.Type)));
      Contract.Requires((toType.Equals(U) || UnchangedType(toType)));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (expr.Type.Equals(toType))
        return expr;

      if (toType.Equals(U)) {
        return Gen.Function(CastFrom(expr.Type), expr);
      } else {
        Contract.Assert(expr.Type.Equals(U));
        return Gen.Function(CastTo(toType), expr);
      }
    }

    public List<VCExpr/*!*/>/*!*/ CastSeq(List<VCExpr/*!*/>/*!*/ exprs, Type toType) {
      Contract.Requires(toType != null);
      Contract.Requires(cce.NonNullElements(exprs));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      List<VCExpr/*!*/>/*!*/ res = new List<VCExpr/*!*/>(exprs.Count);
      foreach (VCExpr/*!*/ expr in exprs) {
        Contract.Assert(expr != null);
        res.Add(Cast(expr, toType));
      }
      return res;
    }


  }

  [ContractClassFor(typeof(TypeAxiomBuilderIntBoolU))]
  public abstract class TypeAxiomBuilderIntBoolUContracts : TypeAxiomBuilderIntBoolU {
    public TypeAxiomBuilderIntBoolUContracts()
      : base((TypeAxiomBuilderIntBoolU)null) {
    }
    protected override VCExpr GenReverseCastAxiom(Function castToU, Function castFromU) {
      Contract.Requires(castToU != null);
      Contract.Requires(castFromU != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      throw new NotImplementedException();
    }

    protected override VCExpr GenCastTypeAxioms(Function castToU, Function castFromU) {
      Contract.Requires(castFromU != null);
      Contract.Requires(castToU != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      throw new NotImplementedException();
    }

    internal override MapTypeAbstractionBuilder MapTypeAbstracter {
      get {
        throw new NotImplementedException();
      }
    }

    protected override void AddVarTypeAxiom(VCExprVar var, Type originalType) {
      throw new NotImplementedException();
    }

    public override object Clone() {
      throw new NotImplementedException();
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Class for computing most general abstractions of map types. An abstraction
  // of a map type t is a maptype t' in which closed proper subtypes have been replaced
  // with type variables. E.g., an abstraction of <a>[C a, int]a would be <a>[C a, b]a.
  // We subsequently consider most general abstractions as ordinary parametrised types,
  // i.e., "<a>[C a, b]a" would be considered as a type "M b" with polymorphically typed
  // access functions
  //
  //            select<a,b>(M b, C a, b) returns (a)
  //            store<a,b>(M b, C a, b, a) returns (M b)
  [ContractClass(typeof(MapTypeAbstractionBuilderContracts))]
  internal abstract class MapTypeAbstractionBuilder {

    protected readonly TypeAxiomBuilder/*!*/ AxBuilder;
    protected readonly VCExpressionGenerator/*!*/ Gen;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(AxBuilder != null);
      Contract.Invariant(Gen != null);
    }


    internal MapTypeAbstractionBuilder(TypeAxiomBuilder axBuilder, VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      Contract.Requires(axBuilder != null);
      this.AxBuilder = axBuilder;
      this.Gen = gen;
      AbstractionVariables = new List<TypeVariable/*!*/>();
      ClassRepresentations = new Dictionary<MapType/*!*/, MapTypeClassRepresentation>();
    }

    // constructor for cloning
    internal MapTypeAbstractionBuilder(TypeAxiomBuilder axBuilder, VCExpressionGenerator gen, MapTypeAbstractionBuilder builder) {
      Contract.Requires(builder != null);
      Contract.Requires(gen != null);
      Contract.Requires(axBuilder != null);
      this.AxBuilder = axBuilder;
      this.Gen = gen;
      AbstractionVariables =
        new List<TypeVariable/*!*/>(builder.AbstractionVariables);
      ClassRepresentations =
        new Dictionary<MapType/*!*/, MapTypeClassRepresentation>(builder.ClassRepresentations);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Type variables used in the abstractions. We use the same variables in the
    // same order in all abstractions in order to obtain comparable abstractions
    // (equals, hashcode)

    private readonly List<TypeVariable/*!*/>/*!*/ AbstractionVariables;
    [ContractInvariantMethod]
    void AbstractionVariablesInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(AbstractionVariables));
    }

    private TypeVariable AbstractionVariable(int num) {
      Contract.Requires((num >= 0));
      Contract.Ensures(Contract.Result<TypeVariable>() != null);
      while (AbstractionVariables.Count <= num)
        AbstractionVariables.Add(new TypeVariable(Token.NoToken,
                                                   "aVar" + AbstractionVariables.Count));
      return AbstractionVariables[num];
    }

    ///////////////////////////////////////////////////////////////////////////
    // The untyped representation of a class of map types, i.e., of a map type
    // <a0, a1, ...>[A0, A1, ...] R, where the argument types and the result type
    // possibly contain free type variables. For each such class, a separate type
    // constructor and separate select/store functions are introduced.

    protected struct MapTypeClassRepresentation {
      public readonly TypeCtorDecl/*!*/ RepresentingType;
      public readonly Function/*!*/ Select;
      public readonly Function/*!*/ Store;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(RepresentingType != null);
        Contract.Invariant(Select != null);
        Contract.Invariant(Store != null);
      }


      public MapTypeClassRepresentation(TypeCtorDecl representingType, Function select, Function store) {
        Contract.Requires(store != null);
        Contract.Requires(select != null);
        Contract.Requires(representingType != null);
        this.RepresentingType = representingType;
        this.Select = select;
        this.Store = store;
      }
    }

    private readonly IDictionary<MapType/*!*/, MapTypeClassRepresentation/*!*/>/*!*/ ClassRepresentations;
    [ContractInvariantMethod]
    void ClassRepresentationsInvariantMethod() {
      Contract.Invariant(ClassRepresentations != null);
    }

    protected MapTypeClassRepresentation GetClassRepresentation(MapType abstractedType) {
      Contract.Requires(abstractedType != null);
      MapTypeClassRepresentation res;
      if (!ClassRepresentations.TryGetValue(abstractedType, out res)) {
        int num = ClassRepresentations.Count;
        TypeCtorDecl/*!*/ synonym =
          new TypeCtorDecl(Token.NoToken, "MapType" + num, abstractedType.FreeVariables.Count);

        Function/*!*/ select, store;
        GenSelectStoreFunctions(abstractedType, synonym, out select, out store);

        res = new MapTypeClassRepresentation(synonym, select, store);
        ClassRepresentations.Add(abstractedType, res);
      }
      return res;
    }

    // the actual select and store functions are generated by the
    // concrete subclasses of this class
    protected abstract void GenSelectStoreFunctions(MapType/*!*/ abstractedType, TypeCtorDecl/*!*/ synonymDecl, out Function/*!*/ select, out Function/*!*/ store);

    ///////////////////////////////////////////////////////////////////////////

    public Function Select(MapType rawType, out List<Type> instantiations) {
      Contract.Requires((rawType != null));
      Contract.Ensures(Contract.ValueAtReturn(out instantiations) != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return AbstractAndGetRepresentation(rawType, out instantiations).Select;
    }

    public Function Store(MapType rawType, out List<Type> instantiations) {
      Contract.Requires((rawType != null));
      Contract.Ensures(Contract.ValueAtReturn(out instantiations) != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return AbstractAndGetRepresentation(rawType, out instantiations).Store;
    }

    private MapTypeClassRepresentation
            AbstractAndGetRepresentation(MapType rawType, out List<Type> instantiations) {
      Contract.Requires((rawType != null));
      Contract.Ensures(Contract.ValueAtReturn(out instantiations) != null);
      instantiations = new List<Type>();
      MapType/*!*/ abstraction = ThinOutMapType(rawType, instantiations);
      return GetClassRepresentation(abstraction);
    }

    public CtorType AbstractMapType(MapType rawType) {
      Contract.Requires(rawType != null);
      Contract.Ensures(Contract.Result<CtorType>() != null);
      List<Type>/*!*/ instantiations = new List<Type>();
      MapType/*!*/ abstraction = ThinOutMapType(rawType, instantiations);

      MapTypeClassRepresentation repr = GetClassRepresentation(abstraction);
      Contract.Assume(repr.RepresentingType.Arity == instantiations.Count);
      return new CtorType(Token.NoToken, repr.RepresentingType, instantiations);
    }

    // TODO: cache the result of this operation
    protected MapType ThinOutMapType(MapType rawType, List<Type> instantiations) {
      Contract.Requires(instantiations != null);
      Contract.Requires(rawType != null);
      Contract.Ensures(Contract.Result<MapType>() != null);
      List<Type>/*!*/ newArguments = new List<Type>();
      foreach (Type/*!*/ subtype in rawType.Arguments.ToList()) {
        Contract.Assert(subtype != null);
        newArguments.Add(ThinOutType(subtype, rawType.TypeParameters,
                                     instantiations));
      }
      Type/*!*/ newResult = ThinOutType(rawType.Result, rawType.TypeParameters,
                                    instantiations);
      return new MapType(Token.NoToken, rawType.TypeParameters, newArguments, newResult);
    }

    // the instantiations of inserted type variables, the order corresponds to the order in which "AbstractionVariable(int)" delivers variables
    private Type/*!*/ ThinOutType(Type rawType, List<TypeVariable> boundTypeParams, List<Type> instantiations) {
      Contract.Requires(instantiations != null);
      Contract.Requires(boundTypeParams != null);
      Contract.Requires(rawType != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (CommandLineOptions.Clo.Monomorphize && AxBuilder.UnchangedType(rawType))
        return rawType;

      if (rawType.FreeVariables.All(var => !boundTypeParams.Contains(var))) {
        // Bingo!
        // if the type does not contain any bound variables, we can simply
        // replace it with a type variable
        TypeVariable/*!*/ abstractionVar = AbstractionVariable(instantiations.Count);
        Contract.Assume(!boundTypeParams.Contains(abstractionVar));
        instantiations.Add(rawType);
        return abstractionVar;
      }

      if (rawType.IsVariable) {
        //
        // then the variable has to be bound, we cannot do anything
        TypeVariable/*!*/ rawVar = rawType.AsVariable;
        Contract.Assume(boundTypeParams.Contains(rawVar));
        return rawVar;
        //
      } else if (rawType.IsMap) {
        //
        // recursively abstract this map type and continue abstracting
        CtorType/*!*/ abstraction = AbstractMapType(rawType.AsMap);
        return ThinOutType(abstraction, boundTypeParams, instantiations);
        //
      } else if (rawType.IsCtor) {
        //
        // traverse the subtypes
        CtorType/*!*/ rawCtorType = rawType.AsCtor;
        List<Type>/*!*/ newArguments = new List<Type>();
        foreach (Type/*!*/ subtype in rawCtorType.Arguments.ToList()) {
          Contract.Assert(subtype != null);
          newArguments.Add(ThinOutType(subtype, boundTypeParams,
                                       instantiations));
        }
        return new CtorType(Token.NoToken, rawCtorType.Decl, newArguments);
        //
      } else {
        System.Diagnostics.Debug.Fail("Don't know how to handle this type: " + rawType);
        return rawType;   // compiler appeasement policy
      }
    }

  }
  [ContractClassFor(typeof(MapTypeAbstractionBuilder))]
  internal abstract class MapTypeAbstractionBuilderContracts : MapTypeAbstractionBuilder {
    public MapTypeAbstractionBuilderContracts()
      : base(null, null) {
    }
    protected override void GenSelectStoreFunctions(MapType abstractedType, TypeCtorDecl synonymDecl, out Function select, out Function store) {
      Contract.Requires(abstractedType != null);
      Contract.Requires(synonymDecl != null);
      Contract.Ensures(Contract.ValueAtReturn(out select) != null);
      Contract.Ensures(Contract.ValueAtReturn(out store) != null);

      throw new NotImplementedException();
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  public class VariableBindings {
    public readonly IDictionary<VCExprVar/*!*/, VCExprVar/*!*/>/*!*/ VCExprVarBindings;
    public readonly IDictionary<TypeVariable/*!*/, VCExpr/*!*/>/*!*/ TypeVariableBindings;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(VCExprVarBindings));
      Contract.Invariant(cce.NonNullDictionaryAndValues(TypeVariableBindings));
    }


    public VariableBindings(IDictionary<VCExprVar/*!*/, VCExprVar/*!*/>/*!*/ vcExprVarBindings,
                            IDictionary<TypeVariable/*!*/, VCExpr/*!*/>/*!*/ typeVariableBindings) {
      Contract.Requires(cce.NonNullDictionaryAndValues(vcExprVarBindings));
      Contract.Requires(cce.NonNullDictionaryAndValues(typeVariableBindings));
      this.VCExprVarBindings = vcExprVarBindings;
      this.TypeVariableBindings = typeVariableBindings;
    }

    public VariableBindings() :
      this(new Dictionary<VCExprVar/*!*/, VCExprVar/*!*/>(),
            new Dictionary<TypeVariable/*!*/, VCExpr/*!*/>()) {
    }

    public VariableBindings Clone() {
      Contract.Ensures(Contract.Result<VariableBindings>() != null);
      IDictionary<VCExprVar/*!*/, VCExprVar/*!*/>/*!*/ newVCExprVarBindings =
        new Dictionary<VCExprVar/*!*/, VCExprVar/*!*/>();
      foreach (KeyValuePair<VCExprVar/*!*/, VCExprVar/*!*/> pair in VCExprVarBindings) {
        Contract.Assert(cce.NonNullElements(pair));
        newVCExprVarBindings.Add(pair);
      }
      IDictionary<TypeVariable/*!*/, VCExpr/*!*/>/*!*/ newTypeVariableBindings =
        new Dictionary<TypeVariable/*!*/, VCExpr/*!*/>();
      foreach (KeyValuePair<TypeVariable/*!*/, VCExpr/*!*/> pair in TypeVariableBindings) {
        Contract.Assert(cce.NonNullElements(pair));
        newTypeVariableBindings.Add(pair);
      }
      return new VariableBindings(newVCExprVarBindings, newTypeVariableBindings);
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // The central class for turning types VCExprs into untyped
  // VCExprs. This class makes use of the type axiom builder to manage
  // the available types and symbols.
  [ContractClass(typeof(TypeEraserContracts))]
  public abstract class TypeEraser : MutatingVCExprVisitor<VariableBindings/*!*/> {

    protected readonly TypeAxiomBuilderIntBoolU/*!*/ AxBuilder;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(AxBuilder != null);
    }


    protected abstract OpTypeEraser/*!*/ OpEraser {
      get;
    }

    ////////////////////////////////////////////////////////////////////////////

    public TypeEraser(TypeAxiomBuilderIntBoolU axBuilder, VCExpressionGenerator gen)
      : base(gen) {
      Contract.Requires(gen != null);
      Contract.Requires(axBuilder != null);
      AxBuilder = axBuilder;
    }

    public VCExpr Erase(VCExpr expr, int polarity) {
      Contract.Requires(expr != null);
      Contract.Requires((polarity >= -1 && polarity <= 1));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      this.Polarity = polarity;
      return Mutate(expr, new VariableBindings());
    }

    internal int Polarity = 1;  // 1 for positive, -1 for negative, 0 for both

    ////////////////////////////////////////////////////////////////////////////

    public override VCExpr Visit(VCExprLiteral node, VariableBindings bindings) {
      Contract.Requires(bindings != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Contract.Assume(node.Type == Type.Bool || node.Type == Type.Int || node.Type == Type.Real || node.Type == Type.RMode);
      return node;
    }

    ////////////////////////////////////////////////////////////////////////////

    public override bool AvoidVisit(VCExprNAry node, VariableBindings arg)
    {
        return node.Op.Equals(VCExpressionGenerator.AndOp) ||
               node.Op.Equals(VCExpressionGenerator.OrOp);
    }

    public override VCExpr Visit(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires(bindings != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExprOp/*!*/ op = node.Op;
      if (op == VCExpressionGenerator.AndOp || op == VCExpressionGenerator.OrOp)
        // more efficient on large conjunctions/disjunctions
        return base.Visit(node, bindings);

      // the visitor that handles all other operators
      return node.Accept<VCExpr/*!*/, VariableBindings/*!*/>(OpEraser, bindings);
    }

    // this method is called by MutatingVCExprVisitor.Visit(VCExprNAry, ...)
    protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode, List<VCExpr/*!*/>/*!*/ newSubExprs, bool changed, VariableBindings/*!*/ bindings) {
      //Contract.Requires(originalNode != null);
      //Contract.Requires(cce.NonNullElements(newSubExprs));
      //Contract.Requires(bindings != null);
      Contract.Assume(originalNode.Op == VCExpressionGenerator.AndOp ||
             originalNode.Op == VCExpressionGenerator.OrOp);
      return Gen.Function(originalNode.Op,
                          AxBuilder.Cast(newSubExprs[0], Type.Bool),
                          AxBuilder.Cast(newSubExprs[1], Type.Bool));
    }

    ////////////////////////////////////////////////////////////////////////////

    public override VCExpr Visit(VCExprVar node, VariableBindings bindings) {
      Contract.Requires(bindings != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExprVar res;
      if (!bindings.VCExprVarBindings.TryGetValue(node, out res))
        return AxBuilder.Typed2Untyped(node);
      return cce.NonNull(res);
    }

    ////////////////////////////////////////////////////////////////////////////

    protected bool IsUniversalQuantifier(VCExprQuantifier node) {
      Contract.Requires(node != null);
      return Polarity == 1 && node.Quan == Quantifier.EX ||
             Polarity == -1 && node.Quan == Quantifier.ALL;
    }

    protected List<VCExprVar/*!*/>/*!*/ BoundVarsAfterErasure(List<VCExprVar/*!*/>/*!*/ oldBoundVars,
      // the mapping between old and new variables
      // is added to this bindings-object
                                                      VariableBindings/*!*/ bindings) {
      Contract.Requires(bindings != null);
      Contract.Requires(cce.NonNullElements(oldBoundVars));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));

      List<VCExprVar/*!*/>/*!*/ newBoundVars = new List<VCExprVar/*!*/>(oldBoundVars.Count);
      foreach (VCExprVar/*!*/ var in oldBoundVars) {
        Type/*!*/ newType = AxBuilder.TypeAfterErasure(var.Type);
        VCExprVar/*!*/ newVar = Gen.Variable(var.Name, newType);
        newBoundVars.Add(newVar);
        bindings.VCExprVarBindings.Add(var, newVar);
      }
      return newBoundVars;
    }

    // We check whether casts Int2U or Bool2U on the bound variables
    // occur in triggers. In case a trigger like f(Int2U(x)) occurs,
    // it may be better to give variable x the type U and remove the
    // cast. The following method returns true if the quantifier
    // should be translated again with a different typing
    protected bool RedoQuantifier(VCExprQuantifier/*!*/ node,
                                  VCExprQuantifier/*!*/ newNode,
      // the bound vars that actually occur in the body or
      // in any of the triggers
                                  List<VCExprVar/*!*/>/*!*/ occurringVars,
                                  VariableBindings/*!*/ oldBindings,
                                  out VariableBindings/*!*/ newBindings,
                                  out List<VCExprVar/*!*/>/*!*/ newBoundVars) {
      Contract.Requires(node != null);
      Contract.Requires(newNode != null);
      Contract.Requires(cce.NonNullElements(occurringVars));
      Contract.Requires(oldBindings != null);
      Contract.Ensures(Contract.ValueAtReturn(out newBindings) != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out newBoundVars)));
      List<VCExprVar/*!*/> castVariables =
        VariableCastCollector.FindCastVariables(node, newNode, AxBuilder);
      if (castVariables.Count == 0) {
        newBindings = oldBindings;         // to make the compiler happy
        newBoundVars = newNode.BoundVars;  // to make the compiler happy
        return false;
      }

      // redo everything with a different typing ...

      newBindings = oldBindings.Clone();
      newBoundVars = new List<VCExprVar/*!*/>(node.BoundVars.Count);
      foreach (VCExprVar/*!*/ var in node.BoundVars) {
        Contract.Assert(var != null);
        Type/*!*/ newType =
          castVariables.Contains(var) ? AxBuilder.U
                                      : AxBuilder.TypeAfterErasure(var.Type);
        Contract.Assert(newType != null);
        VCExprVar/*!*/ newVar = Gen.Variable(var.Name, newType);
        Contract.Assert(newVar != null);
        newBoundVars.Add(newVar);
        newBindings.VCExprVarBindings.Add(var, newVar);
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////////

    public override VCExpr Visit(VCExprLet node, VariableBindings bindings) {
      Contract.Requires(bindings != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VariableBindings/*!*/ newVarBindings = bindings.Clone();

      List<VCExprVar/*!*/>/*!*/ newBoundVars = new List<VCExprVar/*!*/>(node.BoundVars.Count);
      foreach (VCExprVar/*!*/ var in node.BoundVars) {
        Type/*!*/ newType = AxBuilder.TypeAfterErasure(var.Type);
        VCExprVar/*!*/ newVar = Gen.Variable(var.Name, newType);
        newBoundVars.Add(newVar);
        newVarBindings.VCExprVarBindings.Add(var, newVar);
      }

      List<VCExprLetBinding/*!*/>/*!*/ newbindings = new List<VCExprLetBinding/*!*/>(node.Length);
      for (int i = 0; i < node.Length; ++i) {
        VCExprLetBinding/*!*/ binding = node[i];
        Contract.Assert(binding != null);
        VCExprVar/*!*/ newVar = newBoundVars[i];
        Type/*!*/ newType = newVar.Type;

        VCExpr/*!*/ newE = AxBuilder.Cast(Mutate(binding.E, newVarBindings), newType);
        newbindings.Add(Gen.LetBinding(newVar, newE));
      }

      VCExpr/*!*/ newbody = Mutate(node.Body, newVarBindings);
      return Gen.Let(newbindings, newbody);
    }
  }

  [ContractClassFor(typeof(TypeEraser))]
  public abstract class TypeEraserContracts : TypeEraser {
    public TypeEraserContracts()
      : base(null, null) {
    }
    protected override OpTypeEraser OpEraser {
      get {
        Contract.Ensures(Contract.Result<OpTypeEraser>() != null);
        throw new NotImplementedException();
      }
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  public abstract class OpTypeEraser : StandardVCExprOpVisitor<VCExpr/*!*/, VariableBindings/*!*/> {

    protected readonly TypeAxiomBuilderIntBoolU/*!*/ AxBuilder;

    protected readonly TypeEraser/*!*/ Eraser;
    protected readonly VCExpressionGenerator/*!*/ Gen;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(AxBuilder != null);
      Contract.Invariant(Eraser != null);
      Contract.Invariant(Gen != null);
    }


    public OpTypeEraser(TypeEraser/*!*/ eraser, TypeAxiomBuilderIntBoolU/*!*/ axBuilder, VCExpressionGenerator/*!*/ gen) {
      Contract.Requires(eraser != null);
      Contract.Requires(axBuilder != null);
      Contract.Requires(gen != null);
      this.AxBuilder = axBuilder;
      this.Eraser = eraser;
      this.Gen = gen;
    }

    protected override VCExpr StandardResult(VCExprNAry node, VariableBindings bindings) {
      //Contract.Requires(bindings != null);
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      System.Diagnostics.Debug.Fail("Don't know how to erase types in this expression: " + node);
      Contract.Assert(false);
      throw new cce.UnreachableException();  // to please the compiler
    }

    private List<VCExpr/*!*/>/*!*/ MutateSeq(VCExprNAry node, VariableBindings bindings, int newPolarity) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      int oldPolarity = Eraser.Polarity;
      Eraser.Polarity = newPolarity;
      List<VCExpr/*!*/>/*!*/ newArgs = Eraser.MutateSeq(node, bindings);
      Eraser.Polarity = oldPolarity;
      return newArgs;
    }

    private VCExpr CastArguments(VCExprNAry node, Type argType, VariableBindings bindings, int newPolarity) {
      Contract.Requires(bindings != null);
      Contract.Requires(argType != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Gen.Function(node.Op,
                          AxBuilder.CastSeq(MutateSeq(node, bindings, newPolarity),
                          argType));
    }

    // Cast the arguments of the node to their old type if necessary and possible; otherwise use
    // their new type (int, real, bool, or U)
    private VCExpr CastArgumentsToOldType(VCExprNAry node, VariableBindings bindings, int newPolarity) {
      Contract.Requires(bindings != null);
      Contract.Requires(node != null);
      Contract.Requires((node.Arity > 0));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<VCExpr/*!*/>/*!*/ newArgs = MutateSeq(node, bindings, newPolarity);
      Type/*!*/ oldType = node[0].Type;
      if (AxBuilder.UnchangedType(oldType) &&
          node.Skip(1).All(e => e.Type.Equals(oldType)))
        return Gen.Function(node.Op, AxBuilder.CastSeq(newArgs, oldType));
      else
        return Gen.Function(node.Op, AxBuilder.CastSeq(newArgs, AxBuilder.U));
    }

    ///////////////////////////////////////////////////////////////////////////

    public override VCExpr VisitNotOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Bool, bindings, -Eraser.Polarity);
    }
    public override VCExpr VisitEqOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitNeqOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitImpliesOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      // UGLY: the code for tracking polarities should be factored out
      List<VCExpr/*!*/>/*!*/ newArgs = new List<VCExpr/*!*/>(2);
      Eraser.Polarity = -Eraser.Polarity;
      newArgs.Add(Eraser.Mutate(node[0], bindings));
      Eraser.Polarity = -Eraser.Polarity;
      newArgs.Add(Eraser.Mutate(node[1], bindings));
      return Gen.Function(node.Op, AxBuilder.CastSeq(newArgs, Type.Bool));
    }
    public override VCExpr VisitDistinctOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitLabelOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      // argument of the label operator should always be a formula
      // (at least for Simplify ... should this be ensured at a later point?)
      return CastArguments(node, Type.Bool, bindings, Eraser.Polarity);
    }
    public override VCExpr VisitIfThenElseOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      List<VCExpr/*!*/>/*!*/ newArgs = MutateSeq(node, bindings, 0);
      newArgs[0] = AxBuilder.Cast(newArgs[0], Type.Bool);
      Type t = node.Type;
      if (!AxBuilder.UnchangedType(t)) {
        t = AxBuilder.U;
      }
      newArgs[1] = AxBuilder.Cast(newArgs[1], t);
      newArgs[2] = AxBuilder.Cast(newArgs[2], t);
      return Gen.Function(node.Op, newArgs);
    }
    public override VCExpr/*!*/ VisitCustomOp(VCExprNAry/*!*/ node, VariableBindings/*!*/ bindings) {
      Contract.Requires(node != null);
      Contract.Requires(bindings != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<VCExpr/*!*/>/*!*/ newArgs = MutateSeq(node, bindings, 0);
      return Gen.Function(node.Op, newArgs);
    }
    public override VCExpr VisitAddOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, node.Type, bindings, 0);
    }
    public override VCExpr VisitSubOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, node.Type, bindings, 0);
    }
    public override VCExpr VisitMulOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, node.Type, bindings, 0);
    }
    public override VCExpr VisitDivOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Int, bindings, 0);
    }
    public override VCExpr VisitModOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Int, bindings, 0);
    }
    public override VCExpr VisitRealDivOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Real, bindings, 0);
    }
    /*public override VCExpr VisitFloatDivOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Float, bindings, 0);
    }*/
    public override VCExpr VisitPowOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Real, bindings, 0);
    }
    public override VCExpr VisitLtOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitLeOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitGtOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitGeOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitSubtypeOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, AxBuilder.U, bindings, 0);
    }
    public override VCExpr VisitToIntOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitToRealOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatAddOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatSubOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatMulOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatDivOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatLeqOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatLtOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatGeqOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatGtOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatEqOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitFloatNeqOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitBvOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitBvExtractOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires(bindings != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArgumentsToOldType(node, bindings, 0);
    }
    public override VCExpr VisitBvConcatOp(VCExprNAry node, VariableBindings bindings) {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      List<VCExpr/*!*/>/*!*/ newArgs = MutateSeq(node, bindings, 0);

      // each argument is cast to its old type
      Contract.Assert(newArgs.Count == node.Arity && newArgs.Count == 2);
      VCExpr/*!*/ arg0 = AxBuilder.Cast(newArgs[0], node[0].Type);
      Contract.Assert(arg0 != null);
      VCExpr/*!*/ arg1 = AxBuilder.Cast(newArgs[1], node[1].Type);
      Contract.Assert(arg1 != null);
      return Gen.Function(node.Op, arg0, arg1);
    }

  }

  //////////////////////////////////////////////////////////////////////////////

  /// <summary>
  /// Collect all variables x occurring in expressions of the form Int2U(x) or Bool2U(x), and
  /// collect all variables x occurring outside such forms.
  /// </summary>
  internal class VariableCastCollector : TraversingVCExprVisitor<bool, bool> {
    /// <summary>
    /// Determine those bound variables in "oldNode" <em>all</em> of whose relevant uses
    /// have to be cast in potential triggers in "newNode".  It is assume that
    /// the bound variables of "oldNode" correspond to the first bound
    /// variables of "newNode".
    /// </summary>
    public static List<VCExprVar/*!*/>/*!*/ FindCastVariables(VCExprQuantifier oldNode, VCExprQuantifier newNode, TypeAxiomBuilderIntBoolU axBuilder) {
      Contract.Requires((axBuilder != null));
      Contract.Requires((newNode != null));
      Contract.Requires((oldNode != null));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      VariableCastCollector/*!*/ collector = new VariableCastCollector(axBuilder);
      Contract.Assert(collector != null);
      if (newNode.Triggers.Any(trigger => trigger.Pos)) {
        // look in the given triggers
        foreach (VCTrigger/*!*/ trigger in newNode.Triggers) {
          Contract.Assert(trigger != null);
          if (trigger.Pos) {
            foreach (VCExpr/*!*/ expr in trigger.Exprs) {
              Contract.Assert(expr != null);
              collector.Traverse(expr, true);
            }
          }
        }
      } else {
        // look in the body of the quantifier
        collector.Traverse(newNode.Body, true);
      }

      List<VCExprVar/*!*/>/*!*/ castVariables = new List<VCExprVar/*!*/>(collector.varsInCasts.Count);
      foreach (VCExprVar/*!*/ castVar in collector.varsInCasts) {
        Contract.Assert(castVar != null);
        int i = newNode.BoundVars.IndexOf(castVar);
        if (0 <= i && i < oldNode.BoundVars.Count && !collector.varsOutsideCasts.ContainsKey(castVar))
          castVariables.Add(oldNode.BoundVars[i]);
      }
      return castVariables;
    }

    public VariableCastCollector(TypeAxiomBuilderIntBoolU axBuilder) {
      Contract.Requires(axBuilder != null);
      this.AxBuilder = axBuilder;
    }

    readonly List<VCExprVar/*!*/>/*!*/ varsInCasts = new List<VCExprVar/*!*/>();
    readonly Dictionary<VCExprVar/*!*/, object>/*!*/ varsOutsideCasts = new Dictionary<VCExprVar/*!*/, object>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(varsInCasts));
      Contract.Invariant(varsOutsideCasts != null && Contract.ForAll(varsOutsideCasts, voc => voc.Key != null));
      Contract.Invariant(AxBuilder != null);

    }


    readonly TypeAxiomBuilderIntBoolU/*!*/ AxBuilder;

    protected override bool StandardResult(VCExpr node, bool arg) {
      //Contract.Requires(node != null);
      return true; // not used
    }

    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);
      if (node.Op is VCExprBoogieFunctionOp) {
        Function func = ((VCExprBoogieFunctionOp)node.Op).Func;
        Contract.Assert(func != null);
        if ((AxBuilder.IsCast(func)) && node[0] is VCExprVar) {
          VCExprVar castVar = (VCExprVar)node[0];
          if (!varsInCasts.Contains(castVar))
            varsInCasts.Add(castVar);
          return true;
        }
      } else if (node.Op is VCExprNAryOp) {
        VCExpressionGenerator.SingletonOp op = VCExpressionGenerator.SingletonOpDict[node.Op];
        switch (op) {
          // the following operators cannot be used in triggers, so disregard any uses of variables as direct arguments
          case VCExpressionGenerator.SingletonOp.NotOp:
          case VCExpressionGenerator.SingletonOp.EqOp:
          case VCExpressionGenerator.SingletonOp.NeqOp:
          case VCExpressionGenerator.SingletonOp.AndOp:
          case VCExpressionGenerator.SingletonOp.OrOp:
          case VCExpressionGenerator.SingletonOp.ImpliesOp:
          case VCExpressionGenerator.SingletonOp.LtOp:
          case VCExpressionGenerator.SingletonOp.LeOp:
          case VCExpressionGenerator.SingletonOp.GtOp:
          case VCExpressionGenerator.SingletonOp.GeOp:
            foreach (VCExpr n in node) {
              if (!(n is VCExprVar)) {  // don't recurse on VCExprVar argument
                n.Accept<bool, bool>(this, arg);
              }
            }
            return true;
          default:
            break;
        }
      }
      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg) {
      Contract.Requires(node != null);
      if (!varsOutsideCasts.ContainsKey(node))
        varsOutsideCasts.Add(node, null);
      return true;
    }
  }

}
