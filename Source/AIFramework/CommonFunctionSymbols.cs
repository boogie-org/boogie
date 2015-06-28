//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework
{
  using System.Diagnostics.Contracts;
  using System.Collections;
  using System.Collections.Generic;
  //using Microsoft.SpecSharp.Collections;
  using Microsoft.Basetypes;

  /// <summary>
  ///  A basic class for function symbols.
  /// </summary>
  public class FunctionSymbol : IFunctionSymbol
  {
    private readonly string/*!*/ display;
    private readonly AIType/*!*/ typ;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(display != null);
      Contract.Invariant(typ != null);
    }


    public FunctionSymbol(AIType/*!*/ typ)
      : this("FunctionSymbol", typ) {
      Contract.Requires(typ != null);
    }

    internal FunctionSymbol(string/*!*/ display, AIType/*!*/ typ) {
      Contract.Requires(typ != null);
      Contract.Requires(display != null);
      this.display = display;
      this.typ = typ;
      //            base();
    }

    public AIType/*!*/ AIType { get { Contract.Ensures(Contract.Result<AIType>() != null); return typ; } }

    [NoDefaultContract]
    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return display;
    }

  }

  /// <summary>
  ///  A class for integer constants.
  /// </summary>
  public class IntSymbol : FunctionSymbol
  {
    public readonly BigNum Value;

    /// <summary>
    /// The intention is that this constructor be called only from the Int.Const method.
    /// </summary>
    internal IntSymbol(BigNum x)
      : base(cce.NonNull(x.ToString()), Int.Type) {
      this.Value = x;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other) {
      IntSymbol isym = other as IntSymbol;
      return isym != null && isym.Value.Equals(this.Value);
    }

    [Pure]
    public override int GetHashCode() {
      return Value.GetHashCode();
    }
  }

  /// <summary>
  ///  A class for bitvector constants.
  /// </summary>
  public class BvSymbol : FunctionSymbol
  {
    public readonly BigNum Value;
    public readonly int Bits;

    /// <summary>
    /// The intention is that this constructor be called only from the Int.Const method.
    /// </summary>
    internal BvSymbol(BigNum x, int y)
      : base(x + "bv" + y, Bv.Type) {
      this.Value = x;
      this.Bits = y;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other) {
      BvSymbol isym = other as BvSymbol;
      return isym != null && isym.Value == this.Value && isym.Bits == this.Bits;
    }

    [Pure]
    public override int GetHashCode() {
      unchecked {
        return Value.GetHashCode() ^ Bits;
      }
    }
  }

  public class DoubleSymbol : FunctionSymbol
  {
    public readonly double Value;

    /// <summary>
    /// The intention is that this constructor be called only from the Double.Const method.
    /// </summary>
    internal DoubleSymbol(double x)
      : base(cce.NonNull(x.ToString()), Double.Type) {
      this.Value = x;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other) {
      DoubleSymbol dsym = other as DoubleSymbol;
      return dsym != null && dsym.Value == this.Value;
    }

    [Pure]
    public override int GetHashCode() {
      return Value.GetHashCode();
    }
  }

  /// <summary>
  ///  Function symbol based on a string.  Uses the string equality for determining equality
  ///  of symbol.
  /// </summary>
  public class NamedSymbol : FunctionSymbol
  {
    public string/*!*/ Value { [NoDefaultContract] get { Contract.Ensures(Contract.Result<string>() != null); return cce.NonNull(this.ToString()); } }

    public NamedSymbol(string/*!*/ symbol, AIType/*!*/ typ)
      : base(symbol, typ) {
      Contract.Requires(typ != null);
      Contract.Requires(symbol != null);
    }

    [NoDefaultContract]
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other) {
      NamedSymbol nsym = other as NamedSymbol;
      return nsym != null && this.Value.Equals(nsym.Value);
    }

    [NoDefaultContract]
    [Pure]
    public override int GetHashCode() {
      return Value.GetHashCode();
    }
  }

  //
  // In the following, the classes like Value and Prop serve two
  // roles.  The primary role is to be the base types for AIType. 
  // The only objects of these classes are the representative
  // objects that denote an AIType, which are given by the
  // "Type" property.  Subtypes in the AIType language are
  // encoded by subclassing.  This yields some "higher-orderness"
  // for checking subtyping in the AIType language, by using
  // the Spec#/C# subclassing checks.
  //
  // The other role is simply as a module for collecting like function
  // symbols.
  //

  //-------------------------- Terms ----------------------------------

  /// <summary>
  ///  A class with the equality symbol and the ValueType.Type.
  /// </summary>
  public class Value : AIType
  {
    private static readonly AIType/*!*/ valtype = new Value();
    public static AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return valtype; } }

    private static readonly FunctionType[]/*!*/ funtypeCache = new FunctionType[5];
    public static FunctionType/*!*/ FunctionType(int inParameterCount) {
      Contract.Requires((0 <= inParameterCount));
      Contract.Ensures(Contract.Result<FunctionType>() != null);
      // Contract.Ensures(Contract.Result<>().Arity == inParameterCount);
      FunctionType result;
      if (inParameterCount < funtypeCache.Length) {
        result = funtypeCache[inParameterCount];
        if (result != null) {
          return result;
        }
      }
      AIType[] signature = new AIType[1 + inParameterCount];
      for (int i = 0; i < signature.Length; i++) {
        signature[i] = valtype;
      }
      result = new FunctionType(signature);
      if (inParameterCount < funtypeCache.Length) {
        funtypeCache[inParameterCount] = result;
      }
      return result;
    }

    [Once]
    private static AIType/*!*/ binreltype;

    private static AIType/*!*/ BinrelType {
      get {
        Contract.Ensures(Contract.Result<AIType>() != null);
        if (binreltype == null) {
          binreltype = new FunctionType(Type, Type, Prop.Type);
        }
        return binreltype;
      }
    }

    [Once]
    private static FunctionSymbol/*!*/ _eq;
    public static FunctionSymbol/*!*/ Eq {
      get {
        Contract.Ensures(Contract.Result<FunctionSymbol>() != null);
        if (_eq == null) {
          _eq = new FunctionSymbol("=", BinrelType);
        }
        return _eq;
      }
    }
    [Once]
    private static FunctionSymbol/*!*/ _neq;
    public static FunctionSymbol/*!*/ Neq {
      get {
        Contract.Ensures(Contract.Result<FunctionSymbol>() != null);
        if (_neq == null) {
          _neq = new FunctionSymbol("!=", BinrelType);
        }
        return _neq;
      }
    }
    [Once]
    private static FunctionSymbol/*!*/ _subtype;
    public static FunctionSymbol/*!*/ Subtype {
      get {
        Contract.Ensures(Contract.Result<FunctionSymbol>() != null);
        if (_subtype == null) {
          _subtype = new FunctionSymbol("<:", BinrelType);
        }
        return _subtype;
      }
    }

    [Once]
    private static AIType/*!*/ typeof_type;
    private static AIType/*!*/ TypeofType {
      get {
        Contract.Ensures(Contract.Result<AIType>() != null);
        if (typeof_type == null) {
          typeof_type = new FunctionType(Ref.Type, Type);
        }
        return typeof_type;
      }
    }
    [Once]
    private static FunctionSymbol/*!*/ _typeof;
    public static FunctionSymbol/*!*/ Typeof {
      get {
        Contract.Ensures(Contract.Result<FunctionSymbol>() != null);
        if (_typeof == null) {
          _typeof = new FunctionSymbol("typeof", TypeofType);
        }
        return _typeof;
      }
    }

    /// <summary>
    /// Value should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    protected Value() { }

  }

  public class Int : Value
  {
    private static readonly AIType/*!*/ inttype = new Int();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return inttype; } }

    private static readonly AIType/*!*/ unaryinttype = new FunctionType(Type, Type);
    private static readonly AIType/*!*/ bininttype = new FunctionType(Type, Type, Type);
    private static readonly AIType/*!*/ relationtype = new FunctionType(Type, Type, Prop.Type);

    private static readonly FunctionSymbol/*!*/ _negate = new FunctionSymbol("~", unaryinttype);
    private static readonly FunctionSymbol/*!*/ _add = new FunctionSymbol("+", bininttype);
    private static readonly FunctionSymbol/*!*/ _sub = new FunctionSymbol("-", bininttype);
    private static readonly FunctionSymbol/*!*/ _mul = new FunctionSymbol("*", bininttype);
    private static readonly FunctionSymbol/*!*/ _div = new FunctionSymbol("/", bininttype);
    private static readonly FunctionSymbol/*!*/ _mod = new FunctionSymbol("%", bininttype);
    private static readonly FunctionSymbol/*!*/ _atmost = new FunctionSymbol("<=", relationtype);
    private static readonly FunctionSymbol/*!*/ _less = new FunctionSymbol("<", relationtype);
    private static readonly FunctionSymbol/*!*/ _greater = new FunctionSymbol(">", relationtype);
    private static readonly FunctionSymbol/*!*/ _atleast = new FunctionSymbol(">=", relationtype);

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Negate { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _negate; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Add { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _add; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Sub { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _sub; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Mul { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _mul; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Div { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _div; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Mod { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _mod; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ AtMost { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _atmost; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Less { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _less; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Greater { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _greater; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ AtLeast { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _atleast; } }

    public static IntSymbol/*!*/ Const(BigNum x) {
      Contract.Ensures(Contract.Result<IntSymbol>() != null);
      // We could cache things here, but for now we don't.
      return new IntSymbol(x);
    }

    /// <summary>
    /// Int should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private Int() { }
  }

  public class Double : Value
  {
    private static readonly AIType/*!*/ doubletype = new Double();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return doubletype; } }

    public static DoubleSymbol/*!*/ Const(double x) {
      Contract.Ensures(Contract.Result<DoubleSymbol>() != null);
      // We could cache things here, but for now we don't.
      return new DoubleSymbol(x);
    }

    /// <summary>
    /// Double should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private Double() { }
  }

  public class Bv : Value
  {
    private static readonly AIType/*!*/ bvtype = new Bv();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return bvtype; } }

    private static readonly AIType/*!*/ unaryinttype = new FunctionType(Type, Type);
    private static readonly AIType/*!*/ bininttype = new FunctionType(Type, Type, Type);
    private static readonly AIType/*!*/ relationtype = new FunctionType(Type, Type, Prop.Type);

    private static readonly FunctionSymbol/*!*/ _negate = new FunctionSymbol("~", unaryinttype);
    private static readonly FunctionSymbol/*!*/ _add = new FunctionSymbol("+", bininttype);
    private static readonly FunctionSymbol/*!*/ _sub = new FunctionSymbol("-", bininttype);
    private static readonly FunctionSymbol/*!*/ _mul = new FunctionSymbol("*", bininttype);
    private static readonly FunctionSymbol/*!*/ _div = new FunctionSymbol("/", bininttype);
    private static readonly FunctionSymbol/*!*/ _mod = new FunctionSymbol("%", bininttype);
    private static readonly FunctionSymbol/*!*/ _concat = new FunctionSymbol("$concat", bininttype);
    private static readonly FunctionSymbol/*!*/ _extract = new FunctionSymbol("$extract", unaryinttype);
    private static readonly FunctionSymbol/*!*/ _atmost = new FunctionSymbol("<=", relationtype);
    private static readonly FunctionSymbol/*!*/ _less = new FunctionSymbol("<", relationtype);
    private static readonly FunctionSymbol/*!*/ _greater = new FunctionSymbol(">", relationtype);
    private static readonly FunctionSymbol/*!*/ _atleast = new FunctionSymbol(">=", relationtype);

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Negate { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _negate; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Add { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _add; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Sub { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _sub; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Mul { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _mul; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Div { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _div; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Mod { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _mod; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ AtMost { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _atmost; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Less { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _less; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Greater { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _greater; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ AtLeast { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _atleast; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Extract { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _extract; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Concat { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _concat; } }

    public static BvSymbol/*!*/ Const(BigNum x, int y) {
      Contract.Ensures(Contract.Result<BvSymbol>() != null);
      // We could cache things here, but for now we don't.
      return new BvSymbol(x, y);
    }

    /// <summary>
    /// Int should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private Bv() { }
  }

  public class Ref : Value
  {
    private static readonly AIType/*!*/ reftype = new Ref();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return reftype; } }

    private static readonly FunctionSymbol/*!*/ _null = new FunctionSymbol("null", Type);

    public static FunctionSymbol/*!*/ Null { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _null; } }

    /// <summary>
    /// Ref should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private Ref() { }
  }

  public class HeapStructure : Value
  {
    private static readonly AIType/*!*/ reftype = new HeapStructure();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return reftype; } }



    /// <summary>
    /// HeapStructure should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private HeapStructure() { }
  }

  public class FieldName : Value
  {
    private static readonly AIType/*!*/ fieldnametype = new FieldName();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return fieldnametype; } }

    private static readonly FunctionSymbol/*!*/ _allocated = new FunctionSymbol("$allocated", FieldName.Type);
    public static FunctionSymbol/*!*/ Allocated { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _allocated; } }

    /// <summary>
    /// Is this a boolean field that monotonically goes from false to true?
    /// </summary>
    public static bool IsBooleanMonotonicallyWeakening(IFunctionSymbol/*!*/ f) {
      Contract.Requires(f != null);
      return f.Equals(Allocated);
    }

    /// <summary>
    /// FieldName should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private FieldName() { }
  }

  public class Heap : Value
  {
    private static readonly AIType/*!*/ heaptype = new Heap();
    public static new AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return heaptype; } }

    // the types in the following, select1, select2, are hard-coded;
    // these types may not always be appropriate
    private static readonly FunctionSymbol/*!*/ _select1 = new FunctionSymbol("sel1",
      // Heap x FieldName -> Prop
        new FunctionType(Type, FieldName.Type, Prop.Type)
    );
    public static FunctionSymbol/*!*/ Select1 { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _select1; } }

    private static readonly FunctionSymbol/*!*/ _select2 = new FunctionSymbol("sel2",
      // Heap x Ref x FieldName -> Value
        new FunctionType(Type, Ref.Type, FieldName.Type, Value.Type)
    );
    public static FunctionSymbol/*!*/ Select2 { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _select2; } }

    // the types in the following, store1, store2, are hard-coded;
    // these types may not always be appropriate
    private static readonly FunctionSymbol/*!*/ _update1 = new FunctionSymbol("upd1",
      // Heap x FieldName x Value -> Heap
        new FunctionType(Type, FieldName.Type, Value.Type, Type)
    );
    public static FunctionSymbol/*!*/ Update1 { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _update1; } }

    private static readonly FunctionSymbol/*!*/ _update2 = new FunctionSymbol("upd2",
      // Heap x Ref x FieldName x Value -> Heap
        new FunctionType(Type, Ref.Type, FieldName.Type, Value.Type, Type)
    );
    public static FunctionSymbol/*!*/ Update2 { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _update2; } }

    private static readonly FunctionSymbol/*!*/ _unsupportedHeapOp =
        new FunctionSymbol("UnsupportedHeapOp",
      // Heap x FieldName -> Prop
        new FunctionType(Type, FieldName.Type, Prop.Type)
    );
    public static FunctionSymbol/*!*/ UnsupportedHeapOp { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _unsupportedHeapOp; } }

    /// <summary>
    /// Heap should not be instantiated from the outside, except perhaps in
    /// subclasses.
    /// </summary>
    private Heap() { }
  }

  //    public class List : Value
  //    {
  //        private static IDictionary/*<AIType!,AIType!>*/! lists = new Hashtable();
  //        public static AIType! Type(AIType! typeParameter)
  //        {
  //            if (lists.Contains(typeParameter))
  //                return lists[typeParameter];
  //            else
  //            {
  //                AIType! result = new List(typeParameter);
  //                lists[typeParameter] = result;
  //                return result;
  //            }
  //        }
  //
  //        private static IDictionary/*<AIType!,AIType!>*/! nils = new Hashtable();
  //        public static FunctionSymbol! Nil(AIType! typeParameter)
  //        {
  //            if (nils.Contains(typeParameter))
  //                return nils[typeParameter];
  //            else
  //            {
  //                FunctionSymbol! result = new FunctionSymbol(Type(typeParameter));
  //                nils[typeParameter] = result;
  //                return result;
  //            }
  //        }
  //
  //        private static IDictionary/*<AIType!,AIType!>*/! cons = new Hashtable();
  //        public static FunctionSymbol! Cons(AIType! typeParameter)
  //        {
  //            if (cons.Contains(typeParameter))
  //                return cons[typeParameter];
  //            else
  //            {
  //                FunctionSymbol! result = new FunctionSymbol(
  //                    new FunctionType(typeParameter, Type(typeParameter), Type(typeParameter))
  //                );
  //                cons[typeParameter] = result;
  //                return result;
  //            }
  //        }
  //
  //        private AIType! typeParameter;
  //        public AIType(TypeParameter/*!*/ ){
  //Contract.Requires( != null);
  //return typeParameter; } }
  //
  //        /// <summary>
  //        /// List should not be instantiated from the outside.
  //        /// </summary>
  //        private List(AIType! typeParameter)
  //        {
  //            this.typeParameter = typeParameter;
  //        }
  //    }
  //
  //    public class Pair : Value
  //    {
  //        private static IDictionary! pairs = new Hashtable();
  //        public static AIType! Type(AIType! type1, AIType! type2)
  //        {
  //            Microsoft.AbstractInterpretationFramework.Collections.Pair typpair
  //                = new Microsoft.AbstractInterpretationFramework.Collections.Pair(type1, type2);
  //
  //            if (pairs.Contains(typpair))
  //                return pairs[typpair];
  //            else
  //            {
  //                AIType! result = new Pair(type1, type2);
  //                pairs[typpair] = result;
  //                return result;
  //            }
  //        }
  //
  //        private static IDictionary! constructs = new Hashtable();
  //        public static FunctionSymbol! Pair(AIType! type1, AIType! type2)
  //        {
  //            Microsoft.AbstractInterpretationFramework.Collections.Pair typpair
  //                = new Microsoft.AbstractInterpretationFramework.Collections.Pair(type1, type2);
  //
  //            if (constructs.Contains(typpair))
  //                return constructs[typpair];
  //            else
  //            {
  //                FunctionSymbol! result = new FunctionSymbol(
  //                    new FunctionType(type1, type2, Type(type1, type2))
  //                );
  //                constructs[typpair] = result;
  //                return result;
  //            }
  //        }
  //
  //        protected AIType! type1;
  //        protected AIType! type2;
  //
  //        public AIType(Type1/*!*/ ){
  //Contract.Requires( != null);
  // return type1; } }
  //        public AIType(Type2/*!*/ ){
  //Contract.Requires( != null);
  // return type2; } }
  //
  //        /// <summary>
  //        /// Pair should not be instantiated from the outside, except by subclasses.
  //        /// </summary>
  //        protected Pair(AIType! type1, AIType! type2)
  //        {
  //            this.type1 = type1;
  //            this.type2 = type2;
  //        }
  //    }

  //-------------------------- Propositions ---------------------------


  /// <summary>
  ///  A class with global propositional symbols and the Prop.Type.
  /// </summary>
  public sealed class Prop : AIType
  {
    private static readonly AIType/*!*/ proptype = new Prop();

    public static AIType/*!*/ Type { get { Contract.Ensures(Contract.Result<AIType>() != null); return proptype; } }

    private static readonly AIType/*!*/ unaryproptype = new FunctionType(Type, Type);
    private static readonly AIType/*!*/ binproptype = new FunctionType(Type, Type, Type);
    private static readonly AIType/*!*/ quantifiertype =
        new FunctionType(new FunctionType(Value.Type, Type), Type);

    private static readonly FunctionSymbol/*!*/ _false = new FunctionSymbol("false", Type);
    private static readonly FunctionSymbol/*!*/ _true = new FunctionSymbol("true", Type);
    private static readonly FunctionSymbol/*!*/ _not = new FunctionSymbol("!", unaryproptype);
    private static readonly FunctionSymbol/*!*/ _and = new FunctionSymbol("/\\", binproptype);
    private static readonly FunctionSymbol/*!*/ _or = new FunctionSymbol("\\/", binproptype);
    private static readonly FunctionSymbol/*!*/ _implies = new FunctionSymbol("==>", binproptype);
    private static readonly FunctionSymbol/*!*/ _exists = new FunctionSymbol("Exists", quantifiertype);
    private static readonly FunctionSymbol/*!*/ _forall = new FunctionSymbol("Forall", quantifiertype);
    private static readonly FunctionSymbol/*!*/ _lambda = new FunctionSymbol("Lambda", quantifiertype);


    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ False { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _false; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ True { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _true; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Not { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _not; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ And { [Pure] get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _and; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Or { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _or; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Implies { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _implies; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Exists { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _exists; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Forall { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _forall; } }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public static FunctionSymbol/*!*/ Lambda { get { Contract.Ensures(Contract.Result<FunctionSymbol>() != null); return _lambda; } }


    /// <summary>
    ///  Prop should not be instantiated from the outside.
    /// </summary>
    private Prop() { }



    //
    // Utility Methods
    //

    public static IExpr/*!*/ SimplifiedAnd(IPropExprFactory/*!*/ factory, IExpr/*!*/ e0, IExpr/*!*/ e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IFunApp fun0 = e0 as IFunApp;
      if (fun0 != null) {
        if (fun0.FunctionSymbol.Equals(Prop.True)) {
          return e1;
        } else if (fun0.FunctionSymbol.Equals(Prop.False)) {
          return e0;
        }
      }

      IFunApp fun1 = e1 as IFunApp;
      if (fun1 != null) {
        if (fun1.FunctionSymbol.Equals(Prop.True)) {
          return e0;
        } else if (fun1.FunctionSymbol.Equals(Prop.False)) {
          return e1;
        }
      }

      return factory.And(e0, e1);
    }

    public static IExpr/*!*/ SimplifiedAnd(IPropExprFactory/*!*/ factory, IEnumerable/*<IExpr!>*//*!*/ exprs) {
      Contract.Requires(exprs != null);
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IExpr/*!*/ result = factory.True;
      Contract.Assert(result != null);
      foreach (IExpr/*!*/ conjunct in exprs) {
        Contract.Assert(conjunct != null);
        result = SimplifiedAnd(factory, result, conjunct);
      }
      return result;
    }

    public static IExpr/*!*/ SimplifiedOr(IPropExprFactory/*!*/ factory, IExpr/*!*/ e0, IExpr/*!*/ e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IFunApp fun0 = e0 as IFunApp;
      if (fun0 != null) {
        if (fun0.FunctionSymbol.Equals(Prop.False)) {
          return e1;
        } else if (fun0.FunctionSymbol.Equals(Prop.True)) {
          return e0;
        }
      }

      IFunApp fun1 = e1 as IFunApp;
      if (fun1 != null) {
        if (fun1.FunctionSymbol.Equals(Prop.False)) {
          return e0;
        } else if (fun1.FunctionSymbol.Equals(Prop.True)) {
          return e1;
        }
      }

      return factory.Or(e0, e1);
    }

    public static IExpr/*!*/ SimplifiedOr(IPropExprFactory/*!*/ factory, IEnumerable/*<IExpr!>*//*!*/ exprs) {
      Contract.Requires(exprs != null);
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IExpr/*!*/ result = factory.False;
      Contract.Assert(result != null);
      foreach (IExpr/*!*/ disj in exprs) {
        Contract.Assert(disj != null);
        result = SimplifiedOr(factory, result, disj);
      }
      return result;
    }



    /// <summary>
    ///  Break top-level conjuncts into a list of sub-expressions.
    /// </summary>
    /// <param name="e">The expression to examine.</param>
    /// <returns>A list of conjuncts.</returns>
    internal static IList/*<IExpr!>*//*!*/ BreakConjuncts(IExpr/*!*/ e) {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<IList>() != null);
      Contract.Ensures(Contract.ForAll(0, Contract.Result<IList>().Count, i => {
        var sub = Contract.Result<IList>()[i];
        return !(sub is IFunApp) || !((IFunApp)sub).FunctionSymbol.Equals(Prop.And);
      }));
      return BreakJuncts(e, Prop.And);
    }

    /// <summary>
    ///  Break top-level disjuncts into a list of sub-expressions.
    /// </summary>
    /// <param name="e">The expression to examine.</param>
    /// <returns>A list of conjuncts.</returns>
    internal static IList/*<IExpr!>*//*!*/ BreakDisjuncts(IExpr/*!*/ e) {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<IList>() != null);
      Contract.Ensures(Contract.ForAll(0, Contract.Result<IList>().Count, i => {
        var sub = Contract.Result<IList>()[i];
        return !(sub is IFunApp) || !((IFunApp)sub).FunctionSymbol.Equals(Prop.Or);
      }));
      return BreakJuncts(e, Prop.Or);
    }

    private static IList/*<IExpr!>*//*!*/ BreakJuncts(IExpr/*!*/ e, IFunctionSymbol/*!*/ sym) {
      Contract.Requires(sym != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<IList>() != null);
      Contract.Ensures(Contract.ForAll(0, Contract.Result<IList>().Count, i => {
        var sub = Contract.Result<IList>()[i];
        return (sub is IFunApp) || !((IFunApp)sub).FunctionSymbol.Equals(sym);
      }));
      ArrayList/*<IExpr!>*//*!*/ result = new ArrayList();

      IFunApp f = e as IFunApp;
      if (f != null) {
        // If it is a sym, go down into sub-expressions.
        if (f.FunctionSymbol.Equals(sym)) {
          foreach (IExpr/*!*/ arg in f.Arguments) {
            Contract.Assert(arg != null);
            result.AddRange(BreakJuncts(arg, sym));
          }
        }
          // Otherwise, stop.
        else {
          result.Add(e);
        }
      } else {
        result.Add(e);
      }

      return result;
    }
  }

  /// <summary>
  /// A callback to produce a function body given the bound variable.
  /// </summary>
  /// <param name="var">The bound variable to use.</param>
  /// <returns>The function body.</returns>
  public delegate IExpr/*!*/ FunctionBody(IVariable/*!*/ var);

  /// <summary>
  ///  An interface for constructing propositional expressions.
  /// 
  ///  This interface should be implemented by the client.  An implementation of
  ///  of this class should generally be used as a singleton object.
  /// </summary>
  /// 
  [ContractClass(typeof(IPropExprFactoryContracts))]
  public interface IPropExprFactory
  {
    IFunApp/*!*/ False { get /*ensures result.FunctionSymbol.Equals(Prop.False);*/; }
    IFunApp/*!*/ True { get /*ensures result.FunctionSymbol.Equals(Prop.True);*/; }

    IFunApp/*!*/ Not(IExpr/*!*/ p) /*ensures result.FunctionSymbol.Equals(Prop.Not);*/;

    IFunApp/*!*/ And(IExpr/*!*/ p, IExpr/*!*/ q) /*ensures result.FunctionSymbol.Equals(Prop.And);*/;
    IFunApp/*!*/ Or(IExpr/*!*/ p, IExpr/*!*/ q) /*ensures result.FunctionSymbol.Equals(Prop.Or);*/;

    IFunApp/*!*/ Implies(IExpr/*!*/ p, IExpr/*!*/ q) /*ensures result.FunctionSymbol.Equals(Prop.Implies);*/;
  }
  [ContractClassFor(typeof(IPropExprFactory))]
  public abstract class IPropExprFactoryContracts : IPropExprFactory
  {
    #region IPropExprFactory Members
    IFunApp IPropExprFactory.Implies(IExpr p, IExpr q) {
      Contract.Requires(p != null);
      Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp IPropExprFactory.False {

      get { Contract.Ensures(Contract.Result<IFunApp>() != null); throw new System.NotImplementedException(); }
    }

    IFunApp IPropExprFactory.True {
      get { Contract.Ensures(Contract.Result<IFunApp>() != null); throw new System.NotImplementedException(); }
    }

    IFunApp IPropExprFactory.Not(IExpr p) {
      Contract.Requires(p != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp IPropExprFactory.And(IExpr p, IExpr q) {
      Contract.Requires(p != null);
      Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp IPropExprFactory.Or(IExpr p, IExpr q) {
      Contract.Requires(p != null);
      Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }



    #endregion
  }

  /// <summary>
  ///  An interface for constructing value expressions.
  /// 
  ///  This interface should be implemented by the client.  An implementation of
  ///  of this class should generally be used as a singleton object.
  /// </summary>
  /// 
  [ContractClass(typeof(IValueExprFactoryContracts))]
  public interface IValueExprFactory
  {
    IFunApp/*!*/ Eq(IExpr/*!*/ e0, IExpr/*!*/ e1) /*ensures result.FunctionSymbol.Equals(Value.Eq);*/;
    IFunApp/*!*/ Neq(IExpr/*!*/ e0, IExpr/*!*/ e1) /*ensures result.FunctionSymbol.Equals(Value.Neq);*/;
  }
  [ContractClassFor(typeof(IValueExprFactory))]
  public abstract class IValueExprFactoryContracts : IValueExprFactory
  {
    #region IValueExprFactory Members

    IFunApp IValueExprFactory.Eq(IExpr e0, IExpr e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp IValueExprFactory.Neq(IExpr e0, IExpr e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    #endregion
  }

  /// <summary>
  ///  An interface for constructing value expressions having to with null.
  /// 
  ///  This interface should be implemented by the client.  An implementation of
  ///  of this class should generally be used as a singleton object.
  /// </summary>
  /// 
  [ContractClass(typeof(INullnessFactoryContracts))]
  public interface INullnessFactory
  {
    IFunApp/*!*/ Eq(IExpr/*!*/ e0, IExpr/*!*/ e1) /*ensures result.FunctionSymbol.Equals(Value.Eq);*/;
    IFunApp/*!*/ Neq(IExpr/*!*/ e0, IExpr/*!*/ e1) /*ensures result.FunctionSymbol.Equals(Value.Neq);*/;
    IFunApp/*!*/ Null { get; /*ensures result.FunctionSymbol.Equals(Ref.Null);*/ }
  }
  [ContractClassFor(typeof(INullnessFactory))]
  public abstract class INullnessFactoryContracts : INullnessFactory
  {
    #region INullnessFactory Members

    IFunApp INullnessFactory.Eq(IExpr e0, IExpr e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp INullnessFactory.Neq(IExpr e0, IExpr e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp INullnessFactory.Null {
      get {
        Contract.Ensures(Contract.Result<IFunApp>() != null);
        throw new System.NotImplementedException();
      }
    }

    #endregion
  }

  /// <summary>
  ///  An interface for constructing integer expressions.
  /// 
  ///  This interface should be implemented by the client.  An implementation of
  ///  of this class should generally be used as a singleton object.
  /// </summary>
  /// 
  [ContractClass(typeof(IIntExprFactoryContracts))]
  public interface IIntExprFactory : IValueExprFactory
  {
    IFunApp/*!*/ Const(BigNum i) /*ensures result.FunctionSymbol.Equals(new IntSymbol(i));*/;
  }
  [ContractClassFor(typeof(IIntExprFactory))]
  public abstract class IIntExprFactoryContracts : IIntExprFactory
  {

    #region IIntExprFactory Members

    IFunApp IIntExprFactory.Const(BigNum i) {
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    #endregion

    #region IValueExprFactory Members

    IFunApp IValueExprFactory.Eq(IExpr e0, IExpr e1) {
      throw new System.NotImplementedException();
    }

    IFunApp IValueExprFactory.Neq(IExpr e0, IExpr e1) {
      throw new System.NotImplementedException();
    }

    #endregion
  }

  /// <summary>
  ///  An interface for constructing linear integer expressions.
  /// 
  ///  This interface should be implemented by the client.  An implementation of
  ///  of this class should generally be used as a singleton object.
  /// </summary>
  /// 
  [ContractClass(typeof(ILinearExprFactoryContracts))]
  public interface ILinearExprFactory : IIntExprFactory
  {
    IFunApp/*!*/ AtMost(IExpr/*!*/ e0, IExpr/*!*/ e1) /*ensures result.FunctionSymbol.Equals(Value.AtMost);*/;
    IFunApp/*!*/ Add(IExpr/*!*/ e0, IExpr/*!*/ e1) /*ensures result.FunctionSymbol.Equals(Value.Add);*/;
    /// <summary>
    /// If "var" is null, returns an expression representing r.
    /// Otherwise, returns an expression representing r*var.
    /// </summary>
    IExpr/*!*/ Term(Microsoft.Basetypes.Rational r, IVariable var);

    IFunApp/*!*/ False { get /*ensures result.FunctionSymbol.Equals(Prop.False);*/; }
    IFunApp/*!*/ True { get /*ensures result.FunctionSymbol.Equals(Prop.True);*/; }
    IFunApp/*!*/ And(IExpr/*!*/ p, IExpr/*!*/ q) /*ensures result.FunctionSymbol.Equals(Prop.And);*/;
  }
  [ContractClassFor(typeof(ILinearExprFactory))]
  public abstract class ILinearExprFactoryContracts : ILinearExprFactory
  {

    #region ILinearExprFactory Members

    IFunApp ILinearExprFactory.AtMost(IExpr e0, IExpr e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp ILinearExprFactory.Add(IExpr e0, IExpr e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null); Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IExpr ILinearExprFactory.Term(Rational r, IVariable var) {
      Contract.Ensures(Contract.Result<IExpr>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp ILinearExprFactory.False {
      get { Contract.Ensures(Contract.Result<IFunApp>() != null); throw new System.NotImplementedException(); }
    }

    IFunApp ILinearExprFactory.True {
      get { Contract.Ensures(Contract.Result<IFunApp>() != null); throw new System.NotImplementedException(); }
    }

    IFunApp ILinearExprFactory.And(IExpr p, IExpr q) {
      Contract.Requires(p != null);
      Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    #endregion

    #region IIntExprFactory Members

    IFunApp IIntExprFactory.Const(BigNum i) {
      throw new System.NotImplementedException();
    }

    #endregion

    #region IValueExprFactory Members

    IFunApp IValueExprFactory.Eq(IExpr e0, IExpr e1) {
      throw new System.NotImplementedException();
    }

    IFunApp IValueExprFactory.Neq(IExpr e0, IExpr e1) {
      throw new System.NotImplementedException();
    }

    #endregion
  }

  /// <summary>
  ///  An interface for constructing type expressions and performing some type operations.
  ///  The types are assumed to be arranged in a rooted tree.
  ///
  ///  This interface should be implemented by the client.  An implementation of
  ///  of this class should generally be used as a singleton object.
  /// </summary>
  /// 
  [ContractClass(typeof(ITypeExprFactoryContracts))]
  public interface ITypeExprFactory
  {
    /// <summary>
    /// Returns an expression denoting the top of the type hierarchy.
    /// </summary>
    IExpr/*!*/ RootType { get; }

    /// <summary>
    /// Returns true iff "t" denotes a type constant.
    /// </summary>
    [Pure]
    bool IsTypeConstant(IExpr/*!*/ t);

    /// <summary>
    /// Returns true iff t0 and t1 are types such that t0 and t1 are equal.
    /// </summary>
    [Pure]
    bool IsTypeEqual(IExpr/*!*/ t0, IExpr/*!*/ t1);

    /// <summary>
    /// Returns true iff t0 and t1 are types such that t0 is a subtype of t1.
    /// </summary>
    [Pure]
    bool IsSubType(IExpr/*!*/ t0, IExpr/*!*/ t1);

    /// <summary>
    /// Returns the most derived supertype of both "t0" and "t1".  A precondition is
    /// that "t0" and "t1" both represent types.
    /// </summary>
    IExpr/*!*/ JoinTypes(IExpr/*!*/ t0, IExpr/*!*/ t1);

    IFunApp/*!*/ IsExactlyA(IExpr/*!*/ e, IExpr/*!*/ type) /*requires IsTypeConstant(type); ensures result.FunctionSymbol.Equals(Value.Eq);*/;
    IFunApp/*!*/ IsA(IExpr/*!*/ e, IExpr/*!*/ type) /*requires IsTypeConstant(type); ensures result.FunctionSymbol.Equals(Value.Subtype);*/;
  }
  [ContractClassFor(typeof(ITypeExprFactory))]
  public abstract class ITypeExprFactoryContracts : ITypeExprFactory
  {

    #region ITypeExprFactory Members

    IExpr ITypeExprFactory.RootType {
      get { Contract.Ensures(Contract.Result<IExpr>() != null); throw new System.NotImplementedException(); }
    }

    bool ITypeExprFactory.IsTypeConstant(IExpr t) {
      Contract.Requires(t != null);
      throw new System.NotImplementedException();
    }

    bool ITypeExprFactory.IsTypeEqual(IExpr t0, IExpr t1) {
      Contract.Requires(t0 != null);
      Contract.Requires(t1 != null);
      throw new System.NotImplementedException();
    }

    bool ITypeExprFactory.IsSubType(IExpr t0, IExpr t1) {
      Contract.Requires(t0 != null);
      Contract.Requires(t1 != null);
      throw new System.NotImplementedException();
    }

    IExpr ITypeExprFactory.JoinTypes(IExpr t0, IExpr t1) {
      Contract.Requires(t0 != null);
      Contract.Requires(t1 != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp ITypeExprFactory.IsExactlyA(IExpr e, IExpr type) {
      Contract.Requires(e != null);
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    IFunApp ITypeExprFactory.IsA(IExpr e, IExpr type) {
      Contract.Requires(e != null);
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<IFunApp>() != null);
      throw new System.NotImplementedException();
    }

    #endregion
  }
}
