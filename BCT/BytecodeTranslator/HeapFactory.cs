//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;

namespace BytecodeTranslator {

  /// <summary>
  /// Implementations of this interface determine how the heap is represented in
  /// the translated Boogie program.
  /// </summary>
  public interface IHeap {

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
    /// on its type based on the heap representation.
    /// </summary>
    Bpl.Variable CreateFieldVariable(IFieldReference field);

    /// Creates a fresh BPL variable to represent <paramref name="type"/>, deciding
    /// on its type based on the heap representation. I.e., the value of this
    /// variable represents the value of the expression "typeof(type)".
    /// </summary>
    Bpl.Variable CreateTypeVariable(ITypeReference type, List<Bpl.ConstantParent> parents);

    Bpl.Variable CreateEventVariable(IEventDefinition e);

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to the value of the field
    /// <paramref name="f"/> belonging to the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>.
    /// </param>
    Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.Expr f, AccessType accessType, Bpl.Type unboxType);

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.Expr f, Bpl.Expr value, AccessType accessType, Bpl.Type boxType);

    /// <summary>
    /// Returns the BPL expression that corresponds to the value of the dynamic type
    /// of the object represented by the expression <paramref name="o"/>.
    /// </summary>
    Bpl.Expr DynamicType(Bpl.Expr o);

  }
  
  public enum AccessType { Array, Heap, Struct };

  public abstract class Heap : HeapFactory, IHeap
  {
    [RepresentationFor("$ArrayContents", "var $ArrayContents: [Ref][int]Union;")]
    public Bpl.Variable ArrayContentsVariable = null;
    [RepresentationFor("$ArrayLength", "function $ArrayLength(Ref): int;")]
    public Bpl.Function ArrayLengthFunction = null;

    public abstract Bpl.Variable CreateFieldVariable(IFieldReference field);

    #region Boogie Types

    [RepresentationFor("Delegate", "type {:datatype} Delegate;")]
    public Bpl.TypeCtorDecl DelegateTypeDecl = null;
    public Bpl.CtorType DelegateType;

    [RepresentationFor("DelegateMultiset", "type DelegateMultiset = [Delegate]int;")]
    public Bpl.TypeSynonymDecl DelegateMultisetTypeDecl = null;
    public Bpl.TypeSynonymAnnotation DelegateMultisetType;

    [RepresentationFor("MultisetEmpty", "const unique MultisetEmpty: DelegateMultiset;")]
    public Bpl.Constant MultisetEmpty = null;

    [RepresentationFor("MultisetSingleton", "function {:inline} MultisetSingleton(x: Delegate): DelegateMultiset { MultisetEmpty[x := 1] }")]
    public Bpl.Function MultisetSingleton = null;

    [RepresentationFor("MultisetPlus", "function {:inline} MultisetPlus(x: DelegateMultiset, y: DelegateMultiset): DelegateMultiset { mapadd(x, y) }")]
    public  Bpl.Function MultisetPlus = null;

    [RepresentationFor("MultisetMinus", "function {:inline} MultisetMinus(x: DelegateMultiset, y: DelegateMultiset): DelegateMultiset { mapiteint(mapgt(x, y), mapsub(x, y), mapconstint(0)) }")]
    public Bpl.Function MultisetMinus = null;

    [RepresentationFor("Field", "type Field;")]
    public Bpl.TypeCtorDecl FieldTypeDecl = null;
    public Bpl.CtorType FieldType;

    [RepresentationFor("Union", "type {:datatype} Union;")]
    public Bpl.TypeCtorDecl UnionTypeDecl = null;
    public Bpl.CtorType UnionType;

    [RepresentationFor("$DefaultHeapValue", "const unique $DefaultHeapValue : Union;")]
    public Bpl.Constant DefaultHeapValue;

    [RepresentationFor("Ref", "type Ref;")]
    public Bpl.TypeCtorDecl RefTypeDecl = null;
    public Bpl.CtorType RefType;
    [RepresentationFor("null", "const unique null : Ref;")]
    public Bpl.Constant NullRef;

    [RepresentationFor("Type", "type {:datatype} Type;")]
    public Bpl.TypeCtorDecl TypeTypeDecl = null;
    public Bpl.CtorType TypeType;

    [RepresentationFor("Real", "type Real;")]
    protected Bpl.TypeCtorDecl RealTypeDecl = null;
    public Bpl.CtorType RealType;
    [RepresentationFor("$DefaultReal", "const unique $DefaultReal : Real;")]
    public Bpl.Constant DefaultReal;

    #endregion

    #region CLR Boxing

    [RepresentationFor("$BoxFromBool", "procedure $BoxFromBool(b: bool) returns (r: Ref) free ensures $BoxedValue(r) == Bool2Union(b); { call r := Alloc(); assume $BoxedValue(r) == Bool2Union(b); }")]
    public Bpl.Procedure BoxFromBool = null;

    [RepresentationFor("$BoxFromInt", "procedure $BoxFromInt(i: int) returns (r: Ref) free ensures $BoxedValue(r) == Int2Union(i); { call r := Alloc(); assume $BoxedValue(r) == Int2Union(i); }")]
    public Bpl.Procedure BoxFromInt = null;

    [RepresentationFor("$BoxFromReal", "procedure $BoxFromReal(r: Real) returns (rf: Ref) free ensures $BoxedValue(rf) == Real2Union(r); { call rf := Alloc(); assume $BoxedValue(rf) == Real2Union(r); }")]
    public Bpl.Procedure BoxFromReal = null;

    [RepresentationFor("$BoxFromStruct", "procedure $BoxFromStruct(s: Ref) returns (r: Ref) free ensures $BoxedValue(r) == Struct2Union(s); { call r := Alloc(); assume $BoxedValue(r) == Struct2Union(s); }")]
    public Bpl.Procedure BoxFromStruct = null;

    [RepresentationFor("$BoxFromUnion", "procedure {:inline 1} $BoxFromUnion(u: Union) returns (r: Ref) { if (is#Ref2Union(u)) { r := refValue#Ref2Union(u); } else { call r := Alloc(); assume $BoxedValue(r) == u; } }")]
    public Bpl.Procedure BoxFromUnion = null;

    [RepresentationFor("$BoxedValue", "function $BoxedValue(r: Ref): Union;")]
    public Bpl.Function BoxedValue = null;

    [RepresentationFor("$Unbox2Bool", "function $Unbox2Bool(r: Ref): (bool) { boolValue#Bool2Union($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Bool = null;

    [RepresentationFor("$Unbox2Int", "function $Unbox2Int(r: Ref): (int) { intValue#Int2Union($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Int = null;

    [RepresentationFor("$Unbox2Real", "function $Unbox2Real(r: Ref): (Real) { realValue#Real2Union($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Real = null;

    [RepresentationFor("$Unbox2Struct", "function $Unbox2Struct(r: Ref): (Ref) { structValue#Struct2Union($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Struct = null;

    [RepresentationFor("$Unbox2Union", "function $Unbox2Union(r: Ref): (Union) { $BoxedValue(r) }")]
    public Bpl.Function Unbox2Union = null;

    #endregion

    #region Conversions

    #region Heap values

    [RepresentationFor("Union2Bool", "function Union2Bool(u: Union): (bool) { boolValue#Bool2Union(u) }")]
    public Bpl.Function Union2Bool = null;
    
    [RepresentationFor("Union2Int", "function Union2Int(u: Union): (int) { intValue#Int2Union(u) }")]
    public Bpl.Function Union2Int = null;
    
    [RepresentationFor("Union2Ref", "function Union2Ref(u: Union): (Ref) { refValue#Ref2Union(u) }")]
    public Bpl.Function Union2Ref = null;

    [RepresentationFor("Union2Real", "function Union2Real(u: Union): (Real) { realValue#Real2Union(u) }")]
    public Bpl.Function Union2Real = null;

    [RepresentationFor("Union2Struct", "function Union2Struct(u: Union): (Ref) { structValue#Struct2Union(u) }")]
    public Bpl.Function Union2Struct = null;

    [RepresentationFor("Bool2Union", "function {:constructor} Bool2Union(boolValue: bool): Union;")]
    public Bpl.Function Bool2Union = null;

    [RepresentationFor("Int2Union", "function {:constructor} Int2Union(intValue: int): Union;")]
    public Bpl.Function Int2Union = null;

    [RepresentationFor("Ref2Union", "function {:constructor} Ref2Union(refValue: Ref): Union;")]
    public Bpl.Function Ref2Union = null;

    [RepresentationFor("Real2Union", "function {:constructor} Real2Union(realValue: Real): Union;")]
    public Bpl.Function Real2Union = null;

    [RepresentationFor("Struct2Union", "function {:constructor} Struct2Union(structValue: Ref): Union;")]
    public Bpl.Function Struct2Union = null;

    [RepresentationFor("Union2Union", "function {:inline true} Union2Union(u: Union): Union { u }")]
    public Bpl.Function Union2Union = null;

    public Bpl.Expr ToUnion(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr) {
      Bpl.Function conversion;
      if (boogieType == Bpl.Type.Bool)
        conversion = this.Bool2Union;
      else if (boogieType == Bpl.Type.Int)
        conversion = this.Int2Union;
      else if (boogieType == RefType)
        conversion = this.Ref2Union;
      else if (boogieType == RealType)
        conversion = this.Real2Union;
      else if (boogieType == UnionType)
        conversion = this.Union2Union;
      else
        throw new InvalidOperationException(String.Format("Unknown Boogie type: '{0}'", boogieType.ToString()));

      var callConversion = new Bpl.NAryExpr(
        tok,
        new Bpl.FunctionCall(conversion),
        new Bpl.ExprSeq(expr)
        );
      return callConversion;
    }

    public Bpl.Expr FromUnion(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr) {
      Bpl.Function conversion = null;
      if (boogieType == Bpl.Type.Bool)
        conversion = this.Union2Bool;
      else if (boogieType == Bpl.Type.Int)
        conversion = this.Union2Int;
      else if (boogieType == RefType)
        conversion = this.Union2Ref;
      else if (boogieType == RealType)
        conversion = this.Union2Real;
      else if (boogieType == UnionType)
        conversion = this.Union2Union;
      else
        throw new InvalidOperationException(String.Format("Unknown Boogie type: '{0}'", boogieType.ToString()));

      var callExpr = new Bpl.NAryExpr(
        tok,
        new Bpl.FunctionCall(conversion),
        new Bpl.ExprSeq(expr)
        );
      callExpr.Type = boogieType;
      return callExpr;
    }

    #endregion

    #region Real number conversions
    [RepresentationFor("Int2Real", "function Int2Real(int): Real;")]
    public Bpl.Function Int2Real = null;
    [RepresentationFor("Real2Int", "function Real2Int(Real): int;")]
    public Bpl.Function Real2Int = null;
    #endregion

    #region Real number operations
    [RepresentationFor("RealPlus", "function RealPlus(Real, Real): Real;")]
    public Bpl.Function RealPlus = null;
    [RepresentationFor("RealMinus", "function RealMinus(Real, Real): Real;")]
    public Bpl.Function RealMinus = null;
    [RepresentationFor("RealTimes", "function RealTimes(Real, Real): Real;")]
    public Bpl.Function RealTimes = null;
    [RepresentationFor("RealDivide", "function RealDivide(Real, Real): Real;")]
    public Bpl.Function RealDivide = null;
    [RepresentationFor("RealModulus", "function RealModulus(Real, Real): Real;")]
    public Bpl.Function RealModulus = null;
    [RepresentationFor("RealLessThan", "function RealLessThan(Real, Real): bool;")]
    public Bpl.Function RealLessThan = null;
    [RepresentationFor("RealLessThanOrEqual", "function RealLessThanOrEqual(Real, Real): bool;")]
    public Bpl.Function RealLessThanOrEqual = null;
    [RepresentationFor("RealGreaterThan", "function RealGreaterThan(Real, Real): bool;")]
    public Bpl.Function RealGreaterThan = null;
    [RepresentationFor("RealGreaterThanOrEqual", "function RealGreaterThanOrEqual(Real, Real): bool;")]
    public Bpl.Function RealGreaterThanOrEqual = null;
    #endregion

    #region Bitwise operations
    [RepresentationFor("BitwiseAnd", "function BitwiseAnd(int, int): int;")]
    public Bpl.Function BitwiseAnd = null;
    [RepresentationFor("BitwiseOr", "function BitwiseOr(int, int): int;")]
    public Bpl.Function BitwiseOr = null;
    [RepresentationFor("BitwiseExclusiveOr", "function BitwiseExclusiveOr(int, int): int;")]
    public Bpl.Function BitwiseExclusiveOr = null;
    [RepresentationFor("BitwiseNegation", "function BitwiseNegation(int): int;")]
    public Bpl.Function BitwiseNegation = null;
    [RepresentationFor("RightShift", "function RightShift(int,int): int;")]
    public Bpl.Function RightShift = null;
    [RepresentationFor("LeftShift", "function LeftShift(int,int): int;")]
    public Bpl.Function LeftShift = null;
    #endregion

    #endregion

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="type"/>, deciding
    /// on its type based on the heap representation. I.e., the value of this
    /// variable represents the value of the expression "typeof(type)".
    /// </summary>
    public Bpl.Variable CreateTypeVariable(ITypeReference type, List<Bpl.ConstantParent> parents)
    {
      string typename = TypeHelper.GetTypeName(type, NameFormattingOptions.DocumentationId);
        typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
        Bpl.IToken tok = type.Token();
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, typename, this.TypeType);
        Bpl.Constant v = new Bpl.Constant(tok, tident, true /*unique*/, parents, false, null);
        return v;
    }

    public Bpl.Function CreateTypeFunction(ITypeReference type, int parameterCount) {
      System.Diagnostics.Debug.Assert(parameterCount >= 0);
      string typename = TypeHelper.GetTypeName(type, NameFormattingOptions.DocumentationId);
      typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
      Bpl.IToken tok = type.Token();
      Bpl.VariableSeq inputs = new Bpl.VariableSeq();
      //for (int i = 0; i < parameterCount; i++) {
      //  inputs.Add(new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "arg"+i, this.TypeType), true));
      //}
      foreach (var t in TranslationHelper.ConsolidatedGenericParameters(type)) {
        var n = t.Name.Value;
        var n2 = TranslationHelper.TurnStringIntoValidIdentifier(n);
        inputs.Add(new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, n2, this.TypeType), true));
      }
      Bpl.Variable output = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "result", this.TypeType), false);
      Bpl.Function func = new Bpl.Function(tok, typename, inputs, output);
      var attrib = new Bpl.QKeyValue(Bpl.Token.NoToken, "constructor", new List<object>(1), null);
      func.Attributes = attrib;
      return func;
    }
    

    public abstract Bpl.Variable CreateEventVariable(IEventDefinition e);

    public abstract Bpl.Expr ReadHeap(Bpl.Expr o, Bpl.Expr f, AccessType accessType, Bpl.Type unboxType);

    public abstract Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr o, Bpl.Expr f, Bpl.Expr value, AccessType accessType, Bpl.Type boxType);

    [RepresentationFor("$DynamicType", "function $DynamicType(Ref): Type;")]
    protected Bpl.Function DynamicTypeFunction = null;

    /// <summary>
    /// Returns the BPL expression that corresponds to the value of the dynamic type
    /// of the object represented by the expression <paramref name="o"/>.
    /// </summary>
    public Bpl.Expr DynamicType(Bpl.Expr o) {
      // $DymamicType(o)
      var callDynamicType = new Bpl.NAryExpr(
        o.tok,
        new Bpl.FunctionCall(this.DynamicTypeFunction),
        new Bpl.ExprSeq(o)
        );
      return callDynamicType;
    }

    [RepresentationFor("$TypeOf", "function $TypeOf(Type): Ref;")]
    public Bpl.Function TypeOfFunction = null;

    [RepresentationFor("$As", "function $As(Ref, Type): Ref;")]
    public Bpl.Function AsFunction = null;

    [RepresentationFor("$Subtype", "function $Subtype(Type, Type): bool;")]
    public Bpl.Function Subtype = null;

    [RepresentationFor("$DisjointSubtree", "function $DisjointSubtree(Type, Type): bool;")]
    public Bpl.Function DisjointSubtree = null;

    protected readonly string CommonText =
      @"var $Alloc: [Ref] bool;

procedure {:inline 1} Alloc() returns (x: Ref)
  modifies $Alloc;
{
  assume $Alloc[x] == false && x != null;
  $Alloc[x] := true;
}

function {:builtin ""MapAdd""} mapadd([Delegate]int, [Delegate]int) : [Delegate]int;
function {:builtin ""MapSub""} mapsub([Delegate]int, [Delegate]int) : [Delegate]int;
function {:builtin ""MapMul""} mapmul([Delegate]int, [Delegate]int) : [Delegate]int;
function {:builtin ""MapDiv""} mapdiv([Delegate]int, [Delegate]int) : [Delegate]int;
function {:builtin ""MapMod""} mapmod([Delegate]int, [Delegate]int) : [Delegate]int;
function {:builtin ""MapConst""} mapconstint(int) : [Delegate]int;
function {:builtin ""MapConst""} mapconstbool(bool) : [Delegate]bool;
function {:builtin ""MapAnd""} mapand([Delegate]bool, [Delegate]bool) : [Delegate]bool;
function {:builtin ""MapOr""} mapor([Delegate]bool, [Delegate]bool) : [Delegate]bool;
function {:builtin ""MapNot""} mapnot([Delegate]bool) : [Delegate]bool;
function {:builtin ""MapIte""} mapiteint([Delegate]bool, [Delegate]int, [Delegate]int) : [Delegate]int;
function {:builtin ""MapIte""} mapitebool([Delegate]bool, [Delegate]bool, [Delegate]bool) : [Delegate]bool;
function {:builtin ""MapLe""} maple([Delegate]int, [Delegate]int) : [Delegate]bool;
function {:builtin ""MapLt""} maplt([Delegate]int, [Delegate]int) : [Delegate]bool;
function {:builtin ""MapGe""} mapge([Delegate]int, [Delegate]int) : [Delegate]bool;
function {:builtin ""MapGt""} mapgt([Delegate]int, [Delegate]int) : [Delegate]bool;
function {:builtin ""MapEq""} mapeq([Delegate]int, [Delegate]int) : [Delegate]bool;
function {:builtin ""MapIff""} mapiff([Delegate]bool, [Delegate]bool) : [Delegate]bool;
function {:builtin ""MapImp""} mapimp([Delegate]bool, [Delegate]bool) : [Delegate]bool;
axiom MultisetEmpty == mapconstint(0);

/*
// Subtype is reflexive
axiom (forall t: Type :: $Subtype(t, t) );

// Subtype is anti-symmetric
axiom (forall t0 : Type, t1 : Type :: { $Subtype(t0, t1), $Subtype(t1, t0) }
        $Subtype(t0, t1) && $Subtype(t1, t0) ==> (t0 == t1) );

// Subtype is transitive
axiom (forall t0 : Type, t1 : Type, t2 : Type :: { $Subtype(t0, t1), $Subtype(t1, t2) }
        $Subtype(t0, t1) && $Subtype(t1, t2) ==> $Subtype(t0, t2) );

// Incomparable subtypes: the subtrees are disjoint for (some) subtypes (those that imply single inheritance)
function oneDown(t0 : Type, t1 : Type) : Type; // uninterpreted function with no axioms
axiom (forall C : Type, D : Type :: { $DisjointSubtree(D, C) }
        $DisjointSubtree(D, C) <==> (forall z : Type :: $Subtype(z, D) ==> oneDown(C,z) == D) );
*/

function $TypeOfInv(Ref): Type;
axiom (forall t: Type :: {$TypeOf(t)} $TypeOfInv($TypeOf(t)) == t);

procedure {:inline 1} System.Object.GetType(this: Ref) returns ($result: Ref)
{
  $result := $TypeOf($DynamicType(this));
}

axiom Union2Int($DefaultHeapValue) == 0;
axiom Union2Bool($DefaultHeapValue) == false;
axiom Union2Ref($DefaultHeapValue) == null;

function $ThreadDelegate(Ref) : Ref;

procedure {:inline 1} System.Threading.Thread.#ctor$System.Threading.ParameterizedThreadStart(this: Ref, start$in: Ref)
{
  assume $ThreadDelegate(this) == start$in;
}
procedure {:inline 1} System.Threading.Thread.Start$System.Object(this: Ref, parameter$in: Ref)
{
  call {:async} Wrapper_System.Threading.ParameterizedThreadStart.Invoke$System.Object($ThreadDelegate(this), parameter$in);
}
procedure Wrapper_System.Threading.ParameterizedThreadStart.Invoke$System.Object(this: Ref, obj$in: Ref) {
  $Exception := null;
  call System.Threading.ParameterizedThreadStart.Invoke$System.Object(this, obj$in);
}
procedure {:extern} System.Threading.ParameterizedThreadStart.Invoke$System.Object(this: Ref, obj$in: Ref);

procedure {:inline 1} System.Threading.Thread.#ctor$System.Threading.ThreadStart(this: Ref, start$in: Ref) 
{
  assume $ThreadDelegate(this) == start$in;
}
procedure {:inline 1} System.Threading.Thread.Start(this: Ref) 
{
  call {:async} Wrapper_System.Threading.ThreadStart.Invoke($ThreadDelegate(this));
}
procedure Wrapper_System.Threading.ThreadStart.Invoke(this: Ref) {
  $Exception := null;
  call System.Threading.ThreadStart.Invoke(this);
}
procedure {:extern} System.Threading.ThreadStart.Invoke(this: Ref);

procedure {:inline 1} DelegateAdd(a: Ref, b: Ref) returns (c: Ref)
{
  var d: Delegate;

    if (a == null)
    {
        c := b;
    }
    else if (b == null)
    {
        c := a;
    }
    else 
    {
        call c := Alloc();
        assume $RefToDelegate(c) == $RefToDelegate(a) || $RefToDelegate(c) == $RefToDelegate(b);
        assume $RefToDelegateMultiset(c) == MultisetPlus($RefToDelegateMultiset(a), $RefToDelegateMultiset(b));
    }
}

procedure {:inline 1} DelegateRemove(a: Ref, b: Ref) returns (c: Ref)
{
  var d: Delegate;

    if (a == null)
    {
        c := null;
    }
    else if (b == null)
    {
        c := a;
    } 
    else if (MultisetMinus($RefToDelegateMultiset(a), $RefToDelegateMultiset(b)) == MultisetEmpty)
    {
        c := null;
    }
    else 
    {
        call c := Alloc();
        assume $RefToDelegateMultiset(c) == MultisetMinus($RefToDelegateMultiset(a), $RefToDelegateMultiset(b));
    }
}

procedure {:inline 1} DelegateCreate(d: Delegate) returns (c: Ref)
{
    call c := Alloc();
    assume $RefToDelegate(c) == d;
    assume $RefToDelegateMultiset(c) == MultisetSingleton(d);
}

procedure {:inline 1} System.String.op_Equality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool);
procedure {:inline 1} System.String.op_Inequality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool);

implementation System.String.op_Equality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool) {
  $result := (a$in == b$in);
}

implementation System.String.op_Inequality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool) {
  $result := (a$in != b$in);
}

// SILVERLIGHT CONTROL SPECIFIC CODE
var isControlEnabled: [Ref]bool;
var isControlChecked: [Ref]bool;

procedure {:inline 1} System.Windows.Controls.Control.set_IsEnabled$System.Boolean($this: Ref, value$in: bool);
implementation System.Windows.Controls.Control.set_IsEnabled$System.Boolean($this: Ref, value$in: bool) {
  $Exception:=null;
  isControlEnabled[$this] := value$in;
}

procedure {:inline 1} System.Windows.Controls.Control.get_IsEnabled($this: Ref) returns ($result: Ref);
implementation System.Windows.Controls.Control.get_IsEnabled($this: Ref) returns ($result: Ref) {
  var enabledness: bool;
  $Exception:=null;
  enabledness := isControlEnabled[$this];
  $result := Union2Ref(Bool2Union(enabledness));
}

procedure {:inline 1} System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($this: Ref, value$in: Ref);
implementation System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($this: Ref, value$in: Ref) {
  var check: bool;
  $Exception:=null;
  check := Union2Bool(Ref2Union(value$in));
  isControlChecked[$this] := check;
}

procedure {:inline 1} System.Windows.Controls.Primitives.ToggleButton.get_IsChecked($this: Ref) returns ($result: Ref);
implementation System.Windows.Controls.Primitives.ToggleButton.get_IsChecked($this: Ref) returns ($result: Ref) {
  var isChecked: bool;
  $Exception:=null;
  isChecked := isControlChecked[$this];
  $result := Union2Ref(Bool2Union(isChecked));
}

";

    [RepresentationFor("$RefToDelegate", "function $RefToDelegate(Ref): Delegate;")]
    public Bpl.Function RefToDelegate = null;

    [RepresentationFor("$RefToDelegateMultiset", "function $RefToDelegateMultiset(Ref): DelegateMultiset;")]
    public Bpl.Function RefToDelegateMultiset = null;

    [RepresentationFor("$RefToDelegateMultisetCons", "function {:constructor} $RefToDelegateMultisetCons($Method: int, $Receiver: Ref, $TypeParameters: Type): Delegate;")]
    public Bpl.DatatypeConstructor DelegateCons = null;

    public Bpl.Function DelegateMethod {
      get { return DelegateCons.selectors[0]; }
    }

    public Bpl.Function DelegateReceiver {
      get { return DelegateCons.selectors[1]; }
    }

    public Bpl.Function DelegateTypeParameters {
      get { return DelegateCons.selectors[2]; }
    }

    [RepresentationFor("$Exception", "var {:thread_local} $Exception: Ref;")]
    public Bpl.GlobalVariable ExceptionVariable = null;
  }

  public abstract class HeapFactory {

    /// <summary>
    /// Returns two things: an object that determines the heap representation,
    /// and (optionally) an initial program that contains declarations needed
    /// for the heap representation.
    /// </summary>
    /// <param name="sink">
    /// The heap might need to generate declarations so it needs access to the Sink.
    /// </param>
    /// <returns>
    /// false if and only if an error occurrs and the heap and/or program are not in a
    /// good state to be used.
    /// </returns>
    public abstract bool MakeHeap(Sink sink, out Heap heap, out Bpl.Program/*?*/ program);
  }

}