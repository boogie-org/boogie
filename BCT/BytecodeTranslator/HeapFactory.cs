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
    Bpl.Variable CreateTypeVariable(ITypeReference type);

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
    [RepresentationFor("$ArrayContents", "var $ArrayContents: [Ref][int]Box;")]
    public Bpl.Variable ArrayContentsVariable = null;
    [RepresentationFor("$ArrayLength", "function $ArrayLength(Ref): int;")]
    public Bpl.Function ArrayLengthFunction = null;

    public abstract Bpl.Variable CreateFieldVariable(IFieldReference field);

    #region Boogie Types

    [RepresentationFor("Field", "type Field;")]
    public Bpl.TypeCtorDecl FieldTypeDecl = null;
    public Bpl.CtorType FieldType;

    [RepresentationFor("Box", "type Box;")]
    public Bpl.TypeCtorDecl BoxTypeDecl = null;
    public Bpl.CtorType BoxType;

    [RepresentationFor("$DefaultBox", "const unique $DefaultBox : Box;")]
    public Bpl.Constant DefaultBox;

    [RepresentationFor("Ref", "type Ref;")]
    public Bpl.TypeCtorDecl RefTypeDecl = null;
    public Bpl.CtorType RefType;
    [RepresentationFor("null", "const unique null : Ref;")]
    public Bpl.Constant NullRef;

    [RepresentationFor("Type", "type Type;")]
    protected Bpl.TypeCtorDecl TypeTypeDecl = null;
    protected Bpl.CtorType TypeType;

    private Bpl.Type structType = null;
    public Bpl.Type StructType {
      get {
        if (structType == null) {
          structType = new Bpl.MapType(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(FieldType), BoxType);
        }
        return structType;
      }
    }
    [RepresentationFor("$DefaultStruct", "const unique $DefaultStruct : Struct;")]
    public Bpl.Constant DefaultStruct;

    [RepresentationFor("Real", "type Real;")]
    protected Bpl.TypeCtorDecl RealTypeDecl = null;
    public Bpl.CtorType RealType;

    #endregion

    #region Conversions

    #region Heap values

    [RepresentationFor("Box2Int", "function Box2Int(Box): int;")]
    public Bpl.Function Box2Int = null;

    [RepresentationFor("Box2Bool", "function Box2Bool(Box): bool;")]
    public Bpl.Function Box2Bool = null;

    [RepresentationFor("Box2Struct", "function Box2Struct(Box): Struct;")]
    public Bpl.Function Box2Struct = null;

    [RepresentationFor("Box2Ref", "function Box2Ref(Box): Ref;")]
    public Bpl.Function Box2Ref = null;

    [RepresentationFor("Box2Real", "function Box2Real(Box): Real;")]
    public Bpl.Function Box2Real = null;

    [RepresentationFor("Int2Box", "function Int2Box(int): Box;")]
    public Bpl.Function Int2Box = null;

    [RepresentationFor("Bool2Box", "function Bool2Box(bool): Box;")]
    public Bpl.Function Bool2Box = null;

    [RepresentationFor("Struct2Box", "function Struct2Box(Struct): Box;")]
    public Bpl.Function Struct2Box = null;

    [RepresentationFor("Ref2Box", "function Ref2Box(Ref): Box;")]
    public Bpl.Function Ref2Box = null;

    [RepresentationFor("Real2Box", "function Real2Box(Real): Box;")]
    public Bpl.Function Real2Box = null;

    [RepresentationFor("Box2Box", "function {:inline true} Box2Box(b: Box): Box { b }")]
    public Bpl.Function Box2Box = null;

    public Bpl.Expr Box(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr) {
      Bpl.Function conversion;
      if (boogieType == Bpl.Type.Bool)
        conversion = this.Bool2Box;
      else if (boogieType == Bpl.Type.Int)
        conversion = this.Int2Box;
      else if (boogieType == StructType)
        conversion = this.Struct2Box;
      else if (boogieType == RefType)
        conversion = this.Ref2Box;
      else if (boogieType == RealType)
        conversion = this.Real2Box;
      else if (boogieType == BoxType)
        conversion = this.Box2Box;
      else
        throw new InvalidOperationException(String.Format("Unknown Boogie type: '{0}'", boogieType.ToString()));

      var callConversion = new Bpl.NAryExpr(
        tok,
        new Bpl.FunctionCall(conversion),
        new Bpl.ExprSeq(expr)
        );
      return callConversion;
    }

    public Bpl.Expr Unbox(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr) {
      Bpl.Function conversion = null;
      if (boogieType == Bpl.Type.Bool)
        conversion = this.Box2Bool;
      else if (boogieType == Bpl.Type.Int)
        conversion = this.Box2Int;
      else if (boogieType == StructType)
        conversion = this.Box2Struct;
      else if (boogieType == RefType)
        conversion = this.Box2Ref;
      else if (boogieType == RealType)
        conversion = this.Box2Real;
      else if (boogieType == BoxType)
        conversion = this.Box2Box;
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

    #region "Boxing" as done in the CLR
    /// <summary>
    /// Used to represent "boxing" as it is done in the CLR.
    /// </summary>
    [RepresentationFor("Struct2Ref", "function Struct2Ref(Struct): Ref;")]
    public Bpl.Function Struct2Ref = null;
    [RepresentationFor("Int2Ref", "function Int2Ref(int): Ref;")]
    public Bpl.Function Int2Ref = null;
    [RepresentationFor("Bool2Ref", "function Bool2Ref(bool): Ref;")]
    public Bpl.Function Bool2Ref = null;
    #endregion

    #region Real number conversions
    [RepresentationFor("Int2Real", "function Int2Real(int, Type, Type): Real;")]
    public Bpl.Function Int2Real = null;
    [RepresentationFor("Real2Int", "function Real2Int(Real, Type, Type): Real;")]
    public Bpl.Function Real2Int = null;
    #endregion

    #endregion

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="type"/>, deciding
    /// on its type based on the heap representation. I.e., the value of this
    /// variable represents the value of the expression "typeof(type)".
    /// </summary>
    public Bpl.Variable CreateTypeVariable(ITypeReference type)
    {
        Bpl.Variable v;
        string typename = TypeHelper.GetTypeName(type);
        typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
        Bpl.IToken tok = type.Token();
        Bpl.Type t = this.TypeType;
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, typename, t);
        tident.Type = this.TypeType;
        v = new Bpl.Constant(tok, tident, true);
        return v;
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

    protected readonly string DelegateEncodingText =
      @"procedure DelegateAdd(a: Ref, b: Ref) returns (c: Ref)
{
  var m: int;
  var o: Ref;

  if (a == null) {
    c := b;
    return;
  } else if (b == null) {
    c := a;
    return;
  }

  call m, o := GetFirstElement(b);
  
  call c := Alloc();
  $Head[c] := $Head[a];
  $Next[c] := $Next[a];
  $Method[c] := $Method[a];
  $Receiver[c] := $Receiver[a];
  call c := DelegateAddHelper(c, m, o);
}

procedure DelegateRemove(a: Ref, b: Ref) returns (c: Ref)
{
  var m: int;
  var o: Ref;

  if (a == null) {
    c := null;
    return;
  } else if (b == null) {
    c := a;
    return;
  }

  call m, o := GetFirstElement(b);

  call c := Alloc();
  $Head[c] := $Head[a];
  $Next[c] := $Next[a];
  $Method[c] := $Method[a];
  $Receiver[c] := $Receiver[a];
  call c := DelegateRemoveHelper(c, m, o);
}

procedure GetFirstElement(i: Ref) returns (m: int, o: Ref)
{
  var first: Ref;
  first := $Next[i][$Head[i]];
  m := $Method[i][first];
  o := $Receiver[i][first]; 
}

procedure DelegateAddHelper(oldi: Ref, m: int, o: Ref) returns (i: Ref)
{
  var x: Ref;
  var h: Ref;

  if (oldi == null) {
    call i := Alloc();
    call x := Alloc();
    $Head[i] := x;
    $Next[i] := $Next[i][x := x]; 
  } else {
    i := oldi;
  }

  h := $Head[i];
  $Method[i] := $Method[i][h := m];
  $Receiver[i] := $Receiver[i][h := o];
  
  call x := Alloc();
  $Next[i] := $Next[i][x := $Next[i][h]];
  $Next[i] := $Next[i][h := x];
  $Head[i] := x;
}

procedure DelegateRemoveHelper(oldi: Ref, m: int, o: Ref) returns (i: Ref)
{
  var prev: Ref;
  var iter: Ref;
  var niter: Ref;

  i := oldi;
  if (i == null) {
    return;
  }

  prev := null;
  iter := $Head[i];
  while (true) {
    niter := $Next[i][iter];
    if (niter == $Head[i]) {
      break;
    }
    if ($Method[i][niter] == m && $Receiver[i][niter] == o) {
      prev := iter;
    }
    iter := niter;
  }
  if (prev == null) {
    return;
  }

  $Next[i] := $Next[i][prev := $Next[i][$Next[i][prev]]];
  if ($Next[i][$Head[i]] == $Head[i]) {
    i := null;
  }
}

";

    [RepresentationFor("$Head", "var $Head: [Ref]Ref;")]
    public Bpl.GlobalVariable DelegateHead = null;

    [RepresentationFor("$Next", "var $Next: [Ref][Ref]Ref;")]
    public Bpl.GlobalVariable DelegateNext = null;
    
    [RepresentationFor("$Method", "var $Method: [Ref][Ref]int;")]
    public Bpl.GlobalVariable DelegateMethod = null;

    [RepresentationFor("$Receiver", "var $Receiver: [Ref][Ref]Ref;")]
    public Bpl.GlobalVariable DelegateReceiver = null;
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