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
    Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, bool isStruct);

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value, bool isStruct);

    /// <summary>
    /// Returns the BPL expression that corresponds to the value of the dynamic type
    /// of the object represented by the expression <paramref name="o"/>.
    /// </summary>
    Bpl.Expr DynamicType(Bpl.Expr o);

  }

  public abstract class Heap : HeapFactory, IHeap
  {
    public abstract Bpl.Variable CreateFieldVariable(IFieldReference field);

    [RepresentationFor("Field", "type Field;")]
    public Bpl.TypeCtorDecl FieldTypeDecl = null;
    public Bpl.CtorType FieldType;

    [RepresentationFor("box", "type box;")]
    public Bpl.TypeCtorDecl BoxTypeDecl = null;
    public Bpl.CtorType BoxType;

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

    [RepresentationFor("Box2Int", "function Box2Int(box): int;")]
    public Bpl.Function Box2Int = null;

    [RepresentationFor("Box2Bool", "function Box2Bool(box): bool;")]
    public Bpl.Function Box2Bool = null;

    [RepresentationFor("Box2Struct", "function Box2Struct(box): struct;")]
    public Bpl.Function Box2Struct = null;

    [RepresentationFor("Int2Box", "function Int2Box(int): box;")]
    public Bpl.Function Int2Box = null;

    [RepresentationFor("Bool2Box", "function Bool2Box(bool): box;")]
    public Bpl.Function Bool2Box = null;

    [RepresentationFor("Struct2Box", "function Struct2Box(struct): box;")]
    public Bpl.Function Struct2Box = null;

    public Bpl.Expr Box(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr) {
      Bpl.Function conversion;
      if (boogieType == Bpl.Type.Bool)
        conversion = this.Bool2Box;
      else if (boogieType == Bpl.Type.Int)
        conversion = this.Int2Box;
      else if (boogieType == StructType)
        conversion = this.Struct2Box;
      else
        throw new InvalidOperationException("Unknown Boogie type");

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
      else
        throw new InvalidOperationException("Unknown Boogie type");

      var callExpr = new Bpl.NAryExpr(
        tok,
        new Bpl.FunctionCall(conversion),
        new Bpl.ExprSeq(expr)
        );
      callExpr.Type = boogieType;
      return callExpr;
    }
    
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

    public abstract Bpl.Expr ReadHeap(Bpl.Expr o, Bpl.IdentifierExpr f, bool isStruct);

    public abstract Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr o, Bpl.IdentifierExpr f, Bpl.Expr value, bool isStruct);

    [RepresentationFor("$DynamicType", "function $DynamicType(ref): Type;")]
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

    [RepresentationFor("$TypeOf", "function $TypeOf(Type): ref;")]
    public Bpl.Function TypeOfFunction = null;

    protected readonly string DelegateEncodingText =
      @"procedure DelegateAdd(a: int, b: int) returns (c: int)
{
  var m: int;
  var o: int;

  if (a == 0) {
    c := b;
    return;
  } else if (b == 0) {
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

procedure DelegateRemove(a: int, b: int) returns (c: int)
{
  var m: int;
  var o: int;

  if (a == 0) {
    c := 0;
    return;
  } else if (b == 0) {
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

procedure GetFirstElement(i: int) returns (m: int, o: int)
{
  var first: int;
  first := $Next[i][$Head[i]];
  m := $Method[i][first];
  o := $Receiver[i][first]; 
}

procedure DelegateAddHelper(oldi: int, m: int, o: int) returns (i: int)
{
  var x: int;
  var h: int;

  if (oldi == 0) {
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

procedure DelegateRemoveHelper(oldi: int, m: int, o: int) returns (i: int)
{
  var prev: int;
  var iter: int;
  var niter: int;

  i := oldi;
  if (i == 0) {
    return;
  }

  prev := 0;
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
  if (prev == 0) {
    return;
  }

  $Next[i] := $Next[i][prev := $Next[i][$Next[i][prev]]];
  if ($Next[i][$Head[i]] == $Head[i]) {
    i := 0;
  }
}

";

    [RepresentationFor("$Head", "var $Head: [int]int;")]
    public Bpl.GlobalVariable DelegateHead = null;

    [RepresentationFor("$Next", "var $Next: [int][int]int;")]
    public Bpl.GlobalVariable DelegateNext = null;
    
    [RepresentationFor("$Method", "var $Method: [int][int]int;")]
    public Bpl.GlobalVariable DelegateMethod = null;

    [RepresentationFor("$Receiver", "var $Receiver: [int][int]int;")]
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