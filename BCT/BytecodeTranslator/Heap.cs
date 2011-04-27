//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.IO;
using System.Reflection;


namespace BytecodeTranslator {

  /// <summary>
  /// A heap representation that uses a separate global variable for each
  /// field. Each global variable is a map from int to T where T is the
  /// type of the field.
  /// </summary>
  public class SplitFieldsHeap : Heap {

    /// <summary>
    /// Prelude text for which access to the ASTs is not needed
    /// </summary>
    private readonly string InitialPreludeText =
      @"const null: int;
type ref = int;
type struct = [Field]box;
type HeapType = [int,int]int;
var $Heap: HeapType where IsGoodHeap($Heap);
function IsGoodHeap(HeapType): bool;
var $ArrayContents: [int][int]int;
var $ArrayLength: [int]int;

var $Alloc: [int] bool;
procedure {:inline 1} Alloc() returns (x: int)
  free ensures x != 0;
  modifies $Alloc;
{
  assume $Alloc[x] == false;
  $Alloc[x] := true;
}

";
    private Sink sink;

    public override bool MakeHeap(Sink sink, out Heap heap, out Bpl.Program/*?*/ program) {
      heap = this;
      program = null;
      this.sink = sink;
      string prelude = this.InitialPreludeText + this.DelegateEncodingText;
      var b = RepresentationFor.ParsePrelude(prelude, this, out program);
      if (b) {
        this.BoxType = new Bpl.CtorType(this.BoxTypeDecl.tok, this.BoxTypeDecl, new Bpl.TypeSeq());
        this.FieldType = new Bpl.CtorType(this.FieldTypeDecl.tok, this.FieldTypeDecl, new Bpl.TypeSeq());
        this.TypeType = new Bpl.CtorType(this.TypeTypeDecl.tok, this.TypeTypeDecl, new Bpl.TypeSeq());
      }
      return b;
    }

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
    /// on its type based on the heap representation.
    /// </summary>
    public override Bpl.Variable CreateFieldVariable(IFieldReference field) {
      Bpl.Variable v;
      string fieldname = TypeHelper.GetTypeName(field.ContainingType) + "." + field.Name.Value;
      Bpl.IToken tok = field.Token();
      Bpl.Type t = this.sink.CciTypeToBoogie(field.Type.ResolvedType);

      if (field.IsStatic) {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.GlobalVariable(tok, tident);
      }
      else {
        Bpl.Type mt = new Bpl.MapType(tok, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Bpl.Type.Int), t);
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, mt);
        v = new Bpl.GlobalVariable(tok, tident);
      }
      return v;
    }

    public override Bpl.Variable CreateEventVariable(IEventDefinition e) {
      Bpl.Variable v;
      string eventName = TypeHelper.GetTypeName(e.ContainingType) + "." + e.Name.Value;
      Bpl.IToken tok = e.Token();
      Bpl.Type t = this.sink.CciTypeToBoogie(e.Type.ResolvedType);

      if (e.Adder.ResolvedMethod.IsStatic) {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, eventName, t);
        v = new Bpl.GlobalVariable(tok, tident);
      }
      else {
        Bpl.Type mt = new Bpl.MapType(tok, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Bpl.Type.Int), t);
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, eventName, mt);
        v = new Bpl.GlobalVariable(tok, tident);
      }
      return v;
    }

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to the value of the field
    /// <paramref name="f"/> belonging to the object <paramref name="o"/> (which must be non-null).
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>.
    /// </param>
    public override Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, bool isStruct) {
      if (isStruct)
        return Bpl.Expr.Select(o, f);
      else
        return Bpl.Expr.Select(f, o);
    }

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    public override Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value, bool isStruct) {
      Debug.Assert(o != null);
      if (isStruct)
        return Bpl.Cmd.MapAssign(tok, (Bpl.IdentifierExpr)o, f, value);
      else
        return Bpl.Cmd.MapAssign(tok, f, o, value);
    }

  }

  /// <summary>
  /// A heap representation that uses Boogie (in-line) functions
  /// for all heap reads and writes. That way the decision about
  /// how to exactly represent the heap is made in the Prelude.
  /// </summary>
  public class GeneralHeap : Heap {

    #region Fields

    [RepresentationFor("$Heap", "var $Heap: HeapType where IsGoodHeap($Heap);", true)]
    private Bpl.Variable HeapVariable = null;
    
    [RepresentationFor("Read", "function {:inline true} Read(H:HeapType, o:ref, f:Field): box { H[o, f] }")]
    private Bpl.Function Read = null;

    [RepresentationFor("Write", "function {:inline true} Write(H:HeapType, o:ref, f:Field, v:box): HeapType { H[o,f := v] }")]
    private Bpl.Function Write = null;

    /// <summary>
    /// Prelude text for which access to the ASTs is not needed
    /// </summary>
    private readonly string InitialPreludeText =
      @"const null: ref;
type ref = int;
type struct = [Field]box;
type HeapType = [ref,Field]box;
function IsGoodHeap(HeapType): bool;
var $ArrayContents: [int][int]int;
var $ArrayLength: [int]int;

var $Alloc: [ref] bool;
procedure {:inline 1} Alloc() returns (x: ref)
  free ensures x != null;
  modifies $Alloc;
{
  assume $Alloc[x] == false;
  $Alloc[x] := true;
}

";
    private Sink sink;

    #endregion

    public override bool MakeHeap(Sink sink, out Heap heap, out Bpl.Program/*?*/ program) {
      this.sink = sink;
      heap = this;
      program = null;
      string prelude = this.InitialPreludeText + this.DelegateEncodingText;
      var b = RepresentationFor.ParsePrelude(prelude, this, out program);
      if (b) {
        this.BoxType = new Bpl.CtorType(this.BoxTypeDecl.tok, this.BoxTypeDecl, new Bpl.TypeSeq());
        this.FieldType = new Bpl.CtorType(this.FieldTypeDecl.tok, this.FieldTypeDecl, new Bpl.TypeSeq());
        this.TypeType = new Bpl.CtorType(this.TypeTypeDecl.tok, this.TypeTypeDecl, new Bpl.TypeSeq());
      }
      return b;
    }

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
    /// on its type based on the heap representation.
    /// </summary>
    public override Bpl.Variable CreateFieldVariable(IFieldReference field) {
      Bpl.Variable v;
      string fieldname = TypeHelper.GetTypeName(field.ContainingType) + "." + field.Name.Value;
      fieldname = TranslationHelper.TurnStringIntoValidIdentifier(fieldname);
      Bpl.IToken tok = field.Token();

      if (field.IsStatic) {
        Bpl.Type t = this.sink.CciTypeToBoogie(field.Type.ResolvedType);
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.GlobalVariable(tok, tident);
      }
      else {
        Bpl.Type t = this.FieldType;
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.Constant(tok, tident, true);
      }
      this.underlyingTypes.Add(v, field.Type);
      return v;
    }
    private Dictionary<Bpl.Variable, ITypeReference> underlyingTypes = new Dictionary<Bpl.Variable, ITypeReference>();

    public override Bpl.Variable CreateEventVariable(IEventDefinition e) {
      Bpl.Variable v;
      string fieldname = TypeHelper.GetTypeName(e.ContainingType) + "." + e.Name.Value;
      Bpl.IToken tok = e.Token();

      if (e.Adder.ResolvedMethod.IsStatic) {
        Bpl.Type t = this.sink.CciTypeToBoogie(e.Type.ResolvedType);
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.GlobalVariable(tok, tident);
      }
      else {
        Bpl.Type t = this.FieldType;
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.Constant(tok, tident, true);
      }
      this.underlyingTypes.Add(v, e.Type);
      return v;
    }

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to the value of the field
    /// <paramref name="f"/> belonging to the object <paramref name="o"/> (which must be non-null).
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>.
    /// </param>
    public override Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, bool isStruct) {
      Debug.Assert(o != null);

      var callRead = isStruct ?
        Bpl.Expr.Select(o, f) :
        // $Read($Heap, o, f)
        new Bpl.NAryExpr(
          f.tok,
          new Bpl.FunctionCall(this.Read),
          new Bpl.ExprSeq(new Bpl.IdentifierExpr(f.tok, this.HeapVariable), o, f)
          );

      // wrap it in the right conversion function
      var originalType = this.underlyingTypes[f.Decl];
      var boogieType = sink.CciTypeToBoogie(originalType);
      var callExpr = Unbox(f.tok, boogieType, callRead);
      return callExpr;
    }

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    public override Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value, bool isStruct) {
      Debug.Assert(o != null);

      Bpl.IdentifierExpr h;
      Bpl.NAryExpr callWrite;
      var originalType = this.underlyingTypes[f.Decl];
      var boogieType = sink.CciTypeToBoogie(originalType);
      var callConversion = Box(f.tok, boogieType, value);

      if (isStruct) {
        h = (Bpl.IdentifierExpr)o;
        callWrite = Bpl.Expr.Store(h, f, callConversion);
      }
      else {
        // $Write($Heap, o, f)
        h = new Bpl.IdentifierExpr(f.tok, this.HeapVariable);
        callWrite = new Bpl.NAryExpr(
          f.tok,
          new Bpl.FunctionCall(this.Write),
          new Bpl.ExprSeq(h, o, f, callConversion)
          );
      }
      return Bpl.Cmd.SimpleAssign(f.tok, h, callWrite);
    }

  }

  internal class RepresentationFor : Attribute {
    internal string name;
    internal string declaration;
    internal bool required;
    internal RepresentationFor(string name, string declaration) { this.name = name; this.declaration = declaration; this.required = true; }
    internal RepresentationFor(string name, string declaration, bool required) { this.name = name; this.declaration = declaration; this.required = required; }

    internal static bool ParsePrelude(string initialPreludeText, object instance, out Bpl.Program/*?*/ prelude) {

      prelude = null;

      var flags = BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Instance;
      var type = instance.GetType();
      FieldInfo/*?*/[] fields = type.GetFields(flags);
      RepresentationFor[] rfs = new RepresentationFor[fields.Length];
      for (int i = 0; i < fields.Length; i++) {
        var field = fields[i];
        object[] cas = field.GetCustomAttributes(typeof(RepresentationFor), false);
        if (cas == null || cas.Length == 0) { // only look at fields that have the attribute
          fields[i] = null;
        }
        else {
          foreach (var a in cas) { // should be exactly one
            RepresentationFor rf = a as RepresentationFor;
            if (rf != null) {
              rfs[i] = rf;
              break;
            }
          }
        }
      }

      #region Gather all of the Boogie declarations from the fields of this class
      var preludeText = new StringBuilder(initialPreludeText);
      for (int i = 0; i < fields.Length; i++) {
        var field = fields[i];
        if (field == null) continue;
        preludeText.AppendLine(rfs[i].declaration);
      }
      #endregion

      #region Parse the declarations
      var ms = new MemoryStream(ASCIIEncoding.UTF8.GetBytes(preludeText.ToString()));
      int errorCount = Bpl.Parser.Parse(ms, "foo", new List<string>(), out prelude);
      if (prelude == null || errorCount > 0) {
        prelude = null;
        return false;
      }
      #endregion

      #region Use the compiled program to get the ASTs
      for (int i = 0; i < fields.Length; i++) {
        var field = fields[i];
        if (field == null) continue;
        if (!rfs[i].required) continue;
        var val = prelude.TopLevelDeclarations.First(d => { Bpl.NamedDeclaration nd = d as Bpl.NamedDeclaration; return nd != null && nd.Name.Equals(rfs[i].name); });
        field.SetValue(instance, val);
      }
      #endregion

      #region Check that every field in this class has been set
      for (int i = 0; i < fields.Length; i++) {
        var field = fields[i];
        if (field == null) continue;
        if (!rfs[i].required) continue;
        if (field.GetValue(instance) == null) {
          return false;
        }
      }
      #endregion Check that every field in this class has been set

      return true;
    }
  }

}