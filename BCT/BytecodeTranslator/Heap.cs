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
  /// A heap representation that uses a global variable, $Heap, which is
  /// a two-dimensional array indexed by objects and fields, each of which
  /// are represented as an integer.
  /// </summary>
  public class TwoDIntHeap : HeapFactory, IHeap {

    #region Fields
    [RepresentationFor("$Heap", "var $Heap: HeapType where IsGoodHeap($Heap);", true)]
    private Bpl.Variable HeapVariable = null;

    //[RepresentationFor("HeapType", "type HeapType = [int,int]int;")]
    //private Bpl.TypeSynonymDecl HeapType = null;

    //[RepresentationFor("IsGoodHeap", "function IsGoodHeap(HeapType): bool;")]
    //private Bpl.Function IsGoodHeap = null;

    /// <summary>
    /// Prelude text for which access to the ASTs is not needed
    /// </summary>
    private readonly string InitialPreludeText =
      @"const null: int;
type HeapType = [int,int]int;
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
    
    #endregion

    public override bool MakeHeap(Sink sink, out IHeap heap, out Bpl.Program/*?*/ program) {
      heap = this;
      program = null;
      var b = RepresentationFor.ParsePrelude(this.InitialPreludeText, this, out program);
      return b;
    }

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
    /// on its type based on the heap representation.
    /// </summary>
    public Bpl.Variable CreateFieldVariable(IFieldReference field) {
      Bpl.Variable v;
      string fieldname = TypeHelper.GetTypeName(field.ContainingType) + "." + field.Name.Value;
      Bpl.IToken tok = field.Token();
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(field.Type.ResolvedType);

      if (field.IsStatic) {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.GlobalVariable(tok, tident);
      } else {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.Constant(tok, tident, true);
      }
      return v;
    }

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to the value of the field
    /// <paramref name="f"/> belonging to the object <paramref name="o"/> (when
    /// <paramref name="o"/> is non-null, otherwise the value of the static field.
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// Null if <paramref name="f"/> is a static field.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>, when
    /// it is not null. Otherwise the static field whose value should be read.
    /// </param>
    public Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f) {
      return Bpl.Expr.Select(new Bpl.IdentifierExpr(f.tok, HeapVariable), new Bpl.Expr[] { o, f });
    }

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (when
    /// <paramref name="o"/> is non-null, otherwise it is an assignment to the static
    /// field.
    /// </summary>
    public Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value) {
      if (o == null)
        return Bpl.Cmd.SimpleAssign(tok, f, value);
      else
        return
          Bpl.Cmd.MapAssign(tok,
          new Bpl.IdentifierExpr(tok, this.HeapVariable), new Bpl.ExprSeq(o, f), value);
    }


  }

  /// <summary>
  /// A heap representation that uses a separate global variable for each
  /// field. Each global variable is a map from int to T where T is the
  /// type of the field.
  /// </summary>
  public class SplitFieldsHeap : HeapFactory {

    /// <summary>
    /// Prelude text for which access to the ASTs is not needed
    /// </summary>
    private readonly string InitialPreludeText =
      @"const null: int;
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

    public override bool MakeHeap(Sink sink, out IHeap heap, out Bpl.Program/*?*/ program) {
      heap = new HeapRepresentation(sink);
      program = null;
      var b = RepresentationFor.ParsePrelude(this.InitialPreludeText, this, out program);
      return b;
    }

    private class HeapRepresentation : IHeap {

      public HeapRepresentation(Sink sink) {
      }

      /// <summary>
      /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
      /// on its type based on the heap representation.
      /// </summary>
      public Bpl.Variable CreateFieldVariable(IFieldReference field) {
        Bpl.Variable v;
        string fieldname = TypeHelper.GetTypeName(field.ContainingType) + "." + field.Name.Value;
        Bpl.IToken tok = field.Token();
        Bpl.Type t = TranslationHelper.CciTypeToBoogie(field.Type.ResolvedType);

        if (field.IsStatic) {
          Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
          v = new Bpl.GlobalVariable(tok, tident);
        } else {
          Bpl.Type mt = new Bpl.MapType(tok, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Bpl.Type.Int), t);
          Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, mt);
          v = new Bpl.GlobalVariable(tok, tident);
        }
        return v;
      }

      /// <summary>
      /// Returns the (typed) BPL expression that corresponds to the value of the field
      /// <paramref name="f"/> belonging to the object <paramref name="o"/> (when
      /// <paramref name="o"/> is non-null, otherwise the value of the static field.
      /// </summary>
      /// <param name="o">The expression that represents the object to be dereferenced.
      /// Null if <paramref name="f"/> is a static field.
      /// </param>
      /// <param name="f">The field that is used to dereference the object <paramref name="o"/>, when
      /// it is not null. Otherwise the static field whose value should be read.
      /// </param>
      public Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f) {
        return Bpl.Expr.Select(f, o);
      }

      /// <summary>
      /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
      /// to the field <paramref name="f"/> of the object <paramref name="o"/> (when
      /// <paramref name="o"/> is non-null, otherwise it is an assignment to the static
      /// field.
      /// </summary>
      public Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value) {
        if (o == null)
          return Bpl.Cmd.SimpleAssign(tok, f, value);
        else
          return Bpl.Cmd.MapAssign(tok, f, o, value);
      }
    }

  }

  /// <summary>
  /// A heap representation that uses a global variable, $Heap, which is
  /// a two-dimensional array indexed by objects and fields. Objects
  /// are values of type "int", fields are unique constants, and the
  /// elements of the heap are of type "box". Each value that is read/written
  /// from/to the heap is wrapped in a type conversion function.
  /// </summary>
  public class TwoDBoxHeap : HeapFactory, IHeap {

    #region Fields
    [RepresentationFor("$Heap", "var $Heap: HeapType where IsGoodHeap($Heap);", true)]
    private Bpl.Variable HeapVariable = null;

    [RepresentationFor("Box2Int", "function Box2Int(box): int;")]
    private Bpl.Function Box2Int = null;

    [RepresentationFor("Box2Bool", "function Box2Bool(box): bool;")]
    private Bpl.Function Box2Bool = null;

    [RepresentationFor("Int2Box", "function Int2Box(int): box;")]
    private Bpl.Function Int2Box = null;

    [RepresentationFor("Bool2Box", "function Bool2Box(bool): box;")]
    private Bpl.Function Bool2Box = null;

    /// <summary>
    /// Prelude text for which access to the ASTs is not needed
    /// </summary>
    private readonly string InitialPreludeText =
      @"const null: int;
type box;
type HeapType = [int,int]box;
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

    #endregion

    public override bool MakeHeap(Sink sink, out IHeap heap, out Bpl.Program/*?*/ program) {
      this.sink = sink;
      heap = this;
      program = null;
      var b = RepresentationFor.ParsePrelude(this.InitialPreludeText, this, out program);
      return b;
    }

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
    /// on its type based on the heap representation.
    /// </summary>
    public Bpl.Variable CreateFieldVariable(IFieldReference field) {
      Bpl.Variable v;
      string fieldname = TypeHelper.GetTypeName(field.ContainingType) + "." + field.Name.Value;
      Bpl.IToken tok = field.Token();
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(field.Type.ResolvedType);

      if (field.IsStatic) {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.GlobalVariable(tok, tident);
      } else {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.Constant(tok, tident, true);
      }
      return v;
    }

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to the value of the field
    /// <paramref name="f"/> belonging to the object <paramref name="o"/> (when
    /// <paramref name="o"/> is non-null, otherwise the value of the static field.
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// Null if <paramref name="f"/> is a static field.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>, when
    /// it is not null. Otherwise the static field whose value should be read.
    /// </param>
    public Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f) {
      // $Heap[o,f]
      var selectExpr = Bpl.Expr.Select(new Bpl.IdentifierExpr(f.tok, HeapVariable), new Bpl.Expr[] { o, f });
      // wrap it in the right conversion function
      Bpl.Function conversion;
      if (f.Type == Bpl.Type.Bool)
        conversion = this.Box2Bool;
      else if (f.Type == Bpl.Type.Int)
        conversion = this.Box2Int;
      else
        throw new InvalidOperationException("Unknown Boogie type");
      var callExpr = new Bpl.NAryExpr(
        f.tok,
        new Bpl.FunctionCall(conversion),
        new Bpl.ExprSeq(selectExpr)
        );
      return callExpr;

    }

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (when
    /// <paramref name="o"/> is non-null, otherwise it is an assignment to the static
    /// field.
    /// </summary>
    public Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value) {
      if (o == null) {
        return Bpl.Cmd.SimpleAssign(tok, f, value);
      } else {
        // wrap it in the right conversion function
        Bpl.Function conversion;
        if (f.Type == Bpl.Type.Bool)
          conversion = this.Bool2Box;
        else if (f.Type == Bpl.Type.Int)
          conversion = this.Int2Box;
        else
          throw new InvalidOperationException("Unknown Boogie type");

        // $Heap[o,f] := conversion(value)
        var callExpr = new Bpl.NAryExpr(
          f.tok,
          new Bpl.FunctionCall(conversion),
          new Bpl.ExprSeq(value)
          );
        return
          Bpl.Cmd.MapAssign(tok,
          new Bpl.IdentifierExpr(tok, this.HeapVariable), new Bpl.ExprSeq(o, f), callExpr);
      }
    }

  }

  internal class RepresentationFor : Attribute {
    internal string name;
    internal string declaration;
    internal bool required;
    internal RepresentationFor(string name, string declaration) { this.name = name; this.declaration = declaration;  this.required = true; }
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
        } else {
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