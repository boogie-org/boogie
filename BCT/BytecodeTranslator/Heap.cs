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


namespace BytecodeTranslator {

  /// <summary>
  /// A heap representation that uses a global variable, $Heap, which is
  /// a two-dimensional array indexed by objects and fields, each of which
  /// are represented as an integer.
  /// </summary>
  public class TwoDIntHeap : HeapFactory {

    public override IHeap MakeHeap(Sink sink) {
      return new HeapRepresentation(sink);
    }

    private class HeapRepresentation : IHeap {

      public HeapRepresentation(Sink sink) {
      }

      private Bpl.Variable HeapVariable {
        get {
          if (this.heapVariable == null)
            this.heapVariable = new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "$Heap", Bpl.Type.Int));
          return this.heapVariable;
        }
      }
      private Bpl.Variable heapVariable = null;

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
            new Bpl.IdentifierExpr(tok, this.HeapVariable), new Bpl.ExprSeq(f, o), value);
      }
    }

  }

  /// <summary>
  /// A heap representation that uses a separate global variable for each
  /// field. Each global variable is a map from int to T where T is the
  /// type of the field.
  /// </summary>
  public class SplitFieldsHeap : HeapFactory {

    public override IHeap MakeHeap(Sink sink) {
      return new HeapRepresentation(sink);
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
          return Bpl.Cmd.MapAssign(tok, f, o, value);
      }
    }

  }

}