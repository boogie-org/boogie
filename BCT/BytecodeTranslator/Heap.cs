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

  public class Heap {

    public Heap(){
    }

    public Bpl.Variable HeapVariable {
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
    public Bpl.Variable CreateFieldVariable(IFieldDefinition field) {
      Bpl.Variable v;
      string fieldname = field.ContainingTypeDefinition.ToString() + "." + field.Name.Value;
      Bpl.IToken tok = field.Token();
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(field.Type.ResolvedType);

      if (field.IsStatic) {
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
        v = new Bpl.GlobalVariable(tok, tident);
      } else {
        if (CommandLineOptions.SplitFields) {
          Bpl.Type mt = new Bpl.MapType(tok, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Bpl.Type.Int), t);
          Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, mt);
          v = new Bpl.GlobalVariable(tok, tident);
        } else {
          Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);
          v = new Bpl.Constant(tok, tident, true);
        }
      }
      return v;
    }

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to (conceptually) "H[o,f]".
    /// "Conceptually" because the heap might not be represented as a two-dimensional
    /// array.
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// Null if <paramref name="f"/> is a static field.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>.</param>
    public Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o,  Bpl.IdentifierExpr f) {

      if (CommandLineOptions.SplitFields) {
        return Bpl.Expr.Select(f, o);
      } else {
        return Bpl.Expr.Select(new Bpl.IdentifierExpr(f.tok, HeapVariable), new Bpl.Expr[] { o, f });
      }
    }

    /// <summary>
    /// Returns the BPL command that corresponds to (conceptually) "H[o,f] := v".
    /// "Conceptually" because the heap might not be represented as a two-dimensional
    /// array.
    /// </summary>
    public Bpl.Cmd WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.IdentifierExpr f, Bpl.Expr value) {

      if (CommandLineOptions.SplitFields) {
        return Bpl.Cmd.MapAssign(tok, f, o, value);
      } else {
        if (o == null)
          return Bpl.Cmd.SimpleAssign(tok, f, value);
        else
          return
            Bpl.Cmd.MapAssign(tok,
            new Bpl.IdentifierExpr(tok, this.HeapVariable), new Bpl.ExprSeq(f, o), value);
      }
    }
  }

}