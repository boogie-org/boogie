/*
Copyright (c) 2009, Sascha Boehme, Technische Universitaet Muenchen
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.
* Neither the name of the Technische Universitaet Muenchen nor the names of
  its contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
*/

using System;
using System.IO;
using System.Collections.Generic;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.Isabelle
{
  public class IsabelleProverOptions : ProverOptions
  {
    private string filename = null;
    public string! Filename = "";

    public bool AllTypes = false;
  
    protected override bool Parse(string! opt)
    {
      bool v2 = false;
      return
        ParseString(opt, "ISABELLE_INPUT", ref filename) ||
        ParseBool(opt, "ISABELLE_FULL", ref AllTypes) ||
        ParseBool(opt, "V2", ref v2) ||
        base.Parse(opt);
    }
    
    protected override void PostParse()
    {
      base.PostParse();

      if (filename == null)
      {
        ReportError("Missing ISABELLE_INPUT option. " +
          "This option expects a filename (with extension .b2i).");
      }
      else if (!Path.GetExtension(filename).Equals(".b2i"))
      {
        filename = Path.ChangeExtension(filename, ".b2i");
      }
      Filename = (string!) filename;
    }
  }


  public class Factory : ProverFactory
  {
    private static int index = 0;
  
    public override ProverOptions! BlankProverOptions()
    {
      return new IsabelleProverOptions();
    }
  
    public override object! NewProverContext(ProverOptions! options)
    {
      IsabelleProverOptions opts = (IsabelleProverOptions) options;
      string! filename = opts.Filename;
      lock (this)
      {
        if (index > 0)
        {
          filename = Path.ChangeExtension(filename, "." + index + ".b2i");
        }
        index++;
        if (File.Exists(filename)) { File.Delete(filename); }
      }
      return new IsabelleContext(filename, opts.AllTypes);
    }
  
    public override object! SpawnProver(ProverOptions! options, object! ctxt)
    {
      return new IsabelleInterface((ProverContext!) ctxt);
    }

    // we prefer DAG outputs over LET
    public override bool SupportsDags { get { return true; } }

    // this works well in Isabelle, but we do not get structural information
    public override CommandLineOptions.VCVariety DefaultVCVariety
    {
      get { return CommandLineOptions.VCVariety.Dag; }
    }
  }
  
  
  public class IsabelleInterface : ProverInterface
  {
    private static Dictionary<string!, int>! lastVCIndex = 
      new Dictionary<string!, int>();
  
    private IsabelleContext! ctxt;
    
    public IsabelleInterface(ProverContext! ctxt)
    {
      this.ctxt = (IsabelleContext!) ctxt; 
    }
    public override ProverContext! Context { get { return ctxt; } }
    public override VCExpressionGenerator! VCExprGen
    { 
      get { return ctxt.ExprGen; } 
    }

    public override void BeginCheck(string! name, VCExpr! vc, ErrorHandler! h)
    {
      int index;
      lock (lastVCIndex)
      {
        lastVCIndex.TryGetValue(name, out index);
        index++;
        lastVCIndex[name] = index;
      }
      lock (ctxt) { ctxt.AddVC(name + " " + index, vc, h); }
    }
    public override Outcome CheckOutcome(ErrorHandler! handler)
    {
      return Outcome.Undetermined; // we will check the goal later in Isabelle
    }
  }


  public class IsabelleContext : DeclFreeProverContext
  {
    private List<string!>! declaredFunctions = new List<string!>();
    public readonly string! OutputFilename;
    public bool IsFunctionDeclared(string! name)
    {
      return declaredFunctions.Contains(name);
    }
    public readonly bool AllTypes;
    
    public IsabelleContext(string! outputFilename, bool allTypes)
     : base(new VCExpressionGenerator(), new VCGenerationOptions(new List<string!>(new string![] { "bvInt", "bvDefSem", "bvint", "bvz", "external"})))
    {
      this.OutputFilename = outputFilename;
      this.AllTypes = allTypes;
    }
    
    public override object! Clone() { return this; }
  
    public override void DeclareType(TypeCtorDecl! t, string atts)
    {
      B2I! b2i = new B2I(this);
      b2i.Write(B2I.Kind.TypeDecl, t.Name + " " + t.Arity + " " +
        B2I.CountOf(t.Attributes));
      b2i.Indent(2);
      b2i.Write(t.Attributes, BoogieExprTranslator);
      b2i.Close();
    }
    
    public override void DeclareConstant(Constant! c, bool uniq, string atts)
    {
      QKeyValue attributes = c.Attributes;
      if (c.Unique) { attributes = B2I.Add("unique", null, attributes); }
      declaredFunctions.Add(c.Name);
        
      B2I! b2i = new B2I(this);
      if (AllTypes)
      {
        b2i.Write(B2I.Kind.FunDecl, c.Name + " 0 1 " +
          B2I.CountOf(attributes));
      }
      else
      {
        b2i.Write(B2I.Kind.FunDecl, c.Name + " 1 " + B2I.CountOf(attributes));
      }
      b2i.Indent(4);
      b2i.Write(c.TypedIdent.Type);
      b2i.Unindent();
      b2i.Indent(2);
      b2i.Write(attributes, BoogieExprTranslator);
      b2i.Close();
    }
    
    public override void DeclareFunction(Function! f, string atts)
    {
      declaredFunctions.Add(f.Name);
      
      B2I! b2i = new B2I(this);
      if (AllTypes)
      {
        b2i.Write(B2I.Kind.FunDecl, f.Name + " " + f.TypeParameters.Length + 
          " " + (f.InParams.Length + 1) + " " + B2I.CountOf(f.Attributes));
        b2i.Indent(4);
        foreach (TypeVariable! v in f.TypeParameters) { b2i.Write(v); }
        b2i.Unindent();
      }
      else
      {
        b2i.Write(B2I.Kind.FunDecl, f.Name + " " + (f.InParams.Length + 1) +
          " " + B2I.CountOf(f.Attributes));
      }
      b2i.Indent(4);
      foreach (Variable! v in f.InParams) { b2i.Write(v.TypedIdent.Type); }
      assert (f.OutParams.Length == 1);
      b2i.Write(((Variable!) f.OutParams[0]).TypedIdent.Type);
      b2i.Unindent();
      b2i.Indent(2);
      b2i.Write(f.Attributes, BoogieExprTranslator);
      b2i.Close();
    }
    
    public override void AddAxiom(Axiom! a, string atts)
    {
      B2I! b2i = new B2I(this);
      b2i.Write(B2I.Kind.Axiom, B2I.CountOf(a.Attributes).ToString());
      b2i.Indent(4);
      b2i.Write(BoogieExprTranslator.Translate(a.Expr));
      b2i.Unindent();
      b2i.Indent(2);
      b2i.Write(a.Attributes, BoogieExprTranslator);
      b2i.Close();
    }
    
    public override void AddAxiom(VCExpr! e)
    {
      B2I! b2i = new B2I(this);
      b2i.Write(B2I.Kind.Axiom, "0");
      b2i.Indent(4);
      b2i.Write(e);
      b2i.Close();
    }
    
    public override void DeclareGlobalVariable(GlobalVariable! v, string atts)
    {
      B2I! b2i = new B2I(this);
      b2i.Write(B2I.Kind.VarDecl, v.Name + " " + B2I.CountOf(v.Attributes));
      b2i.Indent(4);
      b2i.Write(v.TypedIdent.Type);
      b2i.Unindent();
      b2i.Indent(2);
      b2i.Write(v.Attributes, BoogieExprTranslator);
      b2i.Close();
    }
    
    public void AddVC(string! name, VCExpr! vc,
        ProverInterface.ErrorHandler! h)
    {
      B2I! b2i = new B2I(this);
      b2i.Write(B2I.Kind.VC, name);
      b2i.Indent(4);
      b2i.Write(vc, h);
      b2i.Close();
    }
  }
  
  
  class B2I
  {
    private TextWriter! w;
    private VCExprWriter! exprWriter = new VCExprWriter();
    private VCExprOpWriter! exprOpWriter = new VCExprOpWriter();
    private ProverInterface.ErrorHandler eh = null;
    public ProverInterface.ErrorHandler LabelRenamer { get { return eh; } }
    public readonly IsabelleContext! Context;
    private Stack<int>! indents;
    private static int[] default_indent = new int[] { 0 };

    public B2I(IsabelleContext! ctxt)
    {
      Context = ctxt;
      w = new StreamWriter(ctxt.OutputFilename, true);
      indents = new Stack<int>(default_indent);
    }
    public void Close() { w.Close(); }

    public void Indent(int indent) { indents.Push(indent + indents.Peek()); }
    public void Unindent() { indents.Pop(); }

    private void DoWrite(Kind k, string! s)
    {
      w.WriteLine(new String(' ', indents.Peek()) + StringOfKind(k) + s);
    }
    public void Write(Kind k) { DoWrite(k, ""); }
    public void Write(Kind k, string! s) { DoWrite(k, " " + s); }
    
    public void Write(Type! ty)
    {
      if (ty.IsInt) { Write(B2I.Kind.Int); }
      else if (ty.IsBool) { Write(B2I.Kind.Bool); }
      else if (ty.IsBv) { Write(B2I.Kind.BvType, ty.BvBits.ToString()); }
      else if (ty.IsVariable) { Write(B2I.Kind.TypeVar, ty.AsVariable.Name); }
      else if (ty.IsCtor)
      {
        CtorType! t = ty.AsCtor;
        Write(B2I.Kind.TypeCon, t.Decl.Name + " " + t.Arguments.Length);
        Indent(2);
        foreach (Type! a in t.Arguments) { Write(a); }
        Unindent();
      }
      else if (ty.IsMap)
      {
        MapType! t = ty.AsMap;
        if (Context.AllTypes)
        {
          Write(B2I.Kind.Array, t.TypeParameters.Length + " " +
            (t.Arguments.Length + 1));
          Indent(2);
          foreach (TypeVariable! v in t.TypeParameters) { Write(v); }
          Unindent();
        }
        else { Write(B2I.Kind.Array, (t.Arguments.Length + 1).ToString()); }
        Indent(2);
        foreach (Type! a in t.Arguments) { Write(a); }
        Write(t.Result);
        Unindent();
      }
    }
    
    public void Write(VCExpr! e)
    {
      e.Accept<bool,B2I!>(exprWriter, this);
    }
    public void Write(VCExpr! e, ProverInterface.ErrorHandler! h)
    {
      eh = h; e.Accept<bool,B2I!>(exprWriter, this); eh = null;
    }
    public void Write(VCExprNAry! e)
    {
      e.Accept<bool,B2I!>(exprOpWriter, this);
    }
    
    public B2I! Write(QKeyValue atts, Boogie2VCExprTranslator! tr)
    {
      for (QKeyValue a = atts; a != null; a = a.Next)
      {
        Write(B2I.Kind.Attribute, a.Key + " " + a.Params.Count);
        Indent(2);
        foreach (object! v in a.Params)
        {
          if (v is string)
          {
            string! s = ((string!) v).Replace("\n", " ").Replace("\r", " ")
              .Replace("\t", "\\w");
            Write(B2I.Kind.AttributeString, s);
          }
          else
          {
            Write(B2I.Kind.AttributeExpr);
            Indent(2);
            Write(tr.Translate((Expr!) v));
            Unindent();
          }
        }
        Unindent();
      }
      return this;
    }
    
    public enum Kind {
      TypeDecl, FunDecl, VarDecl, Axiom, VC,
      Attribute, AttributeString, AttributeExpr,
      Type, Int, Bool, BvType, TypeVar, TypeCon, Array,
      True, False, Not, And, Or, Implies, Distinct, Eq,
      IntNumber, Le, Lt, Ge, Gt, Add, Sub, Mul, Div, Mod, 
      BvNumber, BvExtract, BvConcat,
      Variable, Pat, NoPat, Forall, Exists,
      Select, Store, HeapSucc, Subtype, Subtype3, Function, Label };
    
    private string! StringOfKind(Kind k)
    {
      switch (k)
      {
        case Kind.TypeDecl: return "type-decl";
        case Kind.FunDecl: return "fun-decl";
        case Kind.VarDecl: return "var-decl";
        case Kind.Axiom: return "axiom";
        case Kind.VC: return "vc";
        
        case Kind.Attribute: return "attribute";
        case Kind.AttributeString: return "string-attr";
        case Kind.AttributeExpr: return "expr-attr";
        
        case Kind.Type: return "type";
        case Kind.Int: return "int";
        case Kind.Bool: return "bool";
        case Kind.BvType: return "bv";
        case Kind.TypeVar: return "type-var";
        case Kind.TypeCon: return "type-con";
        case Kind.Array: return "array";
        
        case Kind.True: return "true";
        case Kind.False: return "false";
        case Kind.IntNumber: return "int-num";
        case Kind.BvNumber: return "bv-num";
        case Kind.Variable: return "var";

        case Kind.Not: return "not";
        case Kind.And: return "and";
        case Kind.Or: return "or";
        case Kind.Implies: return "implies";
        case Kind.Distinct: return "distinct";
        case Kind.Eq: return "=";
        case Kind.Le: return "<=";
        case Kind.Lt: return "<";
        case Kind.Ge: return ">=";
        case Kind.Gt: return ">";
        case Kind.Add: return "+";
        case Kind.Sub: return "-";
        case Kind.Mul: return "*";
        case Kind.Div: return "/";
        case Kind.Mod: return "%";
        case Kind.Select: return "select";
        case Kind.Store: return "store";
        case Kind.BvExtract: return "bv-extract";
        case Kind.BvConcat: return "bv-concat";
        case Kind.HeapSucc: return "heap-succ";
        case Kind.Subtype: return "subtype";
        case Kind.Subtype3: return "subtype3";

        case Kind.Function: return "fun";

        case Kind.Label: return "label";

        case Kind.Pat: return "pat";
        case Kind.NoPat: return "nopat";
        case Kind.Forall: return "forall";
        case Kind.Exists: return "exists";
      }
      assert false;
    }

    public static int CountOf(QKeyValue atts)
    {
      int i = 0;
      for (QKeyValue a = atts; a != null; a = a.Next) { i++; }
      return i;
    }

    public static QKeyValue! Add(string! key, string value, QKeyValue kv)
    {
      List<object!>! list = new List<object!>();
      if (value != null) { list.Add(value); }
      return new QKeyValue(Token.NoToken, key, list, kv);
    }
  }

  class VCExprWriter : IVCExprVisitor<bool, B2I!>
  {
    public bool Visit(VCExprLiteral! node, B2I! b2i)
    {
      if (node == VCExpressionGenerator.True) { b2i.Write(B2I.Kind.True); }
      else if (node == VCExpressionGenerator.False)
      {
        b2i.Write(B2I.Kind.False);
      }
      else if (node is VCExprIntLit)
      {
        b2i.Write(B2I.Kind.IntNumber, ((VCExprIntLit) node).Val.ToString());
      }
      else assert false;
      return true;
    }
    
    public bool Visit(VCExprNAry! node, B2I! b2i)
    {
      b2i.Write(node);
      return true;
    }
    
    public bool Visit(VCExprVar! node, B2I! b2i)
    {
      if (b2i.Context.IsFunctionDeclared(node.Name))
      {
        b2i.Write(B2I.Kind.Function, node.Name + " 0");
        if (b2i.Context.AllTypes)
        {
          b2i.Indent(2);
          b2i.Write(node.Type);
          b2i.Unindent();
        }
      }
      else
      {
        b2i.Write(B2I.Kind.Variable, node.Name);
        b2i.Indent(2);
        b2i.Write(node.Type);
        b2i.Unindent();
      }
      return true;
    }
   
    public bool Visit(VCExprQuantifier! node, B2I! b2i)
    {
      QKeyValue attribs =
        B2I.Add("qid", node.Infos.qid,
        B2I.Add("uniqueId", node.Infos.uniqueId.ToString(),
        B2I.Add("bvZ3Native", node.Infos.bvZ3Native.ToString(),
        node.Infos.attributes)));

      B2I.Kind all = B2I.Kind.Forall; B2I.Kind ex = B2I.Kind.Exists;
      if (b2i.Context.AllTypes)
      {
        b2i.Write((node.Quan == Quantifier.ALL) ? all : ex,
          node.TypeParameters.Count + " " + node.BoundVars.Count + " " +
          node.Triggers.Count + " " + B2I.CountOf(attribs));
        b2i.Indent(2);
        foreach (TypeVariable! v in node.TypeParameters) { b2i.Write(v); }
        b2i.Unindent();
      }
      else
      {
        b2i.Write((node.Quan == Quantifier.ALL) ? all : ex,
          node.BoundVars.Count + " " + node.Triggers.Count + " " +
          B2I.CountOf(attribs));
      }
      b2i.Indent(2);
      foreach (VCExprVar! v in node.BoundVars)
      {
        b2i.Write(B2I.Kind.Variable, v.Name);
        b2i.Indent(2);
        b2i.Write(v.Type);
        b2i.Unindent();
      }
      foreach (VCTrigger! t in node.Triggers)
      {
        B2I.Kind k = (t.Pos) ? B2I.Kind.Pat : B2I.Kind.NoPat;
        b2i.Write(k, t.Exprs.Count.ToString());
        b2i.Indent(2);
        foreach (VCExpr! e in t.Exprs) { b2i.Write(e); }
        b2i.Unindent();
      }
      b2i.Write(attribs, b2i.Context.BoogieExprTranslator);
      b2i.Unindent();
      b2i.Write(node.Body);
      return true;
    }
    
    public bool Visit(VCExprLet! node, B2I! b2i)
    {
      // we do not support "let"
      assert false;
      return true;
    }
  }


  class VCExprOpWriter : IVCExprOpVisitor<bool, B2I!>
  {
    private void WriteArguments(B2I! b2i, VCExprNAry! node)
    {
      foreach (VCExpr! e in node) { b2i.Write(e); }
    }
    private bool Write(B2I! b2i, B2I.Kind k, VCExprNAry! node)
    {
      b2i.Write(k);
      WriteArguments(b2i, node);
      return true;
    }
  
    public bool VisitNotOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Not, node);
    }
    public bool VisitEqOp(VCExprNAry! node, B2I! b2i)
    {
      b2i.Write(B2I.Kind.Eq);
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        b2i.Write(node[0].Type);
        b2i.Unindent();
      }
      WriteArguments(b2i, node);
      return true;
    }
    public bool VisitNeqOp(VCExprNAry! node, B2I! b2i)
    {
      b2i.Write(B2I.Kind.Not);
      b2i.Write(B2I.Kind.Eq);
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        b2i.Write(node[0].Type);
        b2i.Unindent();
      }
      WriteArguments(b2i, node);
      return true;
    }
    private bool Unroll(B2I.Kind kind, VCExprNAry! node, B2I! b2i)
    {
      List<VCExpr!>! unroll = new List<VCExpr!>();
      foreach (VCExpr! e in node) { unroll.Insert(0, e); }

      List<VCExpr!>! flat = new List<VCExpr!>();

      while (unroll.Count > 0)
      {
        VCExpr! hd = unroll[0];
        unroll.RemoveAt(0);
        if (hd is VCExprNAry && ((VCExprNAry) hd).Op.Equals(node.Op))
        {
          VCExprNAry! n = (VCExprNAry) hd;
          foreach (VCExpr! e in n) { unroll.Insert(0, e); }
        }
        else { flat.Insert(0, hd); }
      }

      b2i.Write(kind, flat.Count.ToString());
      foreach (VCExpr! e in flat) { b2i.Write(e); }
      return true;
    }
    public bool VisitAndOp(VCExprNAry! node, B2I! b2i)
    {
      return Unroll(B2I.Kind.And, node, b2i);
    }
    public bool VisitOrOp(VCExprNAry! node, B2I! b2i)
    {
      return Unroll(B2I.Kind.Or, node, b2i);
    }
    public bool VisitImpliesOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Implies, node);
    }
    public bool VisitDistinctOp(VCExprNAry! node, B2I! b2i)
    {
      b2i.Write(B2I.Kind.Distinct, node.Length.ToString());
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        b2i.Write(node[0].Type);
        b2i.Unindent();
      }
      WriteArguments(b2i, node);
      return true;
    }
    
    public bool VisitLabelOp(VCExprNAry! node, B2I! b2i)
    {
      VCExprLabelOp! op = (VCExprLabelOp!) node.Op;
      string! label = op.label.Substring(1);
      int ln = 0;
      int col = 0;
      if (b2i.LabelRenamer != null)
      {
        Absy! absy = b2i.LabelRenamer.Label2Absy(label);
        if (absy.Line > 0 && absy.Col > 0) { ln = absy.Line; col = absy.Col; }
      }
      string! k = ((op.pos) ? "pos" : "neg");
      b2i.Write(B2I.Kind.Label, k + " " + ln + " " + col);
      WriteArguments(b2i, node);
      return true;
    }
    
    public bool VisitSelectOp(VCExprNAry! node, B2I! b2i)
    {
      b2i.Write(B2I.Kind.Select, node.Length.ToString());
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        foreach (VCExpr! e in node) { b2i.Write(e.Type); }
        b2i.Unindent();
      }
      assert (node.Type.Equals(node[0].Type.AsMap.Result));
      WriteArguments(b2i, node);
      return true;
    }
    public bool VisitStoreOp(VCExprNAry! node, B2I! b2i)
    {
      b2i.Write(B2I.Kind.Store, node.Length.ToString());
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        foreach (VCExpr! e in node) { b2i.Write(e.Type); }
        b2i.Unindent();
      }
      assert (node.Type.Equals(node[0].Type));
      WriteArguments(b2i, node);
      return true;
    }
    
    public bool VisitBvOp(VCExprNAry! node, B2I! b2i)
    {
      VCExprIntLit num = node[0] as VCExprIntLit;
      if (num == null) { assert false; }
      b2i.Write(B2I.Kind.BvNumber, node.Type.BvBits + " " + num.Val);
      return true;
    }
    public bool VisitBvExtractOp(VCExprNAry! node, B2I! b2i)
    {
      VCExprBvExtractOp! op = (VCExprBvExtractOp) node.Op;
      VCExpr! child = node[0];
      b2i.Write(B2I.Kind.BvExtract, op.End + " " + op.Start);
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        b2i.Write(child.Type);
        b2i.Write(node.Type);
        b2i.Unindent();
      }
      b2i.Write(child);
      return true;
    }
    public bool VisitBvConcatOp(VCExprNAry! node, B2I! b2i)
    {
      VCExpr! child1 = node[0];
      VCExpr! child2 = node[1];
      b2i.Write(B2I.Kind.BvConcat);
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        b2i.Write(child1.Type);
        b2i.Write(child2.Type);
        b2i.Write(node.Type);
        b2i.Unindent();
      }
      b2i.Write(child1);
      b2i.Write(child2);
      return true;
    }

    public bool VisitIfThenElseOp(VCExprNAry! node, B2I! b2i)
    {
      throw new System.NotImplementedException(); // TODO
    }

    
    public bool VisitHeapSuccessionOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.HeapSucc, node);
    }
    
    public bool VisitAddOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Add, node);
    }
    public bool VisitSubOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Sub, node);
    }
    public bool VisitMulOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Mul, node);
    }
    public bool VisitDivOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Div, node);
    }
    public bool VisitModOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Mod, node);
    }
    public bool VisitLtOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Lt, node);
    }
    public bool VisitLeOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Le, node);
    }
    public bool VisitGtOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Gt, node);
    }
    public bool VisitGeOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Ge, node);
    }
    
    public bool VisitSubtypeOp(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Subtype, node);
    }
    public bool VisitSubtype3Op(VCExprNAry! node, B2I! b2i)
    {
      return Write(b2i, B2I.Kind.Subtype3, node);
    }
    
    public bool VisitBoogieFunctionOp(VCExprNAry! node, B2I! b2i)
    {
      Function! f = ((VCExprBoogieFunctionOp!) node.Op).Func;
      assert (f.InParams.Length == node.Length);
      b2i.Write(B2I.Kind.Function, f.Name + " " + node.Length);
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        foreach (Variable! v in f.InParams) { b2i.Write(v.TypedIdent.Type); }
        b2i.Unindent();
      }
      assert (f.OutParams.Length == 1);
      assert (f.OutParams[0] != null);
      if (b2i.Context.AllTypes)
      {
        b2i.Indent(2);
        b2i.Write(((Variable!) f.OutParams[0]).TypedIdent.Type);
        b2i.Unindent();
      }
      WriteArguments(b2i, node);
      return true;
    }
  }
}

