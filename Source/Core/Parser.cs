using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using Bpl = Microsoft.Boogie;




using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {



public class Parser {
	public const int _EOF = 0;
	public const int _ident = 1;
	public const int _bvlit = 2;
	public const int _digits = 3;
	public const int _string = 4;
	public const int _decimal = 5;
	public const int _float = 6;
	public const int maxT = 96;

	const bool T = true;
	const bool x = false;
	const int minErrDist = 2;

	public Scanner/*!*/ scanner;
	public Errors/*!*/  errors;

	public Token/*!*/ t;    // last recognized token
	public Token/*!*/ la;   // lookahead token
	int errDist = minErrDist;

readonly Program/*!*/ Pgm;

readonly Expr/*!*/ dummyExpr;
readonly Cmd/*!*/ dummyCmd;
readonly Block/*!*/ dummyBlock;
readonly Bpl.Type/*!*/ dummyType;
readonly List<Expr>/*!*/ dummyExprSeq;
readonly TransferCmd/*!*/ dummyTransferCmd;
readonly StructuredCmd/*!*/ dummyStructuredCmd;

///<summary>
///Returns the number of parsing errors encountered.  If 0, "program" returns as
///the parsed program.
///</summary>
public static int Parse (string/*!*/ filename, /*maybe null*/ List<string/*!*/> defines, out /*maybe null*/ Program program, bool useBaseName=false) /* throws System.IO.IOException */ {
  Contract.Requires(filename != null);
  Contract.Requires(cce.NonNullElements(defines,true));

  if (defines == null) {
    defines = new List<string/*!*/>();
  }

  if (filename == "stdin.bpl") {
    var s = ParserHelper.Fill(Console.In, defines);
    return Parse(s, filename, out program, useBaseName);
  } else {
    FileStream stream = new FileStream(filename, FileMode.Open, FileAccess.Read, FileShare.Read);
    var s = ParserHelper.Fill(stream, defines);
    var ret = Parse(s, filename, out program, useBaseName);
    stream.Close();
    return ret;
  }
}


public static int Parse (string s, string/*!*/ filename, out /*maybe null*/ Program program, bool useBaseName=false) /* throws System.IO.IOException */ {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);

  byte[]/*!*/ buffer = cce.NonNull(UTF8Encoding.Default.GetBytes(s));
  MemoryStream ms = new MemoryStream(buffer,false);
  Errors errors = new Errors();
  Scanner scanner = new Scanner(ms, errors, filename, useBaseName);

  Parser parser = new Parser(scanner, errors, false);
  parser.Parse();
  if (parser.errors.count == 0)
  {
    program = parser.Pgm;
    program.ProcessDatatypeConstructors();
    return 0;
  }
  else
  {
    program = null;
    return parser.errors.count;
  }
}

public Parser(Scanner/*!*/ scanner, Errors/*!*/ errors, bool disambiguation)
 : this(scanner, errors)
{
  // initialize readonly fields
  Pgm = new Program();
  dummyExpr = new LiteralExpr(Token.NoToken, false);
  dummyCmd = new AssumeCmd(Token.NoToken, dummyExpr);
  dummyBlock = new Block(Token.NoToken, "dummyBlock", new List<Cmd>(), new ReturnCmd(Token.NoToken));
  dummyType = new BasicType(Token.NoToken, SimpleType.Bool);
  dummyExprSeq = new List<Expr> ();
  dummyTransferCmd = new ReturnCmd(Token.NoToken);
  dummyStructuredCmd = new BreakCmd(Token.NoToken, null);
}

// Class to represent the bounds of a bitvector expression t[a:b].
// Objects of this class only exist during parsing and are directly
// turned into BvExtract before they get anywhere else
private class BvBounds : Expr {
  public BigNum Lower;
  public BigNum Upper;
  public BvBounds(IToken/*!*/ tok, BigNum lower, BigNum upper)
    : base(tok, /*immutable=*/ false) {
    Contract.Requires(tok != null);
    this.Lower = lower;
    this.Upper = upper;
  }
  public override Bpl.Type/*!*/ ShallowType { get {Contract.Ensures(Contract.Result<Bpl.Type>() != null); return Bpl.Type.Int; } }
  public override void Resolve(ResolutionContext/*!*/ rc) {
    // Contract.Requires(rc != null);
    rc.Error(this, "bitvector bounds in illegal position");
  }
  public override void Emit(TokenTextWriter/*!*/ stream,
                            int contextBindingStrength, bool fragileContext) {
    Contract.Assert(false);throw new cce.UnreachableException();
  }
  public override void ComputeFreeVariables(GSet<object>/*!*/ freeVars) { Contract.Assert(false);throw new cce.UnreachableException(); }
  public override int ComputeHashCode() {
    return base.GetHashCode();
  }
}

/*--------------------------------------------------------------------------*/


	public Parser(Scanner/*!*/ scanner, Errors/*!*/ errors) {
		this.scanner = scanner;
		this.errors = errors;
		Token/*!*/ tok = new Token();
		tok.val = "";
		this.la = tok;
		this.t = new Token(); // just to satisfy its non-null constraint
	}

	void SynErr (int n) {
		if (errDist >= minErrDist) errors.SynErr(la.filename, la.line, la.col, n);
		errDist = 0;
	}

	public void SemErr (string/*!*/ msg) {
		Contract.Requires(msg != null);
		if (errDist >= minErrDist) errors.SemErr(t, msg);
		errDist = 0;
	}

	public void SemErr(IToken/*!*/ tok, string/*!*/ msg) {
	  Contract.Requires(tok != null);
	  Contract.Requires(msg != null);
	  errors.SemErr(tok, msg);
	}

	void Get () {
		for (;;) {
			t = la;
			la = scanner.Scan();
			if (la.kind <= maxT) { ++errDist; break; }

			la = t;
		}
	}

	void Expect (int n) {
		if (la.kind==n) Get(); else { SynErr(n); }
	}

	bool StartOf (int s) {
		return set[s, la.kind];
	}

	void ExpectWeak (int n, int follow) {
		if (la.kind == n) Get();
		else {
			SynErr(n);
			while (!StartOf(follow)) Get();
		}
	}


	bool WeakSeparator(int n, int syFol, int repFol) {
		int kind = la.kind;
		if (kind == n) {Get(); return true;}
		else if (StartOf(repFol)) {return false;}
		else {
			SynErr(n);
			while (!(set[syFol, kind] || set[repFol, kind] || set[0, kind])) {
				Get();
				kind = la.kind;
			}
			return StartOf(syFol);
		}
	}


	void BoogiePL() {
		List<Variable>/*!*/ vs;
		List<Declaration>/*!*/ ds;
		Axiom/*!*/ ax;
		List<Declaration/*!*/>/*!*/ ts;
		Procedure/*!*/ pr;
		Implementation im;
		Implementation/*!*/ nnim;
		
		while (StartOf(1)) {
			switch (la.kind) {
			case 21: {
				Consts(out vs);
				foreach(Bpl.Variable/*!*/ v in vs){
				 Contract.Assert(v != null);
				 Pgm.AddTopLevelDeclaration(v);
				}
				
				break;
			}
			case 25: {
				Function(out ds);
				foreach(Bpl.Declaration/*!*/ d in ds){
				 Contract.Assert(d != null);
				 Pgm.AddTopLevelDeclaration(d);
				}
				
				break;
			}
			case 29: {
				Axiom(out ax);
				Pgm.AddTopLevelDeclaration(ax); 
				break;
			}
			case 30: {
				UserDefinedTypes(out ts);
				foreach(Declaration/*!*/ td in ts){
				 Contract.Assert(td != null);
				 Pgm.AddTopLevelDeclaration(td);
				}
				
				break;
			}
			case 7: {
				GlobalVars(out vs);
				foreach(Bpl.Variable/*!*/ v in vs){
				 Contract.Assert(v != null);
				 Pgm.AddTopLevelDeclaration(v);
				}
				
				break;
			}
			case 32: {
				Procedure(out pr, out im);
				Pgm.AddTopLevelDeclaration(pr);
				if (im != null) {
				  Pgm.AddTopLevelDeclaration(im);
				}
				
				break;
			}
			case 33: {
				Implementation(out nnim);
				Pgm.AddTopLevelDeclaration(nnim); 
				break;
			}
			}
		}
		Expect(0);
	}

	void Consts(out List<Variable>/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null); IToken/*!*/ y; List<TypedIdent>/*!*/ xs;
		ds = new List<Variable>();
		bool u = false; QKeyValue kv = null;
		bool ChildrenComplete = false;
		List<ConstantParent/*!*/> Parents = null; 
		Expect(21);
		y = t; 
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		if (la.kind == 22) {
			Get();
			u = true;  
		}
		IdsType(out xs);
		if (la.kind == 23) {
			OrderSpec(out ChildrenComplete, out Parents);
		}
		bool makeClone = false;
		foreach(TypedIdent/*!*/ x in xs){
		 Contract.Assert(x != null);
		
		 // ensure that no sharing is introduced
		 List<ConstantParent/*!*/> ParentsClone;
		 if (makeClone && Parents != null) {
		   ParentsClone = new List<ConstantParent/*!*/> ();
		   foreach (ConstantParent/*!*/ p in Parents){
		     Contract.Assert(p != null);
		     ParentsClone.Add(new ConstantParent (
		                      new IdentifierExpr (p.Parent.tok, p.Parent.Name),
		                      p.Unique));}
		 } else {
		   ParentsClone = Parents;
		 }
		 makeClone = true;
		
		 ds.Add(new Constant(y, x, u, ParentsClone, ChildrenComplete, kv));
		}
		
		Expect(8);
	}

	void Function(out List<Declaration>/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null);
		ds = new List<Declaration>(); IToken/*!*/ z;
		IToken/*!*/ typeParamTok;
		var typeParams = new List<TypeVariable>();
		var arguments = new List<Variable>();
		TypedIdent/*!*/ tyd;
		TypedIdent retTyd = null;
		Bpl.Type/*!*/ retTy;
		QKeyValue argKv = null;
		QKeyValue kv = null;
		Expr definition = null;
		Expr/*!*/ tmp;
		
		Expect(25);
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		Ident(out z);
		if (la.kind == 19) {
			TypeParams(out typeParamTok, out typeParams);
		}
		Expect(9);
		if (StartOf(2)) {
			VarOrType(out tyd, out argKv);
			arguments.Add(new Formal(tyd.tok, tyd, true, argKv)); 
			while (la.kind == 12) {
				Get();
				VarOrType(out tyd, out argKv);
				arguments.Add(new Formal(tyd.tok, tyd, true, argKv)); 
			}
		}
		Expect(10);
		argKv = null; 
		if (la.kind == 26) {
			Get();
			Expect(9);
			VarOrType(out retTyd, out argKv);
			Expect(10);
		} else if (la.kind == 11) {
			Get();
			Type(out retTy);
			retTyd = new TypedIdent(retTy.tok, TypedIdent.NoName, retTy); 
		} else SynErr(97);
		if (la.kind == 27) {
			Get();
			Expression(out tmp);
			definition = tmp; 
			Expect(28);
		} else if (la.kind == 8) {
			Get();
		} else SynErr(98);
		if (retTyd == null) {
		 // construct a dummy type for the case of syntax error
		 retTyd = new TypedIdent(t, TypedIdent.NoName, new BasicType(t, SimpleType.Int));
		}
		Function/*!*/ func = new Function(z, z.val, typeParams, arguments,
		                                 new Formal(retTyd.tok, retTyd, false, argKv), null, kv);
		Contract.Assert(func != null);
		ds.Add(func);
		bool allUnnamed = true;
		foreach(Formal/*!*/ f in arguments){
		 Contract.Assert(f != null);
		 if (f.TypedIdent.HasName) {
		   allUnnamed = false;
		   break;
		 }
		}
		if (!allUnnamed) {
		 Bpl.Type prevType = null;
		 for (int i = arguments.Count; 0 <= --i; ) {
		   TypedIdent/*!*/ curr = cce.NonNull(arguments[i]).TypedIdent;
		   if (curr.HasName) {
		     // the argument was given as both an identifier and a type
		     prevType = curr.Type;
		   } else {
		     // the argument was given as just one "thing", which syntactically parsed as a type
		     if (prevType == null) {
		       this.errors.SemErr(curr.tok, "the type of the last parameter is unspecified");
		       break;
		     }
		     Bpl.Type ty = curr.Type;
		     var uti = ty as UnresolvedTypeIdentifier;
		     if (uti != null && uti.Arguments.Count == 0) {
		       // the given "thing" was just an identifier, so let's use it as the name of the parameter
		       curr.Name = uti.Name;
		       curr.Type = prevType;
		     } else {
		       this.errors.SemErr(curr.tok, "expecting an identifier as parameter name");
		     }
		   }
		 }
		}
		if (definition != null) {
		 // generate either an axiom or a function body
		 if (QKeyValue.FindBoolAttribute(kv, "inline")) {
		   func.Body = definition;
		 } else {
		   ds.Add(func.CreateDefinitionAxiom(definition, kv));
		 }
		}
		
	}

	void Axiom(out Axiom/*!*/ m) {
		Contract.Ensures(Contract.ValueAtReturn(out m) != null); Expr/*!*/ e; QKeyValue kv = null; 
		Expect(29);
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		IToken/*!*/ x = t; 
		Proposition(out e);
		Expect(8);
		m = new Axiom(x,e, null, kv); 
	}

	void UserDefinedTypes(out List<Declaration/*!*/>/*!*/ ts) {
		Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out ts))); Declaration/*!*/ decl; QKeyValue kv = null; ts = new List<Declaration/*!*/> (); 
		Expect(30);
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		UserDefinedType(out decl, kv);
		ts.Add(decl);  
		while (la.kind == 12) {
			Get();
			UserDefinedType(out decl, kv);
			ts.Add(decl);  
		}
		Expect(8);
	}

	void GlobalVars(out List<Variable>/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null);
		QKeyValue kv = null;
		ds = new List<Variable>();
		var dsx = ds;
		
		Expect(7);
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		IdsTypeWheres(true, "global variables", delegate(TypedIdent tyd) { dsx.Add(new GlobalVariable(tyd.tok, tyd, kv)); } );
		Expect(8);
	}

	void Procedure(out Procedure/*!*/ proc, out /*maybe null*/ Implementation impl) {
		Contract.Ensures(Contract.ValueAtReturn(out proc) != null); IToken/*!*/ x;
		List<TypeVariable>/*!*/ typeParams;
		List<Variable>/*!*/ ins, outs;
		List<Requires>/*!*/ pre = new List<Requires>();
		List<IdentifierExpr>/*!*/ mods = new List<IdentifierExpr>();
		List<Ensures>/*!*/ post = new List<Ensures>();
		
		List<Variable>/*!*/ locals = new List<Variable>();
		StmtList/*!*/ stmtList;
		QKeyValue kv = null;
		impl = null;
		
		Expect(32);
		ProcSignature(true, out x, out typeParams, out ins, out outs, out kv);
		if (la.kind == 8) {
			Get();
			while (StartOf(3)) {
				Spec(pre, mods, post);
			}
		} else if (StartOf(4)) {
			while (StartOf(3)) {
				Spec(pre, mods, post);
			}
			ImplBody(out locals, out stmtList);
			impl = new Implementation(x, x.val, typeParams,
			                         Formal.StripWhereClauses(ins), Formal.StripWhereClauses(outs), locals, stmtList, kv == null ? null : (QKeyValue)kv.Clone(), this.errors);
			
		} else SynErr(99);
		proc = new Procedure(x, x.val, typeParams, ins, outs, pre, mods, post, kv); 
	}

	void Implementation(out Implementation/*!*/ impl) {
		Contract.Ensures(Contract.ValueAtReturn(out impl) != null); IToken/*!*/ x;
		List<TypeVariable>/*!*/ typeParams;
		List<Variable>/*!*/ ins, outs;
		List<Variable>/*!*/ locals;
		StmtList/*!*/ stmtList;
		QKeyValue kv;
		
		Expect(33);
		ProcSignature(false, out x, out typeParams, out ins, out outs, out kv);
		ImplBody(out locals, out stmtList);
		impl = new Implementation(x, x.val, typeParams, ins, outs, locals, stmtList, kv, this.errors); 
	}

	void Attribute(ref QKeyValue kv) {
		Trigger trig = null; 
		AttributeOrTrigger(ref kv, ref trig);
		if (trig != null) this.SemErr("only attributes, not triggers, allowed here"); 
	}

	void IdsTypeWheres(bool allowWhereClauses, string context, System.Action<TypedIdent> action ) {
		IdsTypeWhere(allowWhereClauses, context, action);
		while (la.kind == 12) {
			Get();
			IdsTypeWhere(allowWhereClauses, context, action);
		}
	}

	void LocalVars(List<Variable>/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null);
		QKeyValue kv = null;
		
		Expect(7);
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		IdsTypeWheres(true, "local variables", delegate(TypedIdent tyd) { ds.Add(new LocalVariable(tyd.tok, tyd, kv)); } );
		Expect(8);
	}

	void ProcFormals(bool incoming, bool allowWhereClauses, out List<Variable>/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null);
		ds = new List<Variable>();
		var dsx = ds;
		var context = allowWhereClauses ? "procedure formals" : "the 'implementation' copies of formals";
		
		Expect(9);
		if (la.kind == 1 || la.kind == 27) {
			AttrsIdsTypeWheres(allowWhereClauses, allowWhereClauses, context, delegate(TypedIdent tyd, QKeyValue kv) { dsx.Add(new Formal(tyd.tok, tyd, incoming, kv)); });
		}
		Expect(10);
	}

	void AttrsIdsTypeWheres(bool allowAttributes, bool allowWhereClauses, string context, System.Action<TypedIdent, QKeyValue> action ) {
		AttributesIdsTypeWhere(allowAttributes, allowWhereClauses, context, action);
		while (la.kind == 12) {
			Get();
			AttributesIdsTypeWhere(allowAttributes, allowWhereClauses, context, action);
		}
	}

	void BoundVars(IToken/*!*/ x, out List<Variable>/*!*/ ds) {
		Contract.Requires(x != null);
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null);
		List<TypedIdent>/*!*/ tyds = new List<TypedIdent>();
		ds = new List<Variable>();
		var dsx = ds;
		
		AttrsIdsTypeWheres(true, false, "bound variables", delegate(TypedIdent tyd, QKeyValue kv) { dsx.Add(new BoundVariable(tyd.tok, tyd, kv)); } );
	}

	void IdsType(out List<TypedIdent>/*!*/ tyds) {
		Contract.Ensures(Contract.ValueAtReturn(out tyds) != null); List<IToken>/*!*/ ids;  Bpl.Type/*!*/ ty; 
		Idents(out ids);
		Expect(11);
		Type(out ty);
		tyds = new List<TypedIdent>();
		foreach(Token/*!*/ id in ids){
		 Contract.Assert(id != null);
		 tyds.Add(new TypedIdent(id, id.val, ty, null));
		}
		
	}

	void Idents(out List<IToken>/*!*/ xs) {
		Contract.Ensures(Contract.ValueAtReturn(out xs) != null); IToken/*!*/ id; xs = new List<IToken>(); 
		Ident(out id);
		xs.Add(id); 
		while (la.kind == 12) {
			Get();
			Ident(out id);
			xs.Add(id); 
		}
	}

	void Type(out Bpl.Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken/*!*/ tok; ty = dummyType; 
		if (StartOf(5)) {
			TypeAtom(out ty);
		} else if (la.kind == 1) {
			Ident(out tok);
			List<Bpl.Type>/*!*/ args = new List<Bpl.Type> (); 
			if (StartOf(6)) {
				TypeArgs(args);
			}
			ty = new UnresolvedTypeIdentifier (tok, tok.val, args); 
		} else if (la.kind == 17 || la.kind == 19) {
			MapType(out ty);
		} else SynErr(100);
	}

	void AttributesIdsTypeWhere(bool allowAttributes, bool allowWhereClauses, string context, System.Action<TypedIdent, QKeyValue> action ) {
		QKeyValue kv = null; 
		while (la.kind == 27) {
			Attribute(ref kv);
			if (!allowAttributes) {
			 kv = null;
			 this.SemErr("attributes are not allowed on " + context);
			}
			
		}
		IdsTypeWhere(allowWhereClauses, context, delegate(TypedIdent tyd) { action(tyd, kv); });
	}

	void IdsTypeWhere(bool allowWhereClauses, string context, System.Action<TypedIdent> action ) {
		List<IToken>/*!*/ ids;  Bpl.Type/*!*/ ty;  Expr wh = null;  Expr/*!*/ nne; 
		Idents(out ids);
		Expect(11);
		Type(out ty);
		if (la.kind == 13) {
			Get();
			Expression(out nne);
			if (!allowWhereClauses) {
			 this.SemErr("where clause not allowed on " + context);
			} else {
			 wh = nne;
			}
			
		}
		foreach(Token/*!*/ id in ids){
		 Contract.Assert(id != null);
		 action(new TypedIdent(id, id.val, ty, wh));
		}
		
	}

	void Expression(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		ImpliesExpression(false, out e0);
		while (la.kind == 55 || la.kind == 56) {
			EquivOp();
			x = t; 
			ImpliesExpression(false, out e1);
			e0 = Expr.Binary(x, BinaryOperator.Opcode.Iff, e0, e1); 
		}
	}

	void TypeAtom(out Bpl.Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); ty = dummyType; 
		if (la.kind == 14) {
			Get();
			ty = new BasicType(t, SimpleType.Int); 
		} else if (la.kind == 15) {
			Get();
			ty = new BasicType(t, SimpleType.Real); 
		} else if (la.kind == 16) {
			Get();
			ty = new BasicType(t, SimpleType.Bool); 
		} else if (la.kind == 9) {
			Get();
			Type(out ty);
			Expect(10);
		} else SynErr(101);
	}

	void Ident(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		Expect(1);
		x = t;
		if (x.val.StartsWith("\\"))
		 x.val = x.val.Substring(1);
		
	}

	void TypeArgs(List<Bpl.Type>/*!*/ ts) {
		Contract.Requires(ts != null); IToken/*!*/ tok; Bpl.Type/*!*/ ty; 
		if (StartOf(5)) {
			TypeAtom(out ty);
			ts.Add(ty); 
			if (StartOf(6)) {
				TypeArgs(ts);
			}
		} else if (la.kind == 1) {
			Ident(out tok);
			List<Bpl.Type>/*!*/ args = new List<Bpl.Type> ();
			ts.Add(new UnresolvedTypeIdentifier (tok, tok.val, args)); 
			if (StartOf(6)) {
				TypeArgs(ts);
			}
		} else if (la.kind == 17 || la.kind == 19) {
			MapType(out ty);
			ts.Add(ty); 
		} else SynErr(102);
	}

	void MapType(out Bpl.Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken tok = null;
		IToken/*!*/ nnTok;
		List<Bpl.Type>/*!*/ arguments = new List<Bpl.Type>();
		Bpl.Type/*!*/ result;
		List<TypeVariable>/*!*/ typeParameters = new List<TypeVariable>();
		
		if (la.kind == 19) {
			TypeParams(out nnTok, out typeParameters);
			tok = nnTok; 
		}
		Expect(17);
		if (tok == null) tok = t;  
		if (StartOf(6)) {
			Types(arguments);
		}
		Expect(18);
		Type(out result);
		ty = new MapType(tok, typeParameters, arguments, result);
		
	}

	void TypeParams(out IToken/*!*/ tok, out List<TypeVariable>/*!*/ typeParams) {
		Contract.Ensures(Contract.ValueAtReturn(out tok) != null); Contract.Ensures(Contract.ValueAtReturn(out typeParams) != null); List<IToken>/*!*/ typeParamToks; 
		Expect(19);
		tok = t;  
		Idents(out typeParamToks);
		Expect(20);
		typeParams = new List<TypeVariable> ();
		foreach(Token/*!*/ id in typeParamToks){
		 Contract.Assert(id != null);
		 typeParams.Add(new TypeVariable(id, id.val));}
		
	}

	void Types(List<Bpl.Type>/*!*/ ts) {
		Contract.Requires(ts != null); Bpl.Type/*!*/ ty; 
		Type(out ty);
		ts.Add(ty); 
		while (la.kind == 12) {
			Get();
			Type(out ty);
			ts.Add(ty); 
		}
	}

	void OrderSpec(out bool ChildrenComplete, out List<ConstantParent/*!*/> Parents) {
		Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out Parents),true)); ChildrenComplete = false;
		Parents = null;
		bool u;
		IToken/*!*/ parent; 
		Expect(23);
		Parents = new List<ConstantParent/*!*/> ();
		u = false; 
		if (la.kind == 1 || la.kind == 22) {
			if (la.kind == 22) {
				Get();
				u = true; 
			}
			Ident(out parent);
			Parents.Add(new ConstantParent (
			           new IdentifierExpr(parent, parent.val), u)); 
			while (la.kind == 12) {
				Get();
				u = false; 
				if (la.kind == 22) {
					Get();
					u = true; 
				}
				Ident(out parent);
				Parents.Add(new ConstantParent (
				           new IdentifierExpr(parent, parent.val), u)); 
			}
		}
		if (la.kind == 24) {
			Get();
			ChildrenComplete = true; 
		}
	}

	void VarOrType(out TypedIdent/*!*/ tyd, out QKeyValue kv) {
		Contract.Ensures(Contract.ValueAtReturn(out tyd) != null);
		string/*!*/ varName = TypedIdent.NoName;
		Bpl.Type/*!*/ ty;
		IToken/*!*/ tok;
		kv = null;
		
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		Type(out ty);
		tok = ty.tok; 
		if (la.kind == 11) {
			Get();
			var uti = ty as UnresolvedTypeIdentifier;
			if (uti != null && uti.Arguments.Count == 0) {
			 varName = uti.Name;
			} else {
			 this.SemErr("expected identifier before ':'");
			}
			
			Type(out ty);
		}
		tyd = new TypedIdent(tok, varName, ty); 
	}

	void Proposition(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		Expression(out e);
	}

	void UserDefinedType(out Declaration/*!*/ decl, QKeyValue kv) {
		Contract.Ensures(Contract.ValueAtReturn(out decl) != null); IToken/*!*/ id; List<IToken>/*!*/ paramTokens = new List<IToken> ();
		Bpl.Type/*!*/ body = dummyType; bool synonym = false; 
		Ident(out id);
		if (la.kind == 1) {
			WhiteSpaceIdents(out paramTokens);
		}
		if (la.kind == 31) {
			Get();
			Type(out body);
			synonym = true; 
		}
		if (synonym) {
		 List<TypeVariable>/*!*/ typeParams = new List<TypeVariable>();
		 foreach(Token/*!*/ t in paramTokens){
		   Contract.Assert(t != null);
		   typeParams.Add(new TypeVariable(t, t.val));}
		 decl = new TypeSynonymDecl(id, id.val, typeParams, body, kv);
		} else {
		 decl = new TypeCtorDecl(id, id.val, paramTokens.Count, kv);
		}
		
	}

	void WhiteSpaceIdents(out List<IToken>/*!*/ xs) {
		Contract.Ensures(Contract.ValueAtReturn(out xs) != null); IToken/*!*/ id; xs = new List<IToken>(); 
		Ident(out id);
		xs.Add(id); 
		while (la.kind == 1) {
			Ident(out id);
			xs.Add(id); 
		}
	}

	void ProcSignature(bool allowWhereClausesOnFormals, out IToken/*!*/ name, out List<TypeVariable>/*!*/ typeParams,
out List<Variable>/*!*/ ins, out List<Variable>/*!*/ outs, out QKeyValue kv) {
		Contract.Ensures(Contract.ValueAtReturn(out name) != null); Contract.Ensures(Contract.ValueAtReturn(out typeParams) != null); Contract.Ensures(Contract.ValueAtReturn(out ins) != null); Contract.Ensures(Contract.ValueAtReturn(out outs) != null);
		IToken/*!*/ typeParamTok; typeParams = new List<TypeVariable>();
		outs = new List<Variable>(); kv = null; 
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		Ident(out name);
		if (la.kind == 19) {
			TypeParams(out typeParamTok, out typeParams);
		}
		ProcFormals(true, allowWhereClausesOnFormals, out ins);
		if (la.kind == 26) {
			Get();
			ProcFormals(false, allowWhereClausesOnFormals, out outs);
		}
	}

	void Spec(List<Requires>/*!*/ pre, List<IdentifierExpr>/*!*/ mods, List<Ensures>/*!*/ post) {
		Contract.Requires(pre != null); Contract.Requires(mods != null); Contract.Requires(post != null); List<IToken>/*!*/ ms; 
		if (la.kind == 34) {
			Get();
			if (la.kind == 1) {
				Idents(out ms);
				foreach(IToken/*!*/ m in ms){
				 Contract.Assert(m != null);
				 mods.Add(new IdentifierExpr(m, m.val));
				}
				
			}
			Expect(8);
		} else if (la.kind == 35) {
			Get();
			SpecPrePost(true, pre, post);
		} else if (la.kind == 36 || la.kind == 37) {
			SpecPrePost(false, pre, post);
		} else SynErr(103);
	}

	void ImplBody(out List<Variable>/*!*/ locals, out StmtList/*!*/ stmtList) {
		Contract.Ensures(Contract.ValueAtReturn(out locals) != null); Contract.Ensures(Contract.ValueAtReturn(out stmtList) != null); locals = new List<Variable>(); 
		Expect(27);
		while (la.kind == 7) {
			LocalVars(locals);
		}
		StmtList(out stmtList);
	}

	void SpecPrePost(bool free, List<Requires>/*!*/ pre, List<Ensures>/*!*/ post) {
		Contract.Requires(pre != null); Contract.Requires(post != null); Expr/*!*/ e; Token tok = null; QKeyValue kv = null; 
		if (la.kind == 36) {
			Get();
			tok = t; 
			while (la.kind == 27) {
				Attribute(ref kv);
			}
			Proposition(out e);
			Expect(8);
			pre.Add(new Requires(tok, free, e, null, kv)); 
		} else if (la.kind == 37) {
			Get();
			tok = t; 
			while (la.kind == 27) {
				Attribute(ref kv);
			}
			Proposition(out e);
			Expect(8);
			post.Add(new Ensures(tok, free, e, null, kv)); 
		} else SynErr(104);
	}

	void StmtList(out StmtList/*!*/ stmtList) {
		Contract.Ensures(Contract.ValueAtReturn(out stmtList) != null); List<BigBlock/*!*/> bigblocks = new List<BigBlock/*!*/>();
		/* built-up state for the current BigBlock: */
		IToken startToken = null;  string currentLabel = null;
		List<Cmd> cs = null;  /* invariant: startToken != null ==> cs != null */
		/* temporary variables: */
		IToken label;  Cmd c;  BigBlock b;
		StructuredCmd ec = null;  StructuredCmd/*!*/ ecn;
		TransferCmd tc = null;  TransferCmd/*!*/ tcn;
		
		while (StartOf(7)) {
			if (StartOf(8)) {
				LabelOrCmd(out c, out label);
				if (c != null) {
				 // LabelOrCmd read a Cmd
				 Contract.Assert(label == null);
				 if (startToken == null) { startToken = c.tok;  cs = new List<Cmd>(); }
				 Contract.Assert(cs != null);
				 cs.Add(c);
				} else {
				 // LabelOrCmd read a label
				 Contract.Assert(label != null);
				 if (startToken != null) {
				   Contract.Assert(cs != null);
				   // dump the built-up state into a BigBlock
				   b = new BigBlock(startToken, currentLabel, cs, null, null);
				   bigblocks.Add(b);
				   cs = null;
				 }
				 startToken = label;
				 currentLabel = label.val;
				 cs = new List<Cmd>();
				}
				
			} else if (la.kind == 40 || la.kind == 42 || la.kind == 45) {
				StructuredCmd(out ecn);
				ec = ecn;
				if (startToken == null) { startToken = ec.tok;  cs = new List<Cmd>(); }
				Contract.Assert(cs != null);
				b = new BigBlock(startToken, currentLabel, cs, ec, null);
				bigblocks.Add(b);
				startToken = null;  currentLabel = null;  cs = null;
				
			} else {
				TransferCmd(out tcn);
				tc = tcn;
				if (startToken == null) { startToken = tc.tok;  cs = new List<Cmd>(); }
				Contract.Assert(cs != null);
				b = new BigBlock(startToken, currentLabel, cs, null, tc);
				bigblocks.Add(b);
				startToken = null;  currentLabel = null;  cs = null;
				
			}
		}
		Expect(28);
		IToken/*!*/ endCurly = t;
		if (startToken == null && bigblocks.Count == 0) {
		 startToken = t;  cs = new List<Cmd>();
		}
		if (startToken != null) {
		 Contract.Assert(cs != null);
		 b = new BigBlock(startToken, currentLabel, cs, null, null);
		 bigblocks.Add(b);
		}
		
		stmtList = new StmtList(bigblocks, endCurly);
		
	}

	void LabelOrCmd(out Cmd c, out IToken label) {
		IToken/*!*/ x; Expr/*!*/ e;
		List<IToken>/*!*/ xs;
		List<IdentifierExpr> ids;
		c = dummyCmd;  label = null;
		Cmd/*!*/ cn;
		QKeyValue kv = null;
		
		switch (la.kind) {
		case 1: {
			LabelOrAssign(out c, out label);
			break;
		}
		case 46: {
			Get();
			x = t; 
			while (la.kind == 27) {
				Attribute(ref kv);
			}
			Proposition(out e);
			c = new AssertCmd(x, e, kv); 
			Expect(8);
			break;
		}
		case 47: {
			Get();
			x = t; 
			while (la.kind == 27) {
				Attribute(ref kv);
			}
			Proposition(out e);
			c = new AssumeCmd(x, e, kv); 
			Expect(8);
			break;
		}
		case 48: {
			Get();
			x = t; 
			Idents(out xs);
			Expect(8);
			ids = new List<IdentifierExpr>();
			foreach(IToken/*!*/ y in xs){
			 Contract.Assert(y != null);
			 ids.Add(new IdentifierExpr(y, y.val));
			}
			c = new HavocCmd(x,ids);
			
			break;
		}
		case 35: case 51: case 52: {
			CallCmd(out cn);
			Expect(8);
			c = cn; 
			break;
		}
		case 53: {
			ParCallCmd(out cn);
			c = cn; 
			break;
		}
		case 49: {
			Get();
			x = t; 
			Expect(8);
			c = new YieldCmd(x); 
			break;
		}
		default: SynErr(105); break;
		}
	}

	void StructuredCmd(out StructuredCmd/*!*/ ec) {
		Contract.Ensures(Contract.ValueAtReturn(out ec) != null); ec = dummyStructuredCmd;  Contract.Assume(cce.IsPeerConsistent(ec));
		IfCmd/*!*/ ifcmd;  WhileCmd/*!*/ wcmd;  BreakCmd/*!*/ bcmd;
		
		if (la.kind == 40) {
			IfCmd(out ifcmd);
			ec = ifcmd; 
		} else if (la.kind == 42) {
			WhileCmd(out wcmd);
			ec = wcmd; 
		} else if (la.kind == 45) {
			BreakCmd(out bcmd);
			ec = bcmd; 
		} else SynErr(106);
	}

	void TransferCmd(out TransferCmd/*!*/ tc) {
		Contract.Ensures(Contract.ValueAtReturn(out tc) != null); tc = dummyTransferCmd;
		Token y;  List<IToken>/*!*/ xs;
		List<String> ss = new List<String>();
		
		if (la.kind == 38) {
			Get();
			y = t; 
			Idents(out xs);
			foreach(IToken/*!*/ s in xs){
			 Contract.Assert(s != null);
			 ss.Add(s.val); }
			tc = new GotoCmd(y, ss);
			
		} else if (la.kind == 39) {
			Get();
			tc = new ReturnCmd(t); 
		} else SynErr(107);
		Expect(8);
	}

	void IfCmd(out IfCmd/*!*/ ifcmd) {
		Contract.Ensures(Contract.ValueAtReturn(out ifcmd) != null); IToken/*!*/ x;
		Expr guard;
		StmtList/*!*/ thn;
		IfCmd/*!*/ elseIf;  IfCmd elseIfOption = null;
		StmtList/*!*/ els;  StmtList elseOption = null;
		
		Expect(40);
		x = t; 
		Guard(out guard);
		Expect(27);
		StmtList(out thn);
		if (la.kind == 41) {
			Get();
			if (la.kind == 40) {
				IfCmd(out elseIf);
				elseIfOption = elseIf; 
			} else if (la.kind == 27) {
				Get();
				StmtList(out els);
				elseOption = els; 
			} else SynErr(108);
		}
		ifcmd = new IfCmd(x, guard, thn, elseIfOption, elseOption); 
	}

	void WhileCmd(out WhileCmd/*!*/ wcmd) {
		Contract.Ensures(Contract.ValueAtReturn(out wcmd) != null); IToken/*!*/ x;  Token z;
		Expr guard;  Expr/*!*/ e;  bool isFree;
		List<PredicateCmd/*!*/> invariants = new List<PredicateCmd/*!*/>();
		StmtList/*!*/ body;
		QKeyValue kv = null;
		
		Expect(42);
		x = t; 
		Guard(out guard);
		Contract.Assume(guard == null || cce.Owner.None(guard)); 
		while (la.kind == 35 || la.kind == 43) {
			isFree = false; z = la/*lookahead token*/; 
			if (la.kind == 35) {
				Get();
				isFree = true;  
			}
			Expect(43);
			while (la.kind == 27) {
				Attribute(ref kv);
			}
			Expression(out e);
			if (isFree) {
			 invariants.Add(new AssumeCmd(z, e, kv));
			} else {
			 invariants.Add(new AssertCmd(z, e, kv));
			}
			kv = null;
			
			Expect(8);
		}
		Expect(27);
		StmtList(out body);
		wcmd = new WhileCmd(x, guard, invariants, body); 
	}

	void BreakCmd(out BreakCmd/*!*/ bcmd) {
		Contract.Ensures(Contract.ValueAtReturn(out bcmd) != null); IToken/*!*/ x;  IToken/*!*/ y;
		string breakLabel = null;
		
		Expect(45);
		x = t; 
		if (la.kind == 1) {
			Ident(out y);
			breakLabel = y.val; 
		}
		Expect(8);
		bcmd = new BreakCmd(x, breakLabel); 
	}

	void Guard(out Expr e) {
		Expr/*!*/ ee;  e = null; 
		Expect(9);
		if (la.kind == 44) {
			Get();
			e = null; 
		} else if (StartOf(9)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(109);
		Expect(10);
	}

	void LabelOrAssign(out Cmd c, out IToken label) {
		IToken/*!*/ id; IToken/*!*/ x, y; Expr/*!*/ e0;
		c = dummyCmd;  label = null;
		AssignLhs/*!*/ lhs;
		List<AssignLhs/*!*/>/*!*/ lhss;
		List<Expr/*!*/>/*!*/ rhss;
		List<Expr/*!*/>/*!*/ indexes;
		
		Ident(out id);
		x = t; 
		if (la.kind == 11) {
			Get();
			c = null;  label = x; 
		} else if (la.kind == 12 || la.kind == 17 || la.kind == 50) {
			lhss = new List<AssignLhs/*!*/>(); 
			lhs = new SimpleAssignLhs(id, new IdentifierExpr(id, id.val)); 
			while (la.kind == 17) {
				MapAssignIndex(out y, out indexes);
				lhs = new MapAssignLhs(y, lhs, indexes); 
			}
			lhss.Add(lhs); 
			while (la.kind == 12) {
				Get();
				Ident(out id);
				lhs = new SimpleAssignLhs(id, new IdentifierExpr(id, id.val)); 
				while (la.kind == 17) {
					MapAssignIndex(out y, out indexes);
					lhs = new MapAssignLhs(y, lhs, indexes); 
				}
				lhss.Add(lhs); 
			}
			Expect(50);
			x = t; /* use location of := */ 
			Expression(out e0);
			rhss = new List<Expr/*!*/> ();
			rhss.Add(e0); 
			while (la.kind == 12) {
				Get();
				Expression(out e0);
				rhss.Add(e0); 
			}
			Expect(8);
			c = new AssignCmd(x, lhss, rhss); 
		} else SynErr(110);
	}

	void CallCmd(out Cmd c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); 
		IToken x; 
		bool isAsync = false;
		bool isFree = false;
		QKeyValue kv = null;
		c = null;
		
		if (la.kind == 51) {
			Get();
			isAsync = true;  
		}
		if (la.kind == 35) {
			Get();
			isFree = true;  
		}
		Expect(52);
		x = t; 
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		CallParams(isAsync, isFree, kv, x, out c);
		
	}

	void ParCallCmd(out Cmd d) {
		Contract.Ensures(Contract.ValueAtReturn(out d) != null); 
		IToken x; 
		QKeyValue kv = null;
		Cmd c = null;
		List<CallCmd> callCmds = new List<CallCmd>();
		
		Expect(53);
		x = t; 
		while (la.kind == 27) {
			Attribute(ref kv);
		}
		CallParams(false, false, kv, x, out c);
		callCmds.Add((CallCmd)c); 
		while (la.kind == 54) {
			Get();
			CallParams(false, false, kv, x, out c);
			callCmds.Add((CallCmd)c); 
		}
		Expect(8);
		d = new ParCallCmd(x, callCmds, kv); 
	}

	void MapAssignIndex(out IToken/*!*/ x, out List<Expr/*!*/>/*!*/ indexes) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out indexes))); indexes = new List<Expr/*!*/> ();
		Expr/*!*/ e;
		
		Expect(17);
		x = t; 
		if (StartOf(9)) {
			Expression(out e);
			indexes.Add(e); 
			while (la.kind == 12) {
				Get();
				Expression(out e);
				indexes.Add(e); 
			}
		}
		Expect(18);
	}

	void CallParams(bool isAsync, bool isFree, QKeyValue kv, IToken x, out Cmd c) {
		List<IdentifierExpr> ids = new List<IdentifierExpr>();
		List<Expr> es = new List<Expr>();
		Expr en;
		IToken first; 
		IToken p;
		c = null;
		
		Ident(out first);
		if (la.kind == 9) {
			Get();
			if (StartOf(9)) {
				Expression(out en);
				es.Add(en); 
				while (la.kind == 12) {
					Get();
					Expression(out en);
					es.Add(en); 
				}
			}
			Expect(10);
			c = new CallCmd(x, first.val, es, ids, kv); ((CallCmd) c).IsFree = isFree; ((CallCmd) c).IsAsync = isAsync; 
		} else if (la.kind == 12 || la.kind == 50) {
			ids.Add(new IdentifierExpr(first, first.val)); 
			if (la.kind == 12) {
				Get();
				Ident(out p);
				ids.Add(new IdentifierExpr(p, p.val)); 
				while (la.kind == 12) {
					Get();
					Ident(out p);
					ids.Add(new IdentifierExpr(p, p.val)); 
				}
			}
			Expect(50);
			Ident(out first);
			Expect(9);
			if (StartOf(9)) {
				Expression(out en);
				es.Add(en); 
				while (la.kind == 12) {
					Get();
					Expression(out en);
					es.Add(en); 
				}
			}
			Expect(10);
			c = new CallCmd(x, first.val, es, ids, kv); ((CallCmd) c).IsFree = isFree; ((CallCmd) c).IsAsync = isAsync; 
		} else SynErr(111);
	}

	void Expressions(out List<Expr>/*!*/ es) {
		Contract.Ensures(Contract.ValueAtReturn(out es) != null); Expr/*!*/ e; es = new List<Expr>(); 
		Expression(out e);
		es.Add(e); 
		while (la.kind == 12) {
			Get();
			Expression(out e);
			es.Add(e); 
		}
	}

	void ImpliesExpression(bool noExplies, out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		LogicalExpression(out e0);
		if (StartOf(10)) {
			if (la.kind == 57 || la.kind == 58) {
				ImpliesOp();
				x = t; 
				ImpliesExpression(true, out e1);
				e0 = Expr.Binary(x, BinaryOperator.Opcode.Imp, e0, e1); 
			} else {
				ExpliesOp();
				if (noExplies)
				 this.SemErr("illegal mixture of ==> and <==, use parentheses to disambiguate");
				x = t; 
				LogicalExpression(out e1);
				e0 = Expr.Binary(x, BinaryOperator.Opcode.Imp, e1, e0); 
				while (la.kind == 59 || la.kind == 60) {
					ExpliesOp();
					x = t; 
					LogicalExpression(out e1);
					e0 = Expr.Binary(x, BinaryOperator.Opcode.Imp, e1, e0); 
				}
			}
		}
	}

	void EquivOp() {
		if (la.kind == 55) {
			Get();
		} else if (la.kind == 56) {
			Get();
		} else SynErr(112);
	}

	void LogicalExpression(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		RelationalExpression(out e0);
		if (StartOf(11)) {
			if (la.kind == 61 || la.kind == 62) {
				AndOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = Expr.Binary(x, BinaryOperator.Opcode.And, e0, e1); 
				while (la.kind == 61 || la.kind == 62) {
					AndOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = Expr.Binary(x, BinaryOperator.Opcode.And, e0, e1); 
				}
			} else {
				OrOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = Expr.Binary(x, BinaryOperator.Opcode.Or, e0, e1); 
				while (la.kind == 63 || la.kind == 64) {
					OrOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = Expr.Binary(x, BinaryOperator.Opcode.Or, e0, e1); 
				}
			}
		}
	}

	void ImpliesOp() {
		if (la.kind == 57) {
			Get();
		} else if (la.kind == 58) {
			Get();
		} else SynErr(113);
	}

	void ExpliesOp() {
		if (la.kind == 59) {
			Get();
		} else if (la.kind == 60) {
			Get();
		} else SynErr(114);
	}

	void RelationalExpression(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; BinaryOperator.Opcode op; 
		BvTerm(out e0);
		if (StartOf(12)) {
			RelOp(out x, out op);
			BvTerm(out e1);
			e0 = Expr.Binary(x, op, e0, e1); 
		}
	}

	void AndOp() {
		if (la.kind == 61) {
			Get();
		} else if (la.kind == 62) {
			Get();
		} else SynErr(115);
	}

	void OrOp() {
		if (la.kind == 63) {
			Get();
		} else if (la.kind == 64) {
			Get();
		} else SynErr(116);
	}

	void BvTerm(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		Term(out e0);
		while (la.kind == 73) {
			Get();
			x = t; 
			Term(out e1);
			e0 = new BvConcatExpr(x, e0, e1); 
		}
	}

	void RelOp(out IToken/*!*/ x, out BinaryOperator.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken; op=BinaryOperator.Opcode.Add/*(dummy)*/; 
		switch (la.kind) {
		case 65: {
			Get();
			x = t; op=BinaryOperator.Opcode.Eq; 
			break;
		}
		case 19: {
			Get();
			x = t; op=BinaryOperator.Opcode.Lt; 
			break;
		}
		case 20: {
			Get();
			x = t; op=BinaryOperator.Opcode.Gt; 
			break;
		}
		case 66: {
			Get();
			x = t; op=BinaryOperator.Opcode.Le; 
			break;
		}
		case 67: {
			Get();
			x = t; op=BinaryOperator.Opcode.Ge; 
			break;
		}
		case 68: {
			Get();
			x = t; op=BinaryOperator.Opcode.Neq; 
			break;
		}
		case 69: {
			Get();
			x = t; op=BinaryOperator.Opcode.Subtype; 
			break;
		}
		case 70: {
			Get();
			x = t; op=BinaryOperator.Opcode.Neq; 
			break;
		}
		case 71: {
			Get();
			x = t; op=BinaryOperator.Opcode.Le; 
			break;
		}
		case 72: {
			Get();
			x = t; op=BinaryOperator.Opcode.Ge; 
			break;
		}
		default: SynErr(117); break;
		}
	}

	void Term(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; BinaryOperator.Opcode op; 
		Factor(out e0);
		while (la.kind == 74 || la.kind == 75) {
			AddOp(out x, out op);
			Factor(out e1);
			e0 = Expr.Binary(x, op, e0, e1); 
		}
	}

	void Factor(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; BinaryOperator.Opcode op; 
		Power(out e0);
		while (StartOf(13)) {
			MulOp(out x, out op);
			Power(out e1);
			e0 = Expr.Binary(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken/*!*/ x, out BinaryOperator.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken; op=BinaryOperator.Opcode.Add/*(dummy)*/; 
		if (la.kind == 74) {
			Get();
			x = t; op=BinaryOperator.Opcode.Add; 
		} else if (la.kind == 75) {
			Get();
			x = t; op=BinaryOperator.Opcode.Sub; 
		} else SynErr(118);
	}

	void Power(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		UnaryExpression(out e0);
		if (la.kind == 79) {
			Get();
			x = t; 
			Power(out e1);
			e0 = Expr.Binary(x, BinaryOperator.Opcode.Pow, e0, e1); 
		}
	}

	void MulOp(out IToken/*!*/ x, out BinaryOperator.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken; op=BinaryOperator.Opcode.Add/*(dummy)*/; 
		if (la.kind == 44) {
			Get();
			x = t; op=BinaryOperator.Opcode.Mul; 
		} else if (la.kind == 76) {
			Get();
			x = t; op=BinaryOperator.Opcode.Div; 
		} else if (la.kind == 77) {
			Get();
			x = t; op=BinaryOperator.Opcode.Mod; 
		} else if (la.kind == 78) {
			Get();
			x = t; op=BinaryOperator.Opcode.RealDiv; 
		} else SynErr(119);
	}

	void UnaryExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;
		e = dummyExpr;
		
		if (la.kind == 75) {
			Get();
			x = t; 
			UnaryExpression(out e);
			e = Expr.Unary(x, UnaryOperator.Opcode.Neg, e); 
		} else if (la.kind == 80 || la.kind == 81) {
			NegOp();
			x = t; 
			UnaryExpression(out e);
			e = Expr.Unary(x, UnaryOperator.Opcode.Not, e); 
		} else if (StartOf(14)) {
			CoercionExpression(out e);
		} else SynErr(120);
	}

	void NegOp() {
		if (la.kind == 80) {
			Get();
		} else if (la.kind == 81) {
			Get();
		} else SynErr(121);
	}

	void CoercionExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;
		Bpl.Type/*!*/ coercedTo;
		BigNum bn;
		
		ArrayExpression(out e);
		while (la.kind == 11) {
			Get();
			x = t; 
			if (StartOf(6)) {
				Type(out coercedTo);
				e = Expr.CoerceType(x, e, coercedTo); 
			} else if (la.kind == 3) {
				Nat(out bn);
				if (!(e is LiteralExpr) || !((LiteralExpr)e).isBigNum) {
				 this.SemErr("arguments of extract need to be integer literals");
				 e = new BvBounds(x, bn, BigNum.ZERO);
				} else {
				 e = new BvBounds(x, bn, ((LiteralExpr)e).asBigNum);
				}
				
			} else SynErr(122);
		}
	}

	void ArrayExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;
		Expr/*!*/ index0 = dummyExpr; Expr/*!*/ e1;
		bool store; bool bvExtract;
		List<Expr>/*!*/ allArgs = dummyExprSeq;
		
		AtomExpression(out e);
		while (la.kind == 17) {
			Get();
			x = t; allArgs = new List<Expr> ();
			allArgs.Add(e);
			store = false; bvExtract = false; 
			if (StartOf(15)) {
				if (StartOf(9)) {
					Expression(out index0);
					if (index0 is BvBounds)
					 bvExtract = true;
					else
					 allArgs.Add(index0);
					
					while (la.kind == 12) {
						Get();
						Expression(out e1);
						if (bvExtract || e1 is BvBounds)
						 this.SemErr("bitvectors only have one dimension");
						allArgs.Add(e1);
						
					}
					if (la.kind == 50) {
						Get();
						Expression(out e1);
						if (bvExtract || e1 is BvBounds)
						 this.SemErr("assignment to bitvectors is not possible");
						allArgs.Add(e1); store = true;
						
					}
				} else {
					Get();
					Expression(out e1);
					allArgs.Add(e1); store = true; 
				}
			}
			Expect(18);
			if (store)
			 e = new NAryExpr(x, new MapStore(x, allArgs.Count - 2), allArgs);
			else if (bvExtract)
			 e = new BvExtractExpr(x, e,
			                       ((BvBounds)index0).Upper.ToIntSafe,
			                       ((BvBounds)index0).Lower.ToIntSafe);
			else
			 e = new NAryExpr(x, new MapSelect(x, allArgs.Count - 1), allArgs);
			
		}
	}

	void Nat(out BigNum n) {
		Expect(3);
		try {
		 n = BigNum.FromString(t.val);
		} catch (FormatException) {
		 this.SemErr("incorrectly formatted number");
		 n = BigNum.ZERO;
		}
		
	}

	void AtomExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x; int n; BigNum bn; BigDec bd;
		List<Expr>/*!*/ es;  List<Variable>/*!*/ ds;  Trigger trig;
		List<TypeVariable>/*!*/ typeParams;
		IdentifierExpr/*!*/ id;
		QKeyValue kv;
		e = dummyExpr;
		List<Variable>/*!*/ locals;
		List<Block/*!*/>/*!*/ blocks;
		
		switch (la.kind) {
		case 82: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 83: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 3: {
			Nat(out bn);
			e = new LiteralExpr(t, bn); 
			break;
		}
		case 5: case 6: {
			Dec(out bd);
			e = new LiteralExpr(t, bd); 
			break;
		}
		case 2: {
			BvLit(out bn, out n);
			e = new LiteralExpr(t, bn, n); 
			break;
		}
		case 1: {
			Ident(out x);
			id = new IdentifierExpr(x, x.val);  e = id; 
			if (la.kind == 9) {
				Get();
				if (StartOf(9)) {
					Expressions(out es);
					e = new NAryExpr(x, new FunctionCall(id), es); 
				} else if (la.kind == 10) {
					e = new NAryExpr(x, new FunctionCall(id), new List<Expr>()); 
				} else SynErr(123);
				Expect(10);
			}
			break;
		}
		case 84: {
			Get();
			x = t; 
			Expect(9);
			Expression(out e);
			Expect(10);
			e = new OldExpr(x, e); 
			break;
		}
		case 14: {
			Get();
			x = t; 
			Expect(9);
			Expression(out e);
			Expect(10);
			e = new NAryExpr(x, new ArithmeticCoercion(x, ArithmeticCoercion.CoercionType.ToInt), new List<Expr>{ e }); 
			break;
		}
		case 15: {
			Get();
			x = t; 
			Expect(9);
			Expression(out e);
			Expect(10);
			e = new NAryExpr(x, new ArithmeticCoercion(x, ArithmeticCoercion.CoercionType.ToReal), new List<Expr>{ e }); 
			break;
		}
		case 9: {
			Get();
			if (StartOf(9)) {
				Expression(out e);
				if (e is BvBounds)
				 this.SemErr("parentheses around bitvector bounds " +
				        "are not allowed"); 
			} else if (la.kind == 88 || la.kind == 89) {
				Forall();
				x = t; 
				QuantifierBody(x, out typeParams, out ds, out kv, out trig, out e);
				if (typeParams.Count + ds.Count > 0)
				 e = new ForallExpr(x, typeParams, ds, kv, trig, e); 
			} else if (la.kind == 90 || la.kind == 91) {
				Exists();
				x = t; 
				QuantifierBody(x, out typeParams, out ds, out kv, out trig, out e);
				if (typeParams.Count + ds.Count > 0)
				 e = new ExistsExpr(x, typeParams, ds, kv, trig, e); 
			} else if (la.kind == 92 || la.kind == 93) {
				Lambda();
				x = t; 
				QuantifierBody(x, out typeParams, out ds, out kv, out trig, out e);
				if (trig != null)
				 SemErr("triggers not allowed in lambda expressions");
				if (typeParams.Count + ds.Count > 0)
				 e = new LambdaExpr(x, typeParams, ds, kv, e); 
			} else SynErr(124);
			Expect(10);
			break;
		}
		case 40: {
			IfThenElseExpression(out e);
			break;
		}
		case 85: {
			CodeExpression(out locals, out blocks);
			e = new CodeExpr(locals, blocks); 
			break;
		}
		default: SynErr(125); break;
		}
	}

	void Dec(out BigDec n) {
		string s = ""; 
		if (la.kind == 5) {
			Get();
			s = t.val; 
		} else if (la.kind == 6) {
			Get();
			s = t.val; 
		} else SynErr(126);
		try {
		 n = BigDec.FromString(s);
		} catch (FormatException) {
		 this.SemErr("incorrectly formatted number");
		 n = BigDec.ZERO;
		}
		
	}

	void BvLit(out BigNum n, out int m) {
		Expect(2);
		int pos = t.val.IndexOf("bv");
		string a = t.val.Substring(0, pos);
		string b = t.val.Substring(pos + 2);
		try {
		 n = BigNum.FromString(a);
		 m = Convert.ToInt32(b);
		} catch (FormatException) {
		 this.SemErr("incorrectly formatted bitvector");
		 n = BigNum.ZERO;
		 m = 0;
		}
		
	}

	void Forall() {
		if (la.kind == 88) {
			Get();
		} else if (la.kind == 89) {
			Get();
		} else SynErr(127);
	}

	void QuantifierBody(IToken/*!*/ q, out List<TypeVariable>/*!*/ typeParams, out List<Variable>/*!*/ ds,
out QKeyValue kv, out Trigger trig, out Expr/*!*/ body) {
		Contract.Requires(q != null); Contract.Ensures(Contract.ValueAtReturn(out typeParams) != null); Contract.Ensures(Contract.ValueAtReturn(out ds) != null); Contract.Ensures(Contract.ValueAtReturn(out body) != null);
		trig = null; typeParams = new List<TypeVariable> ();
		IToken/*!*/ tok;
		kv = null;
		ds = new List<Variable> ();
		
		if (la.kind == 19) {
			TypeParams(out tok, out typeParams);
			if (la.kind == 1 || la.kind == 27) {
				BoundVars(q, out ds);
			}
		} else if (la.kind == 1 || la.kind == 27) {
			BoundVars(q, out ds);
		} else SynErr(128);
		QSep();
		while (la.kind == 27) {
			AttributeOrTrigger(ref kv, ref trig);
		}
		Expression(out body);
	}

	void Exists() {
		if (la.kind == 90) {
			Get();
		} else if (la.kind == 91) {
			Get();
		} else SynErr(129);
	}

	void Lambda() {
		if (la.kind == 92) {
			Get();
		} else if (la.kind == 93) {
			Get();
		} else SynErr(130);
	}

	void IfThenElseExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ tok;
		Expr/*!*/ e0, e1, e2;
		e = dummyExpr; 
		Expect(40);
		tok = t; 
		Expression(out e0);
		Expect(87);
		Expression(out e1);
		Expect(41);
		Expression(out e2);
		e = new NAryExpr(tok, new IfThenElse(tok), new List<Expr>{ e0, e1, e2 }); 
	}

	void CodeExpression(out List<Variable>/*!*/ locals, out List<Block/*!*/>/*!*/ blocks) {
		Contract.Ensures(Contract.ValueAtReturn(out locals) != null); Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out blocks))); locals = new List<Variable>(); Block/*!*/ b;
		blocks = new List<Block/*!*/>();
		
		Expect(85);
		while (la.kind == 7) {
			LocalVars(locals);
		}
		SpecBlock(out b);
		blocks.Add(b); 
		while (la.kind == 1) {
			SpecBlock(out b);
			blocks.Add(b); 
		}
		Expect(86);
	}

	void SpecBlock(out Block/*!*/ b) {
		Contract.Ensures(Contract.ValueAtReturn(out b) != null); IToken/*!*/ x; IToken/*!*/ y;
		Cmd c;  IToken label;
		List<Cmd> cs = new List<Cmd>();
		List<IToken>/*!*/ xs;
		List<String> ss = new List<String>();
		b = dummyBlock;
		Expr/*!*/ e;
		
		Ident(out x);
		Expect(11);
		while (StartOf(8)) {
			LabelOrCmd(out c, out label);
			if (c != null) {
			 Contract.Assert(label == null);
			 cs.Add(c);
			} else {
			 Contract.Assert(label != null);
			 SemErr("SpecBlock's can only have one label");
			}
			
		}
		if (la.kind == 38) {
			Get();
			y = t; 
			Idents(out xs);
			foreach(IToken/*!*/ s in xs){
			 Contract.Assert(s != null);
			 ss.Add(s.val); }
			b = new Block(x,x.val,cs,new GotoCmd(y,ss));
			
		} else if (la.kind == 39) {
			Get();
			Expression(out e);
			b = new Block(x,x.val,cs,new ReturnExprCmd(t,e)); 
		} else SynErr(131);
		Expect(8);
	}

	void AttributeOrTrigger(ref QKeyValue kv, ref Trigger trig) {
		IToken/*!*/ tok;  Expr/*!*/ e;  List<Expr>/*!*/ es;
		string key;
		List<object/*!*/> parameters;  object/*!*/ param;
		
		Expect(27);
		tok = t; 
		if (la.kind == 11) {
			Get();
			Expect(1);
			key = t.val;  parameters = new List<object/*!*/>(); 
			if (StartOf(16)) {
				AttributeParameter(out param);
				parameters.Add(param); 
				while (la.kind == 12) {
					Get();
					AttributeParameter(out param);
					parameters.Add(param); 
				}
			}
			if (key == "nopats") {
			 if (parameters.Count == 1 && parameters[0] is Expr) {
			   e = (Expr)parameters[0];
			   if(trig==null){
			     trig = new Trigger(tok, false, new List<Expr> { e }, null);
			   } else {
			     trig.AddLast(new Trigger(tok, false, new List<Expr> { e }, null));
			   }
			 } else {
			   this.SemErr("the 'nopats' quantifier attribute expects a string-literal parameter");
			 }
			} else {
			 if (kv==null) {
			   kv = new QKeyValue(tok, key, parameters, null);
			 } else {
			   kv.AddLast(new QKeyValue(tok, key, parameters, null));
			 }
			}
			
		} else if (StartOf(9)) {
			Expression(out e);
			es = new List<Expr> { e }; 
			while (la.kind == 12) {
				Get();
				Expression(out e);
				es.Add(e); 
			}
			if (trig==null) {
			 trig = new Trigger(tok, true, es, null);
			} else {
			 trig.AddLast(new Trigger(tok, true, es, null));
			}
			
		} else SynErr(132);
		Expect(28);
	}

	void AttributeParameter(out object/*!*/ o) {
		Contract.Ensures(Contract.ValueAtReturn(out o) != null);
		o = "error";
		Expr/*!*/ e;
		
		if (la.kind == 4) {
			Get();
			o = t.val.Substring(1, t.val.Length-2); 
		} else if (StartOf(9)) {
			Expression(out e);
			o = e; 
		} else SynErr(133);
	}

	void QSep() {
		if (la.kind == 94) {
			Get();
		} else if (la.kind == 95) {
			Get();
		} else SynErr(134);
	}



	public void Parse() {
		la = new Token();
		la.val = "";
		Get();
		BoogiePL();
		Expect(0);

		Expect(0);
	}

	static readonly bool[,]/*!*/ set = {
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,T,T,x, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, x,T,x,x, x,x,T,T, T,T,x,T, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, x,T,x,x, x,x,T,T, T,T,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,T,T, T,x,T,x, x,T,T,T, T,T,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,T,T,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,T,T,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,T,T,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, T,T,T,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x}

	};
} // end Parser


public class Errors {
	public int count = 0;                                    // number of errors detected
	public System.IO.TextWriter/*!*/ errorStream = Console.Out;   // error messages go to this stream
	public string errMsgFormat = "{0}({1},{2}): error: {3}"; // 0=filename, 1=line, 2=column, 3=text
	public string warningMsgFormat = "{0}({1},{2}): warning: {3}"; // 0=filename, 1=line, 2=column, 3=text

	public void SynErr(string filename, int line, int col, int n) {
		SynErr(filename, line, col, GetSyntaxErrorString(n));
	}

	public virtual void SynErr(string filename, int line, int col, string/*!*/ msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(errMsgFormat, filename, line, col, msg);
		count++;
	}

	string GetSyntaxErrorString(int n) {
		string s;
		switch (n) {
			case 0: s = "EOF expected"; break;
			case 1: s = "ident expected"; break;
			case 2: s = "bvlit expected"; break;
			case 3: s = "digits expected"; break;
			case 4: s = "string expected"; break;
			case 5: s = "decimal expected"; break;
			case 6: s = "float expected"; break;
			case 7: s = "\"var\" expected"; break;
			case 8: s = "\";\" expected"; break;
			case 9: s = "\"(\" expected"; break;
			case 10: s = "\")\" expected"; break;
			case 11: s = "\":\" expected"; break;
			case 12: s = "\",\" expected"; break;
			case 13: s = "\"where\" expected"; break;
			case 14: s = "\"int\" expected"; break;
			case 15: s = "\"real\" expected"; break;
			case 16: s = "\"bool\" expected"; break;
			case 17: s = "\"[\" expected"; break;
			case 18: s = "\"]\" expected"; break;
			case 19: s = "\"<\" expected"; break;
			case 20: s = "\">\" expected"; break;
			case 21: s = "\"const\" expected"; break;
			case 22: s = "\"unique\" expected"; break;
			case 23: s = "\"extends\" expected"; break;
			case 24: s = "\"complete\" expected"; break;
			case 25: s = "\"function\" expected"; break;
			case 26: s = "\"returns\" expected"; break;
			case 27: s = "\"{\" expected"; break;
			case 28: s = "\"}\" expected"; break;
			case 29: s = "\"axiom\" expected"; break;
			case 30: s = "\"type\" expected"; break;
			case 31: s = "\"=\" expected"; break;
			case 32: s = "\"procedure\" expected"; break;
			case 33: s = "\"implementation\" expected"; break;
			case 34: s = "\"modifies\" expected"; break;
			case 35: s = "\"free\" expected"; break;
			case 36: s = "\"requires\" expected"; break;
			case 37: s = "\"ensures\" expected"; break;
			case 38: s = "\"goto\" expected"; break;
			case 39: s = "\"return\" expected"; break;
			case 40: s = "\"if\" expected"; break;
			case 41: s = "\"else\" expected"; break;
			case 42: s = "\"while\" expected"; break;
			case 43: s = "\"invariant\" expected"; break;
			case 44: s = "\"*\" expected"; break;
			case 45: s = "\"break\" expected"; break;
			case 46: s = "\"assert\" expected"; break;
			case 47: s = "\"assume\" expected"; break;
			case 48: s = "\"havoc\" expected"; break;
			case 49: s = "\"yield\" expected"; break;
			case 50: s = "\":=\" expected"; break;
			case 51: s = "\"async\" expected"; break;
			case 52: s = "\"call\" expected"; break;
			case 53: s = "\"par\" expected"; break;
			case 54: s = "\"|\" expected"; break;
			case 55: s = "\"<==>\" expected"; break;
			case 56: s = "\"\\u21d4\" expected"; break;
			case 57: s = "\"==>\" expected"; break;
			case 58: s = "\"\\u21d2\" expected"; break;
			case 59: s = "\"<==\" expected"; break;
			case 60: s = "\"\\u21d0\" expected"; break;
			case 61: s = "\"&&\" expected"; break;
			case 62: s = "\"\\u2227\" expected"; break;
			case 63: s = "\"||\" expected"; break;
			case 64: s = "\"\\u2228\" expected"; break;
			case 65: s = "\"==\" expected"; break;
			case 66: s = "\"<=\" expected"; break;
			case 67: s = "\">=\" expected"; break;
			case 68: s = "\"!=\" expected"; break;
			case 69: s = "\"<:\" expected"; break;
			case 70: s = "\"\\u2260\" expected"; break;
			case 71: s = "\"\\u2264\" expected"; break;
			case 72: s = "\"\\u2265\" expected"; break;
			case 73: s = "\"++\" expected"; break;
			case 74: s = "\"+\" expected"; break;
			case 75: s = "\"-\" expected"; break;
			case 76: s = "\"div\" expected"; break;
			case 77: s = "\"mod\" expected"; break;
			case 78: s = "\"/\" expected"; break;
			case 79: s = "\"**\" expected"; break;
			case 80: s = "\"!\" expected"; break;
			case 81: s = "\"\\u00ac\" expected"; break;
			case 82: s = "\"false\" expected"; break;
			case 83: s = "\"true\" expected"; break;
			case 84: s = "\"old\" expected"; break;
			case 85: s = "\"|{\" expected"; break;
			case 86: s = "\"}|\" expected"; break;
			case 87: s = "\"then\" expected"; break;
			case 88: s = "\"forall\" expected"; break;
			case 89: s = "\"\\u2200\" expected"; break;
			case 90: s = "\"exists\" expected"; break;
			case 91: s = "\"\\u2203\" expected"; break;
			case 92: s = "\"lambda\" expected"; break;
			case 93: s = "\"\\u03bb\" expected"; break;
			case 94: s = "\"::\" expected"; break;
			case 95: s = "\"\\u2022\" expected"; break;
			case 96: s = "??? expected"; break;
			case 97: s = "invalid Function"; break;
			case 98: s = "invalid Function"; break;
			case 99: s = "invalid Procedure"; break;
			case 100: s = "invalid Type"; break;
			case 101: s = "invalid TypeAtom"; break;
			case 102: s = "invalid TypeArgs"; break;
			case 103: s = "invalid Spec"; break;
			case 104: s = "invalid SpecPrePost"; break;
			case 105: s = "invalid LabelOrCmd"; break;
			case 106: s = "invalid StructuredCmd"; break;
			case 107: s = "invalid TransferCmd"; break;
			case 108: s = "invalid IfCmd"; break;
			case 109: s = "invalid Guard"; break;
			case 110: s = "invalid LabelOrAssign"; break;
			case 111: s = "invalid CallParams"; break;
			case 112: s = "invalid EquivOp"; break;
			case 113: s = "invalid ImpliesOp"; break;
			case 114: s = "invalid ExpliesOp"; break;
			case 115: s = "invalid AndOp"; break;
			case 116: s = "invalid OrOp"; break;
			case 117: s = "invalid RelOp"; break;
			case 118: s = "invalid AddOp"; break;
			case 119: s = "invalid MulOp"; break;
			case 120: s = "invalid UnaryExpression"; break;
			case 121: s = "invalid NegOp"; break;
			case 122: s = "invalid CoercionExpression"; break;
			case 123: s = "invalid AtomExpression"; break;
			case 124: s = "invalid AtomExpression"; break;
			case 125: s = "invalid AtomExpression"; break;
			case 126: s = "invalid Dec"; break;
			case 127: s = "invalid Forall"; break;
			case 128: s = "invalid QuantifierBody"; break;
			case 129: s = "invalid Exists"; break;
			case 130: s = "invalid Lambda"; break;
			case 131: s = "invalid SpecBlock"; break;
			case 132: s = "invalid AttributeOrTrigger"; break;
			case 133: s = "invalid AttributeParameter"; break;
			case 134: s = "invalid QSep"; break;

			default: s = "error " + n; break;
		}
		return s;
	}

	public void SemErr(IToken/*!*/ tok, string/*!*/ msg) {  // semantic errors
		Contract.Requires(tok != null);
		Contract.Requires(msg != null);
		SemErr(tok.filename, tok.line, tok.col, msg);
	}

	public virtual void SemErr(string filename, int line, int col, string/*!*/ msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(errMsgFormat, filename, line, col, msg);
		count++;
	}

	public void Warning(IToken/*!*/ tok, string/*!*/ msg) {  // warnings
		Contract.Requires(tok != null);
		Contract.Requires(msg != null);
		Warning(tok.filename, tok.line, tok.col, msg);
	}

	public virtual void Warning(string filename, int line, int col, string msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(warningMsgFormat, filename, line, col, msg);
	}
} // Errors


public class FatalError: Exception {
	public FatalError(string m): base(m) {}
}


}