using PureCollections;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using Bpl = Microsoft.Boogie;
using AI = Microsoft.AbstractInterpretationFramework;




using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {



public class Parser {
	public const int _EOF = 0;
	public const int _ident = 1;
	public const int _bvlit = 2;
	public const int _digits = 3;
	public const int _string = 4;
	public const int _float = 5;
	public const int maxT = 88;

	const bool T = true;
	const bool x = false;
	const int minErrDist = 2;

	public Scanner/*!*/ scanner;
	public Errors/*!*/  errors;

	public Token/*!*/ t;    // last recognized token
	public Token/*!*/ la;   // lookahead token
	int errDist = minErrDist;

static Program/*!*/ Pgm = new Program();

static Expr/*!*/ dummyExpr = new LiteralExpr(Token.NoToken, false);
static Cmd/*!*/ dummyCmd = new AssumeCmd(Token.NoToken, dummyExpr);
static Block/*!*/ dummyBlock = new Block(Token.NoToken, "dummyBlock", new CmdSeq(),
                                     new ReturnCmd(Token.NoToken));
static Bpl.Type/*!*/ dummyType = new BasicType(Token.NoToken, SimpleType.Bool);
static Bpl.ExprSeq/*!*/ dummyExprSeq = new ExprSeq ();
static TransferCmd/*!*/ dummyTransferCmd = new ReturnCmd(Token.NoToken);
static StructuredCmd/*!*/ dummyStructuredCmd = new BreakCmd(Token.NoToken, null);

///<summary>
///Returns the number of parsing errors encountered.  If 0, "program" returns as
///the parsed program.
///</summary>
public static int Parse (string/*!*/ filename, /*maybe null*/ List<string/*!*/> defines, out /*maybe null*/ Program program) /* throws System.IO.IOException */ {
Contract.Requires(filename != null);
Contract.Requires(cce.NonNullElements(defines,true));


  FileStream stream = new FileStream(filename, FileMode.Open, FileAccess.Read, FileShare.Read);
  var ret = Parse(stream, filename, defines, out program);
  stream.Close();
  return ret;
}

  
public static int Parse (Stream stream, string/*!*/ filename, /*maybe null*/ List<string/*!*/> defines, out /*maybe null*/ Program program) /* throws System.IO.IOException */ {
Contract.Requires(stream != null);
Contract.Requires(filename != null);
Contract.Requires(cce.NonNullElements(defines,true));

  if (defines == null) {
    defines = new List<string/*!*/>();
  }
  string s = ParserHelper.Fill(stream, defines);
  byte[]/*!*/ buffer = cce.NonNull(UTF8Encoding.Default.GetBytes(s));
  MemoryStream ms = new MemoryStream(buffer,false);
  Errors errors = new Errors();
  Scanner scanner = new Scanner(ms, errors, filename);

  Parser parser = new Parser(scanner, errors);
  Pgm = new Program(); // reset the global variable
    parser.Parse();
    if (parser.errors.count == 0)
    {
      program = Pgm;
      return 0;
    }
    else
    {
      program = null;
      return parser.errors.count;
    }
}

// Class to represent the bounds of a bitvector expression t[a:b].
// Objects of this class only exist during parsing and are directly
// turned into BvExtract before they get anywhere else
private class BvBounds : Expr {
  public BigNum Lower;
  public BigNum Upper;
  public BvBounds(IToken/*!*/ tok, BigNum lower, BigNum upper) :base(tok){//BASEMOVE
    Contract.Requires(tok != null);
    //:base(tok);
    this.Lower = lower;
    this.Upper = upper;
  }
  public override Type/*!*/ ShallowType { get {Contract.Ensures(Contract.Result<Type>() != null); return Bpl.Type.Int; } }
  public override void Resolve(ResolutionContext/*!*/ rc) {
  Contract.Requires(rc != null);
    rc.Error(this, "bitvector bounds in illegal position");
  }
  public override void Emit(TokenTextWriter/*!*/ stream,
                            int contextBindingStrength, bool fragileContext) {
    Contract.Requires(stream != null);
    {Contract.Assert(false);throw new cce.UnreachableException();}
  }
  public override void ComputeFreeVariables(Set/*!*/ freeVars) {Contract.Requires(freeVars != null); {Contract.Assert(false);throw new cce.UnreachableException();} }
  public override AI.IExpr/*!*/ IExpr { get { Contract.Ensures(Contract.Result<AI.IExpr>()!=null); {Contract.Assert(false);throw new cce.UnreachableException();} } }
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
		VariableSeq/*!*/ vs;
		DeclarationSeq/*!*/ ds;
		Axiom/*!*/ ax;
		List<Declaration/*!*/>/*!*/ ts;
		Procedure/*!*/ pr;
		Implementation im;
		Implementation/*!*/ nnim;
		
		while (StartOf(1)) {
			switch (la.kind) {
			case 19: {
				Consts(out vs);
				foreach(Bpl.Variable/*!*/ v in vs){
				 Contract.Assert(v != null);
				 Pgm.TopLevelDeclarations.Add(v);
				}
				
				break;
			}
			case 23: {
				Function(out ds);
				foreach(Bpl.Declaration/*!*/ d in ds){
				 Contract.Assert(d != null);
				 Pgm.TopLevelDeclarations.Add(d);
				}
				
				break;
			}
			case 27: {
				Axiom(out ax);
				Pgm.TopLevelDeclarations.Add(ax); 
				break;
			}
			case 28: {
				UserDefinedTypes(out ts);
				foreach(Declaration/*!*/ td in ts){
				 Contract.Assert(td != null);
				 Pgm.TopLevelDeclarations.Add(td);
				}
				
				break;
			}
			case 6: {
				GlobalVars(out vs);
				foreach(Bpl.Variable/*!*/ v in vs){
				 Contract.Assert(v != null);
				 Pgm.TopLevelDeclarations.Add(v);
				}
				
				break;
			}
			case 30: {
				Procedure(out pr, out im);
				Pgm.TopLevelDeclarations.Add(pr);
				if (im != null) {
				  Pgm.TopLevelDeclarations.Add(im);
				}
				
				break;
			}
			case 31: {
				Implementation(out nnim);
				Pgm.TopLevelDeclarations.Add(nnim); 
				break;
			}
			}
		}
		Expect(0);
	}

	void Consts(out VariableSeq/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null); IToken/*!*/ y; TypedIdentSeq/*!*/ xs;
		ds = new VariableSeq();
		bool u = false; QKeyValue kv = null;
		bool ChildrenComplete = false;
		List<ConstantParent/*!*/> Parents = null; 
		Expect(19);
		y = t; 
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		if (la.kind == 20) {
			Get();
			u = true;  
		}
		IdsType(out xs);
		if (la.kind == 21) {
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
		  
		Expect(7);
	}

	void Function(out DeclarationSeq/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null);
		ds = new DeclarationSeq(); IToken/*!*/ z;
		     IToken/*!*/ typeParamTok;
		     TypeVariableSeq/*!*/ typeParams = new TypeVariableSeq();
		     VariableSeq arguments = new VariableSeq();
		     TypedIdent/*!*/ tyd;
		     TypedIdent retTyd = null;
		     Type/*!*/ retTy;
		     QKeyValue kv = null;
		     Expr definition = null;
		     Expr/*!*/ tmp;
		  
		Expect(23);
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		Ident(out z);
		if (la.kind == 17) {
			TypeParams(out typeParamTok, out typeParams);
		}
		Expect(8);
		if (StartOf(2)) {
			VarOrType(out tyd);
			arguments.Add(new Formal(tyd.tok, tyd, true)); 
			while (la.kind == 11) {
				Get();
				VarOrType(out tyd);
				arguments.Add(new Formal(tyd.tok, tyd, true)); 
			}
		}
		Expect(9);
		if (la.kind == 24) {
			Get();
			Expect(8);
			VarOrType(out tyd);
			Expect(9);
			retTyd = tyd; 
		} else if (la.kind == 10) {
			Get();
			Type(out retTy);
			retTyd = new TypedIdent(retTy.tok, "", retTy); 
		} else SynErr(89);
		if (la.kind == 25) {
			Get();
			Expression(out tmp);
			definition = tmp; 
			Expect(26);
		} else if (la.kind == 7) {
			Get();
		} else SynErr(90);
		if (retTyd == null) {
		 // construct a dummy type for the case of syntax error
		 tyd = new TypedIdent(t, "", new BasicType(t, SimpleType.Int));
		} else {
		  tyd = retTyd;
		}
		Function/*!*/ func = new Function(z, z.val, typeParams, arguments,
		                       new Formal(tyd.tok, tyd, false), null, kv);
		Contract.Assert(func != null);
		ds.Add(func);
		bool allUnnamed = true;
		foreach(Formal/*!*/ f in arguments){
		  Contract.Assert(f != null);
		  if (f.TypedIdent.Name != "") {
		    allUnnamed = false;
		break;
		     }
		   }
		   if (!allUnnamed) {
		     Type prevType = null;
		     for (int i = arguments.Length - 1; i >= 0; i--) {
		       TypedIdent/*!*/ curr = cce.NonNull(arguments[i]).TypedIdent;
		       if (curr.Name == "") {
		  if (prevType == null) {
		    this.errors.SemErr(curr.tok, "the type of the last parameter is unspecified");
		    break;
		  }
		  Type ty = curr.Type;
		         if (ty is UnresolvedTypeIdentifier &&
		             cce.NonNull(ty as UnresolvedTypeIdentifier).Arguments.Length == 0) {
		    curr.Name = cce.NonNull(ty as UnresolvedTypeIdentifier).Name;
		    curr.Type = prevType;
		  } else {
		    this.errors.SemErr(curr.tok, "expecting an identifier as parameter name");
		  }
		} else {
		  prevType = curr.Type;
		}
		     }
		   }
		   if (definition != null) {
		     // generate either an axiom or a function body
		     if (QKeyValue.FindBoolAttribute(kv, "inline")) {
		       func.Body = definition;
		     } else {
		       VariableSeq dummies = new VariableSeq();
		       ExprSeq callArgs = new ExprSeq();
		       int i = 0;
		       foreach(Formal/*!*/ f in arguments){
		         Contract.Assert(f != null);
		         string nm = f.TypedIdent.HasName ? f.TypedIdent.Name : "_" + i;
		         dummies.Add(new BoundVariable(f.tok, new TypedIdent(f.tok, nm, f.TypedIdent.Type)));
		         callArgs.Add(new IdentifierExpr(f.tok, nm));
		         i++;
		       }
		       TypeVariableSeq/*!*/ quantifiedTypeVars = new TypeVariableSeq ();
		       foreach(TypeVariable/*!*/ t in typeParams){
		         Contract.Assert(t != null);
		         quantifiedTypeVars.Add(new TypeVariable (Token.NoToken, t.Name));
		       }
		
		        Expr call = new NAryExpr(z, new FunctionCall(new IdentifierExpr(z, z.val)), callArgs);
		        // specify the type of the function, because it might be that
		        // type parameters only occur in the output type
		        call = Expr.CoerceType(z, call, (Type)tyd.Type.Clone());
		        Expr def = Expr.Eq(call, definition);
		        if (quantifiedTypeVars.Length != 0 || dummies.Length != 0) {
		          def = new ForallExpr(z, quantifiedTypeVars, dummies,
		                               kv,
		                               new Trigger(z, true, new ExprSeq(call), null),
		                               def);
		        }
		        ds.Add(new Axiom(z, def, "autogenerated definition axiom", null));
		      }
		    }
		  
	}

	void Axiom(out Axiom/*!*/ m) {
		Contract.Ensures(Contract.ValueAtReturn(out m) != null); Expr/*!*/ e; QKeyValue kv = null; 
		Expect(27);
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		IToken/*!*/ x = t; 
		Proposition(out e);
		Expect(7);
		m = new Axiom(x,e, null, kv); 
	}

	void UserDefinedTypes(out List<Declaration/*!*/>/*!*/ ts) {
		Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out ts))); Declaration/*!*/ decl; QKeyValue kv = null; ts = new List<Declaration/*!*/> (); 
		Expect(28);
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		UserDefinedType(out decl, kv);
		ts.Add(decl);  
		while (la.kind == 11) {
			Get();
			UserDefinedType(out decl, kv);
			ts.Add(decl);  
		}
		Expect(7);
	}

	void GlobalVars(out VariableSeq/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null); TypedIdentSeq/*!*/ tyds = new TypedIdentSeq(); ds = new VariableSeq(); QKeyValue kv = null; 
		Expect(6);
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		IdsTypeWheres(true, tyds);
		Expect(7);
		foreach(TypedIdent/*!*/ tyd in tyds){
		 Contract.Assert(tyd != null);
		 ds.Add(new GlobalVariable(tyd.tok, tyd, kv));
		}
		
	}

	void Procedure(out Procedure/*!*/ proc, out /*maybe null*/ Implementation impl) {
		Contract.Ensures(Contract.ValueAtReturn(out proc) != null); IToken/*!*/ x;
		TypeVariableSeq/*!*/ typeParams;
		VariableSeq/*!*/ ins, outs;
		RequiresSeq/*!*/ pre = new RequiresSeq();
		IdentifierExprSeq/*!*/ mods = new IdentifierExprSeq();
		EnsuresSeq/*!*/ post = new EnsuresSeq();
		
		     VariableSeq/*!*/ locals = new VariableSeq();
		     StmtList/*!*/ stmtList;
		     QKeyValue kv = null;
		     impl = null;
		  
		Expect(30);
		ProcSignature(true, out x, out typeParams, out ins, out outs, out kv);
		if (la.kind == 7) {
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
			                         Formal.StripWhereClauses(ins), Formal.StripWhereClauses(outs), locals, stmtList, null, this.errors); 
			
		} else SynErr(91);
		proc = new Procedure(x, x.val, typeParams, ins, outs, pre, mods, post, kv); 
	}

	void Implementation(out Implementation/*!*/ impl) {
		Contract.Ensures(Contract.ValueAtReturn(out impl) != null); IToken/*!*/ x;
		TypeVariableSeq/*!*/ typeParams;
		VariableSeq/*!*/ ins, outs;
		VariableSeq/*!*/ locals;
		StmtList/*!*/ stmtList;
		QKeyValue kv;
		
		Expect(31);
		ProcSignature(false, out x, out typeParams, out ins, out outs, out kv);
		ImplBody(out locals, out stmtList);
		impl = new Implementation(x, x.val, typeParams, ins, outs, locals, stmtList, kv, this.errors); 
	}

	void Attribute(ref QKeyValue kv) {
		Trigger trig = null; 
		AttributeOrTrigger(ref kv, ref trig);
		if (trig != null) this.SemErr("only attributes, not triggers, allowed here"); 
	}

	void IdsTypeWheres(bool allowWhereClauses, TypedIdentSeq/*!*/ tyds) {
		Contract.Requires(tyds != null);
		IdsTypeWhere(allowWhereClauses, tyds);
		while (la.kind == 11) {
			Get();
			IdsTypeWhere(allowWhereClauses, tyds);
		}
	}

	void LocalVars(VariableSeq/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null); TypedIdentSeq/*!*/ tyds = new TypedIdentSeq(); QKeyValue kv = null; 
		Expect(6);
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		IdsTypeWheres(true, tyds);
		Expect(7);
		foreach(TypedIdent/*!*/ tyd in tyds){
		 Contract.Assert(tyd != null);
		 ds.Add(new LocalVariable(tyd.tok, tyd, kv));
		}
		
	}

	void ProcFormals(bool incoming, bool allowWhereClauses, out VariableSeq/*!*/ ds) {
		Contract.Ensures(Contract.ValueAtReturn(out ds) != null); TypedIdentSeq/*!*/ tyds = new TypedIdentSeq(); ds = new VariableSeq(); 
		Expect(8);
		if (la.kind == 1) {
			IdsTypeWheres(allowWhereClauses, tyds);
		}
		Expect(9);
		foreach(TypedIdent/*!*/ tyd in tyds){
		 Contract.Assert(tyd != null);
		 ds.Add(new Formal(tyd.tok, tyd, incoming));
		}
		
	}

	void BoundVars(IToken/*!*/ x, out VariableSeq/*!*/ ds) {
		Contract.Requires(x != null); Contract.Ensures(Contract.ValueAtReturn(out ds) != null); TypedIdentSeq/*!*/ tyds = new TypedIdentSeq(); ds = new VariableSeq(); 
		IdsTypeWheres(false, tyds);
		foreach(TypedIdent/*!*/ tyd in tyds){
		 Contract.Assert(tyd != null);
		 ds.Add(new BoundVariable(tyd.tok, tyd));
		}
		
	}

	void IdsType(out TypedIdentSeq/*!*/ tyds) {
		Contract.Ensures(Contract.ValueAtReturn(out tyds) != null); TokenSeq/*!*/ ids;  Bpl.Type/*!*/ ty; 
		Idents(out ids);
		Expect(10);
		Type(out ty);
		tyds = new TypedIdentSeq();
		foreach(Token/*!*/ id in ids){
		  Contract.Assert(id != null);
		  tyds.Add(new TypedIdent(id, id.val, ty, null));
		}
		
	}

	void Idents(out TokenSeq/*!*/ xs) {
		Contract.Ensures(Contract.ValueAtReturn(out xs) != null); IToken/*!*/ id; xs = new TokenSeq(); 
		Ident(out id);
		xs.Add(id); 
		while (la.kind == 11) {
			Get();
			Ident(out id);
			xs.Add(id); 
		}
	}

	void Type(out Bpl.Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken/*!*/ tok; ty = dummyType; 
		if (la.kind == 8 || la.kind == 13 || la.kind == 14) {
			TypeAtom(out ty);
		} else if (la.kind == 1) {
			Ident(out tok);
			TypeSeq/*!*/ args = new TypeSeq (); 
			if (StartOf(2)) {
				TypeArgs(args);
			}
			ty = new UnresolvedTypeIdentifier (tok, tok.val, args); 
		} else if (la.kind == 15 || la.kind == 17) {
			MapType(out ty);
		} else SynErr(92);
	}

	void IdsTypeWhere(bool allowWhereClauses, TypedIdentSeq/*!*/ tyds) {
		Contract.Requires(tyds != null); TokenSeq/*!*/ ids;  Bpl.Type/*!*/ ty;  Expr wh = null;  Expr/*!*/ nne; 
		Idents(out ids);
		Expect(10);
		Type(out ty);
		if (la.kind == 12) {
			Get();
			Expression(out nne);
			if (allowWhereClauses) {
			 wh = nne;
			} else {
			  this.SemErr("where clause not allowed here");
			}
			
		}
		foreach(Token/*!*/ id in ids){
		 Contract.Assert(id != null);
		 tyds.Add(new TypedIdent(id, id.val, ty, wh));
		}
		
	}

	void Expression(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		ImpliesExpression(false, out e0);
		while (la.kind == 50 || la.kind == 51) {
			EquivOp();
			x = t; 
			ImpliesExpression(false, out e1);
			e0 = Expr.Binary(x, BinaryOperator.Opcode.Iff, e0, e1); 
		}
	}

	void TypeAtom(out Bpl.Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); ty = dummyType; 
		if (la.kind == 13) {
			Get();
			ty = new BasicType(t, SimpleType.Int); 
		} else if (la.kind == 14) {
			Get();
			ty = new BasicType(t, SimpleType.Bool); 
		} else if (la.kind == 8) {
			Get();
			Type(out ty);
			Expect(9);
		} else SynErr(93);
	}

	void Ident(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		Expect(1);
		x = t;
		if (x.val.StartsWith("\\"))
		  x.val = x.val.Substring(1);
		
	}

	void TypeArgs(TypeSeq/*!*/ ts) {
		Contract.Requires(ts != null); IToken/*!*/ tok; Type/*!*/ ty; 
		if (la.kind == 8 || la.kind == 13 || la.kind == 14) {
			TypeAtom(out ty);
			ts.Add(ty); 
			if (StartOf(2)) {
				TypeArgs(ts);
			}
		} else if (la.kind == 1) {
			Ident(out tok);
			TypeSeq/*!*/ args = new TypeSeq ();
			ts.Add(new UnresolvedTypeIdentifier (tok, tok.val, args)); 
			if (StartOf(2)) {
				TypeArgs(ts);
			}
		} else if (la.kind == 15 || la.kind == 17) {
			MapType(out ty);
			ts.Add(ty); 
		} else SynErr(94);
	}

	void MapType(out Bpl.Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken tok = null;
		IToken/*!*/ nnTok;
		TypeSeq/*!*/ arguments = new TypeSeq();
		Type/*!*/ result;
		TypeVariableSeq/*!*/ typeParameters = new TypeVariableSeq();
		
		if (la.kind == 17) {
			TypeParams(out nnTok, out typeParameters);
			tok = nnTok; 
		}
		Expect(15);
		if (tok == null) tok = t;  
		if (StartOf(2)) {
			Types(arguments);
		}
		Expect(16);
		Type(out result);
		ty = new MapType(tok, typeParameters, arguments, result);
		
	}

	void TypeParams(out IToken/*!*/ tok, out Bpl.TypeVariableSeq/*!*/ typeParams) {
		Contract.Ensures(Contract.ValueAtReturn(out tok) != null); Contract.Ensures(Contract.ValueAtReturn(out typeParams) != null); TokenSeq/*!*/ typeParamToks; 
		Expect(17);
		tok = t;  
		Idents(out typeParamToks);
		Expect(18);
		typeParams = new TypeVariableSeq ();
		foreach(Token/*!*/ id in typeParamToks){
		  Contract.Assert(id != null);
		  typeParams.Add(new TypeVariable(id, id.val));}
		
	}

	void Types(TypeSeq/*!*/ ts) {
		Contract.Requires(ts != null); Bpl.Type/*!*/ ty; 
		Type(out ty);
		ts.Add(ty); 
		while (la.kind == 11) {
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
		Expect(21);
		Parents = new List<ConstantParent/*!*/> ();
		u = false; 
		if (la.kind == 1 || la.kind == 20) {
			if (la.kind == 20) {
				Get();
				u = true; 
			}
			Ident(out parent);
			Parents.Add(new ConstantParent (
			           new IdentifierExpr(parent, parent.val), u)); 
			while (la.kind == 11) {
				Get();
				u = false; 
				if (la.kind == 20) {
					Get();
					u = true; 
				}
				Ident(out parent);
				Parents.Add(new ConstantParent (
				           new IdentifierExpr(parent, parent.val), u)); 
			}
		}
		if (la.kind == 22) {
			Get();
			ChildrenComplete = true; 
		}
	}

	void VarOrType(out TypedIdent/*!*/ tyd) {
		Contract.Ensures(Contract.ValueAtReturn(out tyd) != null); string/*!*/ varName = ""; Bpl.Type/*!*/ ty; IToken/*!*/ tok; 
		Type(out ty);
		tok = ty.tok; 
		if (la.kind == 10) {
			Get();
			if (ty is UnresolvedTypeIdentifier &&
			   cce.NonNull(ty as UnresolvedTypeIdentifier).Arguments.Length == 0) {
			 varName = cce.NonNull(ty as UnresolvedTypeIdentifier).Name;
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
		Contract.Ensures(Contract.ValueAtReturn(out decl) != null); IToken/*!*/ id; TokenSeq/*!*/ paramTokens = new TokenSeq ();
		Type/*!*/ body = dummyType; bool synonym = false; 
		Ident(out id);
		if (la.kind == 1) {
			WhiteSpaceIdents(out paramTokens);
		}
		if (la.kind == 29) {
			Get();
			Type(out body);
			synonym = true; 
		}
		if (synonym) {
		 TypeVariableSeq/*!*/ typeParams = new TypeVariableSeq();
		 foreach(Token/*!*/ t in paramTokens){
		   Contract.Assert(t != null);
		   typeParams.Add(new TypeVariable(t, t.val));}
		 decl = new TypeSynonymDecl(id, id.val, typeParams, body, kv);
		} else {
		  decl = new TypeCtorDecl(id, id.val, paramTokens.Length, kv);
		}
		
	}

	void WhiteSpaceIdents(out TokenSeq/*!*/ xs) {
		Contract.Ensures(Contract.ValueAtReturn(out xs) != null); IToken/*!*/ id; xs = new TokenSeq(); 
		Ident(out id);
		xs.Add(id); 
		while (la.kind == 1) {
			Ident(out id);
			xs.Add(id); 
		}
	}

	void ProcSignature(bool allowWhereClausesOnFormals, out IToken/*!*/ name, out TypeVariableSeq/*!*/ typeParams,
out VariableSeq/*!*/ ins, out VariableSeq/*!*/ outs, out QKeyValue kv) {
		Contract.Ensures(Contract.ValueAtReturn(out name) != null); Contract.Ensures(Contract.ValueAtReturn(out typeParams) != null); Contract.Ensures(Contract.ValueAtReturn(out ins) != null); Contract.Ensures(Contract.ValueAtReturn(out outs) != null);
		IToken/*!*/ typeParamTok; typeParams = new TypeVariableSeq();
		outs = new VariableSeq(); kv = null; 
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		Ident(out name);
		if (la.kind == 17) {
			TypeParams(out typeParamTok, out typeParams);
		}
		ProcFormals(true, allowWhereClausesOnFormals, out ins);
		if (la.kind == 24) {
			Get();
			ProcFormals(false, allowWhereClausesOnFormals, out outs);
		}
	}

	void Spec(RequiresSeq/*!*/ pre, IdentifierExprSeq/*!*/ mods, EnsuresSeq/*!*/ post) {
		Contract.Requires(pre != null); Contract.Requires(mods != null); Contract.Requires(post != null); TokenSeq/*!*/ ms; 
		if (la.kind == 32) {
			Get();
			if (la.kind == 1) {
				Idents(out ms);
				foreach(IToken/*!*/ m in ms){
				 Contract.Assert(m != null);
				 mods.Add(new IdentifierExpr(m, m.val));
				}
				
			}
			Expect(7);
		} else if (la.kind == 33) {
			Get();
			SpecPrePost(true, pre, post);
		} else if (la.kind == 34 || la.kind == 35) {
			SpecPrePost(false, pre, post);
		} else SynErr(95);
	}

	void ImplBody(out VariableSeq/*!*/ locals, out StmtList/*!*/ stmtList) {
		Contract.Ensures(Contract.ValueAtReturn(out locals) != null); Contract.Ensures(Contract.ValueAtReturn(out stmtList) != null); locals = new VariableSeq(); 
		Expect(25);
		while (la.kind == 6) {
			LocalVars(locals);
		}
		StmtList(out stmtList);
	}

	void SpecPrePost(bool free, RequiresSeq/*!*/ pre, EnsuresSeq/*!*/ post) {
		Contract.Requires(pre != null); Contract.Requires(post != null); Expr/*!*/ e; Token tok = null; QKeyValue kv = null; 
		if (la.kind == 34) {
			Get();
			tok = t; 
			while (la.kind == 25) {
				Attribute(ref kv);
			}
			Proposition(out e);
			Expect(7);
			pre.Add(new Requires(tok, free, e, null, kv)); 
		} else if (la.kind == 35) {
			Get();
			tok = t; 
			while (la.kind == 25) {
				Attribute(ref kv);
			}
			Proposition(out e);
			Expect(7);
			post.Add(new Ensures(tok, free, e, null, kv)); 
		} else SynErr(96);
	}

	void StmtList(out StmtList/*!*/ stmtList) {
		Contract.Ensures(Contract.ValueAtReturn(out stmtList) != null); List<BigBlock/*!*/> bigblocks = new List<BigBlock/*!*/>();
		/* built-up state for the current BigBlock: */
		IToken startToken = null;  string currentLabel = null;
		CmdSeq cs = null;  /* invariant: startToken != null ==> cs != null */
		/* temporary variables: */
		IToken label;  Cmd c;  BigBlock b;
		StructuredCmd ec = null;  StructuredCmd/*!*/ ecn;
		TransferCmd tc = null;  TransferCmd/*!*/ tcn;
		
		while (StartOf(5)) {
			if (StartOf(6)) {
				LabelOrCmd(out c, out label);
				if (c != null) {
				 // LabelOrCmd read a Cmd
				 Contract.Assert(label == null);
				 if (startToken == null) { startToken = c.tok;  cs = new CmdSeq(); }
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
				  cs = new CmdSeq();
				}
				
			} else if (la.kind == 38 || la.kind == 40 || la.kind == 43) {
				StructuredCmd(out ecn);
				ec = ecn;
				if (startToken == null) { startToken = ec.tok;  cs = new CmdSeq(); }
				Contract.Assert(cs != null);
				b = new BigBlock(startToken, currentLabel, cs, ec, null);
				bigblocks.Add(b);
				startToken = null;  currentLabel = null;  cs = null;
				
			} else {
				TransferCmd(out tcn);
				tc = tcn;
				if (startToken == null) { startToken = tc.tok;  cs = new CmdSeq(); }
				Contract.Assert(cs != null);
				b = new BigBlock(startToken, currentLabel, cs, null, tc);
				bigblocks.Add(b);
				startToken = null;  currentLabel = null;  cs = null;
				
			}
		}
		Expect(26);
		IToken/*!*/ endCurly = t;
		if (startToken == null && bigblocks.Count == 0) {
		  startToken = t;  cs = new CmdSeq();
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
		TokenSeq/*!*/ xs;
		IdentifierExprSeq ids;
		c = dummyCmd;  label = null;
		Cmd/*!*/ cn;
		QKeyValue kv = null;
		
		if (la.kind == 1) {
			LabelOrAssign(out c, out label);
		} else if (la.kind == 44) {
			Get();
			x = t; 
			while (la.kind == 25) {
				Attribute(ref kv);
			}
			Proposition(out e);
			c = new AssertCmd(x, e, kv); 
			Expect(7);
		} else if (la.kind == 45) {
			Get();
			x = t; 
			while (la.kind == 25) {
				Attribute(ref kv);
			}
			Proposition(out e);
			c = new AssumeCmd(x, e, kv); 
			Expect(7);
		} else if (la.kind == 46) {
			Get();
			x = t; 
			Idents(out xs);
			Expect(7);
			ids = new IdentifierExprSeq();
			foreach(IToken/*!*/ y in xs){
			  Contract.Assert(y != null);
			  ids.Add(new IdentifierExpr(y, y.val));
			}
			c = new HavocCmd(x,ids);
			
		} else if (la.kind == 48) {
			CallCmd(out cn);
			Expect(7);
			c = cn; 
		} else SynErr(97);
	}

	void StructuredCmd(out StructuredCmd/*!*/ ec) {
		Contract.Ensures(Contract.ValueAtReturn(out ec) != null); ec = dummyStructuredCmd;  Contract.Assume(cce.IsPeerConsistent(ec));
		IfCmd/*!*/ ifcmd;  WhileCmd/*!*/ wcmd;  BreakCmd/*!*/ bcmd;
		
		if (la.kind == 38) {
			IfCmd(out ifcmd);
			ec = ifcmd; 
		} else if (la.kind == 40) {
			WhileCmd(out wcmd);
			ec = wcmd; 
		} else if (la.kind == 43) {
			BreakCmd(out bcmd);
			ec = bcmd; 
		} else SynErr(98);
	}

	void TransferCmd(out TransferCmd/*!*/ tc) {
		Contract.Ensures(Contract.ValueAtReturn(out tc) != null); tc = dummyTransferCmd;
		Token y;  TokenSeq/*!*/ xs;
		StringSeq ss = new StringSeq();
		
		if (la.kind == 36) {
			Get();
			y = t; 
			Idents(out xs);
			foreach(IToken/*!*/ s in xs){
			 Contract.Assert(s != null);
			 ss.Add(s.val); }
			tc = new GotoCmd(y, ss);
			
		} else if (la.kind == 37) {
			Get();
			tc = new ReturnCmd(t); 
		} else SynErr(99);
		Expect(7);
	}

	void IfCmd(out IfCmd/*!*/ ifcmd) {
		Contract.Ensures(Contract.ValueAtReturn(out ifcmd) != null); IToken/*!*/ x;
		Expr guard;
		StmtList/*!*/ thn;
		IfCmd/*!*/ elseIf;  IfCmd elseIfOption = null;
		StmtList/*!*/ els;  StmtList elseOption = null;
		
		Expect(38);
		x = t; 
		Guard(out guard);
		Expect(25);
		StmtList(out thn);
		if (la.kind == 39) {
			Get();
			if (la.kind == 38) {
				IfCmd(out elseIf);
				elseIfOption = elseIf; 
			} else if (la.kind == 25) {
				Get();
				StmtList(out els);
				elseOption = els; 
			} else SynErr(100);
		}
		ifcmd = new IfCmd(x, guard, thn, elseIfOption, elseOption); 
	}

	void WhileCmd(out WhileCmd/*!*/ wcmd) {
		Contract.Ensures(Contract.ValueAtReturn(out wcmd) != null); IToken/*!*/ x;  Token z;
		Expr guard;  Expr/*!*/ e;  bool isFree;
		List<PredicateCmd/*!*/> invariants = new List<PredicateCmd/*!*/>();
		StmtList/*!*/ body;
		
		Expect(40);
		x = t; 
		Guard(out guard);
		Contract.Assume(guard == null || cce.Owner.None(guard)); 
		while (la.kind == 33 || la.kind == 41) {
			isFree = false; z = la/*lookahead token*/; 
			if (la.kind == 33) {
				Get();
				isFree = true;  
			}
			Expect(41);
			Expression(out e);
			if (isFree) {
			 invariants.Add(new AssumeCmd(z, e));
			} else {
			  invariants.Add(new AssertCmd(z, e));
			}
			
			Expect(7);
		}
		Expect(25);
		StmtList(out body);
		wcmd = new WhileCmd(x, guard, invariants, body); 
	}

	void BreakCmd(out BreakCmd/*!*/ bcmd) {
		Contract.Ensures(Contract.ValueAtReturn(out bcmd) != null); IToken/*!*/ x;  IToken/*!*/ y;
		string breakLabel = null;
		
		Expect(43);
		x = t; 
		if (la.kind == 1) {
			Ident(out y);
			breakLabel = y.val; 
		}
		Expect(7);
		bcmd = new BreakCmd(x, breakLabel); 
	}

	void Guard(out Expr e) {
		Expr/*!*/ ee;  e = null; 
		Expect(8);
		if (la.kind == 42) {
			Get();
			e = null; 
		} else if (StartOf(7)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(101);
		Expect(9);
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
		if (la.kind == 10) {
			Get();
			c = null;  label = x; 
		} else if (la.kind == 11 || la.kind == 15 || la.kind == 47) {
			lhss = new List<AssignLhs/*!*/>(); 
			lhs = new SimpleAssignLhs(id, new IdentifierExpr(id, id.val)); 
			while (la.kind == 15) {
				MapAssignIndex(out y, out indexes);
				lhs = new MapAssignLhs(y, lhs, indexes); 
			}
			lhss.Add(lhs); 
			while (la.kind == 11) {
				Get();
				Ident(out id);
				lhs = new SimpleAssignLhs(id, new IdentifierExpr(id, id.val)); 
				while (la.kind == 15) {
					MapAssignIndex(out y, out indexes);
					lhs = new MapAssignLhs(y, lhs, indexes); 
				}
				lhss.Add(lhs); 
			}
			Expect(47);
			x = t; /* use location of := */ 
			Expression(out e0);
			rhss = new List<Expr/*!*/> ();
			rhss.Add(e0); 
			while (la.kind == 11) {
				Get();
				Expression(out e0);
				rhss.Add(e0); 
			}
			Expect(7);
			c = new AssignCmd(x, lhss, rhss); 
		} else SynErr(102);
	}

	void CallCmd(out Cmd/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x; IToken/*!*/ first; IToken p;
		List<IdentifierExpr>/*!*/ ids = new List<IdentifierExpr>();
		List<Expr>/*!*/ es = new List<Expr>();
		QKeyValue kv = null;
		Expr en;  List<Expr> args;
		c = dummyCmd;
		
		Expect(48);
		x = t; 
		while (la.kind == 25) {
			Attribute(ref kv);
		}
		if (la.kind == 1) {
			Ident(out first);
			if (la.kind == 8) {
				Get();
				if (StartOf(8)) {
					CallForallArg(out en);
					es.Add(en); 
					while (la.kind == 11) {
						Get();
						CallForallArg(out en);
						es.Add(en); 
					}
				}
				Expect(9);
				c = new CallCmd(x, first.val, es, ids, kv); 
			} else if (la.kind == 11 || la.kind == 47) {
				ids.Add(new IdentifierExpr(first, first.val)); 
				if (la.kind == 11) {
					Get();
					CallOutIdent(out p);
					if (p==null) {
					  ids.Add(null);
					} else {
					   ids.Add(new IdentifierExpr(p, p.val));
					}
					
					while (la.kind == 11) {
						Get();
						CallOutIdent(out p);
						if (p==null) {
						  ids.Add(null);
						} else {
						   ids.Add(new IdentifierExpr(p, p.val));
						}
						
					}
				}
				Expect(47);
				Ident(out first);
				Expect(8);
				if (StartOf(8)) {
					CallForallArg(out en);
					es.Add(en); 
					while (la.kind == 11) {
						Get();
						CallForallArg(out en);
						es.Add(en); 
					}
				}
				Expect(9);
				c = new CallCmd(x, first.val, es, ids, kv); 
			} else SynErr(103);
		} else if (la.kind == 49) {
			Get();
			Ident(out first);
			Expect(8);
			args = new List<Expr>(); 
			if (StartOf(8)) {
				CallForallArg(out en);
				args.Add(en); 
				while (la.kind == 11) {
					Get();
					CallForallArg(out en);
					args.Add(en); 
				}
			}
			Expect(9);
			c = new CallForallCmd(x, first.val, args, kv); 
		} else if (la.kind == 42) {
			Get();
			ids.Add(null); 
			if (la.kind == 11) {
				Get();
				CallOutIdent(out p);
				if (p==null) {
				  ids.Add(null);
				} else {
				   ids.Add(new IdentifierExpr(p, p.val));
				}
				
				while (la.kind == 11) {
					Get();
					CallOutIdent(out p);
					if (p==null) {
					  ids.Add(null);
					} else {
					   ids.Add(new IdentifierExpr(p, p.val));
					}
					
				}
			}
			Expect(47);
			Ident(out first);
			Expect(8);
			if (StartOf(8)) {
				CallForallArg(out en);
				es.Add(en); 
				while (la.kind == 11) {
					Get();
					CallForallArg(out en);
					es.Add(en); 
				}
			}
			Expect(9);
			c = new CallCmd(x, first.val, es, ids, kv); 
		} else SynErr(104);
	}

	void MapAssignIndex(out IToken/*!*/ x, out List<Expr/*!*/>/*!*/ indexes) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out indexes))); indexes = new List<Expr/*!*/> ();
		Expr/*!*/ e;
		
		Expect(15);
		x = t; 
		if (StartOf(7)) {
			Expression(out e);
			indexes.Add(e); 
			while (la.kind == 11) {
				Get();
				Expression(out e);
				indexes.Add(e); 
			}
		}
		Expect(16);
	}

	void CallForallArg(out Expr exprOptional) {
		exprOptional = null;
		Expr/*!*/ e;
		
		if (la.kind == 42) {
			Get();
		} else if (StartOf(7)) {
			Expression(out e);
			exprOptional = e; 
		} else SynErr(105);
	}

	void CallOutIdent(out IToken id) {
		id = null;
		IToken/*!*/ p;
		
		if (la.kind == 42) {
			Get();
		} else if (la.kind == 1) {
			Ident(out p);
			id = p; 
		} else SynErr(106);
	}

	void Expressions(out ExprSeq/*!*/ es) {
		Contract.Ensures(Contract.ValueAtReturn(out es) != null); Expr/*!*/ e; es = new ExprSeq(); 
		Expression(out e);
		es.Add(e); 
		while (la.kind == 11) {
			Get();
			Expression(out e);
			es.Add(e); 
		}
	}

	void ImpliesExpression(bool noExplies, out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		LogicalExpression(out e0);
		if (StartOf(9)) {
			if (la.kind == 52 || la.kind == 53) {
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
				while (la.kind == 54 || la.kind == 55) {
					ExpliesOp();
					x = t; 
					LogicalExpression(out e1);
					e0 = Expr.Binary(x, BinaryOperator.Opcode.Imp, e1, e0); 
				}
			}
		}
	}

	void EquivOp() {
		if (la.kind == 50) {
			Get();
		} else if (la.kind == 51) {
			Get();
		} else SynErr(107);
	}

	void LogicalExpression(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		RelationalExpression(out e0);
		if (StartOf(10)) {
			if (la.kind == 56 || la.kind == 57) {
				AndOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = Expr.Binary(x, BinaryOperator.Opcode.And, e0, e1); 
				while (la.kind == 56 || la.kind == 57) {
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
				while (la.kind == 58 || la.kind == 59) {
					OrOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = Expr.Binary(x, BinaryOperator.Opcode.Or, e0, e1); 
				}
			}
		}
	}

	void ImpliesOp() {
		if (la.kind == 52) {
			Get();
		} else if (la.kind == 53) {
			Get();
		} else SynErr(108);
	}

	void ExpliesOp() {
		if (la.kind == 54) {
			Get();
		} else if (la.kind == 55) {
			Get();
		} else SynErr(109);
	}

	void RelationalExpression(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; BinaryOperator.Opcode op; 
		BvTerm(out e0);
		if (StartOf(11)) {
			RelOp(out x, out op);
			BvTerm(out e1);
			e0 = Expr.Binary(x, op, e0, e1); 
		}
	}

	void AndOp() {
		if (la.kind == 56) {
			Get();
		} else if (la.kind == 57) {
			Get();
		} else SynErr(110);
	}

	void OrOp() {
		if (la.kind == 58) {
			Get();
		} else if (la.kind == 59) {
			Get();
		} else SynErr(111);
	}

	void BvTerm(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; 
		Term(out e0);
		while (la.kind == 68) {
			Get();
			x = t; 
			Term(out e1);
			e0 = new BvConcatExpr(x, e0, e1); 
		}
	}

	void RelOp(out IToken/*!*/ x, out BinaryOperator.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken; op=BinaryOperator.Opcode.Add/*(dummy)*/; 
		switch (la.kind) {
		case 60: {
			Get();
			x = t; op=BinaryOperator.Opcode.Eq; 
			break;
		}
		case 17: {
			Get();
			x = t; op=BinaryOperator.Opcode.Lt; 
			break;
		}
		case 18: {
			Get();
			x = t; op=BinaryOperator.Opcode.Gt; 
			break;
		}
		case 61: {
			Get();
			x = t; op=BinaryOperator.Opcode.Le; 
			break;
		}
		case 62: {
			Get();
			x = t; op=BinaryOperator.Opcode.Ge; 
			break;
		}
		case 63: {
			Get();
			x = t; op=BinaryOperator.Opcode.Neq; 
			break;
		}
		case 64: {
			Get();
			x = t; op=BinaryOperator.Opcode.Subtype; 
			break;
		}
		case 65: {
			Get();
			x = t; op=BinaryOperator.Opcode.Neq; 
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
		default: SynErr(112); break;
		}
	}

	void Term(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; BinaryOperator.Opcode op; 
		Factor(out e0);
		while (la.kind == 69 || la.kind == 70) {
			AddOp(out x, out op);
			Factor(out e1);
			e0 = Expr.Binary(x, op, e0, e1); 
		}
	}

	void Factor(out Expr/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x; Expr/*!*/ e1; BinaryOperator.Opcode op; 
		UnaryExpression(out e0);
		while (la.kind == 42 || la.kind == 71 || la.kind == 72) {
			MulOp(out x, out op);
			UnaryExpression(out e1);
			e0 = Expr.Binary(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken/*!*/ x, out BinaryOperator.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken; op=BinaryOperator.Opcode.Add/*(dummy)*/; 
		if (la.kind == 69) {
			Get();
			x = t; op=BinaryOperator.Opcode.Add; 
		} else if (la.kind == 70) {
			Get();
			x = t; op=BinaryOperator.Opcode.Sub; 
		} else SynErr(113);
	}

	void UnaryExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;
		e = dummyExpr;
		
		if (la.kind == 70) {
			Get();
			x = t; 
			UnaryExpression(out e);
			e = Expr.Binary(x, BinaryOperator.Opcode.Sub, new LiteralExpr(x, BigNum.ZERO), e); 
		} else if (la.kind == 73 || la.kind == 74) {
			NegOp();
			x = t; 
			UnaryExpression(out e);
			e = Expr.Unary(x, UnaryOperator.Opcode.Not, e); 
		} else if (StartOf(12)) {
			CoercionExpression(out e);
		} else SynErr(114);
	}

	void MulOp(out IToken/*!*/ x, out BinaryOperator.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken; op=BinaryOperator.Opcode.Add/*(dummy)*/; 
		if (la.kind == 42) {
			Get();
			x = t; op=BinaryOperator.Opcode.Mul; 
		} else if (la.kind == 71) {
			Get();
			x = t; op=BinaryOperator.Opcode.Div; 
		} else if (la.kind == 72) {
			Get();
			x = t; op=BinaryOperator.Opcode.Mod; 
		} else SynErr(115);
	}

	void NegOp() {
		if (la.kind == 73) {
			Get();
		} else if (la.kind == 74) {
			Get();
		} else SynErr(116);
	}

	void CoercionExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;
		Type/*!*/ coercedTo;
		BigNum bn;
		
		ArrayExpression(out e);
		while (la.kind == 10) {
			Get();
			x = t; 
			if (StartOf(2)) {
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
				
			} else SynErr(117);
		}
	}

	void ArrayExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;
		Expr/*!*/ index0 = dummyExpr; Expr/*!*/ e1;
		bool store; bool bvExtract;
		ExprSeq/*!*/ allArgs = dummyExprSeq;
		
		AtomExpression(out e);
		while (la.kind == 15) {
			Get();
			x = t; allArgs = new ExprSeq ();
			allArgs.Add(e);
			store = false; bvExtract = false; 
			if (StartOf(13)) {
				if (StartOf(7)) {
					Expression(out index0);
					if (index0 is BvBounds)
					 bvExtract = true;
					else
					  allArgs.Add(index0);
					
					while (la.kind == 11) {
						Get();
						Expression(out e1);
						if (bvExtract || e1 is BvBounds)
						 this.SemErr("bitvectors only have one dimension");
						allArgs.Add(e1);
						
					}
					if (la.kind == 47) {
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
			Expect(16);
			if (store)
			 e = new NAryExpr(x, new MapStore(x, allArgs.Length - 2), allArgs);
			else if (bvExtract)
			  e = new BvExtractExpr(x, e,
			                        ((BvBounds)index0).Upper.ToIntSafe,
			                        ((BvBounds)index0).Lower.ToIntSafe);
			else
			  e = new NAryExpr(x, new MapSelect(x, allArgs.Length - 1), allArgs); 
			
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
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x; int n; BigNum bn;
		ExprSeq/*!*/ es;  VariableSeq/*!*/ ds;  Trigger trig;
		TypeVariableSeq/*!*/ typeParams;
		IdentifierExpr/*!*/ id;
		QKeyValue kv;
		e = dummyExpr;
		VariableSeq/*!*/ locals;
		List<Block/*!*/>/*!*/ blocks;
		
		switch (la.kind) {
		case 75: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 76: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 3: {
			Nat(out bn);
			e = new LiteralExpr(t, bn); 
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
			if (la.kind == 8) {
				Get();
				if (StartOf(7)) {
					Expressions(out es);
					e = new NAryExpr(x, new FunctionCall(id), es); 
				} else if (la.kind == 9) {
					e = new NAryExpr(x, new FunctionCall(id), new ExprSeq()); 
				} else SynErr(118);
				Expect(9);
			}
			break;
		}
		case 77: {
			Get();
			x = t; 
			Expect(8);
			Expression(out e);
			Expect(9);
			e = new OldExpr(x, e); 
			break;
		}
		case 8: {
			Get();
			if (StartOf(7)) {
				Expression(out e);
				if (e is BvBounds)
				 this.SemErr("parentheses around bitvector bounds " +
				        "are not allowed"); 
			} else if (la.kind == 49 || la.kind == 81) {
				Forall();
				x = t; 
				QuantifierBody(x, out typeParams, out ds, out kv, out trig, out e);
				if (typeParams.Length + ds.Length > 0)
				 e = new ForallExpr(x, typeParams, ds, kv, trig, e); 
			} else if (la.kind == 82 || la.kind == 83) {
				Exists();
				x = t; 
				QuantifierBody(x, out typeParams, out ds, out kv, out trig, out e);
				if (typeParams.Length + ds.Length > 0)
				 e = new ExistsExpr(x, typeParams, ds, kv, trig, e); 
			} else if (la.kind == 84 || la.kind == 85) {
				Lambda();
				x = t; 
				QuantifierBody(x, out typeParams, out ds, out kv, out trig, out e);
				if (trig != null)
				 SemErr("triggers not allowed in lambda expressions");
				if (typeParams.Length + ds.Length > 0)
				  e = new LambdaExpr(x, typeParams, ds, kv, e); 
			} else SynErr(119);
			Expect(9);
			break;
		}
		case 38: {
			IfThenElseExpression(out e);
			break;
		}
		case 78: {
			CodeExpression(out locals, out blocks);
			e = new CodeExpr(locals, blocks); 
			break;
		}
		default: SynErr(120); break;
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
		if (la.kind == 49) {
			Get();
		} else if (la.kind == 81) {
			Get();
		} else SynErr(121);
	}

	void QuantifierBody(IToken/*!*/ q, out TypeVariableSeq/*!*/ typeParams, out VariableSeq/*!*/ ds,
out QKeyValue kv, out Trigger trig, out Expr/*!*/ body) {
		Contract.Requires(q != null); Contract.Ensures(Contract.ValueAtReturn(out typeParams) != null); Contract.Ensures(Contract.ValueAtReturn(out ds) != null); Contract.Ensures(Contract.ValueAtReturn(out body) != null);
		trig = null; typeParams = new TypeVariableSeq ();
		     IToken/*!*/ tok;
		     kv = null;
		     ds = new VariableSeq ();
		  
		if (la.kind == 17) {
			TypeParams(out tok, out typeParams);
			if (la.kind == 1) {
				BoundVars(q, out ds);
			}
		} else if (la.kind == 1) {
			BoundVars(q, out ds);
		} else SynErr(122);
		QSep();
		while (la.kind == 25) {
			AttributeOrTrigger(ref kv, ref trig);
		}
		Expression(out body);
	}

	void Exists() {
		if (la.kind == 82) {
			Get();
		} else if (la.kind == 83) {
			Get();
		} else SynErr(123);
	}

	void Lambda() {
		if (la.kind == 84) {
			Get();
		} else if (la.kind == 85) {
			Get();
		} else SynErr(124);
	}

	void IfThenElseExpression(out Expr/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ tok;
		Expr/*!*/ e0, e1, e2; 
		e = dummyExpr; 
		Expect(38);
		tok = t; 
		Expression(out e0);
		Expect(80);
		Expression(out e1);
		Expect(39);
		Expression(out e2);
		e = new NAryExpr(tok, new IfThenElse(tok), new ExprSeq(e0, e1, e2)); 
	}

	void CodeExpression(out VariableSeq/*!*/ locals, out List<Block/*!*/>/*!*/ blocks) {
		Contract.Ensures(Contract.ValueAtReturn(out locals) != null); Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out blocks))); locals = new VariableSeq(); Block/*!*/ b;
		blocks = new List<Block/*!*/>();
		
		Expect(78);
		while (la.kind == 6) {
			LocalVars(locals);
		}
		SpecBlock(out b);
		blocks.Add(b); 
		while (la.kind == 1) {
			SpecBlock(out b);
			blocks.Add(b); 
		}
		Expect(79);
	}

	void SpecBlock(out Block/*!*/ b) {
		Contract.Ensures(Contract.ValueAtReturn(out b) != null); IToken/*!*/ x; IToken/*!*/ y;
		Cmd c;  IToken label;
		CmdSeq cs = new CmdSeq();
		TokenSeq/*!*/ xs;
		StringSeq ss = new StringSeq();
		b = dummyBlock;
		Expr/*!*/ e;
		
		Ident(out x);
		Expect(10);
		while (StartOf(6)) {
			LabelOrCmd(out c, out label);
			if (c != null) {
			 Contract.Assert(label == null);
			 cs.Add(c);
			} else {
			  Contract.Assert(label != null);
			  SemErr("SpecBlock's can only have one label");
			}
			
		}
		if (la.kind == 36) {
			Get();
			y = t; 
			Idents(out xs);
			foreach(IToken/*!*/ s in xs){
			 Contract.Assert(s != null);
			 ss.Add(s.val); }
			b = new Block(x,x.val,cs,new GotoCmd(y,ss));
			
		} else if (la.kind == 37) {
			Get();
			Expression(out e);
			b = new Block(x,x.val,cs,new ReturnExprCmd(t,e)); 
		} else SynErr(125);
		Expect(7);
	}

	void AttributeOrTrigger(ref QKeyValue kv, ref Trigger trig) {
		IToken/*!*/ tok;  Expr/*!*/ e;  ExprSeq/*!*/ es;
		string key;
		List<object/*!*/> parameters;  object/*!*/ param;
		
		Expect(25);
		tok = t; 
		if (la.kind == 10) {
			Get();
			Expect(1);
			key = t.val;  parameters = new List<object/*!*/>(); 
			if (StartOf(14)) {
				AttributeParameter(out param);
				parameters.Add(param); 
				while (la.kind == 11) {
					Get();
					AttributeParameter(out param);
					parameters.Add(param); 
				}
			}
			if (key == "nopats") {
			 if (parameters.Count == 1 && parameters[0] is Expr) {
			   e = (Expr)parameters[0];
			   if(trig==null){
			     trig = new Trigger(tok, false, new ExprSeq(e), null);
			   } else {
			     trig.AddLast(new Trigger(tok, false, new ExprSeq(e), null));
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
			
		} else if (StartOf(7)) {
			Expression(out e);
			es = new ExprSeq(e); 
			while (la.kind == 11) {
				Get();
				Expression(out e);
				es.Add(e); 
			}
			if (trig==null) {
			 trig = new Trigger(tok, true, es, null);
			} else {
			  trig.AddLast(new Trigger(tok, true, es, null));
			}
			
		} else SynErr(126);
		Expect(26);
	}

	void AttributeParameter(out object/*!*/ o) {
		Contract.Ensures(Contract.ValueAtReturn(out o) != null);
		o = "error";
		Expr/*!*/ e;
		
		if (la.kind == 4) {
			Get();
			o = t.val.Substring(1, t.val.Length-2); 
		} else if (StartOf(7)) {
			Expression(out e);
			o = e; 
		} else SynErr(127);
	}

	void QSep() {
		if (la.kind == 86) {
			Get();
		} else if (la.kind == 87) {
			Get();
		} else SynErr(128);
	}



	public void Parse() {
		la = new Token();
		la.val = "";
		Get();
		BoogiePL();

		Expect(0);
	}

	static readonly bool[,]/*!*/ set = {
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,T, x,x,x,T, T,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, T,x,x,x, x,T,T,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,x, T,x,x,T, T,T,T,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,T, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x}

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
			case 5: s = "float expected"; break;
			case 6: s = "\"var\" expected"; break;
			case 7: s = "\";\" expected"; break;
			case 8: s = "\"(\" expected"; break;
			case 9: s = "\")\" expected"; break;
			case 10: s = "\":\" expected"; break;
			case 11: s = "\",\" expected"; break;
			case 12: s = "\"where\" expected"; break;
			case 13: s = "\"int\" expected"; break;
			case 14: s = "\"bool\" expected"; break;
			case 15: s = "\"[\" expected"; break;
			case 16: s = "\"]\" expected"; break;
			case 17: s = "\"<\" expected"; break;
			case 18: s = "\">\" expected"; break;
			case 19: s = "\"const\" expected"; break;
			case 20: s = "\"unique\" expected"; break;
			case 21: s = "\"extends\" expected"; break;
			case 22: s = "\"complete\" expected"; break;
			case 23: s = "\"function\" expected"; break;
			case 24: s = "\"returns\" expected"; break;
			case 25: s = "\"{\" expected"; break;
			case 26: s = "\"}\" expected"; break;
			case 27: s = "\"axiom\" expected"; break;
			case 28: s = "\"type\" expected"; break;
			case 29: s = "\"=\" expected"; break;
			case 30: s = "\"procedure\" expected"; break;
			case 31: s = "\"implementation\" expected"; break;
			case 32: s = "\"modifies\" expected"; break;
			case 33: s = "\"free\" expected"; break;
			case 34: s = "\"requires\" expected"; break;
			case 35: s = "\"ensures\" expected"; break;
			case 36: s = "\"goto\" expected"; break;
			case 37: s = "\"return\" expected"; break;
			case 38: s = "\"if\" expected"; break;
			case 39: s = "\"else\" expected"; break;
			case 40: s = "\"while\" expected"; break;
			case 41: s = "\"invariant\" expected"; break;
			case 42: s = "\"*\" expected"; break;
			case 43: s = "\"break\" expected"; break;
			case 44: s = "\"assert\" expected"; break;
			case 45: s = "\"assume\" expected"; break;
			case 46: s = "\"havoc\" expected"; break;
			case 47: s = "\":=\" expected"; break;
			case 48: s = "\"call\" expected"; break;
			case 49: s = "\"forall\" expected"; break;
			case 50: s = "\"<==>\" expected"; break;
			case 51: s = "\"\\u21d4\" expected"; break;
			case 52: s = "\"==>\" expected"; break;
			case 53: s = "\"\\u21d2\" expected"; break;
			case 54: s = "\"<==\" expected"; break;
			case 55: s = "\"\\u21d0\" expected"; break;
			case 56: s = "\"&&\" expected"; break;
			case 57: s = "\"\\u2227\" expected"; break;
			case 58: s = "\"||\" expected"; break;
			case 59: s = "\"\\u2228\" expected"; break;
			case 60: s = "\"==\" expected"; break;
			case 61: s = "\"<=\" expected"; break;
			case 62: s = "\">=\" expected"; break;
			case 63: s = "\"!=\" expected"; break;
			case 64: s = "\"<:\" expected"; break;
			case 65: s = "\"\\u2260\" expected"; break;
			case 66: s = "\"\\u2264\" expected"; break;
			case 67: s = "\"\\u2265\" expected"; break;
			case 68: s = "\"++\" expected"; break;
			case 69: s = "\"+\" expected"; break;
			case 70: s = "\"-\" expected"; break;
			case 71: s = "\"/\" expected"; break;
			case 72: s = "\"%\" expected"; break;
			case 73: s = "\"!\" expected"; break;
			case 74: s = "\"\\u00ac\" expected"; break;
			case 75: s = "\"false\" expected"; break;
			case 76: s = "\"true\" expected"; break;
			case 77: s = "\"old\" expected"; break;
			case 78: s = "\"|{\" expected"; break;
			case 79: s = "\"}|\" expected"; break;
			case 80: s = "\"then\" expected"; break;
			case 81: s = "\"\\u2200\" expected"; break;
			case 82: s = "\"exists\" expected"; break;
			case 83: s = "\"\\u2203\" expected"; break;
			case 84: s = "\"lambda\" expected"; break;
			case 85: s = "\"\\u03bb\" expected"; break;
			case 86: s = "\"::\" expected"; break;
			case 87: s = "\"\\u2022\" expected"; break;
			case 88: s = "??? expected"; break;
			case 89: s = "invalid Function"; break;
			case 90: s = "invalid Function"; break;
			case 91: s = "invalid Procedure"; break;
			case 92: s = "invalid Type"; break;
			case 93: s = "invalid TypeAtom"; break;
			case 94: s = "invalid TypeArgs"; break;
			case 95: s = "invalid Spec"; break;
			case 96: s = "invalid SpecPrePost"; break;
			case 97: s = "invalid LabelOrCmd"; break;
			case 98: s = "invalid StructuredCmd"; break;
			case 99: s = "invalid TransferCmd"; break;
			case 100: s = "invalid IfCmd"; break;
			case 101: s = "invalid Guard"; break;
			case 102: s = "invalid LabelOrAssign"; break;
			case 103: s = "invalid CallCmd"; break;
			case 104: s = "invalid CallCmd"; break;
			case 105: s = "invalid CallForallArg"; break;
			case 106: s = "invalid CallOutIdent"; break;
			case 107: s = "invalid EquivOp"; break;
			case 108: s = "invalid ImpliesOp"; break;
			case 109: s = "invalid ExpliesOp"; break;
			case 110: s = "invalid AndOp"; break;
			case 111: s = "invalid OrOp"; break;
			case 112: s = "invalid RelOp"; break;
			case 113: s = "invalid AddOp"; break;
			case 114: s = "invalid UnaryExpression"; break;
			case 115: s = "invalid MulOp"; break;
			case 116: s = "invalid NegOp"; break;
			case 117: s = "invalid CoercionExpression"; break;
			case 118: s = "invalid AtomExpression"; break;
			case 119: s = "invalid AtomExpression"; break;
			case 120: s = "invalid AtomExpression"; break;
			case 121: s = "invalid Forall"; break;
			case 122: s = "invalid QuantifierBody"; break;
			case 123: s = "invalid Exists"; break;
			case 124: s = "invalid Lambda"; break;
			case 125: s = "invalid SpecBlock"; break;
			case 126: s = "invalid AttributeOrTrigger"; break;
			case 127: s = "invalid AttributeParameter"; break;
			case 128: s = "invalid QSep"; break;

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

	public virtual void Warning(string filename, int line, int col, string msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(warningMsgFormat, filename, line, col, msg);
	}
} // Errors


public class FatalError: Exception {
	public FatalError(string m): base(m) {}
}

}