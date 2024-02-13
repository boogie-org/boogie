using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Boogie.LeanAuto;

public class LeanGenerator : ReadOnlyVisitor
{
  private readonly TextWriter writer;
  private readonly VCGenOptions options;
  private readonly List<NamedDeclaration> globalVars = new();
  private readonly HashSet<string> usedNames = new();
  private bool usesMaps;
  private readonly List<string> mapAxiomNames =
    new(new[]
    {
      "SelectStoreSame1", "SelectStoreDistinct1",
      "SelectStoreSame2", "SelectStoreDistinct2"
    });
  private readonly List<string> userAxiomNames = new();
  private readonly Dictionary<Type, HashSet<string>> uniqueConsts = new();

  private const string AndString = "\u2227"; /* ∧ */
  private const string OrString = "\u2228"; /* ∨ */
  private const string NeqString = "\u2260"; /* ≠ */
  private const string ArrowString = "\u2192"; /* → */

  private LeanGenerator(VCGenOptions options, TextWriter writer)
  {
    this.options = options;
    this.writer = writer;
  }

  public static void EmitPassiveProgramAsLean(VCGenOptions options, Program p, TextWriter writer)
  {
    var generator = new LeanGenerator(options, writer);
    generator.EmitHeader();
    try {
      var allBlocks = p.Implementations.SelectMany(i => i.Blocks);
      var liveDeclarations =
        options.Prune
          ? Prune.GetLiveDeclarations(options, p, allBlocks.ToList()).ToList()
          : p.TopLevelDeclarations;

      generator.Line("-- Type constructors");
      // Always include all type constructors
      p.TopLevelDeclarations.OfType<TypeCtorDecl>().ForEach(tcd => generator.Visit(tcd));
      generator.NL();

      generator.Line("-- Type synonyms");
      liveDeclarations.OfType<TypeSynonymDecl>().ForEach(tcd => generator.Visit(tcd));
      generator.NL();

      generator.Line("-- Constants");
      liveDeclarations.OfType<Constant>().ForEach(c => generator.Visit(c));
      generator.NL();

      generator.Line("-- Unique const axioms");
      generator.EmitUniqueConstAxioms();
      generator.NL();

      generator.Line("-- Variables");
      liveDeclarations.OfType<GlobalVariable>().ForEach(gv => generator.Visit(gv));
      generator.NL();

      generator.Line("-- Functions");
      liveDeclarations.OfType<Function>().ForEach(f => generator.Visit(f));
      generator.NL();

      generator.Line("-- Axioms");
      liveDeclarations.OfType<Axiom>().ForEach(a => generator.Visit(a));
      generator.NL();

      generator.Line("-- Implementations");
      p.Implementations.ForEach(i => generator.Visit(i));
    } catch (LeanConversionException e) {
      Console.WriteLine($"Failed translation: {e.Msg}");
    }
  }

  private void AddUniqueConst(Type t, string name)
  {
    if (!uniqueConsts.ContainsKey(t)) {
      uniqueConsts[t] = new();
    }
    if (!uniqueConsts[t].Contains(name)) {
      uniqueConsts[t].Add(name);
    }
  }

  private void EmitUniqueConstAxioms()
  {
    int i = 0;
    foreach (var kv in uniqueConsts) {
      var axiomName = $"unique{i}";
      userAxiomNames.Add(axiomName);
      Text($"axiom {axiomName}: distinct ");
      List(kv.Value);
      NL();
      i++;
    }
  }

  private void EmitHeader()
  {
    var assembly = System.Reflection.Assembly.GetExecutingAssembly();
    var preludeStream = assembly.GetManifestResourceStream("Prelude.lean");
    if (preludeStream is null) {
      throw new LeanConversionException("Internal: failed to find Lean prelude in assembly.");
    }
    var header = new StreamReader(preludeStream).ReadToEnd();
    writer.WriteLine(header.ReplaceLineEndings());
  }

  private void Indent(int n = 1, string str = null)
  {
    for (var i = 0; i < n; i++) {
      Text("  ");
    }

    if (str is not null) {
      Text(str);
    }
  }

  private void IndentL(int n = 1, string str = null)
  {
    Indent(n, str);
    NL();
  }

  private void NL()
  {
    writer.WriteLine();
  }

  private void Text(string text)
  {
    writer.Write(text);
  }

  private void Line(string text)
  {
    writer.WriteLine(text);
  }

  private void List(IEnumerable<string> strings)
  {
    Text("[");
    Text(String.Join(", ", strings));
    Text("]");
  }

  public override Block VisitBlock(Block node)
  {
    var label = BlockName(node);
    IndentL(1, "@[simp]");
    IndentL(1, $"{label} :=");
    node.Cmds.ForEach(c => Visit(c));
    if (node.TransferCmd is ReturnCmd r) {
      VisitReturnCmd(r);
    }
    if (node.TransferCmd is GotoCmd g) {
      VisitGotoCmd(g);
    }
    NL();
    return node;
  }

  public override Cmd VisitAssertCmd(AssertCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    Line(" $");
    return node;
  }

  public override Cmd VisitAssumeCmd(AssumeCmd node)
  {
    Indent(2, "assume ");
    VisitExpr(node.Expr);
    Line(" $");
    return node;
  }

  public override GotoCmd VisitGotoCmd(GotoCmd node)
  {
    var gotoText = node.labelTargets.Select(l =>
      $"goto {BlockName(l)}").Aggregate((a, b) => $"{a} {AndString} {b}");
    Indent(2, gotoText);
    return node;
  }

  public override ReturnCmd VisitReturnCmd(ReturnCmd node)
  {
    Indent(2, "ret");
    return node;
  }

  public override Expr VisitIdentifierExpr(IdentifierExpr node)
  {
    var name = SanitizeNameForLean(node.Name);
    usedNames.Add(name);
    Text(name);
    return node;
  }

  public override Type VisitType(Type node)
  {
    return node switch
    {
      BasicType basicType => VisitBasicType(basicType),
      BvType bvType => VisitBvType(bvType),
      CtorType ctorType => VisitCtorType(ctorType),
      FloatType floatType => VisitFloatType(floatType),
      MapType mapType => VisitMapType(mapType),
      TypeProxy typeProxy => VisitTypeProxy(typeProxy),
      TypeSynonymAnnotation typeSynonymAnnotation => VisitTypeSynonymAnnotation(typeSynonymAnnotation),
      TypeVariable typeVariable => VisitTypeVariable(typeVariable),
      UnresolvedTypeIdentifier uti => VisitUnresolvedTypeIdentifier(uti),
      _ => throw new LeanConversionException("Unreachable type case.")
    };
  }

  public override Type VisitBasicType(BasicType node)
  {
    if (node.IsBool) {
      Text("Prop");
    } else if (node.IsInt) {
      Text("Int");
    } else if (node.IsReal) {
      Text("Real");
    } else if (node.IsRMode) {
      throw new LeanConversionException("Unsupported: RMode type");
    } else if (node.IsRegEx) {
      throw new LeanConversionException("Unsupported: RegEx type");
    } else if (node.IsMap) {
      var mapType = node.AsMap;
      VisitMapType(mapType);
    } else {
      throw new LeanConversionException($"Unsupported BasicType: {node}");
    }

    return node;
  }

  public override Expr VisitBvConcatExpr(BvConcatExpr node)
  {
    Visit(node.E0);
    Text(" ++ ");
    Visit(node.E1);
    return node;
  }

  public override Type VisitBvType(BvType node)
  {
    Text($"(BitVec {node.Bits})");
    return node;
  }

  public override Constant VisitConstant(Constant node)
  {
    var ti = node.TypedIdent;
    Text("variable ");
    Visit(ti);
    if (node.Unique) {
      AddUniqueConst(ti.Type, Name(node));
    }
    NL();
    globalVars.Add(node);
    return node;
  }

  public override CtorType VisitCtorType(CtorType node)
  {
    if (node.Arguments.Any()) {
      Text("(");
    }

    Text(Name(node.Decl));
    node.Arguments.ForEach(a =>
    {
      Text(" ");
      Visit(a);
    });
    if (node.Arguments.Any()) {
      Text(")");
    }
    return node;
  }

  public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
  {
    var kind = node switch
    {
      ForallExpr => "forall",
      ExistsExpr => "exists",
      _ => throw new LeanConversionException($"Unsupported quantifier type: {node.Kind}")
    };
    Text($"({kind}");
    foreach (var tv in node.TypeParameters) {
      Text($" ({Name(tv)} : Type)");
    }
    foreach (var x in node.Dummies) {
      Text(" ");
      VisitTypedIdent(x.TypedIdent);
    }
    Text(", ");
    Visit(node.Body);
    Text(")");

    return node;
  }

  public override TypedIdent VisitTypedIdent(TypedIdent node)
  {
    Text("(");
    var name = SanitizeNameForLean(node.Name);
    Text(name);
    Text(" : ");
    Visit(node.Type);
    Text(")");
    return node;
  }

  public override Expr VisitBvExtractExpr(BvExtractExpr node)
  {
    Text($"(BitVec.extractLsb {node.End - 1} {node.Start} ");
    Visit(node.Bitvector);
    Text(")");
    return node;
  }

  public override Expr VisitLambdaExpr(LambdaExpr node)
  {
    Text("(λ");
    node.Dummies.ForEach(x => Visit(x.TypedIdent));
    Text("=>");
    Visit(node.Body);
    Text(")");
    return node;
  }

  public override Expr VisitLetExpr(LetExpr node)
  {
    if (node.Dummies.Count > 1) {
      throw new LeanConversionException("Unsupported: LetExpr with more than one binder");
    }
    Text("(let");
    node.Dummies.ForEach(x => Visit(x.TypedIdent));
    Text(" := ");
    node.Rhss.ForEach(e => Visit(e));
    Text("; ");
    Visit(node.Body);
    Text(")");
    return node;
  }

  public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
  {
    Text("variable ");
    Visit(node.TypedIdent);
    NL();
    globalVars.Add(node);
    return node;
  }

  public override Expr VisitLiteralExpr(LiteralExpr node)
  {
    if(node.IsTrue) {
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      Text("true");
    } else if (node.IsFalse) {
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      Text("false");
    } else if (node.isBvConst) {
      var bvConst = node.asBvConst;
      Text("(");
      Text(bvConst.Value.ToString());
      Text($" : BitVec {bvConst.Bits}");
      Text(")");
    } else {
      Text(node.ToString()); // TODO: make sure this is right for all other literal types
    }
    return node;
  }

  public override Type VisitMapType(MapType node)
  {
    if (node.Arguments.Count > 2) {
      throw new LeanConversionException($"Unsupported: MapType with too many index types ({node})");
    }
    if (node.TypeParameters.Any()) {
      var args = node.TypeParameters.Select(Name);
      Text($"forall ({String.Join(" ", args)} : Type), ");
    }
    Text($"(SMTArray{node.Arguments.Count} ");
    node.Arguments.ForEach(a =>
    {
      Visit(a);
      Text(" ");
    });
    Visit(node.Result);
    Text(")");
    return node;
  }

  public override Expr VisitNAryExpr(NAryExpr node)
  {
    var fun = node.Fun;
    var args = node.Args;
    Text("(");
    if (fun is BinaryOperator op && args.Count == 2) {
      Visit(args[0]);
      Text($" {BinaryOpToLean(op.Op)} ");
      Visit(args[1]);
    } else if (fun is IfThenElse && args.Count == 3) {
      Text("if ");
      Visit(args[0]);
      Text(" then ");
      Visit(args[1]);
      Text(" else ");
      Visit(args[2]);
    } else if (fun is TypeCoercion typeCoercion && args.Count == 1) {
      if (!args[0].Type.Equals(typeCoercion.Type)) {
        // TODO: might need to actually call a coercion function
        Console.WriteLine($"Coerce: {args[0].Type} -> {typeCoercion.Type}");
      }
      Text("(");
      Visit(args[0]);
      Text(" : ");
      Visit(typeCoercion.Type);
      Text(")");
    } else if (fun is FieldAccess fieldAccess) {
      throw new LeanConversionException("Unsupported: field access (since the semantics are complex)");
    } else {
      VisitIAppliable(fun);
      foreach (var arg in args) {
        Text(" ");
        Visit(arg);
      }
    }
    Text(")");

    return node;
  }

  private void VisitIAppliable(IAppliable fun)
  {
    switch (fun) {
      case MapSelect:
        usesMaps = true;
        Text($"select{fun.ArgumentCount - 1}");
        break;
      case MapStore:
        usesMaps = true;
        Text($"store{fun.ArgumentCount - 2}");
        break;
      case BinaryOperator op:
        Text(BinaryOpToLean(op.Op));
        break;
      case UnaryOperator op:
        Text(UnaryOpToLean(op.Op));
        break;
      case FunctionCall fc:
        Text(Name(fc.Func));
        break;
      case IsConstructor isConstructor:
        throw new LeanConversionException($"Unsupported: Constructor: {isConstructor.ConstructorName}");
        // Discriminator functions not declared yet
        //Text($"is_{SanitizeNameForLean(isConstructor.ConstructorName)}");
        //break;
      case ArithmeticCoercion arithmeticCoercion:
        var func = arithmeticCoercion.Coercion switch
        {
          ArithmeticCoercion.CoercionType.ToInt => "realToInt",
          ArithmeticCoercion.CoercionType.ToReal => "intToReal",
          _ => throw new LeanConversionException($"Internal: unknown arithmetic coercion: {arithmeticCoercion.Coercion}")
        };
        Text(func);
        break;
      default:
        throw new LeanConversionException($"Unsupported: IAppliable: {fun}");
    }
  }

  public override Expr VisitOldExpr(OldExpr node)
  {
    throw new LeanConversionException("Unsupported: OldExpr");
  }

  public override Type VisitFloatType(FloatType node)
  {
    throw new LeanConversionException("Unsupported: FloatType");
  }

  public override Requires VisitRequires(Requires requires)
  {
    return requires; // Already inlined
  }

  public override Ensures VisitEnsures(Ensures ensures)
  {
    return ensures; // Already inlined
  }

  public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
  {
    throw new LeanConversionException($"Unsupported: DeclWithFormals ({node}).");
  }

  public override Type VisitBvTypeProxy(BvTypeProxy node)
  {
    throw new LeanConversionException($"Unsupported: BvTypeProxy ({node}).");
  }

  public override Expr VisitCodeExpr(CodeExpr node)
  {
    throw new LeanConversionException($"Unsupported: CodeExpr ({node}).");
  }

  public override Cmd VisitCommentCmd(CommentCmd node)
  {
    // Comments are safe to ignore
    return node;
  }

  public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
  {
    return requiresSeq; // Already inlined
  }

  public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
  {
    return ensuresSeq; // Already inlined
  }

  public override Type VisitMapTypeProxy(MapTypeProxy node)
  {
    throw new LeanConversionException($"Unsupported: maptypeproxy: {node}");
  }

  public override QKeyValue VisitQKeyValue(QKeyValue node)
  {
    // Implement this if we want to visit attributes? Or maybe extract them more directly.
    return node;
  }

  public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
  {
    // TODO: wrap in `mutual ... end` when necessary
    var name = Name(node);
    if (node is DatatypeTypeCtorDecl dt) {
      Line($"inductive {name} where");
      foreach (var ctor in dt.Constructors) {
        Indent(1, $"| {Name(ctor)} : ");
        ctor.InParams.ForEach(p =>
        {
          Visit(p.TypedIdent.Type);
          Text(" → ");
        });
        Line($" {name}");
      }
    } else {
      var tyStr = String.Join(" → ", Enumerable.Repeat("Type", node.Arity + 1).ToList());
      Line($"axiom {name} : {tyStr}");

      if(node.Arity == 0) {
        Line($"instance {name}BEq : BEq {name} := by sorry");
      }
    }
    return node;
  }

  public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
  {
    return VisitType(node.ExpandedType);
  }

  public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
  {
    var name = Name(node);
    Text($"def {name}");
    node.TypeParameters.ForEach(tp => Text($" ({Name(tp)} : Type)"));
    Text(" := ");
    Visit(node.Body);
    NL();
    return node;
  }

  public override Type VisitTypeProxy(TypeProxy node)
  {
    var p = node.ProxyFor;
    if (p is null) {
      Text(Name(node));
    } else {
      VisitType(p);
    }
    return node;
  }

  public override Type VisitTypeVariable(TypeVariable node)
  {
    Text(Name(node));
    return node;
  }

  public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    Line(" $");
    return node;
  }

  public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    Line(" $");
    return node;
  }

  public override ActionDeclRef VisitActionDeclRef(ActionDeclRef node)
  {
    throw new LeanConversionException($"Unsupported: ActionDeclRef ({node}).");
  }

  public override ElimDecl VisitElimDecl(ElimDecl node)
  {
    throw new LeanConversionException($"Unsupported: ElimDecl ({node}).");
  }

  public override List<ElimDecl> VisitElimDeclSeq(List<ElimDecl> node)
  {
    throw new LeanConversionException($"Unsupported: List<ElimDecl> ({node}).");
  }

  public override Axiom VisitAxiom(Axiom node)
  {
    // This will take two more steps:
    // * A named lemma with a definition of `by sorry` (using a `name` attribute?) (or `id`, so it's also useful for coverage?)
    // * A named lemma that's defined by a call to a previously-defined proof of the same thing
    int n = 0;
    var name = $"ax_l{node.tok.line}c{node.tok.col}";
    while (userAxiomNames.Contains(name)) {
      name = $"ax_l{node.tok.line}c{node.tok.col}_{n}";
      n += 1;
    }
    Text($"axiom {name}: ");
    VisitExpr(node.Expr);
    NL();
    userAxiomNames.Add(name);
    return node;
  }

  public override Function VisitFunction(Function node)
  {
    // In the long run, this should define functions when possible.
    Text($"axiom {Name(node)} : ");
    node.TypeParameters.ForEach(x =>
    {
      Text($"{{{Name(x)} : Type}}");
      Text($" {ArrowString} ");
    });
    node.InParams.ForEach(x =>
    {
      Visit(x.TypedIdent.Type);
      Text($" {ArrowString} ");
    });
    if (node.OutParams.Count == 1) {
      Visit(node.OutParams[0].TypedIdent.Type);
    } else {
      Text("(");
      node.OutParams.ForEach(x =>
      {
        Visit(x.TypedIdent.Type); Text(", ");
      });
      Text(")");
    }

    NL();
    // Note: definition axioms will be emitted later
    // node.DefinitionAxioms.ForEach(ax => VisitAxiom(ax));
    return node;
  }

  private string BinaryOpToLean(BinaryOperator.Opcode op)
  {
    return op switch
    {
      BinaryOperator.Opcode.Add => "+",
      BinaryOperator.Opcode.Sub => "-",
      BinaryOperator.Opcode.Mul => "*",
      BinaryOperator.Opcode.Div => "/",
      BinaryOperator.Opcode.Mod => "%",
      BinaryOperator.Opcode.Lt => "<",
      BinaryOperator.Opcode.Gt => ">",
      BinaryOperator.Opcode.Le => "<=",
      BinaryOperator.Opcode.Ge => ">=",
      BinaryOperator.Opcode.Eq => "=",
      BinaryOperator.Opcode.Neq => NeqString,
      BinaryOperator.Opcode.And => AndString,
      BinaryOperator.Opcode.Or => OrString,
      BinaryOperator.Opcode.Iff => "=",
      BinaryOperator.Opcode.Imp => ArrowString,
      BinaryOperator.Opcode.Pow => "^",
      BinaryOperator.Opcode.RealDiv => "/",
      BinaryOperator.Opcode.FloatDiv => "/",
      _ => throw new LeanConversionException($"unsupported binary operator: {op.ToString()}")
    };
  }

  private string UnaryOpToLean(UnaryOperator.Opcode op)
  {
    return op switch
    {
      UnaryOperator.Opcode.Not => "Not",
      UnaryOperator.Opcode.Neg => "-",
      _ => throw new LeanConversionException($"unsupported unary operator: {op.ToString()}")
    };
  }

  private string SanitizeNameForLean(string name)
  {
    return "_boogie_" + name
      .Replace('@', '_')
      .Replace('.', '_')
      .Replace('#', '_')
      .Replace("$", "_dollar_");
  }

  private string Name(NamedDeclaration d)
  {
    return SanitizeNameForLean(d.Name);
  }

  private string Name(TypeVariable tv)
  {
    return SanitizeNameForLean(tv.Name);
  }

  private string Name(TypeProxy tp)
  {
    return SanitizeNameForLean(tp.Name);
  }

  private string BlockName(Block b)
  {
    return "β_" + SanitizeNameForLean(b.Label);
  }

  public override Procedure VisitProcedure(Procedure node)
  {
    return node;
  }

  private void WriteParams(Implementation node)
  {
    node.InParams.ForEach(x =>
    {
      Indent();
      VisitTypedIdent(x.TypedIdent);
      NL();
    });
    node.OutParams.ForEach(x =>
    {
      Indent();
      VisitTypedIdent(x.TypedIdent);
      NL();
    });
    node.LocVars.ForEach(x =>
    {
      Indent();
      VisitTypedIdent(x.TypedIdent);
      NL();
    });
  }

  public override Implementation VisitImplementation(Implementation node)
  {
    var name = Name(node);
    var entryLabel = BlockName(node.Blocks[0]);

    usedNames.Clear(); // Skip any globals used only by axioms, etc.
    NL();
    Line($"namespace impl_{name}");
    NL();

    Line("@[simp]");
    Line($"def {name}");
    WriteParams(node);
    IndentL(1, $": Prop := {entryLabel}");
    IndentL(1, "where");
    node.Blocks.ForEach(b => VisitBlock(b));
    NL();
    Line($"theorem {name}_correct");
    WriteParams(node);
    var paramNames =
      globalVars.Select(Name).Where(x => usedNames.Contains(x))
        .Concat(node.InParams.Select(Name))
        .Concat(node.OutParams.Select(Name))
        .Concat(node.LocVars.Select(Name));
    var paramString = String.Join(' ', paramNames);
    Indent(1, $": {name} {paramString} := by"); NL();
    IndentL(2, "try simp"); // Uses `try` because it may make no progress
    IndentL(2, "try auto"); // Uses `try` because there may be no goals remaining
    var axiomNames = usesMaps ? mapAxiomNames.Concat(userAxiomNames) : userAxiomNames;
    Indent(3); List(axiomNames); NL();
    IndentL(3, "u[]");
    NL();
    Line($"end impl_{name}");

    usesMaps = false; // Skip map axioms in the next implementation if it doesn't need them
    usedNames.Clear(); // Skip any globals not used by the next implementation

    return node;
  }

  /* ==== Nodes that should never be visited ==== */

  public override Program VisitProgram(Program node)
  {
    throw new LeanConversionException($"Internal: Program should never be directly visited ({node.tok}).");
  }

  public override Declaration VisitDeclaration(Declaration node)
  {
    throw new LeanConversionException($"Internal: Declaration should never be directly visited ({node.tok}).");
  }

  public override List<Declaration> VisitDeclarationList(List<Declaration> declarationList)
  {
    throw new LeanConversionException($"Internal: List<Declaration> should never be directly visited ({declarationList}).");
  }

  public override List<Block> VisitBlockSeq(List<Block> blockSeq)
  {
    throw new LeanConversionException($"Internal: List<Block> should never be directly visited ({blockSeq}).");
  }

  public override List<Block> VisitBlockList(List<Block> blocks)
  {
    throw new LeanConversionException($"Internal: List<Block> should never be directly visited ({blocks}).");
  }

  public override Trigger VisitTrigger(Trigger node)
  {
    throw new LeanConversionException($"Internal: Trigger should never be directly visited ({node.tok}).");
  }

  public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
  {
    throw new LeanConversionException($"Internal: List<Expr> should never be directly visited ({exprSeq}).");
  }

  public override BoundVariable VisitBoundVariable(BoundVariable node)
  {
    throw new LeanConversionException($"Internal: BoundVariable should never be directly visited ({node.tok}).");
  }

  public override Formal VisitFormal(Formal node)
  {
    throw new LeanConversionException($"Internal: Formal should never be directly visited ({node.tok}).");
  }

  public override LocalVariable VisitLocalVariable(LocalVariable node)
  {
    throw new LeanConversionException($"Internal error: LocalVariable should never be directly visited ({node.tok}).");
  }

  public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
  {
    throw new LeanConversionException($"Internal: UnresolvedTypeIdentifier should never appear ({node.tok}).");
  }

  public override Variable VisitVariable(Variable node)
  {
    throw new LeanConversionException($"Internal: Variable should never be directly visited ({node.tok}).");
  }

  public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
  {
    throw new LeanConversionException($"Internal: List<Variable> should never be directly visited ({variableSeq}).");
  }

  public override HashSet<Variable> VisitVariableSet(HashSet<Variable> node)
  {
    throw new LeanConversionException($"Internal: HashSet<Variable> should never be directly visited ({node}).");
  }

  public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
  {
    throw new LeanConversionException($"Internal: MapAssignLhs should never appear in passive program ({node.tok}).");
  }

  public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
  {
    throw new LeanConversionException($"Internal: SimpleAssignLhs should never appear in passive program ({node.tok}).");
  }

  public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
  {
    throw new LeanConversionException($"Internal: FieldAssignLhs should never appear in passive program ({node.tok}).");
  }

  public override Cmd VisitAssignCmd(AssignCmd node)
  {
    throw new LeanConversionException($"Internal: AssignCmd should never appear in passive program ({node.tok}).");
  }

  public override Cmd VisitUnpackCmd(UnpackCmd node)
  {
    throw new LeanConversionException($"Internal: UnpackCmd should never appear in passive program ({node.tok}).");
  }

  public override Cmd VisitCallCmd(CallCmd node)
  {
    throw new LeanConversionException($"Internal: CallCmd should never appear in passive program ({node.tok}).");
  }

  public override Cmd VisitParCallCmd(ParCallCmd node)
  {
    throw new LeanConversionException($"Internal: ParCallCmd should never appear in passive program ({node.tok}).");
  }

  public override Cmd VisitHavocCmd(HavocCmd node)
  {
    throw new LeanConversionException($"Internal: HavocCmd should never appear in passive program ({node.tok}).");
  }

  public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
  {
    throw new LeanConversionException($"Internal: ReturnExprCmd should never appear in passive program ({node.tok})");
  }

  public override Cmd VisitStateCmd(StateCmd node)
  {
    throw new LeanConversionException($"Internal: StateCmd should never appear in passive program ({node.tok})");
  }

  public override List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds)
  {
    throw new LeanConversionException($"Internal: List<CallCmd> should never appear in passive program ({callCmds}).");
  }

  public override Procedure VisitActionDecl(ActionDecl node)
  {
    throw new LeanConversionException($"Internal: ActionDecl should never appear in passive program ({node.tok}).");
  }

  public override YieldingLoop VisitYieldingLoop(YieldingLoop node)
  {
    throw new LeanConversionException($"Internal: YieldingLoop should never appear in passive program ({node}).");
  }

  public override Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node)
  {
    throw new LeanConversionException($"Internal: YieldingLoops should never appear in passive program.");
  }

  public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
  {
    throw new LeanConversionException($"Internal: YieldProcedureDecl should never appear in passive program ({node.tok}).");
  }

  public override Procedure VisitYieldInvariantDecl(YieldInvariantDecl node)
  {
    throw new LeanConversionException($"Internal: YieldInvariantDecl should never appear in passive program ({node.tok}).");
  }

  public override Cmd VisitRE(RE node)
  {
    throw new LeanConversionException($"Internal: RE should never appear in passive program ({node.tok})");
  }

  public override List<RE> VisitRESeq(List<RE> reSeq)
  {
    throw new LeanConversionException($"Internal: List<RE> should never appear in passive program ({reSeq})");
  }

  public override AtomicRE VisitAtomicRE(AtomicRE node)
  {
    throw new LeanConversionException($"Internal: AtomicRE should never appear in passive program ({node.tok})");
  }

  public override Choice VisitChoice(Choice node)
  {
    throw new LeanConversionException($"Internal: Choice should never appear in passive program ({node.tok}).");
  }

  public override Sequential VisitSequential(Sequential node)
  {
    throw new LeanConversionException($"Internal: Sequential should never appear in passive program ({node.tok})");
  }
}

internal class LeanConversionException : Exception
{
  public string Msg { get; }
  public LeanConversionException(string s)
  {
    Msg = s;
  }
}
