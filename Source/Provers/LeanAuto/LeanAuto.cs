using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Boogie.LeanAuto;

public class LeanGenerator : ReadOnlyVisitor
{
  private readonly TextWriter writer;
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
  private Dictionary<Type, HashSet<string>> uniqueConsts = new();

  private readonly string header = @"import Auto
import Auto.Tactic
import Auto.MathlibEmulator.Basic -- For `Real`
open Lean Std Auto

set_option linter.unusedVariables false
set_option auto.smt true
set_option trace.auto.smt.printCommands false
--set_option auto.smt.proof false
set_option auto.smt.trust true
--set_option auto.duper false
set_option auto.smt.solver.name ""z3""
set_option trace.auto.buildChecker false

@[simp] def assert (ψ β: Prop): Prop := ψ ∧ β
@[simp] def assume (ψ β: Prop): Prop := ψ → β
@[simp] def skip (β: Prop): Prop := β
@[simp] def ret: Prop := true
@[simp] def goto: Prop → Prop := id

-- SMT Array definition
def SMTArray1 (s1 s2: Type) := s1 → s2

def SMTArray2 (s1 s2 s3 : Type) := s1 → s2 → s3

def store1 [BEq s1] (m: SMTArray1 s1 s2) (i: s1) (v: s2): SMTArray1 s1 s2 :=
  fun i' => if i' == i then v else m i'

def select1 (m: SMTArray1 s1 s2) (i: s1): s2 := m i

def store2 [BEq s1] [BEq s2] (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (v: s3): SMTArray2 s1 s2 s3 :=
  fun i' j' => if i' == i && j' == j then v else m i' j'

def select2 (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2): s3 := m i j

axiom SelectStoreSame1 (s1 s2: Type) [BEq s1] (a: SMTArray1 s1 s2) (i: s1) (e: s2):
  select1 (store1 a i e) i = e

axiom SelectStoreDistinct1 (s1 s2: Type) [BEq s1] (a: SMTArray1 s1 s2) (i: s1) (j: s1) (e: s2):
  i ≠ j → select1 (store1 a i e) j = select1 a j

axiom SelectStoreSame2 (s1 s2 s3: Type) [BEq s1] [BEq s2] (a: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (e: s3):
  select2 (store2 a i j e) i j = e

axiom SelectStoreDistinct2 (s1 s2 s3: Type) [BEq s1] [BEq s2] (a: SMTArray2 s1 s2 s3) (i: s1) (i': s1) (j: s2) (j' : s2) (e: s3):
  i ≠ i' \/ j ≠ j' → select2 (store2 a i j e) i' j' = select2 a i' j'

-- TODO: provide either a definition or some functional axioms (or a definition plus some lemmas)
axiom distinct : {a : Type} → List a → Prop

axiom realToInt : Real → Int
axiom intToReal : Int → Real
instance BEqReal: BEq Real := by sorry
";

  private LeanGenerator(TextWriter writer)
  {
    this.writer = writer;
  }

  public static void EmitPassiveProgramAsLean(VCGenOptions options, Program p, TextWriter writer)
  {
    var generator = new LeanGenerator(writer);
    generator.EmitHeader();
    try {
      var allBlocks = p.Implementations.SelectMany(i => i.Blocks);
      var liveDeclarations = Prune.GetLiveDeclarations(options, p, allBlocks.ToList());
      
      generator.writer.WriteLine("-- Type constructors");
      // Include all type constructors
      p.TopLevelDeclarations.OfType<TypeCtorDecl>().ForEach(tcd => generator.Visit(tcd));
      generator.NL();

      generator.writer.WriteLine("-- Type synonyms");
      liveDeclarations.OfType<TypeSynonymDecl>().ForEach(tcd => generator.Visit(tcd));
      generator.NL();

      generator.writer.WriteLine("-- Constants");
      liveDeclarations.OfType<Constant>().ForEach(c => generator.Visit(c));
      generator.NL();

      generator.writer.WriteLine("-- Unique const axioms");
      generator.EmitUniqueConstAxioms();
      generator.NL();

      generator.writer.WriteLine("-- Variables");
      liveDeclarations.OfType<GlobalVariable>().ForEach(gv => generator.Visit(gv));
      generator.NL();

      generator.writer.WriteLine("-- Functions");
      liveDeclarations.OfType<Function>().ForEach(f => generator.Visit(f));
      generator.NL();

      generator.writer.WriteLine("-- Axioms");
      liveDeclarations.OfType<Axiom>().ForEach(a => generator.Visit(a));
      generator.NL();

      generator.writer.WriteLine("-- Implementations");
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
      writer.Write($"axiom {axiomName}: distinct ");
      List(kv.Value);
      NL();
      i++;
    }
  }

  private void EmitHeader()
  {
    writer.WriteLine(header.ReplaceLineEndings());
  }

  private void Indent(int n = 1, string str = null)
  {
    for (var i = 0; i < n; i++) {
      writer.Write("  ");
    }

    if (str is not null) {
      writer.Write(str);
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

  private void List(IEnumerable<string> strings)
  {
    writer.Write("[");
    writer.Write(String.Join(", ", strings));
    writer.Write("]");
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
    writer.WriteLine(" $");
    return node;
  }

  public override Cmd VisitAssumeCmd(AssumeCmd node)
  {
    Indent(2, "assume ");
    VisitExpr(node.Expr);
    writer.WriteLine(" $");
    return node;
  }

  public override GotoCmd VisitGotoCmd(GotoCmd node)
  {
    var gotoText = node.labelTargets.Select(l =>
      $"goto {BlockName(l)}").Aggregate((a, b) => $"{a} \u2227 {b}");
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
    writer.Write(name);
    return node;
  }

  public override Type VisitType(Type node)
  {
    if (node is BasicType basicType) {
      return VisitBasicType(basicType);
    } else if (node is BvType bvType) {
      return VisitBvType(bvType);
    } else if (node is CtorType ctorType) {
      return VisitCtorType(ctorType);
    } else if (node is FloatType floatType) {
      return VisitFloatType(floatType);
    } else if (node is MapType mapType) {
      return VisitMapType(mapType);
    } else if (node is TypeProxy typeProxy) {
      return VisitTypeProxy(typeProxy);
    } else if (node is TypeSynonymAnnotation typeSynonymAnnotation) {
      return VisitTypeSynonymAnnotation(typeSynonymAnnotation);
    } else if (node is TypeVariable typeVariable) {
      return VisitTypeVariable(typeVariable);
    } else if (node is UnresolvedTypeIdentifier uti) {
      return VisitUnresolvedTypeIdentifier(uti);
    } else {
      throw new LeanConversionException("Unreachable type case.");
    }
  }

  public override Type VisitBasicType(BasicType node)
  {
    if (node.IsBool) {
      writer.Write("Prop");
    } else if (node.IsInt) {
      writer.Write("Int");
    } else if (node.IsReal) {
      writer.Write("Real");
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
    writer.Write(" ++ ");
    Visit(node.E1);
    return node;
  }

  public override Type VisitBvType(BvType node)
  {
    writer.Write($"(BitVec {node.Bits})");
    return node;
  }

  public override Constant VisitConstant(Constant node)
  {
    var ti = node.TypedIdent;
    writer.Write("variable ");
    Visit(ti);
    if (node.Unique) {
      AddUniqueConst(ti.Type, SanitizeNameForLean(ti.Name));
    }
    NL();
    globalVars.Add(node);
    return node;
  }

  public override CtorType VisitCtorType(CtorType node)
  {
    if (node.Arguments.Any()) {
      writer.Write("(");
    }

    writer.Write(Name(node.Decl));
    node.Arguments.ForEach(a =>
    {
      writer.Write(" ");
      Visit(a);
    });
    if (node.Arguments.Any()) {
      writer.Write(")");
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
    writer.Write($"({kind}");
    foreach (var tv in node.TypeParameters) {
      writer.Write($" ({SanitizeNameForLean(tv.Name)} : Type)");
    }
    foreach (var x in node.Dummies) {
      writer.Write(" ");
      VisitTypedIdent(x.TypedIdent);
    }
    writer.Write(", ");
    Visit(node.Body);
    writer.Write(")");

    return node;
  }

  public override TypedIdent VisitTypedIdent(TypedIdent node)
  {
    writer.Write("(");
    var name = SanitizeNameForLean(node.Name);
    writer.Write(name);
    writer.Write(" : ");
    Visit(node.Type);
    writer.Write(")");
    return node;
  }

  public override Expr VisitBvExtractExpr(BvExtractExpr node)
  {
    // TODO: double-check range values
    writer.Write($"(BitVec.extractLsb {node.End - 1} {node.Start} ");
    Visit(node.Bitvector);
    writer.Write(")");
    return node;
  }

  public override Expr VisitLambdaExpr(LambdaExpr node)
  {
    writer.Write("(λ");
    node.Dummies.ForEach(x => Visit(x.TypedIdent));
    writer.Write("=>");
    Visit(node.Body);
    writer.Write(")");
    return node;
  }

  public override Expr VisitLetExpr(LetExpr node)
  {
    if (node.Dummies.Count > 1) {
      throw new LeanConversionException("Unsupported: LetExpr with more than one binder");
    }
    writer.Write("(let");
    node.Dummies.ForEach(x => Visit(x.TypedIdent));
    writer.Write(" := ");
    node.Rhss.ForEach(e => Visit(e));
    writer.Write("; ");
    Visit(node.Body);
    writer.Write(")");
    return node;
  }

  public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
  {
    writer.Write("variable ");
    Visit(node.TypedIdent);
    NL();
    globalVars.Add(node);
    return node;
  }

  public override Expr VisitLiteralExpr(LiteralExpr node)
  {
    if(node.IsTrue) {
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      writer.Write("true");
    } else if (node.IsFalse) {
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      writer.Write("false");
    } else if (node.isBvConst) {
      var bvConst = node.asBvConst;
      writer.Write("(");
      writer.Write(bvConst.Value);
      writer.Write($" : BitVec {bvConst.Bits}");
      writer.Write(")");
    } else {
      writer.Write(node); // TODO: make sure this is right for all other literal types
    }
    return node;
  }

  public override Type VisitMapType(MapType node)
  {
    if (node.Arguments.Count > 2) {
      throw new LeanConversionException($"Unsupported: MapType with too many index types ({node})");
    }
    if (node.TypeParameters.Any()) {
      var args = node.TypeParameters.Select(a => SanitizeNameForLean(a.Name));
      writer.Write($"forall ({String.Join(" ", args)} : Type), ");
    }
    writer.Write($"(SMTArray{node.Arguments.Count} ");
    node.Arguments.ForEach(a =>
    {
      Visit(a);
      writer.Write(" ");
    });
    Visit(node.Result);
    writer.Write(")");
    return node;
  }

  public override Expr VisitNAryExpr(NAryExpr node)
  {
    var fun = node.Fun;
    var args = node.Args;
    writer.Write("(");
    if (fun is BinaryOperator op && args.Count == 2) {
      Visit(args[0]);
      writer.Write($" {BinaryOpToLean(op.Op)} ");
      Visit(args[1]);
    } else if (fun is IfThenElse && args.Count == 3) {
      writer.Write("if ");
      Visit(args[0]);
      writer.Write(" then ");
      Visit(args[1]);
      writer.Write(" else ");
      Visit(args[2]);
    } else if (fun is TypeCoercion typeCoercion && args.Count == 1) {
      if (!args[0].Type.Equals(typeCoercion.Type)) {
        // TODO: might need to actually call a coercion function
        Console.WriteLine($"Coerce: {args[0].Type} -> {typeCoercion.Type}");
      }
      writer.Write("(");
      Visit(args[0]);
      writer.Write(" : ");
      Visit(typeCoercion.Type);
      writer.Write(")");
    } else if (fun is FieldAccess fieldAccess) {
      throw new LeanConversionException("Unsupported: field access (since the semantics are complex)");
      // TODO: implement
      /*
      Visit(args[0]);
      writer.Write($".{SanitizeNameForLean(fieldAccess.FieldName)}");
      */
    } else {
      VisitIAppliable(fun);
      foreach (var arg in args) {
        writer.Write(" ");
        Visit(arg);
      }
    }
    writer.Write(")");

    return node;
  }

  private void VisitIAppliable(IAppliable fun)
  {
    switch (fun) {
      case MapSelect:
        usesMaps = true;
        writer.Write($"select{fun.ArgumentCount - 1}");
        break;
      case MapStore:
        usesMaps = true;
        writer.Write($"store{fun.ArgumentCount - 2}");
        break;
      case BinaryOperator op:
        writer.Write(BinaryOpToLean(op.Op));
        break;
      case UnaryOperator op:
        writer.Write(UnaryOpToLean(op.Op));
        break;
      case FunctionCall fc:
        writer.Write(SanitizeNameForLean(fc.Func.Name));
        break;
      case IsConstructor isConstructor:
        // TODO: declare these discriminator functions
        writer.Write($"is_{SanitizeNameForLean(isConstructor.ConstructorName)}");
        break;
      case ArithmeticCoercion arithmeticCoercion:
        var func = arithmeticCoercion.Coercion switch
        {
          ArithmeticCoercion.CoercionType.ToInt => "realToInt",
          ArithmeticCoercion.CoercionType.ToReal => "intToReal",
          _ => throw new LeanConversionException($"Internal: unknown arithmetic coercion: {arithmeticCoercion.Coercion}")
        };
        writer.Write(func);
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
    Console.WriteLine($"DeclWithFormals: {node}");
    return node; // TODO: do something?
  }

  public override Type VisitBvTypeProxy(BvTypeProxy node)
  {
    // TODO: confirm that this is unreachable
    throw new LeanConversionException($"Unsupported: bvtypeproxy: {node}");
  }

  public override Expr VisitCodeExpr(CodeExpr node)
  {
    // TODO: what is this?
    throw new LeanConversionException($"Unsupported: codexpr: {node}");
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
    // TODO: confirm that this is unreachable
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
    if (node is DatatypeTypeCtorDecl dt) {
      writer.WriteLine($"inductive {SanitizeNameForLean(dt.Name)} where");
      foreach (var ctor in dt.Constructors) {
        Indent(1, $"| {SanitizeNameForLean(ctor.Name)} : ");
        ctor.InParams.ForEach(p =>
        {
          Visit(p.TypedIdent.Type);
          writer.Write(" → ");
        });
        writer.WriteLine($" {SanitizeNameForLean(dt.Name)}");
      }
    } else {
      var name = Name(node);
      var tyStr = String.Join(" → ", Enumerable.Repeat("Type", node.Arity + 1).ToList());
      writer.WriteLine($"axiom {name} : {tyStr}");

      if(node.Arity == 0) {
        writer.WriteLine($"instance {name}BEq : BEq {name} := by sorry");
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
    writer.Write($"def {name}");
    node.TypeParameters.ForEach(tp => writer.Write($" ({SanitizeNameForLean(tp.Name)} : Type)"));
    writer.Write(" := ");
    Visit(node.Body);
    NL();
    return node;
  }

  public override Type VisitTypeProxy(TypeProxy node)
  {
    var p = node.ProxyFor;
    if (p is null) {
      writer.Write(SanitizeNameForLean(node.Name));
    } else {
      VisitType(p);
    }
    return node;
  }

  public override Type VisitTypeVariable(TypeVariable node)
  {
    writer.Write(SanitizeNameForLean(node.Name));
    return node;
  }

  public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    writer.WriteLine(" $");
    return node;
  }

  public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    writer.WriteLine(" $");
    return node;
  }

  public override ActionDeclRef VisitActionDeclRef(ActionDeclRef node)
  {
    // TODO: what is this?
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override ElimDecl VisitElimDecl(ElimDecl node)
  {
    // TODO: support this?
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override List<ElimDecl> VisitElimDeclSeq(List<ElimDecl> node)
  {
    // TODO: support this?
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Axiom VisitAxiom(Axiom node)
  {
    // This will take two more steps:
    // * A named lemma with a definition of `by sorry` (using a `name` attribute?) (or `id`, so it's also useful for proof dependencies?)
    // * A named lemma that's defined by a call to a previously-defined proof of the same thing
    int n = 0;
    var name = $"ax_l{node.tok.line}c{node.tok.col}_{n}";
    while (userAxiomNames.Contains(name)) {
      n += 1;
      name = $"ax_l{node.tok.line}c{node.tok.col}_{n}";
    }
    writer.Write($"axiom {name}: ");
    VisitExpr(node.Expr);
    NL();
    userAxiomNames.Add(name);
    return node;
  }

  public override Function VisitFunction(Function node)
  {
    // In the long run, this should define functions when possible.
    writer.Write($"axiom {Name(node)} : ");
    node.TypeParameters.ForEach(x =>
    {
      var name = SanitizeNameForLean(x.Name);
      writer.Write($"{{{name} : Type}}");
      writer.Write(" \u2192 ");
      //writer.Write($"[BEq {name}]");
      //writer.Write(" \u2192 ");
    });
    node.InParams.ForEach(x =>
    {
      Visit(x.TypedIdent.Type);
      writer.Write(" \u2192 ");
    });
    if (node.OutParams.Count == 1) {
      Visit(node.OutParams[0].TypedIdent.Type);
    } else {
      writer.Write("(");
      node.OutParams.ForEach(x =>
      {
        Visit(x.TypedIdent.Type); writer.Write(", ");
      });
      writer.Write(")");
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
      BinaryOperator.Opcode.Neq => "\u2260", /* ≠ */
      BinaryOperator.Opcode.And => "\u2227", /* ∧ */
      BinaryOperator.Opcode.Or => "\u2228", /* ∨ */
      BinaryOperator.Opcode.Iff => "=",
      BinaryOperator.Opcode.Imp => "\u2192", /* → */
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
    writer.WriteLine($"namespace impl_{name}");
    NL();

    writer.WriteLine("@[simp]");
    writer.WriteLine($"def {name}");
    WriteParams(node);
    IndentL(1, $": Prop := {entryLabel}");
    IndentL(1, "where");
    node.Blocks.ForEach(b => VisitBlock(b));
    NL();
    writer.WriteLine($"theorem {name}_correct");
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
    writer.WriteLine($"end impl_{name}");

    usesMaps = false; // Skip map axioms in the next implementation if it doesn't need them
    usedNames.Clear(); // Skip any globals not used by the next implementation

    return node;
  }

  /* ==== Nodes that should never be visited ==== */

  public override Program VisitProgram(Program node)
  {
    throw new LeanConversionException($"Internal: Program should never be directly visited {node.tok}");
  }

  public override Declaration VisitDeclaration(Declaration node)
  {
    throw new LeanConversionException($"Internal: Declaration should never be directly visited {node.tok}");
  }

  public override List<Declaration> VisitDeclarationList(List<Declaration> declarationList)
  {
    throw new LeanConversionException($"Internal: List<Declaration> should never be directly visited {declarationList}");
  }

  public override List<Block> VisitBlockSeq(List<Block> blockSeq)
  {
    throw new LeanConversionException($"Internal: List<Block> should never be directly visited {blockSeq}");
  }

  public override List<Block> VisitBlockList(List<Block> blocks)
  {
    throw new LeanConversionException($"Internal: List<Block> should never be directly visited {blocks}");
  }

  public override Trigger VisitTrigger(Trigger node)
  {
    throw new LeanConversionException($"Internal: Trigger should never be directly visited {node.tok}");
  }

  public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
  {
    throw new LeanConversionException($"Internal: List<Expr> should never be directly visited {exprSeq}");
  }

  public override BoundVariable VisitBoundVariable(BoundVariable node)
  {
    throw new LeanConversionException($"Internal: BoundVariable should never be directly visited {node.tok}");
  }

  public override Formal VisitFormal(Formal node)
  {
    throw new LeanConversionException($"Internal: Formal should never be directly visited {node.tok}");
  }

  public override LocalVariable VisitLocalVariable(LocalVariable node)
  {
    throw new LeanConversionException($"Internal error: LocalVariable should never be directly visited {node.tok}");
  }

  public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
  {
    throw new LeanConversionException($"Internal: UnresolvedTypeIdentifier should never appear ({node.tok})");
  }

  public override Variable VisitVariable(Variable node)
  {
    throw new LeanConversionException($"Internal: Variable should never be directly visited {node.tok}");
  }

  public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
  {
    throw new LeanConversionException($"Internal: List<Variable> should never be directly visited {variableSeq}");
  }

  public override HashSet<Variable> VisitVariableSet(HashSet<Variable> node)
  {
    throw new LeanConversionException($"Internal: HashSet<Variable> should never be directly visited {node}");
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
