using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Boogie.LeanAuto;

public class LeanGenerator : ReadOnlyVisitor
{
  private readonly TextWriter writer;
  private readonly List<NamedDeclaration> globalVars = new();
  private readonly List<string> axiomNames =
    new(new[]
    {
      "SelectStoreSame", "SelectStoreDistinct"
    });
  private readonly List<string> defNames =
    new(new[]
    {
      "assert", "assume", "goto", "ret", "skip"
    });

  private readonly string header = @"
import Auto
import Auto.Tactic
open Lean Std

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
@[simp] def goto: Prop -> Prop := id

-- SMT Array definition
def SMTArray (s1 s2: Type) := s1 -> s2

def store [BEq s1] (m: SMTArray s1 s2) (i: s1) (v: s2): SMTArray s1 s2 :=
  fun i' => if i' == i then v else m i'

def select (m: SMTArray s1 s2) (i: s1): s2 := m i

axiom SelectStoreSame (s1 s2: Type) [BEq s1] (a: SMTArray s1 s2) (i: s1) (e: s2):
  select (store a i e) i = e

axiom SelectStoreDistinct (s1 s2: Type) [BEq s1] (a: SMTArray s1 s2) (i: s1) (j: s1) (e: s2):
  i ≠ j → select (store a i e) j = select a j
";

  private LeanGenerator(TextWriter writer)
  {
    this.writer = writer;
  }

  public static void EmitPassiveProgramAsLean(Program p, TextWriter writer)
  {
    var generator = new LeanGenerator(writer);
    generator.EmitHeader();
    try {
      p.Constants.ForEach(c => generator.Visit(c));
      p.GlobalVariables.ForEach(gv => generator.Visit(gv));
      p.Functions.ForEach(f => generator.Visit(f));
      p.Axioms.ForEach(a => generator.Visit(a));
      p.Implementations.ForEach(i => generator.Visit(i));
    } catch (LeanConversionException e) {
      writer.WriteLine($"-- failed translation: {e.Msg}");
    }
  }

  private void EmitHeader()
  {
    writer.WriteLine(header);
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
    // TODO: names less likely to clash
    var label = SanitizeNameForLean(node.Label);
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
      $"goto {l.Label}").Aggregate((a, b) => $"{a} \u2227 {b}");
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
    writer.Write(SanitizeNameForLean(node.Name));
    return node;
  }

  public override Type VisitBasicType(BasicType node)
  {
    if (node.IsBool) {
      writer.Write("Bool");
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
      writer.Write("(SMTArray ");
      Visit(mapType.Arguments[0]);
      writer.Write(" ");
      Visit(mapType.Result);
      writer.Write(")");
    } else {
      throw new LeanConversionException($"Unsupported BasicType: {node}");
    }

    return node;
  }

  public override Expr VisitBvConcatExpr(BvConcatExpr node)
  {
    // TODO: implement
    throw new LeanConversionException("Unsupported: BvConcatExpr");
  }

  public override Type VisitBvType(BvType node)
  {
    // TODO: implement
    throw new LeanConversionException("Unsupported: BvType");
  }

  public override Constant VisitConstant(Constant node)
  {
    writer.Write("variable ");
    Visit(node.TypedIdent);
    NL();
    globalVars.Add(node);
    return node;
  }

  public override CtorType VisitCtorType(CtorType node)
  {
    // TODO: implement (next)
    throw new LeanConversionException("Unsupported: CtorType");
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
    writer.Write(SanitizeNameForLean(node.Name));
    writer.Write(" : ");
    Visit(node.Type);
    writer.Write(")");
    return node;
  }

  public override Expr VisitBvExtractExpr(BvExtractExpr node)
  {
    // TODO: implement
    throw new LeanConversionException("Unsupported: BvExtractExpr");
  }

  public override Expr VisitLambdaExpr(LambdaExpr node)
  {
    // TODO: implement
    throw new LeanConversionException("Unsupported: LambdaExpr");
  }

  public override Expr VisitLetExpr(LetExpr node)
  {
    // TODO: implement
    throw new LeanConversionException("Unsupported: LetExpr");
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
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      writer.Write(node + "/- TODO: bit vector constants -/");
    } else {
      writer.Write(node); // TODO: make sure this is right
    }
    return node;
  }

  public override Type VisitMapType(MapType node)
  {
    writer.Write("SMTArray ");
    Visit(node.Arguments[0]);
    writer.Write(" ");
    Visit(node.Result);
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
      // TODO: actually coerce to target type
      Visit(args[0]);
      writer.Write(" : ");
      Visit(typeCoercion.Type);
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
        writer.Write("select");
        break;
      case MapStore:
        writer.Write("store");
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
      default:
        throw new LeanConversionException($"Unsupported: IAppliable: {fun}");
    }
  }

  public override Expr VisitOldExpr(OldExpr node)
  {
    // TODO: implement
    throw new LeanConversionException("Unsupported: OldExpr");
  }

  public override Type VisitFloatType(FloatType node)
  {
    // TODO: implement (but low priority)
    throw new LeanConversionException("Unsupported: FloatType");
  }

  public override Requires VisitRequires(Requires requires)
  {
    return requires; // TODO: do something with it
  }

  public override Ensures VisitEnsures(Ensures ensures)
  {
    return ensures; // TODO: do something with it
  }

  public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
  {
    return node; // TODO: do something
  }

  public override Type VisitBvTypeProxy(BvTypeProxy node)
  {
    // TODO: implement
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
    return requiresSeq; // TODO: do something
  }

  public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
  {
    return ensuresSeq; // TODO: do something
  }

  public override Type VisitMapTypeProxy(MapTypeProxy node)
  {
    // TODO: implement
    throw new LeanConversionException($"Unsupported: maptypeproxy: {node}");
  }

  public override QKeyValue VisitQKeyValue(QKeyValue node)
  {
    // Implement this if we want to visit attributes? Or maybe extract them more directly.
    return node;
  }

  public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
  {
    // TODO: implement
    throw new LeanConversionException($"Unsupported: typectordecl: {node}");
  }

  public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
  {
    // TODO: implement
    throw new LeanConversionException($"Unsupported: typesynonymannotation: {node}");
  }

  public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
  {
    // TODO: implement
    throw new LeanConversionException($"Unsupported: typesynonymdecl: {node}");
  }

  public override Type VisitTypeProxy(TypeProxy node)
  {
    // TODO: implement
    throw new LeanConversionException($"Unsupported: typeproxy: {node}");
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
    var name = $"ax_l{node.tok.line}c{node.tok.col}";
    writer.Write($"axiom {name}: ");
    VisitExpr(node.Expr);
    NL();
    axiomNames.Add(name);
    return node;
  }

  public override Function VisitFunction(Function node)
  {
    // In the long run, this should define functions when possible.
    writer.Write($"def {Name(node)} : ");
    node.InParams.ForEach(x =>
    {
      Visit(x.TypedIdent.Type); writer.Write(" -> ");
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
    writer.WriteLine(" := by sorry");
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
      BinaryOperator.Opcode.Neq => "!=",
      BinaryOperator.Opcode.And => "\u2227",
      BinaryOperator.Opcode.Or => "||",
      BinaryOperator.Opcode.Iff => "=",
      BinaryOperator.Opcode.Imp => "->",
      BinaryOperator.Opcode.Pow => "TODO",
      BinaryOperator.Opcode.FloatDiv => "TODO",
      BinaryOperator.Opcode.RealDiv => "TODO",
      _ => throw new LeanConversionException($"unsupported binary operator: {op.ToString()}")
    };
  }

  private string UnaryOpToLean(UnaryOperator.Opcode op)
  {
    return op switch
    {
      UnaryOperator.Opcode.Not => "!",
      UnaryOperator.Opcode.Neg => "-",
      _ => throw new LeanConversionException($"unsupported unary operator: {op.ToString()}")
    };
  }

  private string SanitizeNameForLean(string name)
  {
    return name.Replace('@', '_');
  }

  private string Name(NamedDeclaration d)
  {
    return SanitizeNameForLean(d.Name);
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

    NL();
    writer.WriteLine($"namespace impl_{name}");
    NL();

    writer.WriteLine("@[simp]");
    writer.WriteLine($"def {name}");
    WriteParams(node);
    IndentL(1, $": Prop := {node.Blocks[0].Label}");
    IndentL(1, "where");
    node.Blocks.ForEach(b => VisitBlock(b));
    NL();
    writer.WriteLine($"theorem {name}_correct");
    WriteParams(node);
    var paramNames =
      globalVars.Select(Name)
        .Concat(node.InParams.Select(Name))
        .Concat(node.OutParams.Select(Name))
        .Concat(node.LocVars.Select(Name));
    var paramString = String.Join(' ', paramNames);
    Indent(1, $": {name} {paramString} := by"); NL();
    IndentL(2, "simp");
    IndentL(2, "auto");
    Indent(3); List(axiomNames); NL();
    IndentL(3, "u[]");
    NL();
    writer.WriteLine($"end impl_{name}"); NL();
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

  public override Type VisitTypeVariable(TypeVariable node)
  {
    throw new LeanConversionException($"Internal: TypeVariable should never be directly visited {node.tok}");
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
