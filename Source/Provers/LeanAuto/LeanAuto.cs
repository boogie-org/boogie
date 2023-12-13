using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Xml.Linq;

namespace Microsoft.Boogie.LeanAuto;

public class LeanGenerator : ReadOnlyVisitor
{
  private TextWriter writer;

  private readonly string header = @"
import Auto
import Auto.Tactic
open Lean Std

set_option auto.smt true
set_option trace.auto.smt.printCommands false
set_option auto.smt.trust true
set_option auto.duper false
set_option auto.smt.solver.name ""z3""
set_option trace.auto.buildChecker false

def assert (ψ β: Prop): Prop := ψ ∧ β
def assume (ψ β: Prop): Prop := ψ → β
def skip (β: Prop): Prop := β
def ret: Prop := true
def goto: Prop -> Prop := id

-- SMT Array definition
def SMTArray (s1 s2: Type) := s1 -> s2

def store [BEq s1] (m: SMTArray s1 s2) (i: s1) (v: s2): SMTArray s1 s2 :=
  fun i' => if i' == i then v else m i'

def select (m: SMTArray s1 s2) (i: s1): s2 := m i
";

  public LeanGenerator(TextWriter writer)
  {
    this.writer = writer;
  }

  public static void EmitPassiveProgramAsLean(Program p, TextWriter writer)
  {
    var generator = new LeanGenerator(writer);
    generator.EmitHeader();
    try {
      generator.Visit(p);
    } catch (LeanConversionException e) {
      writer.WriteLine($"-- failed translation: {e.Msg}");
    }
  }

  private void EmitHeader()
  {
    writer.WriteLine(header);
  }

  public override Block VisitBlock(Block node)
  {
    writer.WriteLine($"  {node.Label} :=");
    node.Cmds.ForEach(c => Visit(c));
    if (node.TransferCmd is ReturnCmd r) {
      VisitReturnCmd(r);
    }
    if (node.TransferCmd is GotoCmd g) {
      VisitGotoCmd(g);
    }
    writer.WriteLine();
    return node;
  }

  public override Cmd VisitAssertCmd(AssertCmd node)
  {
    writer.Write($"    assert ");
    VisitExpr(node.Expr);
    writer.WriteLine(" $");
    return node;
  }

  public override Cmd VisitAssumeCmd(AssumeCmd node)
  {
    writer.Write($"    assume ");
    VisitExpr(node.Expr);
    writer.WriteLine(" $");
    return node;
  }

  public override GotoCmd VisitGotoCmd(GotoCmd node)
  {
    var gotoText = node.labelTargets.Select(l =>
      $"goto {l.Label}").Aggregate((a, b) => $"{a} \u2227 {b}");
    writer.WriteLine("    " + gotoText);
    return node;
  }

  public override ReturnCmd VisitReturnCmd(ReturnCmd node)
  {
    writer.WriteLine("    ret");
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
    } else if (node.IsMap) {
      var mapType = node.AsMap;
      var domain = mapType.Arguments[0];
      var range = mapType.Result;
      writer.Write("SMTArray ");
      Visit(mapType.Arguments[0]);
      writer.Write(" ");
      Visit(mapType.Result);
    } else {
      writer.Write("(TODO: BasicType)");
    }

    return node;
  }

  public override Expr VisitBvConcatExpr(BvConcatExpr node)
  {
    throw new LeanConversionException("Unsupported: BvConcatExpr");
  }

  public override Type VisitBvType(BvType node)
  {
    throw new LeanConversionException("Unsupported: BvType");
  }

  public override BoundVariable VisitBoundVariable(BoundVariable node)
  {
    throw new LeanConversionException("Unsupported: BoundVariable");
  }

  public override Constant VisitConstant(Constant node)
  {
    writer.Write("variable ");
    Visit(node.TypedIdent);
    writer.WriteLine();
    return node;
  }

  public override CtorType VisitCtorType(CtorType node)
  {
    throw new LeanConversionException("Unsupported: CtorType");
  }

  public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
  {
    var kind = node switch
    {
      ForallExpr => "forall",
      ExistsExpr => "exists",
      _ => "<other quantifier>"
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
    throw new LeanConversionException("Unsupported: BvExtractExpr");
  }

  public override Expr VisitLambdaExpr(LambdaExpr node)
  {
    throw new LeanConversionException("Unsupported: LambdaExpr");
  }

  public override Expr VisitLetExpr(LetExpr node)
  {
    throw new LeanConversionException("Unsupported: LetExpr");
  }

  public override Formal VisitFormal(Formal node)
  {
    throw new LeanConversionException("Unsupported: Formal");
  }

  public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
  {
    writer.Write("variable ");
    Visit(node.TypedIdent);
    writer.WriteLine();
    return node;
  }

  public override Expr VisitLiteralExpr(LiteralExpr node)
  {
    writer.Write(node.ToString()); // TODO: make sure this is right
    return node;
  }

  public override LocalVariable VisitLocalVariable(LocalVariable node)
  {
    throw new LeanConversionException("Unsupported: LocalVariable");
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
    throw new LeanConversionException("Unsupported: OldExpr");
  }

  public override Type VisitFloatType(FloatType node)
  {
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

  public override Cmd VisitAssignCmd(AssignCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitUnpackCmd(UnpackCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override AtomicRE VisitAtomicRE(AtomicRE node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Type VisitBvTypeProxy(BvTypeProxy node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Expr VisitCodeExpr(CodeExpr node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitCallCmd(CallCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitParCallCmd(ParCallCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Choice VisitChoice(Choice node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitCommentCmd(CommentCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
  {
    return requiresSeq; // TODO: do something
  }

  public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
  {
    return ensuresSeq; // TODO: do something
  }

  public override Cmd VisitHavocCmd(HavocCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Type VisitMapTypeProxy(MapTypeProxy node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override QKeyValue VisitQKeyValue(QKeyValue node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitRE(RE node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override List<RE> VisitRESeq(List<RE> reSeq)
  {
    throw new LeanConversionException($"Unsupported: {reSeq}");
  }

  public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Sequential VisitSequential(Sequential node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitStateCmd(StateCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Type VisitTypeVariable(TypeVariable node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Type VisitTypeProxy(TypeProxy node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
  {
    writer.Write($"    assert ");
    VisitExpr(node.Expr);
    writer.WriteLine(" $");
    return node;
  }

  public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds)
  {
    throw new LeanConversionException($"Unsupported: CallCmds");
  }

  public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override ActionDeclRef VisitActionDeclRef(ActionDeclRef node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override ElimDecl VisitElimDecl(ElimDecl node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override List<ElimDecl> VisitElimDeclSeq(List<ElimDecl> node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Procedure VisitActionDecl(ActionDecl node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override YieldingLoop VisitYieldingLoop(YieldingLoop node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
  {
    throw new LeanConversionException($"Unsupported: {node}");
  }

  public override Procedure VisitYieldInvariantDecl(YieldInvariantDecl node)
  {
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
    writer.WriteLine();
    return node;
  }

  public override Function VisitFunction(Function node)
  {
    writer.WriteLine($"-- function {node.Name}");
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

  public override Procedure VisitProcedure(Procedure node)
  {
    return node;
  }
  
  public override Implementation VisitImplementation(Implementation node)
  {
    
    writer.WriteLine();
    writer.WriteLine($"namespace impl_{node.Name}");
    writer.WriteLine();

    foreach (var x in node.LocVars) {
      writer.Write("variable ");
      VisitTypedIdent(x.TypedIdent);
      writer.WriteLine();
    }

    writer.WriteLine();
    writer.Write($"def {node.Name}_correct ");
    node.InParams.ForEach(x => VisitTypedIdent(x.TypedIdent));
    node.OutParams.ForEach(x => VisitTypedIdent(x.TypedIdent));
    writer.WriteLine($" : Prop := {node.Blocks[0].Label}");
    writer.WriteLine("  where");
    node.Blocks.ForEach(b => VisitBlock(b));
    writer.WriteLine($"end impl_{node.Name}");
    writer.WriteLine();
    return node;
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
