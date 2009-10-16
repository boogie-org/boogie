//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional

trait ASTNode extends Positional

// classes and types

case class TopLevelDecl(id: String) extends ASTNode

sealed case class Class(classId: String, parameters: List[Class], module: String, members: List[Member]) extends TopLevelDecl(classId) {
  var mm = Map[String,Member]()
  def LookupMember(id: String): Option[Member] = {
    if (mm.keys exists { i => i.equals(id)})
      Some(mm(id))
    else if (IsRef && (RootClass.mm contains id)) {
      val m = RootClass.mm(id)
      if (m.Hidden) None else Some(m)
    } else
      None
  }
  def IsInt: boolean = false
  def IsBool: boolean = false
  def IsRef: boolean = true
  def IsNull: boolean = false
  def IsMu: boolean = false
  def IsSeq: boolean = false
  def IsToken: boolean = false
  def IsChannel: boolean = false
  def IsState: boolean = false
  def IsNormalClass = true;
  var IsExternal = false;  // says whether or not to compile the class (compilation ignores external classes)

  def Fields: List[Field] = {
    members flatMap (m => m match { case f:Field => List(f) case _ => List() })
  }
  def Invariants: List[MonitorInvariant] = {
    (members :\ List[MonitorInvariant]()) { (m,list) => m match {
      case m:MonitorInvariant => m :: list
      case _ => list }}
  }
  def FullName: String = if(parameters.isEmpty) id else id + "<" + parameters.tail.foldLeft(parameters.head.FullName){(a, b) => a + ", " + b.FullName} + ">"
}

sealed case class Channel(channelId: String, parameters: List[Variable], where: Expression) extends TopLevelDecl(channelId)

case class SeqClass(parameter: Class) extends Class("seq", List(parameter), "default", Nil) {
  override def IsRef = false;
  override def IsSeq = true;
  override def IsNormalClass = false;
}
object IntClass extends Class("int", Nil, "default", Nil) {
  override def IsRef = false
  override def IsInt = true
  override def IsNormalClass = false;
}
object BoolClass extends Class("bool", Nil, "default", Nil) {
  override def IsRef = false
  override def IsBool = true
  override def IsNormalClass = false;
}
object NullClass extends Class("null", Nil, "default", Nil) {
  override def IsNull = true
  override def IsNormalClass = false;
}
object MuClass extends Class("$Mu", Nil, "default", Nil) {
  override def IsRef = false
  override def IsMu = true
  override def IsNormalClass = false;
}
case class TokenClass(c: Type, m: String) extends Class("token", Nil, "default", List( 
  new SpecialField("joinable", new Type(BoolClass))
))
{
  var method = null: Method;
  override def IsRef = true;
  override def IsToken = true;
  override def IsNormalClass = false;
  override def FullName: String = "token<" + c.FullName + "." + m + ">"
  mm = mm.+(("joinable", Fields(0)));
}
case class ChannelClass(ch: Channel) extends Class(ch.id, Nil, "default", Nil) {
  override def IsRef = true;
  override def IsChannel = true;
  override def IsNormalClass = false;
}

object RootClass extends Class("$root", Nil, "default", List(
  new SpecialField("mu", new Type(MuClass)),
  new SpecialField("held", new Type(BoolClass)){ override val Hidden = true },
  new SpecialField("rdheld", new Type(BoolClass)){ override val Hidden = true }
  ))  // joinable and held are bool in Chalice, but translated into an int in Boogie
{
  def MentionableFields = Fields filter {fld => fld.id != "held" && fld.id != "rdheld"}
}

sealed case class Type(id: String, params: List[Type]) extends ASTNode {  // denotes the use of a type
  var typ: Class = null
  def this(id: String) = { this(id, Nil); }
  def this(cl: Class) = { this(cl.id); typ = cl }
  def FullName: String = if(params.isEmpty) id else id + "<" + params.tail.foldLeft(params.head.FullName){(a, b) => a + ", " + b.FullName} + ">"
}

sealed case class TokenType(C: Type, m: String) extends Type("token", Nil) {  // denotes the use of a type
  typ = TokenClass(C, m);
  var method = null : Method;

  override def FullName: String = "token<" + C.FullName + "." + m + ">"
}

// members

sealed abstract class Member extends ASTNode {
  val Hidden: boolean = false  // hidden means not mentionable in source
}
case class MonitorInvariant(e: Expression) extends Member
sealed abstract class NamedMember(id: String) extends Member {
  val Id = id
  var Parent: Class = null
  def FullName = Parent.id + "." + Id
}
case class Field(id: String, typ: Type) extends NamedMember(id) {
  val IsGhost: boolean = false
}
case class SpecialField(name: String, tp: Type) extends Field(name, tp) {  // direct assignments are not allowed to a SpecialField
  override def FullName = id
}
case class Method(id: String, ins: List[Variable], outs: List[Variable], spec: List[Specification], body: List[Statement]) extends NamedMember(id)
case class Predicate(id: String, definition: Expression) extends NamedMember(id)
case class Function(id: String, ins: List[Variable], out: Type, spec: List[Specification], definition: Expression) extends NamedMember(id) {
  def apply(rec: Expression, args: List[Expression]): FunctionApplication = {
    val result = FunctionApplication(rec, id, args);
    result.f = this;
    result
  }
}
case class Condition(id: String, where: Option[Expression]) extends NamedMember(id)
class Variable(name: String, typ: Type) extends ASTNode {
  val id = name
  val t = typ
  val IsGhost: boolean = false
  val IsImmutable: boolean = false
  val UniqueName = {
    val n = S_Variable.VariableCount
    S_Variable.VariableCount = S_Variable.VariableCount + 1
    name + "#" + n
  }
}
object S_Variable { var VariableCount = 0 }
class ImmutableVariable(id: String, t: Type) extends Variable(id, t) {
  override val IsImmutable: boolean = true
}
class SpecialVariable(name: String, typ: Type) extends Variable(name, typ) {
  override val UniqueName = name
}

sealed abstract class Specification extends ASTNode
case class Precondition(e: Expression) extends Specification
case class Postcondition(e: Expression) extends Specification
case class LockChange(ee: List[Expression]) extends Specification

// statements

sealed abstract class Statement extends ASTNode
case class Assert(e: Expression) extends Statement
case class Assume(e: Expression) extends Statement
case class BlockStmt(ss: List[Statement]) extends Statement
case class IfStmt(guard: Expression, thn: BlockStmt, els: Option[Statement]) extends Statement
case class WhileStmt(guard: Expression,
                     invs: List[Expression], lkch: List[Expression],
                     body: BlockStmt) extends Statement {
  var LoopTargets: Set[Variable] = null
  lazy val LoopTargetsList: List[Variable] = {  // to be called only after LoopTargets has been completely filled in
    var vv = List[Variable]()
    LoopTargets foreach (v => vv = v :: vv)
    vv
  }
}
case class Assign(lhs: VariableExpr, rhs: RValue) extends Statement
case class FieldUpdate(lhs: MemberAccess, rhs: RValue) extends Statement
case class LocalVar(id: String, t: Type, const: boolean, ghost: boolean, rhs: Option[RValue]) extends Statement {
  val v =
    if (const)
      new ImmutableVariable(id, t){override val IsGhost = ghost}
    else
      new Variable(id, t){override val IsGhost = ghost}
}
case class Call(declaresLocal: List[boolean], lhs: List[VariableExpr], obj: Expression, id: String, args: List[Expression]) extends Statement {
  var locals = List[Variable]()
  var m: Method = null
}
case class Install(obj: Expression, lowerBounds: List[Expression], upperBounds: List[Expression]) extends Statement
case class Share(obj: Expression, lowerBounds: List[Expression], upperBounds: List[Expression]) extends Statement
case class Unshare(obj: Expression) extends Statement
case class Acquire(obj: Expression) extends Statement
case class Release(obj: Expression) extends Statement
case class RdAcquire(obj: Expression) extends Statement
case class RdRelease(obj: Expression) extends Statement
case class Downgrade(obj: Expression) extends Statement
case class Lock(obj: Expression, b: BlockStmt, rdLock: boolean) extends Statement
case class Free(obj: Expression) extends Statement
case class CallAsync(declaresLocal: boolean, lhs: VariableExpr, obj: Expression, id: String, args: List[Expression]) extends Statement {
  var local: Variable = null
  var m: Method = null
}
case class JoinAsync(lhs: List[VariableExpr], token: Expression) extends Statement {
  var m: Method = null
}
case class Wait(obj: Expression, id: String) extends Statement {
  var c: Condition = null
}
case class Signal(obj: Expression, id: String, all: boolean) extends Statement {
  var c: Condition = null
}
case class Send(ch: Expression, args: List[Expression]) extends Statement {
}
case class Receive(declaresLocal: List[boolean], ch: Expression, outs: List[VariableExpr]) extends Statement {
  var locals = List[Variable]()
}
case class Fold(pred: PermissionExpr) extends Statement
case class Unfold(pred: PermissionExpr) extends Statement

// expressions

sealed abstract class RValue extends ASTNode {
  var typ: Class = null
}
case class NewRhs(id: String, initialization: List[Init], lowerBounds: List[Expression], upperBounds: List[Expression]) extends RValue
case class Init(id: String, e: Expression) extends ASTNode {
  var f: Field = null;
}
sealed abstract class Expression extends RValue
sealed abstract class Literal extends Expression
case class IntLiteral(n: int) extends Literal
case class BoolLiteral(b: boolean) extends Literal
case class NullLiteral extends Literal
case class MaxLockLiteral extends Literal
case class LockBottomLiteral extends Literal
case class VariableExpr(id: String) extends Expression {
  var v: Variable = null
  def this(vr: Variable) = { this(vr.id); v = vr; typ = vr.t.typ }
  def Resolve(vr: Variable) = { v = vr; typ = vr.t.typ }
}
case class Result extends Expression
sealed abstract class ThisExpr extends Expression {
  override def equals(other: Any): Boolean = {
    // needed in autoMagic, which checks for syntactic equality using equals
    other.isInstanceOf[ThisExpr]
  }
}
case class ExplicitThisExpr extends ThisExpr
case class ImplicitThisExpr extends ThisExpr
case class MemberAccess(e: Expression, id: String) extends Expression {
  var isPredicate: Boolean = false;
  var f: Field = null
  var predicate: Predicate = null
}
case class IfThenElse(con: Expression, then: Expression, els: Expression) extends Expression

sealed abstract class PermissionExpr extends Expression {
  def getMemberAccess : MemberAccess
}

case class Access(e: MemberAccess, perm: Option[Expression]) extends PermissionExpr {
  def getMemberAccess = e : MemberAccess;
}
case class RdAccess(e: MemberAccess, perm: Option[Option[Expression]]) extends PermissionExpr {
  def getMemberAccess = e : MemberAccess;
}

case class AccessAll(obj: Expression, perm: Option[Expression]) extends Expression
case class RdAccessAll(obj: Expression, perm: Option[Option[Expression]]) extends Expression

case class Credit(e: Expression, n: Option[Expression]) extends Expression {
  def N = n match { case None => IntLiteral(1) case Some(n) => n }
}

case class Holds(e: Expression) extends Expression
case class RdHolds(e: Expression) extends Expression
case class Assigned(id: String) extends Expression {
  var v: Variable = null
}
case class Old(e: Expression) extends Expression
case class Not(e: Expression) extends Expression
case class FunctionApplication(obj: Expression, id: String, args: List[Expression]) extends Expression {
  var f: Function = null
}
case class Unfolding(pred: PermissionExpr, in: Expression) extends Expression
sealed abstract class BinaryExpr(e0: Expression, e1: Expression) extends Expression {
  def E0 = e0
  def E1 = e1
  def ExpectedLhsType: Class = BoolClass  // sometimes undefined
  def ExpectedRhsType: Class = BoolClass  // sometimes undefined
  val ResultType: Class = BoolClass
  val OpName: String
}
case class Iff(e0: Expression, e1: Expression) extends BinaryExpr(e0,e1) {
  override val OpName = "<==>"
}
case class Implies(e0: Expression, e1: Expression) extends BinaryExpr(e0,e1) {
  override val OpName = "==>"
}
case class And(e0: Expression, e1: Expression) extends BinaryExpr(e0,e1) {
  override val OpName = "&&"
}
case class Or(e0: Expression, e1: Expression) extends BinaryExpr(e0,e1) {
  override val OpName = "||"
}
sealed abstract class ArithmeticExpr(e0: Expression, e1: Expression) extends BinaryExpr(e0,e1) {
  override def ExpectedLhsType = IntClass
  override def ExpectedRhsType = IntClass
  override val ResultType = IntClass
}
case class Plus(e0: Expression, e1: Expression) extends ArithmeticExpr(e0,e1) {
  override val OpName = "+"
}
case class Minus(e0: Expression, e1: Expression) extends ArithmeticExpr(e0,e1) {
  override val OpName = "-"
}
case class Times(e0: Expression, e1: Expression) extends ArithmeticExpr(e0,e1) {
  override val OpName = "*"
}
case class Div(e0: Expression, e1: Expression) extends ArithmeticExpr(e0,e1) {
  override val OpName = "/"
}
case class Mod(e0: Expression, e1: Expression) extends ArithmeticExpr(e0,e1) {
  override val OpName = "%"
}
sealed abstract class CompareExpr(e0: Expression, e1: Expression) extends BinaryExpr(e0,e1) {
  override def ExpectedLhsType = IntClass
  override def ExpectedRhsType = IntClass
}
sealed abstract class EqualityCompareExpr(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override def ExpectedLhsType = throw new Exception("EqualityCompareExpr does not have a single ExpectedArgsType")
  override def ExpectedRhsType = throw new Exception("EqualityCompareExpr does not have a single ExpectedArgsType")
}
case class Eq(e0: Expression, e1: Expression) extends EqualityCompareExpr(e0,e1) {
  override val OpName = "=="
}
case class Neq(e0: Expression, e1: Expression) extends EqualityCompareExpr(e0,e1) {
  override val OpName = "!="
}
case class Less(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override val OpName = "<"
}
case class AtMost(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override val OpName = "<="
}
case class AtLeast(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override val OpName = ">="
}
case class Greater(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override val OpName = ">"
}
case class LockBelow(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override def ExpectedLhsType = throw new Exception("LockBelow does not have a single ExpectedArgsType")
  override def ExpectedRhsType = throw new Exception("LockBelow does not have a single ExpectedArgsType")
  override val OpName = "<<"
}
sealed abstract class Quantification(is: List[String], seq: Expression, e: Expression) extends Expression {
  def Quantor: String; 
  def Is = is
  def Seq = seq
  def E = e
  var variables = null: List[Variable];
}
case class Forall(is: List[String], seq: Expression, e: Expression) extends Quantification(is, seq, e) {
  override def Quantor = "forall"
}

// sequences

case class EmptySeq(t: Type) extends Literal
case class ExplicitSeq(elems: List[Expression]) extends Expression
case class Range(min: Expression, max: Expression /* non-inclusive*/) extends Expression
case class Append(s0: Expression, s1: Expression) extends SeqAccess(s0, s1) {
  override val OpName = "++"
}
 sealed abstract case class SeqAccess(e0: Expression, e1: Expression) extends BinaryExpr(e0, e1)
case class Length(e: Expression) extends Expression
case class At(s: Expression, n: Expression) extends SeqAccess(s, n) {
  override val OpName = "@"
}
case class Drop(s: Expression, n: Expression) extends SeqAccess(s, n) {
  override val OpName = ""
}
case class Take(s: Expression, n: Expression) extends SeqAccess(s, n) {
  override val OpName = ""
}


// eval

case class Eval(h: EvalState, e: Expression) extends Expression
sealed abstract class EvalState {
  def target(): Expression;
}
case class AcquireState(obj: Expression) extends EvalState {
  def target() = obj
}
case class ReleaseState(obj: Expression) extends EvalState {
  def target() = obj
}
case class CallState(token: Expression, obj: Expression, id: String, args: List[Expression]) extends EvalState {
  var m = null: Method;
  def target() = token;
}
