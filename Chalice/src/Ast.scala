//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition
import scala.util.parsing.input.Positional

trait ASTNode extends Positional

/**
 * Classes and types
 */

sealed abstract class TopLevelDecl(val id: String) extends ASTNode

sealed case class Class(classId: String, parameters: List[Class], module: String, members: List[Member]) extends TopLevelDecl(classId) {
  def IsInt: Boolean = false
  def IsBool: Boolean = false
  def IsRef: Boolean = true
  def IsNull: Boolean = false
  def IsMu: Boolean = false
  def IsSeq: Boolean = false
  def IsToken: Boolean = false
  def IsChannel: Boolean = false
  def IsState: Boolean = false
  def IsNormalClass = true
  def IsPermission = false

  lazy val DeclaredFields = members flatMap {case x: Field => List(x); case _ => Nil}
  lazy val MentionableFields = Fields filter {x => ! x.Hidden}
  lazy val MonitorInvariants = members flatMap {case x: MonitorInvariant => List(x); case _ => Nil}
  lazy val Fields:List[Field] = DeclaredFields ++ (if (IsRefinement) refines.Fields else Nil) 

  private lazy val id2member:Map[String,NamedMember] = Map() ++ {
    val named = members flatMap {case x: NamedMember => List(x); case _ => Nil};
    (named map {x => x.Id}) zip named
  }
  def LookupMember(id: String): Option[NamedMember] = {
    if (id2member contains id)
      Some(id2member(id))
    else if (IsRefinement)
      refines.LookupMember(id)         
    else if (IsRef && this != RootClass) {
      // check with root class
      RootClass LookupMember id match {
        case Some(m) if (! m.Hidden) => Some(m)
        case _ => None
      }
    } else
      None
  }
  def FullName: String = if(parameters.isEmpty) id else id + "<" + parameters.tail.foldLeft(parameters.head.FullName){(a, b) => a + ", " + b.FullName} + ">"
  override def toString = FullName

  // Says whether or not to compile the class (compilation ignores external classes)
  var IsExternal = false

  // Refinement extension
  var IsRefinement = false
  var refinesId: String = null
  var refines: Class = null
  lazy val CouplingInvariants = members flatMap {case x: CouplingInvariant => List(x); case _ => Nil}
  lazy val Replaces: List[Field] = CouplingInvariants flatMap (_.fields)
}

sealed case class Channel(channelId: String, parameters: List[Variable], private val rawWhere: Expression) extends TopLevelDecl(channelId) {
  lazy val where: Expression = rawWhere.transform {
    case Epsilon | MethodEpsilon => Some(ChannelEpsilon(None))
    case _ => None
  }
}

sealed case class SeqClass(parameter: Class) extends Class("seq", List(parameter), "default", Nil) {
  override def IsRef = false;
  override def IsSeq = true;
  override def IsNormalClass = false
}
object PermClass extends Class("$Permission", Nil, "default", Nil) {
  override def IsRef = false
  override def IsPermission = true
  override def IsNormalClass = false
}
object IntClass extends Class("int", Nil, "default", Nil) {
  override def IsRef = false
  override def IsInt = true
  override def IsNormalClass = false
}
object BoolClass extends Class("bool", Nil, "default", Nil) {
  override def IsRef = false
  override def IsBool = true
  override def IsNormalClass = false
}
object NullClass extends Class("null", Nil, "default", Nil) {
  override def IsNull = true
  override def IsNormalClass = false
}
object MuClass extends Class("$Mu", Nil, "default", Nil) {
  override def IsRef = false
  override def IsMu = true
  override def IsNormalClass = false
}
case class TokenClass(c: Type, m: String) extends Class("token", Nil, "default", List( 
  new SpecialField("joinable", new Type(BoolClass), false)
))
{
  var method = null: Method
  override def IsRef = true
  override def IsToken = true
  override def IsNormalClass = false
  override def FullName: String = "token<" + c.FullName + "." + m + ">"  
}
case class ChannelClass(ch: Channel) extends Class(ch.id, Nil, "default", Nil) {
  override def IsRef = true
  override def IsChannel = true
  override def IsNormalClass = false
}

object RootClass extends Class("$root", Nil, "default", List(
  new SpecialField("mu", new Type(MuClass), false),
  new SpecialField("held", new Type(BoolClass), true),
  new SpecialField("rdheld", new Type(BoolClass), true)
  ))  // joinable and held are bool in Chalice, but translated into an int in Boogie

sealed case class Type(id: String, params: List[Type]) extends ASTNode {  // denotes the use of a type
  if (id equals "seq") TranslatorPrelude.addComponent(AxiomatizationOfSequencesPL) // include sequence axioms if necessary
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

/**
 * Members 
 */

sealed abstract class Member extends ASTNode {
  val Hidden: Boolean = false  // hidden means not mentionable in source
}
case class MonitorInvariant(private val rawE: Expression) extends Member {
  lazy val e: Expression = rawE.transform {
    case Epsilon | MethodEpsilon => Some(MonitorEpsilon(None))
    case _ => None
  }
}

sealed abstract class NamedMember(id: String) extends Member {
  val Id = id
  var Parent: Class = null
  def FullName = Parent.id + "." + Id
}
case class Field(id: String, typ: Type, isGhost: Boolean) extends NamedMember(id)
case class SpecialField(name: String, tp: Type, hidden: Boolean) extends Field(name, tp, false) {  // direct assignments are not allowed to a SpecialField
  override def FullName = id
  override val Hidden = hidden
}
sealed abstract class Callable(id: String) extends NamedMember(id) {
  def Spec:List[Specification]
  def Body:List[Statement]
  def Ins:List[Variable]
  def Outs:List[Variable]
}
case class Method(id: String, ins: List[Variable], outs: List[Variable], spec: List[Specification], body: List[Statement]) extends Callable(id) {
  override def Spec = spec
  override def Body = body
  override def Ins = ins
  override def Outs = outs
}
case class Predicate(id: String, private val rawDefinition: Expression) extends NamedMember(id) {
  lazy val definition: Expression = rawDefinition.transform {
    case Epsilon | MethodEpsilon => Some(PredicateEpsilon(None))
    case _ => None
  }
}
case class Function(id: String, ins: List[Variable], out: Type, spec: List[Specification], definition: Option[Expression]) extends NamedMember(id) {
  def apply(rec: Expression, args: List[Expression]): FunctionApplication = {
    val result = FunctionApplication(rec, id, args);
    result.f = this;
    result
  }
  var isUnlimited = false
  var isRecursive = false
  var SCC: List[Function] = Nil
}
case class Condition(id: String, where: Option[Expression]) extends NamedMember(id)
case class Variable(id: String, t: Type, isGhost: Boolean, isImmutable: Boolean) extends ASTNode {
  val UniqueName = {
    val n = S_Variable.VariableCount
    S_Variable.VariableCount = S_Variable.VariableCount + 1
    id + "#" + n
  }
  val Id = id;
  def this(name: String, typ: Type) = this(name,typ,false,false);
  override def toString = (if (isGhost) "ghost " else "") + (if (isImmutable) "const " else "var ") + id;
}
object S_Variable { var VariableCount = 0 }
case class SpecialVariable(name: String, typ: Type) extends Variable(name, typ, false, false) {
  override val UniqueName = name
}
sealed abstract class Specification extends ASTNode
case class Precondition(e: Expression) extends Specification
case class Postcondition(e: Expression) extends Specification
case class LockChange(ee: List[Expression]) extends Specification

/**
 * Refinement members
 */

case class CouplingInvariant(ids: List[String], e: Expression) extends Member {
  assert(ids.size > 0)
  var fields = Nil:List[Field]
  /* Distribute 100 between fields */
  def fraction(field: Field) = {
    val k = fields.indexOf(field)
    assert (0 <= k && k < fields.size)
    val part: Int = 100 / fields.size
    if (k == fields.size - 1) IntLiteral(100 - part * k) else IntLiteral(part)          
  }
}
case class MethodTransform(id: String, ins: List[Variable], outs: List[Variable], spec: List[Specification], trans: Transform) extends Callable(id) {
  var refines = null: Callable
  var body = null:List[Statement]
  def Spec = {assert(refines != null); refines.Spec ++ spec}
  def Body = {
    assert(body != null);
    // make sure the body appears as if it is from a normal method
    def concretize(ss: List[Statement]): List[Statement] = ss flatMap {
      case r @ RefinementBlock(con, abs) =>
        con :::
        (for ((a,c) <- (r.during._1 zip r.during._2)) yield LocalVar(a, Some(new VariableExpr(c))))
      case BlockStmt(ss) => List(BlockStmt(concretize(ss)))
      case IfStmt(guard, BlockStmt(thn), None) => List(IfStmt(guard, BlockStmt(concretize(thn)), None))
      case IfStmt(guard, BlockStmt(thn), Some(els)) => List(IfStmt(guard, BlockStmt(concretize(thn)), Some(BlockStmt(concretize(List(els))))))
      case WhileStmt(guard, oi, ni, lks, BlockStmt(ss)) => List(WhileStmt(guard, oi ++ ni, Nil, lks, BlockStmt(concretize(ss))))
      case s => List(s)
    }
    concretize(body)
  }
  def Ins = {assert(refines != null); refines.Ins}
  def Outs = {assert(refines != null); refines.Outs ++ outs.drop(refines.Outs.size)}
}

sealed abstract class Transform extends ASTNode
/** Pattern matching within a block (zero or more) over deterministic statements */
case class BlockPat() extends Transform {
  def matches(s: Statement) = s match {
    case _:Assert => true
    case _:Assume => true
    case _:Assign => true
    case _:FieldUpdate => true
    case _:LocalVar => true
    case _ => false
  }
}
/** Matches any block of code (greedily) and acts as identity */
case class SkipPat() extends Transform
/** Replacement pattern for arbitrary block */
case class ProgramPat(code: List[Statement]) extends Transform {
  if (code.size > 0) pos = code.head.pos
}
case class IfPat(thn: Transform, els: Option[Transform]) extends Transform
case class WhilePat(invs: List[Expression], body: Transform) extends Transform
case class NonDetPat(is: List[String], code: List[Statement]) extends Transform {
  def matches(s: Statement) = s match {
    case _:Call => true
    case _:SpecStmt => true
    case _ => false
  }
}
case class InsertPat(code: List[Statement]) extends Transform
case class SeqPat(pats: List[Transform]) extends Transform {
  assert(pats.size > 0)
  pos = pats.head.pos;
}
case class RefinementBlock(con: List[Statement], abs: List[Statement]) extends Statement {
  if (con.size > 0) pos = con.head.pos
  // local variables in context at the beginning of the block
  var before: List[Variable] = null
  // shared declared local variables (mapping between abstract and concrete)
  lazy val during: (List[Variable], List[Variable]) = {
    val a = for (v <- abs.flatMap(s => s.Declares)) yield v;
    val c = for (v <- a) yield con.flatMap(s => s.Declares).find(_ == v).get
    (a,c)
  }         
  override def Declares = con flatMap {_.Declares}
  override def Targets = (con ++ abs :\ Set[Variable]()) { (s, vars) => vars ++ s.Targets}
}

/**
 * Statements
 */

sealed abstract class Statement extends ASTNode {
  def Declares: List[Variable] = Nil // call after resolution
  def Targets: Set[Variable] = Set() // assigned local variables
}
case class Assert(e: Expression) extends Statement
case class Assume(e: Expression) extends Statement
case class BlockStmt(ss: List[Statement]) extends Statement {
  override def Targets = (ss :\ Set[Variable]()) { (s, vars) => vars ++ s.Targets}
}
case class IfStmt(guard: Expression, thn: BlockStmt, els: Option[Statement]) extends Statement {
  override def Targets = thn.Targets ++ (els match {case None => Set(); case Some(els) => els.Targets})
}
case class WhileStmt(guard: Expression,
                     oldInvs: List[Expression], newInvs: List[Expression], lkch: List[Expression], 
                     body: BlockStmt) extends Statement {
  val Invs = oldInvs ++ newInvs
  var LoopTargets: List[Variable] = Nil
  override def Targets = body.Targets
}
case class Assign(lhs: VariableExpr, rhs: RValue) extends Statement {
  override def Targets = if (lhs.v != null) Set(lhs.v) else Set()
}
case class FieldUpdate(lhs: MemberAccess, rhs: RValue) extends Statement
case class LocalVar(v: Variable, rhs: Option[RValue]) extends Statement {
  override def Declares = List(v)
  override def Targets = rhs match {case None => Set(); case Some(_) => Set(v)}
}
case class Call(declaresLocal: List[Boolean], lhs: List[VariableExpr], obj: Expression, id: String, args: List[Expression]) extends Statement {
  var locals = List[Variable]()
  var m: Callable = null
  override def Declares = locals
  override def Targets = (lhs :\ Set[Variable]()) { (ve, vars) => if (ve.v != null) vars + ve.v else vars }
}
case class SpecStmt(lhs: List[VariableExpr], locals:List[Variable], pre: Expression, post: Expression) extends Statement {
  override def Declares = locals
  override def Targets = (lhs :\ Set[Variable]()) { (ve, vars) => if (ve.v != null) vars + ve.v else vars }
}
case class Install(obj: Expression, lowerBounds: List[Expression], upperBounds: List[Expression]) extends Statement
case class Share(obj: Expression, lowerBounds: List[Expression], upperBounds: List[Expression]) extends Statement
case class Unshare(obj: Expression) extends Statement
case class Acquire(obj: Expression) extends Statement
case class Release(obj: Expression) extends Statement
case class RdAcquire(obj: Expression) extends Statement
case class RdRelease(obj: Expression) extends Statement
case class Downgrade(obj: Expression) extends Statement
case class Lock(obj: Expression, b: BlockStmt, rdLock: Boolean) extends Statement
case class Free(obj: Expression) extends Statement
case class CallAsync(declaresLocal: Boolean, lhs: VariableExpr, obj: Expression, id: String, args: List[Expression]) extends Statement {
  var local: Variable = null
  var m: Method = null
  override def Declares = if (local != null) List(local) else Nil
  override def Targets = if (lhs != null && lhs.v != null) Set(lhs.v) else Set()
}
case class JoinAsync(lhs: List[VariableExpr], token: Expression) extends Statement {
  var m: Method = null
}
case class Wait(obj: Expression, id: String) extends Statement {
  var c: Condition = null
}
case class Signal(obj: Expression, id: String, all: Boolean) extends Statement {
  var c: Condition = null
}
case class Send(ch: Expression, args: List[Expression]) extends Statement {
}
case class Receive(declaresLocal: List[Boolean], ch: Expression, outs: List[VariableExpr]) extends Statement {
  var locals = List[Variable]()
  override def Declares = locals
}
case class Fold(pred: Access) extends Statement
case class Unfold(pred: Access) extends Statement

/**
 * Expressions
 */

sealed abstract class RValue extends ASTNode {
  var typ: Class = null
}
case class NewRhs(id: String, initialization: List[Init], lowerBounds: List[Expression], upperBounds: List[Expression]) extends RValue
case class Init(id: String, e: Expression) extends ASTNode {
  var f: Field = null;
}
sealed abstract class Expression extends RValue {
  def transform(f: Expression => Option[Expression]) = AST.transform(this, f)
  def visit(f: RValue => Unit) = AST.visit(this, f)
}
sealed abstract class Literal extends Expression
case class IntLiteral(n: Int) extends Literal
case class BoolLiteral(b: Boolean) extends Literal
case class NullLiteral() extends Literal
case class MaxLockLiteral() extends Literal
case class LockBottomLiteral() extends Literal
case class VariableExpr(id: String) extends Expression {
  var v: Variable = null
  def this(vr: Variable) = { this(vr.id); v = vr; typ = vr.t.typ }
  def Resolve(vr: Variable) = { v = vr; typ = vr.t.typ }
}
case class Result() extends Expression
sealed abstract class ThisExpr extends Expression
case class ExplicitThisExpr() extends ThisExpr {
  override def hashCode = 0
  override def equals(other: Any) = other.isInstanceOf[ThisExpr]
}
case class ImplicitThisExpr() extends ThisExpr {
  override def hashCode = 0
  override def equals(other: Any) = other.isInstanceOf[ThisExpr]  
}
case class MemberAccess(e: Expression, id: String) extends Expression {
  var isPredicate: Boolean = false
  var f: Field = null
  var predicate: Predicate = null
}
case class IfThenElse(con: Expression, then: Expression, els: Expression) extends Expression

object PermissionType extends Enumeration {
  type PermissionType = Value
  val Fraction, Epsilons, Mixed = Value
}
import PermissionType._
sealed abstract class Permission extends Expression {
  typ = PermClass
  def permissionType: PermissionType
}
sealed abstract class Write extends Permission {
  override def permissionType = PermissionType.Fraction
}
object Full extends Write                // None
case class Frac(n: Expression) extends Write // Some(n)
sealed abstract class Read extends Permission {
  override def permissionType = PermissionType.Epsilons
}
object Epsilon extends Write                      // None
// we use Option for the argument of the next three classes as follows:
// the argument is Some(_) if the exression originates from the user (e.g. if he used acc(x,rd(monitor))),
// and None otherwise. If Some(_) is used, we have additional checks to ensure that we have read access
// to _ and _ is not null.
case class PredicateEpsilon(predicate: Option[Expression]) extends Write
case class MonitorEpsilon(monitor: Option[Expression]) extends Write
case class ChannelEpsilon(channel: Option[Expression]) extends Write
object MethodEpsilon extends Write
case class ForkEpsilon(token: Expression) extends Write
object Star extends Write               // Some(None)
case class Epsilons(n: Expression) extends Read   // Some(Some(n))

sealed abstract class ArithmeticPermission extends Permission
case class PermTimes(val lhs: Permission, val rhs: Permission) extends ArithmeticPermission {
  override def permissionType = {
    if (lhs.permissionType == rhs.permissionType) lhs.permissionType
    else Mixed
  }
}
case class IntPermTimes(val lhs: Expression, val rhs: Permission) extends ArithmeticPermission {
  override def permissionType = rhs.permissionType
}
case class PermPlus(val lhs: Permission, val rhs: Permission) extends ArithmeticPermission {
  override def permissionType = {
    if (lhs.permissionType == rhs.permissionType) lhs.permissionType
    else Mixed
  }
}
case class PermMinus(val lhs: Permission, val rhs: Permission) extends ArithmeticPermission {
  override def permissionType = {
    if (lhs.permissionType == rhs.permissionType) lhs.permissionType
    else Mixed
  }
}


sealed abstract class PermissionExpr(perm: Permission) extends Expression
sealed abstract class WildCardPermission(perm: Permission) extends PermissionExpr(perm)
case class Access(ma: MemberAccess, var perm: Permission) extends PermissionExpr(perm) 
case class AccessAll(obj: Expression, var perm: Permission) extends WildCardPermission(perm)
case class AccessSeq(s: Expression, f: Option[MemberAccess], var perm: Permission) extends WildCardPermission(perm)

case class Credit(e: Expression, n: Option[Expression]) extends Expression {
  val N = n match { case None => IntLiteral(1) case Some(n) => n }
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
case class Unfolding(pred: Access, in: Expression) extends Expression
sealed abstract class BinaryExpr(e0: Expression, e1: Expression) extends Expression {
  val E0 = e0
  val E1 = e1
  val ExpectedLhsType: Class = BoolClass  // sometimes undefined
  val ExpectedRhsType: Class = BoolClass  // sometimes undefined
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
  override val ExpectedLhsType = IntClass
  override val ExpectedRhsType = IntClass
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
  override val ExpectedLhsType = IntClass
  override val ExpectedRhsType = IntClass
}
sealed abstract class EqualityCompareExpr(e0: Expression, e1: Expression) extends CompareExpr(e0,e1) {
  override val ExpectedLhsType = null;
  override val ExpectedRhsType = null;
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
  override val ExpectedLhsType = null;
  override val ExpectedRhsType = null;
  override val OpName = "<<"
}

/**
 * Expressions: quantifiers
 */

trait Quant
object Forall extends Quant
object Exists extends Quant

sealed abstract class Quantification(q: Quant, is: List[String], e: Expression) extends Expression {
  val Q = q;
  val Is = is;
  val E = e;
  var variables = null: List[Variable]; // resolved by type checker
}
case class SeqQuantification(q: Quant, is: List[String], seq: Expression, e: Expression) extends Quantification(q, is, e) {
  TranslatorPrelude.addComponent(AxiomatizationOfSequencesPL) // include sequence axioms if necessary
}
// The minmax field stores the minimum and maximum of a range if the TypeQuantification originates from
// a SeqQuantification (e.g. from "forall i in [0..2] :: ..". This is later needed in isDefined to
// assert that min <= max
case class TypeQuantification(q: Quant, is: List[String], t: Type, e: Expression, minmax: (Expression, Expression)) extends Quantification(q, is, e) {
  def this(q: Quant, is: List[String], t: Type, e: Expression) = this(q, is, t, e, null)
}

/**
 * Expressions: sequences
 */

case class EmptySeq(t: Type) extends Literal
case class ExplicitSeq(elems: List[Expression]) extends Expression
case class Range(min: Expression, max: Expression /* non-inclusive*/) extends Expression
case class Append(s0: Expression, s1: Expression) extends SeqAccess(s0, s1) {
  override val OpName = "++"
}
sealed abstract class SeqAccess(e0: Expression, e1: Expression) extends BinaryExpr(e0, e1) {
  override val ExpectedLhsType = null
  override val ExpectedRhsType = null
  override val ResultType = null
}
case class Length(e: Expression) extends Expression
case class At(s: Expression, n: Expression) extends SeqAccess(s, n) {
  override val OpName = ""
}
case class Drop(s: Expression, n: Expression) extends SeqAccess(s, n) {
  override val OpName = ""
}
case class Take(s: Expression, n: Expression) extends SeqAccess(s, n) {
  override val OpName = ""
}
case class Contains(n: Expression, s: Expression) extends SeqAccess(n, s) {
  override val OpName = "in"
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

/**
 * AST operations
 */

object AST {
  /**
   * Flattens sequences of transforms and merges consecutive block patterns
   */
  def normalize(trans: Transform): Transform = trans match {
    case IfPat(thn, Some(els)) => IfPat(normalize(thn), Some(normalize(els)))
    case IfPat(thn, None) => IfPat(normalize(thn), None)
    case SeqPat(pats) =>
      val rec = pats flatMap {pat => normalize(pat) match {
        case SeqPat(pats) => pats;
        case x => List(x)
      }}
      def noTwoBlocks: List[Transform] => List[Transform] = {
        case BlockPat() :: (bp @ BlockPat()) :: l => noTwoBlocks(bp :: l)
        case x :: l => x :: noTwoBlocks(l)
        case Nil => Nil
      }
      SeqPat(noTwoBlocks(rec))
    case _ => trans
  }

  sealed abstract class TransformMatch
  case class Matched(ss: List[Statement]) extends TransformMatch {
    def this(s: Statement) = this(List(s))
  }
  case class Unmatched(t: Transform) extends TransformMatch

  /**
   * Matches a proper block to a transform.
   * Effects: some statements might be replaced by refinements blocks; Loops might have new invariants.
   * Requires: transform is normalized
   */
  def refine:(List[Statement], Transform) => TransformMatch = {
    // order is important!
    // reduction of base cases
    case (l, SeqPat(List(t))) => refine(l, t)
    case (List(BlockStmt(ss)), t) => refine(ss, t)
    // whole program 
    case (l, ProgramPat(code)) => new Matched(RefinementBlock(code, l))
    case (l, SkipPat()) => Matched(l)    
    // if pattern
    case (List(IfStmt(guard, thn, None)), t @ IfPat(thnT, None)) =>
      refine(thn.ss, thnT) match {
        case Matched(thn0) => new Matched(IfStmt(guard, BlockStmt(thn0), None))
        case _ => Unmatched(t)
      }
    case (List(IfStmt(guard, thn, Some(els))), t @ IfPat(thnT, Some(elsT))) =>
      (refine(thn.ss, thnT), refine(List(els), elsT)) match {
        case (Matched(thn0), Matched(els0)) => new Matched(IfStmt(guard, BlockStmt(thn0), Some(BlockStmt(els0))))
        case _ => Unmatched(t)
      }
    // while pattern
    case (List(WhileStmt(guard, oi, Nil, lks, body)), wp @ WhilePat(l, t)) =>
      refine(body.ss, t) match {
        case Matched(body0) => new Matched(WhileStmt(guard, oi, l, lks, BlockStmt(body0)))
        case _ => Unmatched(wp)
      }
    // non det pat
    case (l @ List(_: Call), NonDetPat(_, code)) => new Matched(RefinementBlock(code, l))
    case (l @ List(_: SpecStmt), NonDetPat(_, code)) => new Matched(RefinementBlock(code, l))
    // insert pat
    case (Nil, InsertPat(code)) => new Matched(RefinementBlock(code, Nil))
    // block pattern (greedy matching)
    case (l, bp @ BlockPat()) if (l forall {s => bp matches s}) => Matched(l)
    case (s :: ss, t @ SeqPat((bp @ BlockPat()) :: _)) if (bp matches s) =>
      refine(ss, t) match {
        case Matched(l) => Matched(s :: l)
        case x => x
      }
    case (l, SeqPat((bp @ BlockPat()) :: ts)) if (l.size == 0 || !(bp matches l.head)) =>
      refine(l, SeqPat(ts))
    // sequence pattern
    case (s :: ss, SeqPat((np: NonDetPat) :: ts)) =>
      (refine(List(s), np), refine(ss, SeqPat(ts))) match {
        case (Matched(a), Matched(b)) => Matched(a ::: b)
        case _ => Unmatched(np)
      }
    case (s :: ss, SeqPat((ip: IfPat) :: ts)) =>
      (refine(List(s), ip), refine(ss, SeqPat(ts))) match {
        case (Matched(a), Matched(b)) => Matched(a ::: b)
        case _ => Unmatched(ip)
      }
    case (l, SeqPat(InsertPat(code) :: ts)) =>
      refine(l, SeqPat(ts)) match {
        case Matched(a) => Matched(RefinementBlock(code, Nil) :: a)
        case x => x
      }
    case (s :: ss, SeqPat((wp: WhilePat) :: ts)) =>
      (refine(List(s), wp), refine(ss, SeqPat(ts))) match {
        case (Matched(a), Matched(b)) => Matched(a ::: b)
        case _ => Unmatched(wp)
      }
    case (_, t) => Unmatched(t)
  }

  /**
   * Transforms an expression using f. f must produce expressions of the appropriate type (e.g. not replace int literal with a bool literal)
   * Ensures that mutable fields of expressions are carried over. f must make sure that mutable fields of its value are filled in.
   */
  def transform(expr: Expression, f: Expression => Option[Expression]):Expression = {
    val func = (e:Expression) => transform(e, f);
    val x = f(expr);
    // apply recursively
    val result = if (x isDefined) x.get else expr match {
      case _:Literal => expr
      case _:ThisExpr => expr
      case _:Result => expr
      case _:VariableExpr => expr
      case ma@MemberAccess(e, id) =>
        val g = MemberAccess(func(e), id);
        g.f = ma.f;
        g.predicate = ma.predicate;
        g.isPredicate = ma.isPredicate;
        g
      case ForkEpsilon(token) => ForkEpsilon(func(token))
      case MonitorEpsilon(Some(monitor)) => MonitorEpsilon(Some(func(monitor)))
      case ChannelEpsilon(Some(channel)) => ChannelEpsilon(Some(func(channel)))
      case PredicateEpsilon(Some(predicate)) => PredicateEpsilon(Some(func(predicate)))
      case ChannelEpsilon(None) | MonitorEpsilon(None) | PredicateEpsilon(None) => expr
      case Full | Star | Epsilon | MethodEpsilon => expr
      case Frac(perm) => Frac(func(perm))
      case Epsilons(perm) => Epsilons(func(perm))
      case PermTimes(lhs, rhs) => PermTimes(func(lhs).asInstanceOf[Permission], func(rhs).asInstanceOf[Permission])
      case IntPermTimes(lhs, rhs) => IntPermTimes(func(lhs), func(rhs).asInstanceOf[Permission])
      case PermPlus(lhs, rhs) => PermPlus(func(lhs).asInstanceOf[Permission], func(rhs).asInstanceOf[Permission])
      case PermMinus(lhs, rhs) => PermMinus(func(lhs).asInstanceOf[Permission], func(rhs).asInstanceOf[Permission])
      case Access(e, perm) => Access(func(e).asInstanceOf[MemberAccess], func(perm).asInstanceOf[Permission]);
      case AccessAll(obj, perm) => AccessAll(func(obj), func(perm).asInstanceOf[Permission]);
      case AccessSeq(s, None, perm) => AccessSeq(func(s), None, func(perm).asInstanceOf[Permission])
      case AccessSeq(s, Some(f), perm) => AccessSeq(func(s), Some(func(f).asInstanceOf[MemberAccess]), func(perm).asInstanceOf[Permission])
      case Credit(e, None) => Credit(func(e), None)
      case Credit(e, Some(n)) => Credit(func(e), Some(func(n)))
      case Holds(e) => Holds(func(e))
      case RdHolds(e) => RdHolds(func(e))
      case _: Assigned => expr
      case Old(e) => Old(func(e))
      case IfThenElse(con, then, els) => IfThenElse(func(con), func(then), func(els))
      case Not(e) => Not(func(e))
      case funapp@FunctionApplication(obj, id, args) =>
        val appl = FunctionApplication(func(obj), id, args map { arg => func(arg)});
        appl.f = funapp.f;
        appl
      case Unfolding(pred, e) =>
        Unfolding(func(pred).asInstanceOf[Access], func(e))
      case Iff(e0,e1) => Iff(func(e0), func(e1))
      case Implies(e0,e1) => Implies(func(e0), func(e1))
      case And(e0,e1) => And(func(e0), func(e1))
      case Or(e0,e1) => Or(func(e0), func(e1))
      case Eq(e0,e1) => Eq(func(e0), func(e1))
      case Neq(e0,e1) => Neq(func(e0), func(e1))
      case Less(e0,e1) => Less(func(e0), func(e1))
      case AtMost(e0,e1) => AtMost(func(e0), func(e1))
      case AtLeast(e0,e1) => AtLeast(func(e0), func(e1))
      case Greater(e0,e1) => Greater(func(e0), func(e1))
      case LockBelow(e0,e1) => LockBelow(func(e0), func(e1))
      case Plus(e0,e1) => Plus(func(e0), func(e1))
      case Minus(e0,e1) => Minus(func(e0), func(e1))
      case Times(e0,e1) => Times(func(e0), func(e1))
      case Div(e0,e1) => Div(func(e0), func(e1))
      case Mod(e0,e1) => Mod(func(e0), func(e1))
      case ExplicitSeq(es) => ExplicitSeq(es map { e => func(e) })
      case Range(min, max)=> Range(func(min), func(max))
      case Append(e0, e1) => Append(func(e0), func(e1))
      case At(e0, e1) => At(func(e0), func(e1))
      case Drop(e0, e1) => Drop(func(e0), func(e1))
      case Take(e0, e1) => Take(func(e0), func(e1))
      case Length(e) => Length(func(e))
      case Contains(e0, e1) => Contains(func(e0), func(e1))
      case qe @ SeqQuantification(q, is, seq, e) =>
        val result = SeqQuantification(q, is, func(seq), func(e));
        result.variables = qe.variables;
        result;
      case qe @ TypeQuantification(q, is, t, e, (min, max)) =>
        val result = TypeQuantification(q, is, t, func(e), (func(min),func(max)));
        result.variables = qe.variables;
        result;
      case qe @ TypeQuantification(q, is, t, e, null) =>
        val result = new TypeQuantification(q, is, t, func(e));
        result.variables = qe.variables;
        result;
      case Eval(h, e) =>
        Eval(h match {
          case AcquireState(obj) => AcquireState(func(obj))
          case ReleaseState(obj) => ReleaseState(func(obj))
          case cs @ CallState(token, obj, i, args) =>
            val result = CallState(func(token), func(obj), i, args map { a => func(a)});
            result.m = cs.m;
            result;
        }, func(e))
    };
    
    // preserve type
    if (result.typ == null) result.typ = expr.typ;
    // preserve position
    if (result.pos == NoPosition) result.pos = expr.pos
    result
  }

  // Applies recursively the function f first to the expression and then to its subexpressions (that is members of type RValue)  
  def visit(expr: RValue, f: RValue => Unit) {
    f(expr);
    expr match {
     case _:Literal => ;
     case _:ThisExpr => ;
     case _:Result => ;
     case _:VariableExpr => ;
     case MemberAccess(e, _) =>
       visit(e, f);

     case Frac(p) => visit(p, f);
     case Epsilons(p) => visit(p, f);
     case Full | Epsilon | Star | MethodEpsilon =>;
     case ChannelEpsilon(None) | PredicateEpsilon(None) | MonitorEpsilon(None) =>;
     case ChannelEpsilon(Some(e)) => visit(e, f);
     case PredicateEpsilon(Some(e)) => visit(e, f);
     case MonitorEpsilon(Some(e)) => visit(e, f);
     case ForkEpsilon(tk) => visit(tk, f);
     case IntPermTimes(n, p) =>
       visit(n, f); visit(p, f);
     case PermTimes(e0, e1) =>
       visit(e0, f); visit(e1, f);
     case PermPlus(e0, e1) =>
       visit(e0, f); visit(e1, f);
     case PermMinus(e0, e1) =>
       visit(e0, f); visit(e1, f);
     case Access(e, perm) =>
       visit(e, f); visit(perm, f);
     case AccessAll(obj, perm) =>
       visit(obj, f); visit(perm, f);
     case AccessSeq(s, _, perm) =>
       visit(s, f); visit(perm, f);

     case Credit(e, n) =>
       visit(e, f); n match { case Some(n) => visit(n, f); case _ => }
     case Holds(e) => visit(e, f);
     case RdHolds(e) => visit(e, f);

     case e: BinaryExpr =>
       visit(e.E0, f); visit(e.E1, f);
     case Range(min, max) =>
       visit(min, f); visit(max, f);
     case e: Assigned => e
     case Old(e) => visit(e, f);
     case IfThenElse(con, then, els) => visit(con, f); visit(then, f); visit(els, f);
     case Not(e) => visit(e, f);
     case funapp@FunctionApplication(obj, id, args) =>
       visit(obj, f); args foreach { arg => visit(arg, f) };
     case Unfolding(pred, e) =>
       visit(pred, f); visit(e, f);

     case SeqQuantification(_, _, seq, e) => visit(seq, f); visit(e, f);
     case TypeQuantification(_, _, _, e, (min,max)) => visit(e, f); visit(min, f); visit(max, f);
     case TypeQuantification(_, _, _, e, _) => visit(e, f);
     case ExplicitSeq(es) =>
       es foreach { e => visit(e, f) }
     case Length(e) =>
       visit(e, f)
     case Eval(h, e) =>
       h match {
         case AcquireState(obj) => visit(obj, f);
         case ReleaseState(obj) => visit(obj, f);
         case CallState(token, obj, id, args) =>
           visit(token, f); visit(obj, f); args foreach {a : Expression => visit(a, f)};
       }
       visit(e, f);
     case NewRhs(_, init, lowerBounds, upperBounds) =>
       lowerBounds foreach { e => visit(e, f)};
       upperBounds foreach { e => visit(e, f)};
   }
 }
}