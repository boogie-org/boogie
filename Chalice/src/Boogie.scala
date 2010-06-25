//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

object Boogie {
 
 sealed abstract class Decl
 case class Const(id: String, unique: boolean, t: BType) extends Decl
 case class Proc(id: String, ins: List[BVar], outs: List[BVar],
                 mod: List[String], PrePost: List[String],
                 body: List[Stmt]) extends Decl
 case class Function(id: String, ins: List[BVar], out: BVar) extends Decl
 case class Axiom(expr: Expr) extends Decl

 sealed abstract class BType
 case class NamedType(s: String) extends BType
 case class ClassType(cl: Class) extends BType
 case class IndexedType(id: String, t: BType) extends BType

 sealed abstract class Stmt {
   def Locals = List[BVar]()
 }
 case class Comment(comment: String) extends Stmt
 case class Assert(e: Expr) extends Stmt {
   def this(e: Expr, p: Position, txt: String) = { this(e); this.pos = p; this.message = txt; this } 
   var pos = NoPosition : Position
   var message = "" : String
 }
 case class Assume(e: Expr) extends Stmt
 case class Assign(lhs: Expr, rhs: Expr) extends Stmt
 case class AssignMap(lhs: Expr, index: Expr, rhs: Expr) extends Stmt
 case class Havoc(x: Expr) extends Stmt
 case class MapUpdate(map: Expr, arg0: Expr, arg1: String, rhs: Expr) extends Stmt {
   def this(map: Expr, arg0: Expr, rhs: Expr) = this(map, arg0, null, rhs)
 }
 case class If(guard: Expr, thn: List[Stmt], els: List[Stmt]) extends Stmt {
   override def Locals = (thn flatMap (_.Locals)) ::: (els flatMap (_.Locals))
 }
 case class LocalVar(x: BVar) extends Stmt {
   def this(id: String, tp: BType) = this(BVar(id, tp))

   override def Locals = List(x)
 }

 sealed abstract class Expr {
   def &&(that: Expr) = BinaryExpr("&&", this, that)
   def ||(that: Expr) = BinaryExpr("||", this, that)
   def ==@(that: Expr) = BinaryExpr("==", this, that)
   def !=@(that: Expr) = BinaryExpr("!=", this, that)
   def Equals(that: Expr) = BinaryExpr("==", this, that)
   def ==>(that: Expr) = BinaryExpr("==>", this, that)
   def <==>(that: Expr) = BinaryExpr("<==>", this, that)
   def unary_! = UnaryExpr("!", this)
   def <=(that: Expr) = BinaryExpr("<=", this, that)
   def <(that: Expr) = BinaryExpr("<", this, that)
   def >=(that: Expr) = BinaryExpr(">=", this, that)
   def >(that: Expr) = BinaryExpr(">", this, that)
   def +(that: Expr) = BinaryExpr("+", this, that)
   def -(that: Expr) = BinaryExpr("-", this, that)
   def *(that: Expr) = BinaryExpr("*", this, that)
   def /(that: Expr) = BinaryExpr("/", this, that)
   def %(that: Expr) = BinaryExpr("%", this, that)
   def := (that: Expr) = Assign(this, that)
   def select(e: Expr, f: Expr) = new MapSelect(this, e, PrintExpr(f))
   def store(e: Expr, f: Expr, rhs: Expr) = MapUpdate(this, e, PrintExpr(f), rhs)
 }
 case class IntLiteral(n: int) extends Expr
 case class BoolLiteral(b: boolean) extends Expr
 case class Null extends Expr
 case class VarExpr(id: String) extends Expr {
   def this(v: BVar) = this(v.id)
 }
 case class MapSelect(map: Expr, arg0: Expr, arg1: String) extends Expr {
   def this(map: Expr, arg0: Expr) = this(map, arg0, null) // for one-dimensional maps
   def this(map: Expr, arg0: Expr, arg1: String, arg2: String) = // for 3-dimensional maps
     this(MapSelect(map, arg0, arg1), VarExpr(arg2), null)
 }
 case class MapStore(map: Expr, arg0: String, rhs: Expr) extends Expr
 case class Old(e: Expr) extends Expr
 case class UnaryExpr(op: String, e: Expr) extends Expr
 case class BinaryExpr(op: String, e0: Expr, e1: Expr) extends Expr
 case class FunctionApp(f: String, args: List[Expr]) extends Expr {
   def this(f: String, a0: Expr) = this(f, List(a0))
   def this(f: String, a0: Expr, a1: Expr) = this(f, List(a0, a1))
   def this(f: String, a0: Expr, a1: Expr, a2: Expr) = this(f, List(a0, a1, a2))
 }
 case class Forall(ta: List[TVar], xs: List[BVar], triggers: List[Expr], body: Expr) extends Expr {
   def this(xs: List[BVar], triggers: List[Expr], body: Expr) = this(List(), xs, triggers, body)
   def this(x: BVar, body: Expr) = this(List(), List(x), List(), body)
   def this(t: TVar, x: BVar, body: Expr) = this(List(t), List(x), List(), body)
 }
 case class Exists(xs: List[BVar], triggers: List[Expr], body: Expr) extends Expr {
   def this(x: BVar, body: Expr) = this(List(x), List(), body)
 }
 case class Ite(con: Expr, then: Expr, els: Expr) extends Expr

 case class BVar(id: String, t: BType) {
   def this(id: String, t: BType, uniquifyName: boolean) =
     this(if (uniquifyName) {
            val n = S_BVar.VariableCount
            S_BVar.VariableCount = S_BVar.VariableCount + 1
            id + "#_" + n
          } else {
            id
          }, t)
   val where: Expr = null
 }
 object S_BVar { var VariableCount = 0 }
 def NewBVar(id: String, t: BType, uniquifyName: boolean) = {
   val v = new Boogie.BVar(id, t, uniquifyName)
   val e = new Boogie.VarExpr(v)
   (v,e)
 }
 case class TVar(id: String) {
   def this(id: String, uniquifyName: boolean) =
     this(if (uniquifyName) {
            val n = S_TVar.VariableCount
            S_TVar.VariableCount = S_TVar.VariableCount + 1
            id + "#_" + n
          } else {
            id
          })
   val where: Expr = null
 }
 object S_TVar { var VariableCount = 0 }
 def NewTVar(id: String) = {
   val v = new Boogie.TVar(id, true)
   val e = new Boogie.NamedType(v.id)
   (v,e)
 }

 var vsMode = false;  // global variable settable from outside the class (non-ideal design)

 // def out(s: String) = Console.out.print(s)
 var indentLevel = 1
 def indent: String = {
   def doIndent(i: int): String = {
     if(i==0) { "" } else { "  " + doIndent(i-1) }
   }
   doIndent(indentLevel);
 }

 def IndentMore(what: => String) = {
   val prev = indentLevel
   indentLevel = indentLevel + 1
   val result = what
   indentLevel = prev
   result
 }
 def nl = System.getProperty("line.separator");
 
 def Print[T](list: List[T], sep: String, p: T => String): String = list match {
   case Nil => ""
   case x :: Nil => p(x)
   case x :: xs => p(x) + sep + Print(xs, sep, p)
 }
 def PrintType(t: BType): String = t match {
   case nt@ NamedType(s) =>
     s
   case ClassType(cl) =>
     if (cl.IsRef) "ref" else cl.id
   case IndexedType(id,t) =>
     id + " (" + PrintType(t) + ")"
 }
 def Print(d: Decl): String = d match {
   case Const(id, u, t) =>
     "const " + (if (u) "unique " else "" ) + id + ": " + PrintType(t) + ";" + nl
   case p: Proc =>
     "procedure " + p.id +
     "(" + Print(p.ins, ", ", PrintVar) + ")" +
     " returns (" + Print(p.outs, ", ", PrintVar) + ")" + nl + 
     (p.mod match {
       case Nil => ""
       case x :: xs =>
         indent +  "modifies " +
         Print(p.mod, ", ", { s: String => s }) +
         ";" + nl
     }) + 
     Print(p.PrePost, nl, { spec: String => indent + spec }) + nl +
     "{" + nl + 
     Print(p.body flatMap (_.Locals), "", { v:BVar => indent + "var " + PrintVar(v) + ";" + nl}) + 
     Print(p.body, "", PrintStmt) + 
     "}" + nl
   case Function(id, ins, out) =>
     "function " + id + "(" + Print(ins, ", ", PrintVar) + ") returns (" + PrintVar(out) + ");" + nl
   case Axiom(e) =>
     "axiom " + PrintExpr(e) + ";" + nl
 }
 def PrintVar(v: BVar): String = {
   v.id + ": " + PrintType(v.t) +
   (if (v.where != null) {" where " + PrintExpr(v.where) } else { "" })
 }
 def PrintStmt(s: Stmt): String = s match {
   case Comment(msg) => indent +  "// " +  msg + nl
   case assert@Assert(e) =>
     val pos = if (vsMode) {
       val r = assert.pos.line - 1;
       val c = assert.pos.column - 1;
       r + "," + c + "," + r + "," + (c+5) + ":"
     } else {
       "  " + assert.pos + ": "
     }
     indent +  "assert " + "{:msg \"" + pos + assert.message + "\"}" + " " + PrintExpr(e) + ";" + nl
   case Assume(e) => indent + "assume " + PrintExpr(e) +  ";" + nl
   case If(guard, thn, els) =>
     indent + "if (" +
     (if (guard == null) "*" else PrintExpr(guard)) +
     ") {" +  nl + 
     IndentMore { Print(thn, "", PrintStmt)  } + 
     indent +  "} else {"  + nl + 
     IndentMore { Print(els, "", PrintStmt)  } + 
     indent + "}" + nl
   case Assign(lhs, rhs) =>
     indent + PrintExpr(lhs) + " := " + PrintExpr(rhs) + ";" + nl
   case AssignMap(lhs, index, rhs) =>
     indent + PrintExpr(lhs) + "[" + PrintExpr(index) + "] := " + PrintExpr(rhs) + ";" + nl
   case Havoc(lhs) =>
     indent + "havoc " + PrintExpr(lhs) + ";" + nl
   case MapUpdate(map, a0, a1, rhs) =>
     indent + PrintExpr(map) + "[" +
     PrintExpr(a0) +
     (if (a1 != null) { ", " + a1 } else { "" }) +
     "] := " + 
     PrintExpr(rhs) + ";" + nl
   case _:LocalVar => "" /* print nothing */
 }
 def PrintExpr(e: Expr): String = {
   PrintExpr(e, false)
 }
 def PrintExpr(e: Expr, useParens: boolean): String = e match {
   case IntLiteral(n) => n.toString
   case BoolLiteral(b) => b.toString
   case Null() => "null"
   case VarExpr(id) => id
   case MapSelect(map, arg0, arg1) =>
     PrintExpr(map) + "[" + PrintExpr(arg0, false) + 
     (if (arg1 != null) { ", " + arg1 } else { "" }) +
     "]"
   case MapStore(map, arg0, rhs) =>
     PrintExpr(map) + "[" + arg0 + " := " + PrintExpr(rhs, false) + "]"
   case Old(e) => "old(" + PrintExpr(e, false) + ")"
   case UnaryExpr(op, e) =>
     (if (useParens)  { "(" } else "") +
     op + PrintExpr(e, true) +
     (if (useParens) ")" else "" )
   case BinaryExpr(op, e0, e1) =>
     // reduce parentheses in a special common case:
     val binIsAndImpIff = op=="&&" || op=="==>" || op=="<==>";
     def IsAnd(e: Expr) = e match { case BinaryExpr(op,_,_) if op=="&&" => true case _ => false }
     (if (useParens) "(" else "") + PrintExpr(e0, !(binIsAndImpIff && IsAnd(e0))) + 
     " " + op + " " + 
     PrintExpr(e1, !(binIsAndImpIff && IsAnd(e1))) +
     (if (useParens) ")" else "")
   case FunctionApp(f, args) =>
     f + "(" +
     Print(args, ", ", { e: Expr => PrintExpr(e, false) }) +
     ")"
   case Ite(con, then, els) =>
     "ite(" + PrintExpr(con) + ", " + PrintExpr(then) + ", " + PrintExpr(els) + ")"
   case Forall(ts, xs, triggers, body) =>
     "(forall" +
     (if (ts.length == 0) " " else "<" + Print(ts, ", ", { x: TVar => x.id }) + "> ") +
     Print(xs, ", ", { x: BVar => x.id +  ": " + PrintType(x.t) }) +
     " :: " +
     Print(triggers , "", { s: Expr => "{" + PrintExpr(s) + "} " }) +
     PrintExpr(body) +
     ")"
   case Exists(xs, triggers, body) =>
     "(exists " +
     Print(xs, ", ", { x: BVar => x.id +  ": " + PrintType(x.t) }) +
     " :: " +
     Print(triggers , "", { s: Expr => "{" + PrintExpr(s) + "} " }) +
     PrintExpr(body) +
     ")"
 }
}
