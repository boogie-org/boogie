//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
object PrintProgram {
  def P(prog: List[TopLevelDecl]) =
    for (decl <- prog) decl match {
      case cl: Class =>
        if (cl.IsExternal) print("external ")
        println("class " + cl.id + " module " + cl.module + " {")
        cl.members foreach Member
        println("}")
      case ch: Channel =>
        println("channel " + ch.id + " where " + Expr(ch.where) + Semi)
    }
  def Semi = ";"
  def Member(m: Member) = m match {
    case MonitorInvariant(e) =>
      print("  invariant "); Expr(e); println(Semi)
    case f@ Field(id, t) =>
      println("  " + (if (f.IsGhost) "ghost " else "") + "var " + id + ": " + t.id + Semi)
    case m: Method =>
      print("  method " + m.id)
      print("("); VarList(m.ins); print(")")
      if (m.outs != Nil) {
        print(" returns ("); VarList(m.outs); print(")")
      }
      println
      m.spec foreach {
        case Precondition(e) => print("    requires "); Expr(e); println(Semi)
        case Postcondition(e) => print("    ensures "); Expr(e); println(Semi)
        case LockChange(ee) => print("    lockchange "); ExprList(ee); println(Semi)
      }
      println("  {");
      for (s <- m.body) {
        print("    "); Stmt(s, 4)
      }
      println("  }")
    case Condition(id, optE) =>
      print("  condition " + id)
      optE match {
        case None =>
        case Some(e) => print(" where " + Expr(e))
      }
      println(Semi)
    case Predicate(id, definition) =>
      println("  predicate " + id + "  { " + Expr(definition) + "}")
    case Function(id, ins, out, specs, e) =>
      print("  function " + id + "(" + VarList(ins) + ")" + ": " + out.id);
      specs foreach {
        case Precondition(e) => print("    requires "); Expr(e); println(Semi)
        case Postcondition(e) => print("    ensures "); Expr(e); println(Semi)
        case LockChange(ee) => print("    lockchange "); ExprList(ee); println(Semi)
      }
      print("  { " + Expr(e) + "}");
  }
  def Stmt(s: Statement, indent: int): unit = s match {
    case Assert(e) =>
      print("assert "); Expr(e); println(Semi)
    case Assume(e) =>
      print("assume "); Expr(e); println(Semi)
    case BlockStmt(ss) =>
      PrintBlockStmt(ss, indent); println
    case IfStmt(guard, BlockStmt(thn), els) =>
      print("if ("); Expr(guard); print(") ")
      PrintBlockStmt(thn, indent)
      els match {
        case None => println
        case Some(s) => print(" else "); Stmt(s, indent)
      }
    case WhileStmt(guard, invs, lkch, body) =>
      print("while ("); Expr(guard); println(")")
      for (inv <- invs) {
        Spaces(indent+2)
        print("invariant "); Expr(inv); println(Semi)
      }
      for (l <- lkch) {
        Spaces(indent+2)
        print("lockchange "); Expr(l); println(Semi)
      }
      Spaces(indent); Stmt(body, indent)
    case Assign(lhs,rhs) =>
      Expr(lhs); print(" := "); Rhs(rhs); println(Semi)
    case FieldUpdate(lhs,rhs) =>
      Expr(lhs); print(" := "); Rhs(rhs); println(Semi)
    case LocalVar(id,t,c,g,rhs) =>
      if (g) print("ghost ")
      if (c) print("const ") else print("var ")
      print(id + ": " + t.id)
      rhs match { case None => case Some(rhs) => print(" := "); Rhs(rhs) }
      println(Semi)
    case Call(_, outs, obj, id, args) =>
      print("call ")
      outs match {
        case Nil =>
        case x :: xs => Expr(x); xs foreach { x => print(", "); Expr(x) }; print(" := ")
      }
      MemberSelect(obj,id,0,false)
      print("(")
      ExprList(args)
      println(");")
    case Install(obj,lower,upper) =>
      print("reorder ")
      Expr(obj)
      PrintBounds(lower, upper)
      println(Semi)
    case Share(obj,lower,upper) =>
      print("share ")
      Expr(obj)
      PrintBounds(lower, upper)
      println(Semi)
    case Unshare(e) =>
      print("unshare "); Expr(e); println(Semi)
    case Acquire(e) =>
      print("acquire "); Expr(e); println(Semi)
    case Release(e) =>
      print("release "); Expr(e); println(Semi)
    case RdAcquire(e) =>
      print("rd acquire "); Expr(e); println(Semi)
    case RdRelease(e) =>
      print("rd release "); Expr(e); println(Semi)
    case Lock(e, b, rdLock) =>
      if (rdLock) print("rd lock (") else print("lock (")
      Expr(e); print(") ")
      Stmt(b, indent)
    case Downgrade(e) =>
      print("downgrade "); Expr(e); println(Semi)
    case Free(e) =>
      print("free "); Expr(e); println(Semi)
    case Fold(e) =>
      print("fold "); Expr(e); println(Semi)
    case Unfold(e) =>
      print("unfold "); Expr(e); println(Semi)
    case CallAsync(declaresLocal, token, obj, name, args) =>
      print("call async ");
      if (token != null) {
        Expr(token); print(" := ");
      }
      Expr(obj); print("."); print(name); print("("); ExprList(args); print(")");
    case JoinAsync(lhs, token) =>
      print("join async "); ExprList(lhs); print(" := "); Expr(token);
    case Wait(obj, id) =>
      print("wait ")
      MemberSelect(obj, id, 0, false)
      println(Semi)
    case Signal(obj, id, all) =>
      print("signal "); if (all) { print(" forall") }
      MemberSelect(obj, id, 0, false)
      println(Semi)
    case Send(ch, args) =>
      print("send "); Expr(ch); print("("); ExprList(args); print(")"); println(Semi)
    case Receive(_, ch, outs) =>
      print("receive ")
      outs match {
        case Nil =>
        case x :: xs => Expr(x); xs foreach { x => print(", "); Expr(x) }; print(" := ")
      }
      Expr(ch); println(Semi)
  }
  def PrintBounds(lower: List[Expression], upper: List[Expression]) = {
    if (lower == Nil && upper == Nil) {
    } else if (lower == Nil) {
      print(" below "); ExprList(upper)
    } else if (upper == Nil) {
      print(" above "); ExprList(lower)
    } else {
      print(" between "); ExprList(lower); print(" and "); ExprList(upper)
    }
  }
  def PrintBlockStmt(ss: List[Statement], indent: int) = {
    println("{")
    for (s <- ss) { Spaces(indent+2); Stmt(s, indent+2) }
    Spaces(indent);  print("}")
  }
  def VarList(vv: List[Variable]) = vv match {
    case Nil =>
    case v :: rest =>
      print(v.id + ": " + v.t.id)
      rest foreach { v => print(", " + v.id + ": " + v.t.id) }
  }
  def ExprList(ee: List[Expression]) = ee match {
    case Nil =>
    case e :: rest =>
      Expr(e)
      rest foreach { e => print(", "); Expr(e) }
  }
  def Rhs(e: RValue) = e match {
    case NewRhs(id, initialization, lower, upper) => 
      print("new " + id); 
      if(0 < initialization.length) { 
        print(" {"); print(initialization(0).id); print(":="); Expr(initialization(0).e); initialization.foreach({ init => print(", "); print(init.id); print(":="); Expr(init.e); }); print("}");
      }
      PrintBounds(lower, upper)
    case e: Expression => Expr(e)
  }
  def Expr(e: Expression): Unit = Expr(e, 0, false)
  def Expr(e: Expression, contextBindingPower: int, fragileContext: boolean): Unit = e match {
    case IntLiteral(n) => print(n)
    case BoolLiteral(b) => print(b)
    case NullLiteral() => print("null")
    case MaxLockLiteral() => print("waitlevel")
    case LockBottomLiteral() => print("lockbottom")
    case _:ThisExpr => print("this")
    case _:Result => print("result")
    case VariableExpr(id) => print(id)
    case MemberAccess(e,f) => MemberSelect(e,f,contextBindingPower,fragileContext)
    case Access(e,perm) =>
      print("acc("); Expr(e)
      perm match { case None => case Some(perm) => print(", "); Expr(perm) }
      print(")")
    case RdAccess(e,p) =>
      print("rd("); Expr(e)
      p match {
        case None =>          print(")")
        case Some(None) =>    print(", *)")
        case Some(Some(e)) => print(", "); Expr(e); print(")")
      }
    case AccessAll(obj, perm) =>
      print("acc("); Expr(obj); print(".*");
      perm match { case None => case Some(perm) => print(", "); Expr(perm) }
      print(")")
    case RdAccessAll(obj, p) =>
     print("rd("); Expr(e); print(".*");
      p match {
        case None =>          print(")")
        case Some(None) =>    print(", *)")
        case Some(Some(e)) => print(", "); Expr(e); print(")")
      }
    case Credit(e, n) =>
      print("credit("); Expr(e)
      n match { case None => case Some(n) => print(", "); Expr(n) }
      print(")")
    case Holds(e) =>
          print("holds("); Expr(e); print(")")
    case RdHolds(e) =>
          print("rd holds("); Expr(e); print(")")
    case Assigned(id) => print("assigned(" + id + ")")
    case Old(e) =>
          print("old("); Expr(e); print(")")
    case IfThenElse(con, then, els) => 
      print("ite("); Expr(con); print(", "); Expr(then); print(", "); Expr(els); print(")");
    case Not(e) => print("!"); Expr(e, 0x80, false)
    case FunctionApplication(obj, id, ins) =>
      Expr(obj); print("."); print(id); print("("); ExprList(ins); print(")");
    case Unfolding(pred, e) =>
      print("unfolding "); Expr(pred); print(" in "); Expr(e); 
    case e:Iff => BinExpr(e, e.OpName, 0x10, false, false, contextBindingPower, fragileContext)
    case e:Implies => BinExpr(e, e.OpName, 0x20, true, false, contextBindingPower, fragileContext)
    case e:And => BinExpr(e, e.OpName, 0x30, false, false, contextBindingPower, fragileContext)
    case e:Or => BinExpr(e, e.OpName, 0x31, false, false, contextBindingPower, fragileContext)
    case e:Eq => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:Neq => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:Less => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:AtMost => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:AtLeast => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:Greater => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:LockBelow => BinExpr(e, e.OpName, 0x40, true, true, contextBindingPower, fragileContext)
    case e:Plus => BinExpr(e, e.OpName, 0x50, false, false, contextBindingPower, fragileContext)
    case e:Minus => BinExpr(e, e.OpName, 0x50, false, true, contextBindingPower, fragileContext)
    case e:Times => BinExpr(e, e.OpName, 0x60, false, false, contextBindingPower, fragileContext)
    case e:Div => BinExpr(e, e.OpName, 0x60, false, true, contextBindingPower, fragileContext)
    case e:Mod => BinExpr(e, e.OpName, 0x60, false, true, contextBindingPower, fragileContext)
    case q:Quantification => 
      print(q.Quantor + "{"); 
      q.Is match {
        case Nil =>
        case i :: rest => print(i); rest foreach { v => print(", " + v) }
      }
      print(" in "); Expr(q.Seq); print("; "); Expr(q.E); print("}");
    case EmptySeq(t) =>
      print("nil<"); print(t.FullName); print(">");
    case ExplicitSeq(es) =>
      print("["); ExprList(es); print("]");
    case Range(min, max) =>
      print("("); Expr(min); print(":"); Expr(max); print(")");
    case Length(e)=>
      print("|"); Expr(e); print("|");
    case e:At =>
      BinExpr(e, e.OpName, 0x45, true, true, contextBindingPower, fragileContext)
    case e:Append =>
      BinExpr(e, e.OpName, 0x45, true, true, contextBindingPower, fragileContext)
    case Drop(s, n) =>
      Expr(s); print("["); Expr(n); print(" ..]");
    case Take(s, n) =>
      Expr(s); print("[.. "); Expr(n); print("]");
    case Eval(h, e) =>
      print("eval("); (h match 
        { 
          case AcquireState(obj) => Expr(obj); print(".acquire"); 
          case ReleaseState(obj) => Expr(obj); print(".release"); 
          case CallState(token, obj, id, args) => Expr(token); print(".joinable"); print(", "); Expr(obj); print("." + id + "("); ExprList(args); print(")"); 
        }); print(", "); Expr(e); print(")"); 
  }
  def MemberSelect(e: Expression, f: String, contextBindingPower: int, fragileContext: boolean) = e match {
    case e:ImplicitThisExpr => print(f)
    case _ =>
      ParenExpr(0x90, contextBindingPower, fragileContext, { Expr(e,0x90,false); print("." + f) })
  }
  def BinExpr(bin: BinaryExpr, op: String, power: int, fragileLeft: boolean, fragileRight: boolean,
              context: int, fragileContext: boolean) = {
    ParenExpr(power, context, fragileContext,
          { Expr(bin.E0, power, fragileLeft); print(" " + op + " "); Expr(bin.E1, power, fragileRight) })
  }
  def ParenExpr(power: int, context: int, fragileContext: boolean, pe: =>Unit) {
    val ap = power & 0xF0;
    val cp = context & 0xF0;
    val parensNeeded = ap < cp || (ap == cp && (power != context || fragileContext));
    if (parensNeeded) { print("(") }
    pe
    if (parensNeeded) { print(")") }
  }
  def Spaces(N: int) = {
    val abunchaSpaces = "          "
    var n = N
    while (abunchaSpaces.length <= n) {
      print(abunchaSpaces)
      n = n - abunchaSpaces.length
    }
    if (0 < n) {
      print(abunchaSpaces.substring(0, n))
    }
  }
}
