//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional

object Resolver {
 sealed abstract class ResolverOutcome
 case class Success extends ResolverOutcome
 case class Errors(ss: List[(Position,String)]) extends ResolverOutcome

 var seqClasses = Map[String, SeqClass]();

 class ProgramContext(decls: Map[String,TopLevelDecl], currentClass: Class) {
   val Decls = decls
   val CurrentClass = currentClass
   var currentMember = null: Member;
   def CurrentMember = currentMember: Member;  
   var errors: List[(Position,String)] = Nil
   def Error(pos: Position, msg: String) {
     errors = errors + (pos, msg)
   }
   def AddVariable(v: Variable): ProgramContext = {
     new LProgramContext(v, this);
   }
   def LookupVariable(id: String): Option[Variable] = None
   def IsVariablePresent(vr: Variable): boolean = false

   private class LProgramContext(v: Variable, parent: ProgramContext) extends ProgramContext(parent.Decls, parent.CurrentClass) {
     override def Error(pos: Position, msg: String) = parent.Error(pos, msg)
     override def LookupVariable(id: String): Option[Variable] = {
       if (id == v.id) Some(v) else parent.LookupVariable(id)
     }
     override def IsVariablePresent(vr: Variable): boolean = {
       if (vr == v) true else parent.IsVariablePresent(vr)
     }
     override def CurrentMember() = {
       parent.CurrentMember
     }
   }
 }

 def Resolve(prog: List[TopLevelDecl]): ResolverOutcome = {
   // register the channels as well as the classes and their members
   var decls = Map[String,TopLevelDecl]()
   for (decl <- BoolClass :: IntClass :: RootClass :: NullClass :: MuClass :: prog) {
     if (decls contains decl.id) {
       return Errors(List((decl.pos, "duplicate class/channel name: " + decl.id)))
     } else {
       decl match {
         case cl: Class =>
           for (m <- cl.members) m match {
             case _:MonitorInvariant =>
             case m: NamedMember =>
               m.Parent = cl
               if (cl.mm contains m.Id) {
                 return Errors(List((m.pos, "duplicate member name " + m.Id + " in class " + cl.id)))
               } else {
                 cl.mm = cl.mm + (m.Id -> m)
               }
           }
         case ch: Channel =>
       }
       decls = decls + (decl.id -> decl)
     }
   }
   var errors = List[(Position,String)]()

   // resolve types of members
   val contextNoCurrentClass = new ProgramContext(decls, null)
   for (decl <- prog) decl match {
     case ch: Channel =>
       for (v <- ch.parameters) {
         ResolveType(v.t, contextNoCurrentClass)
        }
     case cl: Class =>
       for (m <- cl.asInstanceOf[Class].members) m match {
         case _:MonitorInvariant =>
         case Field(id,t) =>
           ResolveType(t, contextNoCurrentClass)
         case Method(id, ins, outs, spec, body) =>
           for (v <- ins ++ outs) {
             ResolveType(v.t, contextNoCurrentClass)
           }
         case _:Condition =>
         case _:Predicate =>
         case Function(id, ins, out, specs, definition) => 
           for (v <- ins) {
             ResolveType(v.t, contextNoCurrentClass)
           }
           ResolveType(out, contextNoCurrentClass)
       }
   }
   errors = errors ++ contextNoCurrentClass.errors;

   // now, resolve and typecheck all
   //  * Field types and Method formal-parameter types
   //  * Assign, FieldUpdate, and Call statements
   //  * VariableExpr and FieldSelect expressions
   for (decl <- prog) decl match {
     case ch: Channel =>
        val context = new ProgramContext(decls, ChannelClass(ch))
       var ctx = context
       for (v <- ch.parameters) {
         ctx = ctx.AddVariable(v)
       }
       ResolveExpr(ch.where, ctx, false, true)(false)
        errors = errors ++ context.errors
     case cl: Class =>
       val context = new ProgramContext(decls, cl)
       for (m <- cl.members) {
         context.currentMember = m;
         m match {
           case MonitorInvariant(e) =>
             ResolveExpr(e, context, true, true)(true)
             if (!e.typ.IsBool) context.Error(m.pos, "monitor invariant requires a boolean expression (found " + e.typ.FullName + ")")
           case _:Field => // nothing more to do
           case m@Method(id, ins, outs, spec, body) =>
             var ctx = context
             for (v <- ins ++ outs) {
               ctx = ctx.AddVariable(v)
             }
             spec foreach {
               case Precondition(e) => ResolveExpr(e, ctx, false, true)(false)
               case Postcondition(e) => ResolveExpr(e, ctx, true, true)(false)
               case lc@LockChange(ee) => 
               if(m.id.equals("run")) context.Error(lc.pos, "lockchange not allowed on method run") 
               ee foreach (e => ResolveExpr(e, ctx, true, false)(false))
             }
             ResolveStmt(BlockStmt(body), ctx)
           case Condition(id, None) =>
           case c@Condition(id, Some(e)) =>
             ResolveExpr(e, context, false, true)(false)
             if (!e.typ.IsBool) context.Error(c.pos, "where clause requires a boolean expression (found " + e.typ.FullName + ")")
           case p@Predicate(id, e) =>
             var ctx = context;
             ResolveExpr(e, ctx, false, true)(true);
             if(!e.typ.IsBool) context.Error(e.pos, "predicate requires a boolean expression (found " + e.typ.FullName + ")")
           case f@Function(id, ins, out, spec, e) =>
             var ctx = context
             for (v <- ins) {
               ctx = ctx.AddVariable(v)
             }
          // TODO: disallow credit(...) expressions in function specifications
             spec foreach {
               case Precondition(e) => ResolveExpr(e, ctx, false, true)(false)
               case pc@Postcondition(e) => assert(ctx.CurrentMember != null); ResolveExpr(e, ctx, false, true)(false)
               case lc@LockChange(ee) => context.Error(lc.pos, "lockchange not allowed on function") 
             }
             ResolveExpr(e, ctx, false, false)(false)
             if(! canAssign(out.typ, e.typ)) context.Error(e.pos, "function body does not match declared type (expected: " + out.FullName + ", found: " + e.typ.FullName + ")")
         }
       }
       errors = errors ++ context.errors
   }

   if (errors.length == 0) {
     Success()
   } else {
     Errors(errors)
   }
 }

 def ResolveType(t: Type, context: ProgramContext): unit = {
     for(p <- t.params){
       ResolveType(p, context);
     }
     if(t.isInstanceOf[TokenType]){
       val tt = t.asInstanceOf[TokenType];
       ResolveType(tt.C, context);
       if(! tt.C.typ.IsNormalClass) context.Error(t.pos, "Invalid token type. " + tt.C.FullName + " is not a user-defined class.");
       tt.C.typ.LookupMember(tt.m) match {
         case Some(m: Method) => val tc = TokenClass(tt.C, tt.m); tc.method = m; tt.typ = tc;
         case _ => context.Error(t.pos, "Invalid token type. " + tt.C.FullName + " does not declare a method " + tt.m + ".");
       }
       return;
     }
     if (context.Decls contains t.FullName) {
       context.Decls(t.FullName) match {
         case cl: Class => t.typ = cl
         case ch: Channel => t.typ = ChannelClass(ch)
         case _ =>
           context.Error(t.pos, "Invalid class: " + t.FullName + " does not denote a class")
           t.typ = IntClass
       }
     } else {
       if(seqClasses.contains(t.FullName)) {
         t.typ = seqClasses(t.FullName)
       } else if(t.id.equals("seq") && t.params.length == 1) {
         val seqt = new SeqClass(t.params(0).typ);
         seqClasses = seqClasses + ((seqt.FullName, seqt));
         t.typ = seqt;
       } else {
         context.Error(t.pos, "undeclared type " + t.FullName)
         t.typ = IntClass
       }
     }
 }

 def getSeqType(param: Class, context: ProgramContext): Class = {
   if(seqClasses.contains("seq<" + param.FullName + ">")) {
     seqClasses("seq<" + param.FullName + ">")
   } else {
     val seqt = new SeqClass(param);
     seqClasses = seqClasses + ((seqt.FullName, seqt));
     seqt
   }
 }

 def ResolveStmt(s: Statement, context: ProgramContext): unit = s match {
   case Assert(e) =>
     ResolveExpr(e, context, true, true)(false)
     if (!e.typ.IsBool) context.Error(e.pos, "assert statement requires a boolean expression (found " + e.typ.FullName + ")")
   case Assume(e) =>
     ResolveExpr(e, context, false, false)(false)  // assume expressions remain at run-time, so OLD is not allowed
     if (!e.typ.IsBool) context.Error(e.pos, "assume statement requires a boolean expression (found " + e.typ.FullName + ")")
     CheckNoGhost(e, context)
   case BlockStmt(ss) =>
     var ctx = context
     for (s <- ss) s match {
       case l @ LocalVar(id, t, c, g, rhs) =>
         ResolveType(l.v.t, ctx)
         val oldCtx = ctx
         ctx = ctx.AddVariable(l.v)
         rhs match {
           case None =>
           case Some(rhs) =>
             val lhs = VariableExpr(id)
             lhs.pos = l.pos;
             ResolveExpr(lhs, ctx, false, false)(false)
             ResolveAssign(lhs, rhs, oldCtx)
         }
       case c: CallAsync =>
         ResolveStmt(c, ctx)
         if (c.local != null) {
           ctx = ctx.AddVariable(c.local)
         }
       case c: Call =>
         ResolveStmt(c, ctx)
         for (v <- c.locals) { ctx = ctx.AddVariable(v) } 
       case r: Receive =>
         ResolveStmt(r, ctx)
         for (v <- r.locals) { ctx = ctx.AddVariable(v) } 
       case s =>
         ResolveStmt(s, ctx)
     }
   case IfStmt(guard, thn, els) =>
     ResolveExpr(guard, context, false, false)(false)
     if (!guard.typ.IsBool) context.Error(guard.pos, "if statement requires a boolean guard (found " + guard.typ.FullName + ")")
     CheckNoGhost(guard, context)
     ResolveStmt(thn, context)
     els match { case None => case Some(s) => ResolveStmt(s, context) }
   case w@ WhileStmt(guard, invs, lkch, body) =>
     ResolveExpr(guard, context, false, false)(false)
     if (!guard.typ.IsBool) context.Error(guard.pos, "while statement requires a boolean guard (found " + guard.typ.FullName + ")")
     CheckNoGhost(guard, context)
     for (inv <- invs) {
       ResolveExpr(inv, context, true, true)(false)
       if (!inv.typ.IsBool) context.Error(inv.pos, "loop invariant must be boolean (found " + inv.typ.FullName + ")")
     }
     for (l <- lkch) {
       ResolveExpr(l, context, true, false)(false)
       if (!l.typ.IsRef) context.Error(l.pos, "lockchange expression must be reference (found " + l.typ.FullName + ")")
     }
     ResolveStmt(body, context)
     w.LoopTargets = ComputeLoopTargets(body) filter context.IsVariablePresent
   case Assign(lhs, rhs) => 
     ResolveExpr(lhs, context, false, false)(false)
     ResolveAssign(lhs, rhs, context)
     if (lhs.v != null && lhs.v.IsImmutable) {
       if (lhs.v.IsGhost)
         CheckNoGhost(rhs, context)
       else
         context.Error(lhs.pos, "cannot assign to immutable variable " + lhs.v.id)
     }
   case fu@FieldUpdate(lhs, rhs) =>
     ResolveExpr(lhs, context, false, false)(false)
     if (! lhs.isPredicate && lhs.f != null && !lhs.f.IsGhost) CheckNoGhost(lhs.e, context)
     if (! lhs.isPredicate && lhs.f.isInstanceOf[SpecialField]) context.Error(lhs.pos, "cannot assign directly to special field: " + lhs.id)
     ResolveExpr(rhs, context, false, false)(false)
     if (! lhs.isPredicate && !canAssign(lhs.typ, rhs.typ)) context.Error(fu.pos, "type mismatch in assignment, lhs=" + lhs.typ.FullName + " rhs=" + rhs.typ.FullName)
     if (! lhs.isPredicate && lhs.f != null && !lhs.f.IsGhost) CheckNoGhost(rhs, context)
   case lv:LocalVar => throw new Exception("unexpected LocalVar; should have been handled in BlockStmt above")
   case c @ Call(declaresLocal, lhs, obj, id, args) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     args foreach { a => ResolveExpr(a, context, false, false)(false); CheckNoGhost(a, context) }
     // lookup method
     var typ: Class = IntClass
     obj.typ.LookupMember(id) match {
       case None =>
         context.Error(c.pos, "call of undeclared member " + id + " in class " + obj.typ.FullName)
       case Some(m: Method) =>
         c.m = m
         if (args.length != m.ins.length)
           context.Error(c.pos, "wrong number of actual in-parameters in call to " + obj.typ.FullName + "." + id +
                         " (" + args.length + " instead of " + m.ins.length + ")")
         else {
           for((actual, formal) <- args zip m.ins){
             if(! canAssign(formal.t.typ, actual.typ))
               context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
           }
         }     
         if (lhs.length != m.outs.length)
           context.Error(c.pos, "wrong number of actual out-parameters in call to " + obj.typ.FullName + "." + id +
                         " (" + lhs.length + " instead of " + m.outs.length + ")")
         else
           c.locals = ResolveLHS(declaresLocal, lhs, m.outs, context)
       case _ => context.Error(c.pos, "call expression does not denote a method: " + obj.typ.FullName + "." + id)
     }
   case Install(obj, lowerBounds, upperBounds) =>
     ResolveExpr(obj, context, false, false)(false)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in reorder statement must be of a reference type (found " + obj.typ.FullName + ")")
     if (obj.typ.IsChannel) context.Error(obj.pos, "object in reorder statement must not be a channel (found " + obj.typ.FullName + ")")
     ResolveBounds(lowerBounds, upperBounds, context, "install")
   case Share(obj, lowerBounds, upperBounds) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in share statement must be of a reference type (found " + obj.typ.FullName + ")")
     if (obj.typ.IsChannel) context.Error(obj.pos, "object in share statement must not be a channel (found " + obj.typ.FullName + ")")
     ResolveBounds(lowerBounds, upperBounds, context, "share")
   case Unshare(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in unshare statement must be of a reference type (found " + obj.typ.FullName + ")")
     if (obj.typ.IsChannel) context.Error(obj.pos, "object in unshare statement must not be a channel (found " + obj.typ.FullName + ")")
   case Acquire(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in acquire statement must be of a reference type (found " + obj.typ.FullName + ")")
   case Release(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in release statement must be of a reference type (found " + obj.typ.FullName + ")")
   case RdAcquire(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in rd acquire statement must be of a reference type (found " + obj.typ.FullName + ")")
   case RdRelease(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in rd release statement must be of a reference type (found " + obj.typ.FullName + ")")
   case Lock(obj, b, rdLock) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) {
       val sname = if (rdLock) "rd lock" else "lock";
       context.Error(obj.pos, "object in " + sname + " statement must be of a reference type (found " + obj.typ.FullName + ")")
                                      
     }
     ResolveStmt(b, context)
   case Downgrade(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in downgrade statement must be of a reference type (found " + obj.typ.FullName + ")")
   case Free(obj) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     if (!obj.typ.IsRef) context.Error(obj.pos, "object in free statement must be of a reference type (found " + obj.typ.FullName + ")")
   case fld@Fold(e) =>
     ResolveExpr(e, context, false, true)(false);
     CheckNoGhost(e, context);
     if(!e.getMemberAccess.isPredicate) context.Error(fld.pos, "Fold can only be applied to predicates.")
   case ufld@Unfold(e) =>
     ResolveExpr(e, context, false, true)(false);
     CheckNoGhost(e, context);
     if(!e.getMemberAccess.isPredicate) context.Error(ufld.pos, "Unfold can only be applied to predicates.")
   case c@CallAsync(declaresLocal, token, obj, id, args) => 
     // resolve receiver
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     // resolve arguments
     args foreach { a => ResolveExpr(a, context, false, false)(false); CheckNoGhost(a, context) }
     // lookup method
     var typ: Class = IntClass
     obj.typ.LookupMember(id) match {
       case None =>
         context.Error(c.pos, "call of undeclared member " + id + " in class " + obj.typ.FullName)
       case Some(m: Method) =>
         c.m = m
         if (args.length != m.ins.length)
           context.Error(c.pos, "wrong number of actual in-parameters in call to " + obj.typ.FullName + "." + id +
                         " (" + args.length + " instead of " + m.ins.length + ")")
         else {
           for((actual, formal) <- args zip m.ins){
             if(! canAssign(formal.t.typ, actual.typ))
               context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
           }
         }
       case _ => context.Error(c.pos, "call expression does not denote a method: " + obj.typ.FullName + "." + id)
     }
     // resolve the token
     if (declaresLocal) {
       c.local = new Variable(token.id, TokenType(new Type(obj.typ), id))
       ResolveType(c.local.t, context)
       token.Resolve(c.local)
     } else if (token != null) {
       ResolveExpr(token, context, false, false)(false)
       if(! canAssign(token.typ, TokenClass(new Type(obj.typ), id)))
         context.Error(token.pos, "wrong token type")
     }
   case jn@JoinAsync(lhs, token) =>
     // resolve the assignees
     var vars = Set[Variable]()
     for (v <- lhs) {
       ResolveExpr(v, context, false, false)(false)
       if (v.v != null) {
         if (v.v.IsImmutable) context.Error(v.pos, "cannot use immutable variable " + v.id + " as actual out-parameter")
         if (vars contains v.v) {
           context.Error(v.pos, "duplicate actual out-parameter: " + v.id)
         } else {
           vars = vars + v.v
         }
       }
     }
     // resolve the token
     ResolveExpr(token, context, false, false)(false);
     if(token.typ == null || ! token.typ.IsToken || ! token.typ.isInstanceOf[TokenClass] || token.typ.asInstanceOf[TokenClass].method == null)
       context.Error(token.pos, "the first argument of a join async must be a token")
     else {
       val m = token.typ.asInstanceOf[TokenClass].method;
       jn.m = m
       if (lhs.length != m.outs.length)
         context.Error(jn.pos, "wrong number of actual out-parameters in join async of " + m.FullName +
                        " (" + lhs.length + " instead of " + m.outs.length + ")")
       else {
         for((out, l) <- m.outs zip lhs){
           if(! canAssign(l.typ, out.t.typ))
             context.Error(l.pos, "the out parameter cannot be assigned to the lhs (expected: " + l.typ.FullName + ", found: " + out.t.FullName + ")")
         }
       }
     
     }
   case w@Wait(obj, id) =>
     // resolve receiver
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     // lookup condition
     obj.typ.LookupMember(id) match {
       case None =>
         context.Error(w.pos, "wait on undeclared member " + id + " in class " + obj.typ.FullName)
       case Some(c: Condition) => w.c = c
       case _ =>
         context.Error(w.pos, "wait expression does not denote a condition: " + obj.typ.FullName + "." + id)
     }
   case s@Signal(obj, id, all) =>
     // resolve receiver
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     // lookup condition
     obj.typ.LookupMember(id) match {
       case None =>
         context.Error(s.pos, "signal on undeclared member " + id + " in class " + obj.typ.FullName)
       case Some(c: Condition) => s.c = c
       case _ =>
         context.Error(s.pos, "signal expression does not denote a condition: " + obj.typ.FullName + "." + id)
     }
   case s@Send(ch, args) =>
     ResolveExpr(ch, context, false, false)(false)
     CheckNoGhost(ch, context)
     args foreach { a => ResolveExpr(a, context, false, false)(false); CheckNoGhost(a, context) }
     // match types of arguments
     ch.typ match {
       case ChannelClass(channel) =>
         if (args.length != channel.parameters.length)
           context.Error(s.pos, "wrong number of actual in-parameters in send for channel type " + ch.typ.FullName +
                         " (" + args.length + " instead of " + channel.parameters.length + ")")
         else {
           for ((actual, formal) <- args zip channel.parameters) {
             if (! canAssign(formal.t.typ, actual.typ))
               context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
           }
         }
       case _ => context.Error(s.pos, "send expression (which has type " + ch.typ.FullName + ") does not denote a channel")
     }
   case r@Receive(declaresLocal, ch, outs) =>
     ResolveExpr(ch, context, false, false)(false)
     CheckNoGhost(ch, context)
     // match types of arguments
     ch.typ match {
       case ChannelClass(channel) =>
         if (outs.length != channel.parameters.length)
           context.Error(r.pos, "wrong number of actual out-parameters in receive for channel type " + ch.typ.FullName +
                         " (" + outs.length + " instead of " + channel.parameters.length + ")")
         else
           r.locals = ResolveLHS(declaresLocal, outs, channel.parameters, context)
       case _ => context.Error(r.pos, "receive expression (which has type " + ch.typ.FullName + ") does not denote a channel")
     }
 }

 def ResolveLHS(declaresLocal: List[boolean], actuals: List[VariableExpr], formals: List[Variable], context: ProgramContext): List[Variable] = {
   var locals = List[Variable]()
   var vars = Set[Variable]()
   var ctx = context
   for (((declareLocal, actual), formal) <- declaresLocal zip actuals zip formals) {
     if (declareLocal) {
       val local = new Variable(actual.id, new Type(formal.t.typ))
       locals = locals + local
       ResolveType(local.t, ctx)
       actual.Resolve(local)
       vars = vars + actual.v
       ctx = ctx.AddVariable(local)
     } else {
       ResolveExpr(actual, ctx, false, false)(false)
       CheckNoGhost(actual, ctx)
       if (actual.v != null) {
         if (! canAssign(actual.typ, formal.t.typ))
           ctx.Error(actual.pos, "the type of the formal argument is not assignable to the actual parameter (expected: " +
                         formal.t.FullName + ", found: " + actual.typ.FullName + ")")
         if (vars contains actual.v)
           ctx.Error(actual.pos, "duplicate actual out-parameter: " + actual.id)
         else if (actual.v.IsImmutable)
           ctx.Error(actual.pos, "cannot use immutable variable " + actual.id + " as actual out-parameter")
         vars = vars + actual.v
       }
     }
   }
   locals
 }

 def ResolveBounds(lowerBounds: List[Expression], upperBounds: List[Expression], context: ProgramContext, descript: String) =
   for (b <- lowerBounds ++ upperBounds) {
     ResolveExpr(b, context, true, false)(false)
     if (!b.typ.IsRef && !b.typ.IsMu)
       context.Error(b.pos, descript + " bound must be of a reference type or Mu type (found " + b.typ.FullName + ")")
   }

 def ComputeLoopTargets(s: Statement): Set[Variable] = s match {  // local variables
   case BlockStmt(ss) =>
     (ss :\ Set[Variable]()) { (s,vars) => vars ++ ComputeLoopTargets(s) }
   case IfStmt(guard, thn, els) =>
     val vars = ComputeLoopTargets(thn)
     els match { case None => vars; case Some(els) => vars ++ ComputeLoopTargets(els) }
   case w: WhileStmt =>
     // assume w.LoopTargets is non-null and that it was computed with a larger context
     w.LoopTargets
   case Assign(lhs, rhs) =>
     if (lhs.v != null) Set(lhs.v) else Set()  // don't assume resolution was successful
   case lv: LocalVar =>
     lv.rhs match { case None => Set() case Some(_) => Set(lv.v) }
   case Call(_, lhs, obj, id, args) =>
     (lhs :\ Set[Variable]()) { (ve,vars) => if (ve.v != null) vars + ve.v else vars }
   case _ => Set()
 }

 def ResolveAssign(lhs: VariableExpr, rhs: RValue, context: ProgramContext) = {
   rhs match {
     case ExplicitSeq(Nil) => rhs.typ = lhs.typ; // if [] appears on the rhs of an assignment, we "infer" its type by looking at the type of the lhs
     case _ => ResolveExpr(rhs, context, false, false)(false)
   }
   if (! canAssign(lhs.typ, rhs.typ))
     context.Error(lhs.pos, "type mismatch in assignment, lhs=" + lhs.typ.FullName + " rhs=" + rhs.typ.FullName)
   if (lhs.v != null && !lhs.v.IsGhost) CheckNoGhost(rhs, context)
 }

 // ResolveExpr resolves all parts of an RValue, if possible, and (always) sets the RValue's typ field
 def ResolveExpr(e: RValue, context: ProgramContext,
                 twoStateContext: boolean, specContext: boolean)(implicit inPredicate: Boolean): unit = e match {
   case e @ NewRhs(id, initialization, lower, upper) =>
     if (context.Decls contains id) {
       context.Decls(id) match {
         case ch: Channel =>
           e.typ = ChannelClass(ch)
         case cl: Class =>
           e.typ = cl
           if (lower != Nil || upper != Nil)
             context.Error(e.pos, "A new object of a class type is not allowed to have a wait-order bounds clause (use the share statement instead)")
       }
       // initialize the fields
       var fieldNames = Set[String]()
       for(ini@Init(f, init) <- initialization) {
         if (fieldNames contains f) {
           context.Error(ini.pos, "The field " + f + " occurs more than once in initializer.")
         } else {
           fieldNames = fieldNames + f
           e.typ.LookupMember(f) match {
             case Some(field@Field(name, tp)) =>
               if(field.isInstanceOf[SpecialField]) context.Error(init.pos, "Initializer cannot assign to special field " + name + ".");
               ResolveExpr(init, context, false, false);
               if(! canAssign(tp.typ, init.typ)) context.Error(init.pos, "The field " + name + " cannot be initialized with an expression of type " + init.typ.id + ".");
               ini.f = field;
             case _ => 
               context.Error(e.pos, "The type " + id + " does not declare a field " + f + ".");  
           }
         }
       }
       // resolve the bounds
       ResolveBounds(lower, upper, context, "new")
     } else {
       context.Error(e.pos, "undefined class or channel " + id + " used in new expression")
       e.typ = IntClass
     }
   case i:IntLiteral =>
     i.typ = IntClass
   case b:BoolLiteral =>
     b.typ = BoolClass
   case n:NullLiteral =>
     n.typ = NullClass
   case mx:MaxLockLiteral =>
     mx.typ = MuClass
   case mx:LockBottomLiteral =>
     mx.typ = MuClass
   case r:Result =>
     assert(context.CurrentMember!=null);
     r.typ = IntClass
     if(context.CurrentMember==null || ! context.CurrentMember.isInstanceOf[Function]){
       context.Error(r.pos, "The variable result can only be used in the postcondition of a function.");
     } else {
       r.typ = context.CurrentMember.asInstanceOf[Function].out.typ;
     }
   case ve @ VariableExpr(id) =>
     context.LookupVariable(id) match {
       case None => context.Error(ve.pos, "undefined local variable " + id); ve.typ = IntClass
       case Some(v) => ve.Resolve(v) }
   case v:ThisExpr => v.typ = context.CurrentClass
   case sel @ MemberAccess(e, id) =>
     ResolveExpr(e, context, twoStateContext, false)
     var typ: Class = IntClass
     e.typ.LookupMember(id) match {
       case None =>
         context.Error(sel.pos, "undeclared member " + id + " in class " + e.typ.FullName)
       case Some(f: Field) => sel.f = f; typ = f.typ.typ
       case Some(pred@Predicate(id, body)) =>
         if(! specContext)
           context.Error(sel.pos, "predicate can only be used in positive predicate contexts")
         sel.predicate = pred;
         sel.isPredicate = true;
         typ = BoolClass
       case _ => context.Error(sel.pos, "field-select expression does not denote a field: " + e.typ.FullName + "." + id);
     }
     sel.typ = typ
   case expr@ Access(e, perm) =>
     if (!specContext) context.Error(expr.pos, "acc expression is allowed only in positive predicate contexts")
     ResolveExpr(e, context, twoStateContext, true)
     perm match {
       case None =>
       case Some(perm) => ResolveExpr(perm, context, twoStateContext, false) }
     expr.typ = BoolClass
   case expr@ RdAccess(e,perm) =>
     if (!specContext) context.Error(expr.pos, "rd expression is allowed only in positive predicate contexts")
     ResolveExpr(e, context, twoStateContext, true)
     perm match {
       case Some(Some(p)) => ResolveExpr(p, context, twoStateContext, false)
       case _ => }
     expr.typ = BoolClass
   case expr@AccessAll(obj, perm) =>
     if (!specContext) context.Error(expr.pos, "acc expression is allowed only in positive predicate contexts")
     ResolveExpr(obj, context, twoStateContext, false)
     if(!obj.typ.IsRef) context.Error(expr.pos, "Target of .* must be object reference.")
     perm match {
       case None =>
       case Some(perm) => ResolveExpr(perm, context, twoStateContext, false) }
     expr.typ = BoolClass
   case expr@RdAccessAll(obj,perm) =>
     if (!specContext) context.Error(expr.pos, "rd expression is allowed only in positive predicate contexts")
     ResolveExpr(obj, context, twoStateContext, false)
     if(!obj.typ.IsRef) context.Error(expr.pos, "Target of .* must be object reference.")
     perm match {
       case Some(Some(p)) => ResolveExpr(p, context, twoStateContext, false)
       case _ => }
     expr.typ = BoolClass
   case expr@ Credit(e,n) =>
     if (!specContext) context.Error(expr.pos, "credit expression is allowed only in positive predicate contexts")
     ResolveExpr(e, context, twoStateContext, false)
     if(!e.typ.IsChannel) context.Error(expr.pos, "credit argument must denote a channel.")
     ResolveExpr(expr.N, context, twoStateContext, false)
     expr.typ = BoolClass
   case expr@ Holds(e) =>
     if(inPredicate) context.Error(expr.pos, "holds cannot be mentioned in monitor invariants or predicates")
     if(! specContext)
       context.Error(expr.pos, "holds is allowed only in positive predicate contexts"); 
     //todo: check that we are not in an invariant
     ResolveExpr(e, context, twoStateContext, false)
     expr.typ = BoolClass
   case expr@ RdHolds(e) =>
     if(inPredicate) context.Error(expr.pos, "rdholds cannot be mentioned in monitor invariants or predicates")
     ResolveExpr(e, context, twoStateContext, false)
     expr.typ = BoolClass
   case expr@ Assigned(id) =>
     context.LookupVariable(id) match {
       case None => context.Error(expr.pos, "undefined local variable " + id)
       case Some(v) =>
         expr.v = v
         if (!(v.IsImmutable && v.IsGhost))
           context.Error(expr.pos, "assigned can only be used with ghost consts")
     }
     expr.typ = BoolClass
   case expr@ Old(e) =>
     if (! twoStateContext) { context.Error(expr.pos, "old expression is not allowed here") }
     ResolveExpr(e, context, twoStateContext, false)
     expr.typ = e.typ
   case ite@IfThenElse(con, then, els) => 
     ResolveExpr(con, context, twoStateContext, false); ResolveExpr(then, context, twoStateContext, specContext); ResolveExpr(els, context, twoStateContext, specContext);
     if (!con.typ.IsBool) context.Error(con.pos, "condition of if-then-else expression must be a boolean");
     if (! canAssign(then.typ, els.typ)) context.Error(ite.pos, "the then and else branch of an if-then-else expression must have compatible types");
     ite.typ = then.typ;
   case expr@ Not(e) =>
     ResolveExpr(e, context, twoStateContext, false)
     if (!e.typ.IsBool) context.Error(expr.pos, "not-expression requires boolean operand")
     expr.typ = BoolClass
   case appl@FunctionApplication(obj, id, args) =>
     ResolveExpr(obj, context, twoStateContext, false);
     args foreach { arg => ResolveExpr(arg, context, twoStateContext, false)};
     // lookup function
     appl.typ = IntClass
     obj.typ.LookupMember(id) match {
       case None =>
         context.Error(appl.pos, "function " + id + " not found in class " + obj.typ.FullName)
       case Some(func@Function(f, ins, out, specs, body)) =>
         appl.f = func
         appl.typ = func.out.typ;
         if (args.length != ins.length)
           context.Error(appl.pos, "wrong number of actual arguments in function application of " + obj.typ.FullName + "." + id +
                         " (" + args.length + " instead of " + ins.length + ")")
         else {
           for((actual, formal) <- args zip func.ins){
             if(! canAssign(formal.t.typ, actual.typ))
               context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
           }
         }
       case _ => context.Error(appl.pos, obj.typ.id + "." + id + " is not a function")
     }
   case uf@Unfolding(pred, e) =>
     ResolveExpr(pred, context, twoStateContext, true);
     ResolveExpr(e, context, twoStateContext, false);
     if(! pred.getMemberAccess.isPredicate) context.Error(uf.pos, "Only predicates can be unfolded.")
     uf.typ = e.typ;
   case bin: EqualityCompareExpr =>
     ResolveExpr(bin.E0, context, twoStateContext, false)
     ResolveExpr(bin.E1, context, twoStateContext, false)
     if (bin.E0.typ == bin.E1.typ) { /* all is well */ }
     else if (bin.E0.typ.IsRef && bin.E1.typ.IsNull) { /* all is well */ }
     else if (bin.E0.typ.IsNull && bin.E1.typ.IsRef) { /* all is well */ }
     else
       context.Error(bin.pos, bin.OpName + " requires operands of the same type, found " + bin.E0.typ.FullName + " and " + bin.E1.typ.FullName)
     bin.typ = BoolClass
   case bin: LockBelow =>
     ResolveExpr(bin.E0, context, twoStateContext, false)
     ResolveExpr(bin.E1, context, twoStateContext, false)
     if (!(bin.E0.typ.IsRef || bin.E0.typ.IsMu))
       context.Error(bin.pos, "type of " + bin.OpName + " LHS operand must be a reference or Mu type (found " + bin.E0.typ.FullName + ")")
     if (!(bin.E1.typ.IsRef || bin.E1.typ.IsMu))
       context.Error(bin.pos, "type of " + bin.OpName + " RHS operand must be a reference or Mu type (found " + bin.E1.typ.FullName + ")")
     bin.typ = BoolClass
   case app@Append(e0, e1) =>
     ResolveExpr(e0, context, twoStateContext, false);
     ResolveExpr(e1, context, twoStateContext, false);
     if(! e0.typ.IsSeq) context.Error(app.pos, "LHS operand of ++ must be sequence (found: " + e0.typ.FullName + ").");
     if(! e1.typ.IsSeq) context.Error(app.pos, "RHS operand of ++ must be sequence (found: " + e1.typ.FullName + ").");
     if(e0.typ != e1.typ) context.Error(app.pos, "++ can only be applied to sequences of the same type.");
     app.typ = e0.typ;
   case at@At(e0, e1) =>
     ResolveExpr(e0, context, twoStateContext, false);
     ResolveExpr(e1, context, twoStateContext, false);
     if(! e0.typ.IsSeq) context.Error(at.pos, "LHS operand of @ must be sequence. (found: " + e0.typ.FullName + ").");
     if(! e1.typ.IsInt) context.Error(at.pos, "RHS operand of @ must be an integer (found: " + e1.typ.FullName + ").");
     if(e0.typ.IsSeq) at.typ = e0.typ.parameters(0) else at.typ = IntClass;
   case drop@Drop(e0, e1) =>
     ResolveExpr(e0, context, twoStateContext, false);
     ResolveExpr(e1, context, twoStateContext, false);
     if(! e0.typ.IsSeq) context.Error(drop.pos, "LHS operand of drop must be sequence. (found: " + e0.typ.FullName + ").");
     if(! e1.typ.IsInt) context.Error(drop.pos, "RHS operand of drop must be an integer (found: " + e1.typ.FullName + ").");
     drop.typ = e0.typ;
   case take@Take(e0, e1) =>
     ResolveExpr(e0, context, twoStateContext, false);
     ResolveExpr(e1, context, twoStateContext, false);
     if(! e0.typ.IsSeq) context.Error(take.pos, "LHS operand of take must be sequence. (found: " + e0.typ.FullName + ").");
     if(! e1.typ.IsInt) context.Error(take.pos, "RHS operand of take must be an integer (found: " + e1.typ.FullName + ").");
     take.typ = e0.typ;
   case bin: BinaryExpr =>
     ResolveExpr(bin.E0, context, twoStateContext, specContext && bin.isInstanceOf[And])
     ResolveExpr(bin.E1, context, twoStateContext, specContext && (bin.isInstanceOf[And] || bin.isInstanceOf[Implies]))
     if (bin.E0.typ != bin.ExpectedLhsType)
       context.Error(bin.E0.pos, "incorrect type of " + bin.OpName + " LHS" +
                     " (expected " + bin.ExpectedLhsType.FullName + 
                     ", found " + bin.E0.typ.FullName + ")")
     if (bin.E1.typ != bin.ExpectedRhsType)
       context.Error(bin.E1.pos, "incorrect type of " + bin.OpName + " RHS" +
                     " (expected " + bin.ExpectedRhsType.FullName + ", found " + bin.E1.typ.FullName + ")")
     bin.typ = bin.ResultType
   case q: Quantification =>
     q.Is foreach { i => if(context.LookupVariable(i).isDefined) context.Error(q.pos, "The variable " + i + " hides another local.") }
     ResolveExpr(q.Seq, context, twoStateContext, false);
     if(! q.Seq.typ.IsSeq) 
       context.Error(q.Seq.pos, "A quantification must range over a sequence. (found: " + q.Seq.typ.FullName + ").");
     else {
       val elementType = q.Seq.typ.parameters(0);
       var bodyContext = context;
       var bvariables = Nil: List[Variable];
       q.Is foreach { i =>
         val variable = new Variable(i, new Type(elementType));
         bodyContext = bodyContext.AddVariable(variable);
         bvariables = bvariables + variable;
       }
       ResolveExpr(q.E, bodyContext, twoStateContext, true);
       if(! q.E.typ.IsBool) context.Error(q.E.pos, "Body of quantification must be a boolean. (found: " +  q.E.typ.FullName + ").");
       q.variables = bvariables;
     }
     q.typ = BoolClass
   case seq@EmptySeq(t) =>
     ResolveType(t, context)
     seq.typ = getSeqType(t.typ, context);
   case seq@ExplicitSeq(es) =>
     es foreach { e => ResolveExpr(e, context, twoStateContext, false) }
     es match {
       case Nil => seq.typ = getSeqType(IntClass, context);
       case h :: t =>
         t foreach { e => if(! (e.typ == h.typ)) context.Error(e.pos, "The elements of the sequence expression have different types.")};
         seq.typ = getSeqType(h.typ, context);
     }
   case ran@Range(min, max) =>
     ResolveExpr(min, context, twoStateContext, false);
     if(! min.typ.IsInt) context.Error(min.pos, "The mininum of a range expression must be an integer (found: " + min.typ.FullName + ").");
     ResolveExpr(max, context, twoStateContext, false);
     if(! max.typ.IsInt) context.Error(max.pos, "The maximum of a range expression must be an integer (found: " + max.typ.FullName + ").");
     ran.typ = getSeqType(IntClass, context);
   case len@Length(e) =>
     ResolveExpr(e, context, twoStateContext, false);
     if(! e.typ.IsSeq) context.Error(len.pos, "The operand of a length expression must be sequence. (found: " + e.typ.FullName + ").");
     len.typ = IntClass;
   case ev@Eval(h, e) =>
     if(inPredicate) context.Error(ev.pos, "eval cannot be used in monitor invariants or predicates")
     h match {
       case AcquireState(obj) => 
         ResolveExpr(obj, context, twoStateContext, false)
         if(! obj.typ.IsRef) context.Error(ev.pos, "The target of acquire must be a reference.");
       case ReleaseState(obj) => ResolveExpr(obj, context, twoStateContext, false)
         if(! obj.typ.IsRef) context.Error(ev.pos, "The target of acquire must be a reference.");
       case c@CallState(token, obj, id, args) =>
         ResolveExpr(token, context, twoStateContext, false);
         if( ! token.typ.IsToken) context.Error(token.pos, "joinable is only applicable to tokens");
         ResolveExpr(obj, context, false, false)
         CheckNoGhost(obj, context)
         args foreach { a => ResolveExpr(a, context, false, false); CheckNoGhost(a, context) }
         // lookup method
         var typ: Class = IntClass
         obj.typ.LookupMember(id) match {
           case None =>
             context.Error(obj.pos, "call of undeclared member " + id + " in class " + obj.typ.FullName)
           case Some(m: Method) =>
             c.m = m
             if (args.length != m.ins.length)
               context.Error(obj.pos, "wrong number of actual in-parameters in call to " + obj.typ.FullName + "." + id +
                         " (" + args.length + " instead of " + m.ins.length + ")")
             else {
               for((actual, formal) <- args zip m.ins){
                 if(! canAssign(formal.t.typ, actual.typ))
                  context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
             }
           }
         case _ => context.Error(obj.pos, "call expression does not denote a method: " + obj.typ.FullName + "." + id)
     }
           
         
     }
     ResolveExpr(e, context, false, specContext)
     ev.typ = e.typ;
 }

 def LookupRunMethod(cl: Class, context: ProgramContext, op: String, pos: Position): Option[Method] = {
   cl.LookupMember("run") match {
     case None =>
       context.Error(pos, "object given in " + op + " statement must be of a type with a parameter-less run method" +
                     " (found type " + cl.id + ")")
       None
     case Some(m: Method) =>
       m.spec foreach {
         case Precondition(e) => CheckRunSpecification(e, context, true)
         case Postcondition(e) => CheckRunSpecification(e, context, false)
         case lc: LockChange => context.Error(lc.pos, "lockchange is not allowed in specification of run method")
       }
       if(0<m.ins.length || 0<m.outs.length) {
         context.Error(pos, "object given in " + op + " statement must be of a type with a parameter-less run method" +
                     " (found " + m.ins.length + " in-parameters and " + m.outs.length + " out-parameters)"); None
       } else
         Some(m)
     case _ =>
       context.Error(pos, "object given in " + op + " statement must be of a type with a parameter-less run method" +
                     " (found non-method member)")
       None
   }
 }

 // assumes that lhs and rhs are resolved
 def canAssign(lhs: Class, rhs: Class): Boolean = {
   (lhs, rhs) match {
     case (TokenClass(c1, m1), TokenClass(c2, m2)) => c1.id.equals(c2.id) && m1.equals(m2)
     case (TokenClass(c1, m1), _) => false
     case (_, TokenClass(c2, m2)) => false
     case (lhs, rhs) => lhs == rhs || (lhs.IsRef && rhs.IsNull)
   }
 }

 def CheckNoGhost(expr: RValue, context: ProgramContext): Unit = {
   def specOk(e: RValue): Unit = { 
     e match {
       case ve: VariableExpr =>
         if (ve.v != null && ve.v.IsGhost) context.Error(ve.pos, "ghost variable not allowed here")
       case fs@ MemberAccess(e, id) =>
         if (!fs.isPredicate && fs.f != null && fs.f.IsGhost) context.Error(fs.pos, "ghost fields not allowed here")
         CheckNoGhost(e, context)
       case a: Assigned =>
         if (a.v != null && a.v.IsGhost) context.Error(a.pos, "ghost variable not allowed here")
       case _ => visitE(e, specOk)
     }
   }
   specOk(expr)
 }

 def CheckNoImmutableGhosts(expr: RValue, context: ProgramContext): Unit = {
   def specOk(e: RValue): Unit = { 
     e match {
       case ve: VariableExpr =>
         if (ve.v != null && ve.v.IsGhost && ve.v.IsImmutable) context.Error(ve.pos, "ghost const not allowed here")
       case a: Assigned =>
         if (a.v != null && a.v.IsGhost && a.v.IsImmutable) context.Error(a.pos, "ghost const not allowed here")
       case _ => visitE(e, specOk)
     }
   }
   specOk(expr)
 }

 def CheckRunSpecification(e: Expression, context: ProgramContext, allowMaxLock: boolean): unit = e match {
   case _:MaxLockLiteral =>
     if (!allowMaxLock) context.Error(e.pos, "specification of run method is not allowed to mention waitlevel here")
   case _:Literal =>
   case _:VariableExpr =>
   case _:ThisExpr =>
   case _:Result =>
   case MemberAccess(e, id) =>
     CheckRunSpecification(e, context, false)
   case Access(e, perm) =>
     CheckRunSpecification(e, context, false)
     perm match { case None => case Some(perm) => CheckRunSpecification(perm, context, false) }
   case RdAccess(e, perm) =>
     CheckRunSpecification(e, context, false)
     perm match { case Some(Some(p)) => CheckRunSpecification(p, context, false) case _ => }
   case AccessAll(obj, perm) =>
     CheckRunSpecification(obj, context, false)
     perm match { case None => case Some(perm) => CheckRunSpecification(perm, context, false) }
   case RdAccessAll(obj, perm) =>
     CheckRunSpecification(obj, context, false)
     perm match { case Some(Some(p)) => CheckRunSpecification(p, context, false) case _ => }
   case expr@ Credit(e, n) =>
     CheckRunSpecification(e, context, false)
     CheckRunSpecification(expr.N, context, false)
   case Holds(e) =>
     context.Error(e.pos, "holds is not allowed in specification of run method")
   case RdHolds(e) =>
     context.Error(e.pos, "rd holds is not allowed in specification of run method")
   case _:Assigned =>
   case Old(e) =>
     CheckRunSpecification(e, context, false)  // OLD occurs only in postconditions and monitor invariants, where waitlevel is not allowed anyhow
   case IfThenElse(con, then, els) =>
     CheckRunSpecification(con, context, false);
     CheckRunSpecification(con, context, allowMaxLock); 
     CheckRunSpecification(con, context, allowMaxLock); 
   case Not(e) =>
     CheckRunSpecification(e, context, false)
   case FunctionApplication(obj, id, args) =>
     obj :: args foreach { arg => CheckRunSpecification(arg, context, false)} 
   case Unfolding(pred, e) =>
     CheckRunSpecification(pred, context, true);
     CheckRunSpecification(e, context, allowMaxLock);
   case LockBelow(e0,e1) =>
     CheckRunSpecification(e0, context, allowMaxLock)
     CheckRunSpecification(e1, context, false)
   case And(e0,e1) =>
     CheckRunSpecification(e0, context, allowMaxLock)
     CheckRunSpecification(e1, context, allowMaxLock)
   case Implies(e0,e1) =>
     CheckRunSpecification(e0, context, false)
     CheckRunSpecification(e1, context, allowMaxLock)
   case bin: BinaryExpr =>
     CheckRunSpecification(bin.E0, context, false)
     CheckRunSpecification(bin.E1, context, false)
   case q: Quantification =>
     CheckRunSpecification(q.Seq, context, false)
     CheckRunSpecification(q.E, context, true)
   case Length(e) =>
     CheckRunSpecification(e, context, false);
   case ExplicitSeq(es) =>
     es foreach { e => CheckRunSpecification(e, context, false) }
   case Range(min, max) =>
     CheckRunSpecification(min, context, false)
     CheckRunSpecification(max, context, false)
   case Eval(h, e) =>
     h match {
       case AcquireState(obj) =>  CheckRunSpecification(obj, context, false);
       case ReleaseState(obj) =>  CheckRunSpecification(obj, context, false);
       case CallState(token, obj, id, args) => CheckRunSpecification(token, context, false); CheckRunSpecification(obj, context, false);  args foreach { a: Expression => CheckRunSpecification(a, context, false)};
     }
     CheckRunSpecification(e, context, allowMaxLock)
 }

 def visitE(expr: RValue, func: RValue => Unit): Unit = {
   expr match {
     case _:NewRhs =>
     case e: Literal => ;
     case _:ThisExpr => ;
     case _:Result => ;
     case e:VariableExpr => ;
     case acc@MemberAccess(e,f) =>
       func(e);
     case Access(e, perm) =>
       func(e); perm match { case Some(p) => func(p); case _ => ; }
     case RdAccess(e, perm) =>
       func(e); perm match { case Some(Some(p)) => func(p); case _ => ; }
     case AccessAll(obj, perm) =>
       func(obj); perm match { case Some(p) => func(p); case _ => ; }
     case RdAccessAll(obj, perm) =>
       func(obj); perm match { case Some(Some(p)) => func(p); case _ => ; }
     case Credit(e, n) =>
       func(e); n match { case Some(n) => func(n); case _ => }
     case Holds(e) => func(e);
     case RdHolds(e) => func(e);
     case e: Assigned => e
     case Old(e) => func(e);
     case IfThenElse(con, then, els) => func(con); func(then); func(els);
     case Not(e) => func(e);
     case funapp@FunctionApplication(obj, id, args) =>
       func(obj); args foreach { arg => func(arg) };
     case Unfolding(pred, e) =>
       func(pred); func(e); 
     case Iff(e0,e1) => func(e0); func(e1);
     case Implies(e0,e1) => func(e0); func(e1);
     case And(e0,e1) =>func(e0); func(e1);
     case Or(e0,e1) => func(e0); func(e1);
     case Eq(e0,e1) => func(e0); func(e1);
     case Neq(e0,e1) => func(e0); func(e1);
     case Less(e0,e1) => func(e0); func(e1);
     case AtMost(e0,e1) => func(e0); func(e1);
     case AtLeast(e0,e1) => func(e0); func(e1);
     case Greater(e0,e1) => func(e0); func(e1);
     case LockBelow(e0,e1) => func(e0); func(e1);
     case Plus(e0,e1) => func(e0); func(e1);
     case Minus(e0,e1) => func(e0); func(e1);
     case Times(e0,e1) => func(e0); func(e1);
     case Div(e0,e1) => func(e0); func(e1);
     case Mod(e0,e1) => func(e0); func(e1);
     case Forall(i, seq, e) => func(seq); func(e);
     case ExplicitSeq(es) =>
       es foreach { e => func(e) }
     case Range(min, max) =>
       func(min); func(max);
     case Append(e0, e1) =>
       func(e0); func(e1);
     case at@At(e0, e1) =>
       func(e0); func(e1);
     case Drop(e0, e1) =>
       func(e0); func(e1);
     case Take(e0, e1) =>
       func(e0); func(e1);
     case Length(e) =>
       func(e)
     case Eval(h, e) =>
       h match {
         case AcquireState(obj) => func(obj);
         case ReleaseState(obj) => func(obj);
         case CallState(token, obj, id, args) => func(token); func(obj); args foreach {a : Expression => func(a)};
       }
       func(e);
   }
 }
}
