//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional
import collection.mutable.ListBuffer

object Resolver {
 sealed abstract class ResolverOutcome
 case class Success() extends ResolverOutcome
 case class Errors(ss: List[(Position,String)]) extends ResolverOutcome

 val runMethod = "run";

 sealed class ProgramContext(val decls: Map[String,TopLevelDecl], val currentClass: Class,
                      val currentMember: Member, val errors: ListBuffer[(Position,String)]) {
   final def AddVariable(v: Variable): ProgramContext = new LProgramContext(v, this);
   final def Error(pos: Position, msg: String) {errors += ((pos, msg))}
   final def SetClass(cl: Class): ProgramContext = new MProgramContext(cl, null, this)
   final def SetMember(m: Member): ProgramContext = {
     var ctx:ProgramContext = new MProgramContext(currentClass, m, this)
     m match {
       case m: Method =>
         assert(currentClass == m.Parent)
         for (v <- m.Ins ++ m.Outs) ctx = ctx.AddVariable(v)
       case f: Function =>
         assert(currentClass == f.Parent)
         for (v <- f.ins) ctx = ctx.AddVariable(v)
       case mt: MethodTransform =>
         assert(currentClass == mt.Parent)
         for (v <- mt.Ins ++ mt.Outs) ctx = ctx.AddVariable(v)
       case _ =>
     }
     ctx
   }

   def LookupVariable(id: String): Option[Variable] = None
   def IsVariablePresent(vr: Variable): Boolean = false

   private class LProgramContext(v: Variable, parent: ProgramContext) extends ProgramContext(parent.decls, parent.currentClass, parent.currentMember, errors) {
     assert (v!=null)
     override def LookupVariable(id: String): Option[Variable] =
       if (id == v.id) Some(v) else parent.LookupVariable(id)
     override def IsVariablePresent(vr: Variable): Boolean =
       if (vr == v) true else parent.IsVariablePresent(vr)
   }
   private class MProgramContext(cl: Class, m: Member, parent: ProgramContext) extends ProgramContext(parent.decls, cl, m, errors) {
     override def LookupVariable(id: String) = parent.LookupVariable(id)
     override def IsVariablePresent(vr: Variable) = parent.IsVariablePresent(vr)
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
           val ids = scala.collection.mutable.Set.empty[String]
           for (m <- cl.members) m match {
             case _:MonitorInvariant =>
             case _:CouplingInvariant =>
             case m: NamedMember =>
               m.Parent = cl
               if (ids contains m.Id) {
                 return Errors(List((m.pos, "duplicate member name " + m.Id + " in class " + cl.id)))
               } else {
                 ids += m.Id
               }
           }
         case ch: Channel =>
       }
       decls = decls + (decl.id -> decl)
     }
   }

   // resolve refinements
   val refinesRel = new DiGraph[Class];
   for (decl <- prog) decl match {
     case cl: Class if cl.IsRefinement =>
       if (! (decls contains cl.refinesId)) {
         return Errors(List((cl.pos, "refined class " + cl.refinesId + " does not exist")))
       } else if (cl.refinesId == cl.id) {
         return Errors(List((cl.pos, "class cannot refine itself")))
       } else decls(cl.refinesId) match {
         case abs: Class =>
           cl.refines = abs;
           refinesRel.addNode(cl);
           refinesRel.addNode(cl.refines);
           refinesRel.addEdge(cl, cl.refines);
         case _ =>
           return Errors(List((cl.pos, "refined declaration " + cl.refinesId + " is not a class")))
       }
     case _ =>
   }
   val (dag, refinesSCC) = refinesRel.computeSCC;
   refinesSCC.values foreach {l =>
     if (l.size > 1) {
       val msg = new StringBuilder("a refinement cycle detected ")
       return Errors(List((l(0).pos, l.map(cl => cl.id).addString(msg, "->").toString)))
     }
   }

   // resolve refinement members: set-up refinement between members and check for duplicates
   for (decl <- prog) decl match {
     case cl: Class =>
       if (! cl.IsRefinement) {
         // check has no refinement members
         if (cl.members.exists{
           case _: CouplingInvariant => true
           case _: MethodTransform => true
           case _ => false})
           return Errors(List((cl.pos, "non-refinement class cannot have refinement members")))
       } else for (member <- cl.members) member match {
         case r: MethodTransform =>
           r.refines = cl.refines.LookupMember(r.Id) match {
             case Some(m: Method) => m;
             case Some(mt: MethodTransform) => mt
             case None => return Errors(List((r.pos, "abstract class has no method with name " + r.Id))) 
             case _ => return Errors(List((r.pos, "method transform can only refine a method or a method transform")))
           }
         case m: NamedMember =>
           cl.refines.LookupMember(m.Id) match {
             case Some(x) => return Errors(List((m.pos, "member needs to be a refinement since abstract class has a member with the same name: " + x.pos)))
             case None =>
           }
         case _ =>
       }
     case _ =>
   }

   // collect errors
   val baseContext = new ProgramContext(decls, null, null, new ListBuffer[(Position,String)])

   // resolve types of members
   for (decl <- prog) decl match {
     case ch: Channel =>
       for (v <- ch.parameters) {
         ResolveType(v.t, baseContext)
        }
     case cl: Class =>
       for (m <- cl.members) m match {
         case _: MonitorInvariant =>
         case _: CouplingInvariant =>
         case Field(_, t, _) =>
           ResolveType(t, baseContext)
         case Method(id, ins, outs, _, _) =>
           val ids = scala.collection.mutable.Set.empty[String]
           for (v <- ins ++ outs) {
             ResolveType(v.t, baseContext)
             if (ids contains v.Id) {
               return Errors(List((m.pos, "duplicate parameter " + v.Id + " of method " + id + " in class " + cl.id)))
             } else {
               ids += v.Id
             }
           }
         case _: Condition =>
         case _: Predicate =>
         case Function(id, ins, out, specs, _) => 
           val ids = scala.collection.mutable.Set.empty[String]
           for (v <- ins) {
             ResolveType(v.t, baseContext)
             if (ids contains v.Id) {
               return Errors(List((m.pos, "duplicate parameter " + v.Id + " of function " + id + " in class " + cl.id)))
             } else {
               ids += v.Id
             }
           }
           ResolveType(out, baseContext)
         case mt: MethodTransform =>
           val ids = scala.collection.mutable.Set.empty[String]
           for (v <- mt.ins ++ mt.outs) {
             ResolveType(v.t, baseContext)
             if (ids contains v.Id) {
               return Errors(List((m.pos, "duplicate parameter " + v.Id + " of method transform " + mt.Id + " in class " + cl.id)))
             } else {
               ids += v.Id
             }
           }
       }
   }   

   // now, resolve and typecheck all
   //  * Field types and Method formal-parameter types
   //  * Assign, FieldUpdate, and Call statements
   //  * VariableExpr and FieldSelect expressions
   //  * Call graph for functions
   val calls = new DiGraph[Function];
   for (decl <- prog) decl match {
     case ch: Channel =>
       val context = baseContext.SetClass(ChannelClass(ch))
       var ctx = context
       for (v <- ch.parameters) {
         ctx = ctx.AddVariable(v)
       }
       ResolveExpr(ch.where, ctx, false, true)(false)
     case cl: Class =>
       for (m <- cl.members) {
         val context = baseContext.SetClass(cl).SetMember(m);
         m match {
           case MonitorInvariant(e) =>
             ResolveExpr(e, context, true, true)(true)
             if (!e.typ.IsBool) context.Error(m.pos, "monitor invariant requires a boolean expression (found " + e.typ.FullName + ")")
           case _:Field => // nothing more to do
           case m@Method(id, ins, outs, spec, body) =>
             spec foreach {
               case Precondition(e) => ResolveExpr(e, context, false, true)(false)
               case Postcondition(e) => ResolveExpr(e, context, true, true)(false)
               case lc@LockChange(ee) => 
               if (m.id == runMethod) context.Error(lc.pos, "lockchange not allowed on method run")
               ee foreach (e => ResolveExpr(e, context, true, false)(false))
             }
             ResolveStmt(BlockStmt(body), context)
           case Condition(id, None) =>
           case c@Condition(id, Some(e)) =>
             ResolveExpr(e, context, false, true)(false)
             if (!e.typ.IsBool) context.Error(c.pos, "where clause requires a boolean expression (found " + e.typ.FullName + ")")
           case p@Predicate(id, e) =>
             var ctx = context;
             ResolveExpr(e, ctx, false, true)(true);
             if(!e.typ.IsBool) context.Error(e.pos, "predicate requires a boolean expression (found " + e.typ.FullName + ")")
           case f@Function(id, ins, out, spec, definition) =>
              // TODO: disallow credit(...) expressions in function specifications
             spec foreach {
               case Precondition(e) => ResolveExpr(e, context, false, true)(false)
               case Postcondition(e) => ResolveExpr(e, context, false, true)(false)
               case lc : LockChange => context.Error(lc.pos, "lockchange not allowed on function") 
             }

             definition match {
               case Some(e) =>
                 ResolveExpr(e, context, false, false)(false)
                 if(! canAssign(out.typ, e.typ)) context.Error(e.pos, "function body does not match declared type (expected: " + out.FullName + ", found: " + e.typ.FullName + ")")
                 // resolve function calls
                 calls addNode f;
                 e visit {
                   case app : FunctionApplication if app.f != null /* may not be resolved */ =>
                     calls addNode app.f;
                     calls.addEdge(f, app.f);
                     if (app.f == f) f.isRecursive = true; // self-recursion
                   case _ =>
                 }
               case None =>
             }
           case mt: MethodTransform => // need to resolve them in reverse refinement order
           case ci: CouplingInvariant => ResolveCouplingInvariant(ci, cl, baseContext)
         }
       }
   }

   // fill in SCC for recursive functions 
   val (_, h) = calls.computeSCC;
   h.keys foreach {f:Function =>
     f.SCC = h(f);
     assert(f.SCC contains f);
     if (h(f).size > 1)
       f.isRecursive = true;
   }

   // resolve refinement members (starting from abstract programs): assign types to expressions
   for (List(cl) <- dag.computeTopologicalSort.reverse) {
     for (m <- cl.members) m match {
       case mt: MethodTransform => ResolveTransform(mt, baseContext)
       case _ =>
     }
   }

   val errors = baseContext.errors.toList
   if (errors.length == 0) {
     Success()
   } else {
     Errors(errors)
   }
 }

 def ResolveType(t: Type, context: ProgramContext): Unit = {
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
     if (context.decls contains t.FullName) {
       context.decls(t.FullName) match {
         case cl: Class => t.typ = cl
         case ch: Channel => t.typ = ChannelClass(ch)
         case _ =>
           context.Error(t.pos, "Invalid class: " + t.FullName + " does not denote a class")
           t.typ = IntClass
       }
     } else {
       if(t.id.equals("seq") && t.params.length == 1) {
         t.typ = new SeqClass(t.params(0).typ);
       } else {
         context.Error(t.pos, "undeclared type " + t.FullName)
         t.typ = IntClass
       }
     }
 }

 def ResolveStmt(s: Statement, context: ProgramContext):Unit = s match {
   case Assert(e) =>
     ResolveExpr(e, context, true, true)(false)
     if (!e.typ.IsBool) context.Error(e.pos, "assert statement requires a boolean expression (found " + e.typ.FullName + ")")
   case Assume(e) =>
     ResolveExpr(e, context, true, true)(false)  
     if (!e.typ.IsBool) context.Error(e.pos, "assume statement requires a boolean expression (found " + e.typ.FullName + ")")
   case RefinementBlock(ss, _) => throw new InternalErrorException("unexpected statement")
   case BlockStmt(ss) =>
     var ctx = context
     for (s <- ss) s match {
       case l @ LocalVar(v, rhs) =>
         if (ctx.LookupVariable(v.id).isDefined) {
           context.Error(l.pos, "local variable name "+v.id+" collides with parameter or other local variable")
         }
         ResolveType(v.t, ctx)
         val oldCtx = ctx
         ctx = ctx.AddVariable(v)
         rhs match {
           case None =>
           case Some(rhs) =>
             val lhs = VariableExpr(v.id)
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
       case s: SpecStmt =>
         for (v <- s.locals) { ResolveType(v.t, ctx); ctx = ctx.AddVariable(v) }
         for (v <- s.lhs) {
           ResolveExpr(v, ctx, true, true)(false)
           if (v.v != null && !s.locals.contains(v.v) && v.v.isImmutable)
             context.Error(s.pos, "Immutable variable cannot be updated by a spec statement: " + v.id);           
         }
         ResolveExpr(s.pre, ctx, false, true)(false)
         ResolveExpr(s.post, ctx, true, true)(false)
       case s =>
         ResolveStmt(s, ctx)
     }
   case IfStmt(guard, thn, els) =>
     ResolveExpr(guard, context, false, false)(false)
     if (!guard.typ.IsBool) context.Error(guard.pos, "if statement requires a boolean guard (found " + guard.typ.FullName + ")")
     CheckNoGhost(guard, context)
     ResolveStmt(thn, context)
     els match { case None => case Some(s) => ResolveStmt(s, context) }
   case w@ WhileStmt(guard, invs, ref, lkch, body) =>
     if (ref.size > 0) throw new InternalErrorException("unexpected statement")
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
     w.LoopTargets = body.Targets.filter(context.IsVariablePresent).toList
   case Assign(lhs, rhs) =>
     ResolveExpr(lhs, context, false, false)(false)
     ResolveAssign(lhs, rhs, context)
     if (lhs.v != null && lhs.v.isImmutable) {
       if (lhs.v.isGhost)
         CheckNoGhost(rhs, context)
       else
         context.Error(lhs.pos, "cannot assign to immutable variable " + lhs.v.id)
     }
   case fu@FieldUpdate(lhs, rhs) =>
     ResolveExpr(lhs, context, false, false)(false)
     if (! lhs.isPredicate && lhs.f != null && !lhs.f.isGhost) CheckNoGhost(lhs.e, context)
     if (! lhs.isPredicate && lhs.f.isInstanceOf[SpecialField]) context.Error(lhs.pos, "cannot assign directly to special field: " + lhs.id)
     ResolveExpr(rhs, context, false, false)(false)
     if (! lhs.isPredicate && !canAssign(lhs.typ, rhs.typ)) context.Error(fu.pos, "type mismatch in assignment, lhs=" + lhs.typ.FullName + " rhs=" + rhs.typ.FullName)
     if (! lhs.isPredicate && lhs.f != null && !lhs.f.isGhost) CheckNoGhost(rhs, context)
   case _:LocalVar => throw new InternalErrorException("unexpected LocalVar; should have been handled in BlockStmt above")
   case _:SpecStmt => throw new InternalErrorException("should have been handled before")
   case c @ Call(declaresLocal, lhs, obj, id, args) =>
     ResolveExpr(obj, context, false, false)(false)
     CheckNoGhost(obj, context)
     args foreach { a => ResolveExpr(a, context, false, false)(false); CheckNoGhost(a, context) }
     // lookup method
     var typ: Class = IntClass
     c.m = obj.typ.LookupMember(id) match {
       case None =>
         context.Error(c.pos, "call of undeclared member " + id + " in class " + obj.typ.FullName)
         null
       case Some(m: Method) => m
       case Some(mt: MethodTransform) => mt
       case _ =>
         context.Error(c.pos, "call expression does not denote a method: " + obj.typ.FullName + "." + id)
         null
     }
     if (c.m != null) {
       if (args.size != c.m.Ins.size)
         context.Error(c.pos, "wrong number of actual in-parameters in call to " + obj.typ.FullName + "." + id +
                       " (" + args.size + " instead of " + c.m.Ins.size + ")")
       else {
         for((actual, formal) <- args zip c.m.Ins){
           if(! canAssign(formal.t.typ, actual.typ))
             context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
         }
       }
       if (lhs.size != c.m.Outs.size)
         context.Error(c.pos, "wrong number of actual out-parameters in call to " + obj.typ.FullName + "." + id +
                       " (" + lhs.size + " instead of " + c.m.Outs.size + ")")
       else
         c.locals = ResolveLHS(declaresLocal, lhs, c.m.Outs, context)
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
     if(!e.ma.isPredicate) context.Error(fld.pos, "Fold can only be applied to predicates.")
   case ufld@Unfold(e) =>
     ResolveExpr(e, context, false, true)(false);
     CheckNoGhost(e, context);
     if(!e.ma.isPredicate) context.Error(ufld.pos, "Unfold can only be applied to predicates.")
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
         if (v.v.isImmutable) context.Error(v.pos, "cannot use immutable variable " + v.id + " as actual out-parameter")
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

 def ResolveLHS(declaresLocal: List[Boolean], actuals: List[VariableExpr], formals: List[Variable], context: ProgramContext): List[Variable] = {
   var locals = List[Variable]()
   var vars = Set[Variable]()
   var ctx = context
   for (((declareLocal, actual), formal) <- declaresLocal zip actuals zip formals) {
     if (declareLocal) {
       val local = new Variable(actual.id, new Type(formal.t.typ))
       locals = locals ::: List(local)
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
         else if (actual.v.isImmutable)
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

 def ResolveAssign(lhs: VariableExpr, rhs: RValue, context: ProgramContext) = {
   rhs match {
     case ExplicitSeq(Nil) => rhs.typ = lhs.typ; // if [] appears on the rhs of an assignment, we "infer" its type by looking at the type of the lhs
     case _ => ResolveExpr(rhs, context, false, false)(false)
   }
   if (! canAssign(lhs.typ, rhs.typ))
     context.Error(lhs.pos, "type mismatch in assignment, lhs=" + lhs.typ.FullName + " rhs=" + rhs.typ.FullName)
   if (lhs.v != null && !lhs.v.isGhost) CheckNoGhost(rhs, context)
 }
 
 // ResolvePermissionExpr resolves all parts of a permission expression, and replaces arithmetic operations
 // by the appropriate operation on permissions
 // Note that the parsing of permissions can be highly inaccurate. Besides historic reasons, we also need type information
 // to decide how rd(x) inside acc(o.f, ***) should be interpreted. If x is an integer expression, it stands for Epsilons(x),
 // but x could also be a channel, monitor or predicate.
 // For instance, acc(x,rd(n)) is parsed to
 //    Access(MemberAccess(ImplicitThisExpr(),x),Frac(Access(MemberAccess(ImplicitThisExpr(),n),Epsilon)))
 // These error during parsing are corrected here during the resolve process. In particular, the following corrections are done:
 // - Plus and Minus are replaced by the corresponding operation on permission (i.e. PermPlus and PermMinus)
 // - Integer expressions x are replaced by Frac(x)
 def ResolvePermissionExpr(e: Expression, context: ProgramContext, twoStateContext: Boolean,
                 specContext: Boolean, pos: Position)(implicit inPredicate: Boolean): Permission = e match {
   case ve @ VariableExpr(id) =>
     ResolvePermissionExpr(Frac(ve), context, twoStateContext, specContext, pos)(inPredicate);
   case f @ Frac(perm) =>
     ResolveExpr(perm, context, twoStateContext, false);
     if(perm.typ != IntClass)
       context.Error(pos, "fraction in permission must be of type integer")
     f
   case sel @ MemberAccess(e, id) =>
     ResolvePermissionExpr(Frac(sel), context, twoStateContext, specContext, pos)(inPredicate);
   case ep @ Epsilons(exp) => 
     ResolveExpr(exp, context, twoStateContext, false)
     var p: Permission = Epsilon
     exp.typ match {
       case BoolClass if exp.isInstanceOf[MemberAccess] && exp.asInstanceOf[MemberAccess].isPredicate =>
         p = PredicateEpsilon(Some(exp.asInstanceOf[MemberAccess]))
         p.pos = ep.pos
       case IntClass =>
         p = Epsilons(exp)
         p.pos = ep.pos
       case TokenClass(c, m) =>
         p = ForkEpsilon(exp)
         p.pos = ep.pos
       case c:Channel =>
         p = ChannelEpsilon(Some(exp))
         p.pos = ep.pos
       case c:Class if (c.IsNormalClass) =>
         p = MonitorEpsilon(Some(exp))
         p.pos = ep.pos
       case _ =>
         p = Star
         context.Error(ep.pos, "type " + exp.typ.FullName + " is not supported inside a rd expression.");
     }
     exp.pos = ep.pos
     p
   case f @ Full => f
   case f:PredicateEpsilon => f
   case f:ForkEpsilon => f
   case f:ChannelEpsilon => f
   case f:MonitorEpsilon => f
   case Epsilon => Epsilon
   case MethodEpsilon => MethodEpsilon
   case f @ Star => f
   case p @ Plus(ee0, ee1) =>
     if (ContainsStar(ee0) || ContainsStar(ee1))
       context.Error(p.pos, "rd* is not allowed inside permission expressions.")
     val e0 = ResolvePermissionExpr(ee0, context, twoStateContext, specContext, pos)(inPredicate);
     val e1 = ResolvePermissionExpr(ee1, context, twoStateContext, specContext, pos)(inPredicate);
     val pp = PermPlus(e0, e1)
     pp.pos = p.pos;
     pp
   case p @ Minus(ee0, ee1) =>
     if (ContainsStar(ee0) || ContainsStar(ee1))
       context.Error(p.pos, "rd* is not allowed inside permission expressions.")
     val e0 = ResolvePermissionExpr(ee0, context, twoStateContext, specContext, pos)(inPredicate);
     val e1 = ResolvePermissionExpr(ee1, context, twoStateContext, specContext, pos)(inPredicate);
     val pp = PermMinus(e0, e1)
     pp.pos = p.pos;
     pp
   case a @ Access(sel @ MemberAccess(e, id),Epsilon) =>
     var exp: Expression = sel
     var typ: Class = null
     if (e.getClass == classOf[ImplicitThisExpr]) { // id could be a local variable, if e == ImplicitThisExpr()
       val ve = VariableExpr(id)
       context.LookupVariable(id) match {
         case Some(v) => ve.Resolve(v); typ = ve.typ; exp = ve;
         case None =>
       }
     }
     if (typ == null) {
       ResolveExpr(e, context, twoStateContext, false)
       e.typ.LookupMember(id) match {
         case None =>
           context.Error(sel.pos, "undeclared member " + id + " in class " + e.typ.FullName)
         case Some(f: Field) => sel.f = f; typ = f.typ.typ
         case Some(pred@Predicate(id, body)) =>
           sel.predicate = pred;
           sel.isPredicate = true;
           typ = BoolClass
         case _ => context.Error(sel.pos, "field-select expression does not denote a field: " + e.typ.FullName + "." + id);
       }
       sel.typ = typ
       exp = sel
     }
     var p: Permission = Epsilon
     typ match {
       case BoolClass if sel.isPredicate =>
         p = PredicateEpsilon(Some(sel))
         p.pos = a.pos
       case IntClass =>
         p = Epsilons(exp)
         p.pos = a.pos
       case TokenClass(c, m) =>
         p = ForkEpsilon(exp)
         p.pos = a.pos
       case c:Channel =>
         p = ChannelEpsilon(Some(exp))
         p.pos = a.pos
       case c:Class if (c.IsNormalClass) =>
         p = MonitorEpsilon(Some(exp))
         p.pos = a.pos
       case _ =>
         context.Error(a.pos, "type " + typ.FullName + " of variable " + id + " is not supported inside a rd expression.")
         p = Star
     }
     exp.pos = a.pos
     p
   // multiplication is a bit tricky: we want to support integer multiplication i0*i1 (which will
   // correspond to a percentage i0*i1), but also the multiplication of an integer i0 with a permission
   // amount p1 (and vice versa): i0*p1 or p0*i1.
   // we first try to resolve both expressions as integer, and if not successful, try again as
   // permission amount
   case bin @ Times(e0, e1) =>
     var p0, p1: Permission = null
     var ee0 = e0
     var ee1 = e1
     var oldErrors = (new ListBuffer[(Position,String)]) ++= context.errors
     ResolveExpr(bin.E0, context, twoStateContext, false)
     if (context.errors.size > oldErrors.size) {
       context.errors.clear; context.errors ++= oldErrors // reset errors
       p0 = ResolvePermissionExpr(bin.E0, context, twoStateContext, specContext, pos)(inPredicate)
       ee0 = p0
     }
     
     oldErrors = (new ListBuffer[(Position,String)]) ++= context.errors
     ResolveExpr(bin.E1, context, twoStateContext, false)
     if (context.errors.size > oldErrors.size) {
       context.errors.clear; context.errors ++= oldErrors // reset errors
       p1 = ResolvePermissionExpr(bin.E1, context, twoStateContext, specContext, pos)(inPredicate)
       ee1 = p1
     }
     
     if (ee0.typ.IsInt && ee1.typ.IsInt) {
       bin.typ = IntClass
       val pp = Frac(bin)
       pp.pos = bin.pos
       pp
     } else if (ee0.typ.IsInt && ee1.typ.IsPermission) {
       val pp = IntPermTimes(ee0,p1)
       pp.pos = bin.pos
       pp
     } else if (ee0.typ.IsPermission && ee1.typ.IsInt) {
       val pp = IntPermTimes(ee1,p0)
       pp.pos = bin.pos
       pp
     } else {
       context.Error(pos, "multiplication of permission amounts not supported"); Star
     }
   case expr =>
     ResolveExpr(expr, context, twoStateContext, specContext)(inPredicate);
     if (expr.typ == IntClass) {
       val pp = Frac(expr)
       pp.pos = expr.pos;
       pp
     } else {
       context.Error(pos, "expression of type " + expr.typ.FullName + " invalid in permission"); Star
     }
 }
 
 // does e contain a Star (i.e., rd*)?
 def ContainsStar(expr: Expression): Boolean = {
   var x: Boolean = false
   AST.visit(expr,
     e => e match {
       case Star => x = true
       case _ =>
     }
   )
   x
 }

 // ResolveExpr resolves all parts of an RValue, if possible, and (always) sets the RValue's typ field
 def ResolveExpr(e: RValue, context: ProgramContext,
                 twoStateContext: Boolean, specContext: Boolean)(implicit inPredicate: Boolean): Unit = e match {
   case e @ NewRhs(id, initialization, lower, upper) =>
     if (context.decls contains id) {
       context.decls(id) match {
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
             case Some(field@Field(name, tp, _)) =>
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
     assert(context.currentMember!=null);
     r.typ = IntClass
     if(context.currentMember==null || ! context.currentMember.isInstanceOf[Function]){
       context.Error(r.pos, "The variable result can only be used in the postcondition of a function.");
     } else {
       r.typ = context.currentMember.asInstanceOf[Function].out.typ;
     }
   case ve @ VariableExpr(id) =>
     context.LookupVariable(id) match {
       case None => context.Error(ve.pos, "undefined local variable " + id); ve.typ = IntClass
       case Some(v) => ve.Resolve(v) }
   case v:ThisExpr => v.typ = context.currentClass
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
   case p: Permission => context.Error(p.pos, "permission not expected here.")
   case expr @ Access(e, perm) =>
     if (!specContext) context.Error(expr.pos, permExpressionName(perm) + " expression is allowed only in positive predicate contexts")
     ResolveExpr(e, context, twoStateContext, true)
     val p = ResolvePermissionExpr(perm match { case Frac(f) => f; case o => o;}, context, twoStateContext, false, expr.pos);
     expr.perm = p;
     expr.typ = BoolClass
   case expr @ AccessAll(obj, perm) =>
     if (!specContext) context.Error(expr.pos, permExpressionName(perm) + " expression is allowed only in positive predicate contexts")
     ResolveExpr(obj, context, twoStateContext, false)
     if(!obj.typ.IsRef) context.Error(expr.pos, "Target of .* must be object reference.")
     val p = ResolvePermissionExpr(perm match { case Frac(f) => f; case o => o;}, context, twoStateContext, false, expr.pos);
     expr.perm = p;
     expr.typ = BoolClass
   case expr @ AccessSeq(s, f, perm) =>
     if (!specContext) context.Error(expr.pos, permExpressionName(perm) + " expression is allowed only in positive predicate contexts")
     ResolveExpr(s, context, twoStateContext, false)
     if(!s.typ.IsSeq) context.Error(expr.pos, "Target of [*] must be sequence.")
     val p = ResolvePermissionExpr(perm match { case Frac(f) => f; case o => o;}, context, twoStateContext, false, expr.pos);
     expr.perm = p;
     f match {
       case Some(x) =>
         ResolveExpr(x, context, twoStateContext, true);
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
         if (!(v.isImmutable && v.isGhost))
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
     if(! pred.ma.isPredicate) context.Error(uf.pos, "Only predicates can be unfolded.")
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
   case contains@Contains(e0, e1) =>
     ResolveExpr(e0, context, twoStateContext, false);
     ResolveExpr(e1, context, twoStateContext, false);
     if(! e1.typ.IsSeq)
       context.Error(contains.pos, "RHS operand of 'in' must be sequence. (found: " + e1.typ.FullName + ").");
     else if(! canAssign(e1.typ.parameters(0), e0.typ))
       context.Error(contains.pos, "LHS operand's type must be element type of sequence. (found: " + e0.typ.FullName + ", expected: " + e1.typ.parameters(0).FullName + ").");
     contains.typ = BoolClass;
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
     q.Is foreach { i => if(context.LookupVariable(i).isDefined) context.Error(q.pos, "The variable " + i + " hides another local.") };
     val typ = q match {
       case q: SeqQuantification =>
         ResolveExpr(q.seq, context, twoStateContext, false);
         if(! q.seq.typ.IsSeq) {
           context.Error(q.seq.pos, "A quantification must range over a sequence. (found: " + q.seq.typ.FullName + ").");
           None;
         } else
           Some(q.seq.typ.parameters(0));
       case q: TypeQuantification =>
         ResolveType(q.t, context);
         if (q.t.typ == null) None else Some(q.t.typ);
     };

     if (typ.isDefined) {
       val vartype = typ.get;
       var bodyContext = context;
       var bvariables = Nil: List[Variable];
       q.Is foreach { i =>
         val variable = new Variable(i, new Type(vartype));
         bodyContext = bodyContext.AddVariable(variable);
         bvariables = bvariables ::: List(variable);
       }
       ResolveExpr(q.E, bodyContext, twoStateContext, true);
       if(! q.E.typ.IsBool) context.Error(q.E.pos, "Body of quantification must be a boolean. (found: " +  q.E.typ.FullName + ").");
       q.variables = bvariables;
     }
     q.typ = BoolClass
   case seq@EmptySeq(t) =>
     ResolveType(t, context)
     seq.typ = SeqClass(t.typ);
   case seq@ExplicitSeq(es) =>
     es foreach { e => ResolveExpr(e, context, twoStateContext, false) }
     es match {
       case Nil => seq.typ = SeqClass(IntClass);
       case h :: t =>
         t foreach { e => if(! (e.typ == h.typ)) context.Error(e.pos, "The elements of the sequence expression have different types.")};
         seq.typ = SeqClass(h.typ);
     }
   case ran@Range(min, max) =>
     ResolveExpr(min, context, twoStateContext, false);
     if(! min.typ.IsInt) context.Error(min.pos, "The mininum of a range expression must be an integer (found: " + min.typ.FullName + ").");
     ResolveExpr(max, context, twoStateContext, false);
     if(! max.typ.IsInt) context.Error(max.pos, "The maximum of a range expression must be an integer (found: " + max.typ.FullName + ").");
     ran.typ = SeqClass(IntClass);
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
         args foreach { a => a match {
            case VariableExpr("?") => 
            case _ => ResolveExpr(a, context, false, false); CheckNoGhost(a, context)
         }}
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
                 actual match {
                    case VariableExpr("?") =>
                    case _ => if (!canAssign(formal.t.typ, actual.typ))
                        context.Error(actual.pos, "the type of the actual argument is not assignable to the formal parameter (expected: " + formal.t.FullName + ", found: " + actual.typ.FullName + ")")
                 }
                 
             }
           }
         case _ => context.Error(obj.pos, "call expression does not denote a method: " + obj.typ.FullName + "." + id)
     }
           
         
     }
     ResolveExpr(e, context, false, specContext)
     ev.typ = e.typ;
 }

 def LookupRunMethod(cl: Class, context: ProgramContext, op: String, pos: Position): Option[Method] = {
   cl.LookupMember(runMethod) match {
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
   AST.visit(expr, e => e match {
     case ve: VariableExpr =>
       if (ve.v != null && ve.v.isGhost) context.Error(ve.pos, "ghost variable not allowed here")
     case fs@ MemberAccess(e, id) =>
       if (!fs.isPredicate && fs.f != null && fs.f.isGhost) context.Error(fs.pos, "ghost fields not allowed here")
     case a: Assigned =>
       if (a.v != null && a.v.isGhost) context.Error(a.pos, "ghost variable not allowed here")
     case _ => // do nothing
   })   
 }

 def CheckNoImmutableGhosts(expr: RValue, context: ProgramContext): Unit = {
   AST.visit(expr, e => e match {
     case ve: VariableExpr =>
       if (ve.v != null && ve.v.isGhost && ve.v.isImmutable) context.Error(ve.pos, "ghost const not allowed here")
     case a: Assigned =>
       if (a.v != null && a.v.isGhost && a.v.isImmutable) context.Error(a.pos, "ghost const not allowed here")
     case _ => // do nothing
   })
 }

 def CheckRunSpecification(e: Expression, context: ProgramContext, allowMaxLock: Boolean): Unit = e match {
   case _:MaxLockLiteral =>
     if (!allowMaxLock) context.Error(e.pos, "specification of run method is not allowed to mention waitlevel here")
   case _:Literal =>
   case _:VariableExpr =>
   case _:ThisExpr =>
   case _:Result =>
   case MemberAccess(e, id) =>
     CheckRunSpecification(e, context, false)
   case Frac(perm) => CheckRunSpecification(perm, context, false)
   case Epsilons(perm) => CheckRunSpecification(perm, context, false)
   case PermPlus(p0, p1) =>
     CheckRunSpecification(p0, context, false)
     CheckRunSpecification(p1, context, false)
   case PermMinus(p0, p1) =>
     CheckRunSpecification(p0, context, false)
     CheckRunSpecification(p1, context, false)
   case PermTimes(p0, p1) =>
     CheckRunSpecification(p0, context, false)
     CheckRunSpecification(p1, context, false)
   case IntPermTimes(p0, p1) =>
     CheckRunSpecification(p0, context, false)
     CheckRunSpecification(p1, context, false)
   case Full | Epsilon | Star | MethodEpsilon =>
   case ChannelEpsilon(None) | PredicateEpsilon(None) | MonitorEpsilon(None) =>;
   case ChannelEpsilon(Some(e)) => CheckRunSpecification(e, context, false);
   case PredicateEpsilon(Some(e)) => CheckRunSpecification(e, context, false);
   case MonitorEpsilon(Some(e)) => CheckRunSpecification(e, context, false);
   case ForkEpsilon(tk) => CheckRunSpecification(tk, context, false);
   case Access(e, perm) =>
     CheckRunSpecification(e, context, false);
     CheckRunSpecification(perm, context, false);
   case AccessAll(obj, perm) =>
     CheckRunSpecification(obj, context, false);
     CheckRunSpecification(perm, context, false);
   case AccessSeq(s, f, perm) =>
     CheckRunSpecification(s, context, false);
     CheckRunSpecification(perm, context, false);
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
   case q: SeqQuantification =>
     CheckRunSpecification(q.seq, context, false)
     CheckRunSpecification(q.e, context, true)
   case q: TypeQuantification =>
     CheckRunSpecification(q.e, context, true)
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

 def ResolveTransform(mt: MethodTransform, context: ProgramContext) {
   mt.spec foreach {
     case Precondition(e) =>
       context.Error(e.pos, "Method refinement cannot add a pre-condition")
     case Postcondition(e) =>
       ResolveExpr(e, context.SetClass(mt.Parent).SetMember(mt), true, true)(false)
     case _ : LockChange => throw new NotSupportedException("not implemented")
   }
   if (mt.ins != mt.refines.Ins) context.Error(mt.pos, "Refinement must have same input arguments")
   if (! mt.outs.startsWith(mt.refines.Outs)) context.Error(mt.pos, "Refinement must declare all abstract output variables")

   mt.body = AST.refine(mt.refines.Body, mt.trans) match {
     case AST.Matched(ss) => ss
     case AST.Unmatched(t) => context.Error(mt.pos, "Cannot match transform around " + t.pos); Nil
   }
                                
   def resolveBody(ss: List[Statement], con: ProgramContext, abs: List[Variable]) {
     var ctx = con;
     var locals = abs;
     for (s <- ss) {
       s match {
         case r @ RefinementBlock(c, a) =>
           // abstract globals available at this point in the program
           r.before = locals
           ResolveStmt(BlockStmt(c), ctx)
           val vs = c flatMap {s => s.Declares};
           for (v <- a flatMap {s => s.Declares}; if (! vs.contains(v)))
             ctx.Error(r.pos, "Refinement block must declare a local variable from abstract program: " + v.id)
         case w @ WhileStmt(guard, oi, ni, lks, body) =>
           for (inv <- ni) {
             ResolveExpr(inv, ctx, true, true)(false)
             if (!inv.typ.IsBool) ctx.Error(inv.pos, "loop invariant must be boolean (found " + inv.typ.FullName + ")")
           }
           resolveBody(body.ss, ctx, locals)
           w.LoopTargets = body.Targets.filter(ctx.IsVariablePresent).toList
         case IfStmt(_, thn, None) =>
           resolveBody(thn.ss, ctx, locals)
         case IfStmt(_, thn, Some(els)) =>
           resolveBody(thn.ss, ctx, locals)
           resolveBody(List(els), ctx, locals)
         case BlockStmt(ss) =>
           resolveBody(ss, ctx, locals)
         case _ =>
       }
       // declare concrete and abstract locals
       for (v <- s.Declares) ctx = ctx.AddVariable(v);
       s match {
         case RefinementBlock(_, a) => locals = locals ++ (a flatMap {s => s.Declares})
         case _ => locals = locals ++ s.Declares 
       }
     }
   }
   resolveBody(mt.body, context.SetClass(mt.Parent).SetMember(mt), Nil)
 }

 def ResolveCouplingInvariant(ci: CouplingInvariant, cl: Class, context: ProgramContext) {
   assert (cl.IsRefinement)
   for (id <- ci.ids) cl.refines.LookupMember(id) match {
     case Some(f: Field) => ci.fields = f :: ci.fields
     case Some(_) => context.Error(ci.pos, "coupling invariant can only be bound to a field of the abstract program")
     case None => context.Error(ci.pos, "coupling invariant does not refer to a member of the abstract program")
   }
   ResolveExpr(ci.e, context.SetClass(cl).SetMember(ci), false, true)(true)
   if (!ci.e.typ.IsBool) context.Error(ci.pos, "coupling invariant requires a boolean expression (found " + ci.e.typ.FullName + ")")
   // TODO: check coupling invariant may only give permissions to newly declared fields
   // TODO: check concrete body cannot refer to replaced fields
 }
 
 // TODO: this method might need to be replaced at some point. it is not possible
 // to decide what name is used on the source level just by the permission (e.g.,
 // Epsilons can be rd(x,1) or acc(x,rd(1))
 def permExpressionName(perm: Permission): String = {
   perm match {
     case _:Epsilons => "rd";
     case Epsilon => "rd";
     case MethodEpsilon => "rd"
     case Star => "rd";
     case Full => "acc";
     case _:Frac => "acc";
     case _:ArithmeticPermission => "acc";
     case _:ChannelEpsilon | _:ForkEpsilon | _:MonitorEpsilon | _:PredicateEpsilon => "acc";
   }
 }
}
