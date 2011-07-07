//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

import Boogie.Proc, Boogie.NamedType, Boogie.NewBVar, Boogie.Havoc, Boogie.Stmt, Boogie.Const,
       Boogie.Decl, Boogie.Expr, Boogie.FunctionApp, Boogie.Axiom, Boogie.BVar, Boogie.BType,
       Boogie.VarExpr, Boogie.IndexedType, Boogie.Comment, Boogie.MapUpdate, Boogie.MapSelect,
       Boogie.If, Boogie.Lambda, Boogie.Trigger;

case class ErrorMessage(pos: Position, message: String)

class Translator {
  import TranslationHelper._;
  var currentClass = null: Class;
  var modules = Nil: List[String]
  var etran = new ExpressionTranslator(null);

  def translateProgram(decls: List[TopLevelDecl]): List[Decl] = {
    decls flatMap {
      case cl: Class => translateClass(cl)
      case ch: Channel => translateClass(ChannelClass(ch))
        /* TODO: admissibility check of where clause */
        /* TODO: waitlevel not allowed in postcondition of things forked (or, rather, joined) */
    }
  }

  def translateClass(cl: Class): List[Decl] = {
    currentClass = cl;
    etran = new ExpressionTranslator(cl);
    var declarations: List[Decl] = Nil;
    // add module (if no added yet)
    if(modules forall {mname => ! mname.equals(cl.module)}) {
      declarations = Const(ModuleName(cl), true, ModuleType) :: declarations;
      modules = cl.module :: modules;
    }
    // add class name
    declarations = Const(className(cl).id, true, TypeName) :: declarations;
    // translate monitor invariant
    declarations = declarations ::: translateMonitorInvariant(cl.MonitorInvariants, cl.pos);
    // translate each member
    for(member <- cl.members) {
      declarations = declarations ::: translateMember(member);
    }
    declarations
  }

  /**********************************************************************
  *****************            MEMBERS                  *****************
  **********************************************************************/

  def translateMember(member: Member): List[Decl] = {
    member match {
      case f: Field =>
        translateField(f)
      case m: Method =>
        translateMethod(m)
      case f: Function => 
        translateFunction(f)
      case pred: Predicate =>
        translatePredicate(pred)
      case inv: MonitorInvariant =>
        Nil // already dealt with before
      case _: Condition =>
        throw new NotSupportedException("not yet implemented")
      case mt: MethodTransform =>
        translateMethodTransform(mt)
      case ci: CouplingInvariant =>
        Nil
    }
  }

  def translateMonitorInvariant(invs: List[MonitorInvariant], pos: Position): List[Decl] = {
    val (h0V, h0) = NewBVar("h0", theap, true); val (m0V, m0) = NewBVar("m0", tmask, true);
    val (c0V, c0) = NewBVar("c0", tcredits, true);
    val (h1V, h1) = NewBVar("h1", theap, true); val (m1V, m1) = NewBVar("m1", tmask, true);
    val (c1V, c1) = NewBVar("c1", tcredits, true);
    val (lkV, lk) = NewBVar("lk", tref, true);
    
    // pick new k
    val (methodKV, methodK) = Boogie.NewBVar("methodK", tint, true)
    val methodKStmts = BLocal(methodKV) :: bassume(0 < methodK && 1000*methodK < permissionOnePercent)
    
    val oldTranslator = new ExpressionTranslator(List(h1, m1, c1), List(h0, m0, c0), currentClass);
    Proc(currentClass.id + "$monitorinvariant$checkDefinedness",
      List(NewBVarWhere("this", new Type(currentClass))),
      Nil,
      GlobalNames,
      DefaultPrecondition(),
        methodKStmts :::
        BLocal(h0V) :: BLocal(m0V) :: BLocal(c0V) :: BLocal(h1V) :: BLocal(m1V) :: BLocal(c1V) :: BLocal(lkV) ::
        bassume(wf(h0, m0)) :: bassume(wf(h1, m1)) ::
        (oldTranslator.Mask := ZeroMask) :: (oldTranslator.Credits := ZeroCredits) ::
        oldTranslator.Inhale(invs map { mi => mi.e}, "monitor invariant", false, methodK) :::
        (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
        Havoc(etran.Heap) ::
        // check that invariant is well-defined
        etran.WhereOldIs(h1, m1, c1).Inhale(invs map { mi => mi.e}, "monitor invariant", true, methodK) :::
        (if (! Chalice.checkLeaks || invs.length == 0) Nil else
          // check that there are no loops among .mu permissions in monitors
          // !CanWrite[this,mu]
          bassert(!etran.CanWrite(VarExpr("this"), "mu"), invs(0).pos, "Monitor invariant is not allowed to hold write permission to this.mu") ::
          // (forall lk :: lk != null && lk != this && CanRead[lk,mu] ==>
          //   CanRead[this,mu] && Heap[this,mu] << Heap[lk,mu])
          bassert(
            (lk !=@ NullLiteral() && lk !=@ VarExpr("this") && etran.CanRead(lk, "mu")) ==>
            (etran.CanRead(VarExpr("this"), "mu") &&
             new FunctionApp("MuBelow", etran.Heap.select(VarExpr("this"), "mu"), etran.Heap.select(lk, "mu"))),
            invs(0).pos,
            "Monitor invariant can hold permission of other o.mu field only this.mu if this.mu<<o.mu")
        ) :::
        //check that invariant is reflexive
        etran.UseCurrentAsOld().Exhale(invs map {mi => (mi.e, ErrorMessage(mi.pos, "Monitor invariant might not be reflexive."))}, "invariant reflexive?", false, methodK, true) :::
        bassert(DebtCheck(), pos, "Monitor invariant is not allowed to contain debt.")
    )
  }

  def translateField(f: Field): List[Decl] = {
    Const(f.FullName, true, FieldType(f.typ.typ)) ::
    Axiom(NonPredicateField(f.FullName))
  }

  def translateFunction(f: Function): List[Decl] = {
    val myresult = BVar("result", f.out.typ);
    etran = etran.CheckTermination(! Chalice.skipTermination);
    val checkBody = f.definition match {case Some(e) => isDefined(e); case None => Nil};
    etran = etran.CheckTermination(false);
    
    // pick new k
    val (functionKV, functionK) = Boogie.NewBVar("functionK", tint, true)
    val functionKStmts = BLocal(functionKV) :: bassume(0 < functionK && 1000*functionK < permissionOnePercent)
    
    // Boogie function that represents the Chalice function
    Boogie.Function(functionName(f), BVar("heap", theap) :: BVar("mask", tmask) :: BVar("this", tref) :: (f.ins map Variable2BVar), BVar("$myresult", f.out.typ)) ::
    // check definedness of the function's precondition and body
    Proc(f.FullName + "$checkDefinedness", 
      NewBVarWhere("this", new Type(currentClass)) :: (f.ins map {i => Variable2BVarWhere(i)}),
      Nil,
      GlobalNames,
      DefaultPrecondition(),
      functionKStmts :::
      DefinePreInitialState :::
      // check definedness of the precondition
      InhaleWithChecking(Preconditions(f.spec) map { p => (if(0 < Chalice.defaults) UnfoldPredicatesWithReceiverThis(p) else p)}, "precondition", functionK) :::
      bassume(CurrentModule ==@ VarExpr(ModuleName(currentClass))) :: // verify the body assuming that you are in the module
      // check definedness of function body
      checkBody :::
      (f.definition match {case Some(e) => BLocal(myresult) :: (Boogie.VarExpr("result") := etran.Tr(e)); case None => Nil}) :::
      // check that postcondition holds
      ExhaleWithChecking(Postconditions(f.spec) map { post => ((if(0 < Chalice.defaults) UnfoldPredicatesWithReceiverThis(post) else post),
              ErrorMessage(f.pos, "Postcondition at " + post.pos + " might not hold."))}, "function postcondition", functionK, true)) ::
    // definition axiom
    (f.definition match {
      case Some(definition) => definitionAxiom(f, definition);
      case None => Nil
    }) :::
    // framing axiom (+ frame function)
    framingAxiom(f) :::
    // postcondition axiom(s)
    postconditionAxiom(f)
  }

  def definitionAxiom(f: Function, definition: Expression): List[Decl] = {
    val inArgs = (f.ins map {i => Boogie.VarExpr(i.UniqueName)});
    val args = VarExpr("this") :: inArgs;
    val formals = BVar(HeapName, theap) :: BVar(MaskName, tmask) :: BVar("this", tref) :: (f.ins map Variable2BVar);
    val applyF = FunctionApp(functionName(f), List(etran.Heap, etran.Mask) ::: args);

    /** Limit application of the function by introducing a second (limited) function */
    val body = etran.Tr(
      if (f.isRecursive && ! f.isUnlimited) {
        val limited = Map() ++ (f.SCC zip (f.SCC map {f =>
          val result = Function(f.id + "#limited", f.ins, f.out, f.spec, None);
          result.Parent = f.Parent;
          result;
        }));
        def limit: Expression => Option[Expression] = _ match {
          case app @ FunctionApplication(obj, id, args) if (f.SCC contains app.f) =>
            val result = FunctionApplication(obj transform limit, id, args map (e => e transform limit));
            result.f = limited(app.f);
            Some(result)
          case _ => None
        }
        definition transform limit;
      } else {
        definition
      }
    );

    /* axiom (forall h: HeapType, m: MaskType, this: ref, x_1: t_1, ..., x_n: t_n ::
         wf(h, m) && CurrentModule == module#C ==> #C.f(h, m, this, x_1, ..., x_n) == tr(body))
    */    
    Axiom(new Boogie.Forall(
      formals, new Trigger(applyF),
        (wf(VarExpr(HeapName), VarExpr(MaskName)) && (CurrentModule ==@ ModuleName(currentClass)))
        ==>
        (applyF ==@ body))) ::
    (if (f.isRecursive)
      // define the limited function (even for unlimited function since its SCC might have limited functions)
      Boogie.Function(functionName(f) + "#limited", formals, BVar("$myresult", f.out.typ)) ::
      Axiom(new Boogie.Forall(
        formals, new Trigger(applyF),
        applyF ==@ FunctionApp(functionName(f) + "#limited", List(etran.Heap, etran.Mask) ::: args))) ::
      Nil
    else
      Nil)            
  }

  def framingAxiom(f: Function): List[Decl] = {
    val pre = Preconditions(f.spec).foldLeft(BoolLiteral(true): Expression)({ (a, b) => And(a, b) });
    var hasAccessSeq = false;
    pre visit {_ match {case _: AccessSeq => hasAccessSeq = true; case _ => }}

    if (!hasAccessSeq) {
      // Encoding with nostate and combine
      /* function ##C.f(state, ref, t_1, ..., t_n) returns (t);
         axiom (forall h: HeapType, m: MaskType, this: ref, x_1: t_1, ..., x_n: t_n ::
            wf(h, m) && IsGoodState(version) ==> #C.f(h, m, this, x_1, ..., x_n) ==  ##C.f(version, this, x_1, ..., x_n))
      */
      // make sure version is of HeapType
      val version = Boogie.FunctionApp("combine", List("nostate", Version(pre, etran)));
      val inArgs = (f.ins map {i => Boogie.VarExpr(i.UniqueName)});
      val frameFunctionName = "#" + functionName(f);

      val args = VarExpr("this") :: inArgs;
      val applyF = FunctionApp(functionName(f) + (if (f.isRecursive) "#limited" else ""), List(etran.Heap, etran.Mask) ::: args);
      val applyFrameFunction = FunctionApp(frameFunctionName, version :: args);
      Boogie.Function(frameFunctionName, Boogie.BVar("state", theap) :: Boogie.BVar("this", tref) :: (f.ins map Variable2BVar), new BVar("$myresult", f.out.typ)) ::
      Axiom(new Boogie.Forall(
        BVar(HeapName, theap) :: BVar(MaskName, tmask) :: BVar("this", tref) :: (f.ins map Variable2BVar),
        new Trigger(applyF),
          (wf(VarExpr(HeapName), VarExpr(MaskName)) && IsGoodState(version) && CanAssumeFunctionDefs)
          ==>
          (applyF ==@ applyFrameFunction))
      )
    } else {
      // Encoding with universal quantification over two heaps
      /* axiom (forall h1, h2: HeapType, m1, m2: MaskType, this: ref, x_1: t_1, ..., x_n: t_n ::
            wf(h1,m1) && wf(h2,m2) && version(h1, h2, #C.f) ==>
              #C.f(h1, m1, this, x_1, ..., x_n) == #C.f(h2, m2, this, x_1, ..., x_n)
       */
      var args = VarExpr("this") :: (f.ins map {i => Boogie.VarExpr(i.UniqueName)});

      // create two heaps
      val globals1 = etran.FreshGlobals("a"); val etran1 = new ExpressionTranslator(globals1 map {v => new Boogie.VarExpr(v)}, currentClass);
      val globals2 = etran.FreshGlobals("b"); val etran2 = new ExpressionTranslator(globals2 map {v => new Boogie.VarExpr(v)}, currentClass);
      val List(heap1, mask1, _) = globals1;
      val List(heap2, mask2, _) = globals2;
      val apply1 = FunctionApp(functionName(f), etran1.Heap :: etran1.Mask :: args);
      val apply2 = FunctionApp(functionName(f), etran2.Heap :: etran2.Mask :: args);

      Axiom(new Boogie.Forall(
        heap1 :: heap2 :: mask1 :: mask2 :: BVar("this", tref) :: (f.ins map Variable2BVar),
        new Trigger(List(apply1, apply2)),
          ((wf(etran1.Heap, etran1.Mask) && wf(etran2.Heap, etran2.Mask) && Version(pre, etran1, etran2) && CanAssumeFunctionDefs)
          ==>
          (apply1 ==@ apply2))
      ))
    }
  }

  def postconditionAxiom(f: Function): List[Decl] = {
    /* axiom (forall h: HeapType, m: MaskType, this: ref, x_1: t_1, ..., x_n: t_n ::
          wf(h, m) && CanAssumeFunctionDefs ==> Q[#C.f(h, m, this, x_1, ..., x_n)/result]
    */
    val inArgs = (f.ins map {i => Boogie.VarExpr(i.UniqueName)});
    val myresult = Boogie.BVar("result", f.out.typ);
    val args = VarExpr("this") :: inArgs;
    val applyF = FunctionApp(functionName(f), List(VarExpr(HeapName), VarExpr(MaskName)) ::: args)
    //postcondition axioms
    (Postconditions(f.spec) map { post : Expression =>
      Axiom(new Boogie.Forall(
        BVar(HeapName, theap) :: BVar(MaskName, tmask) :: BVar("this", tref) :: (f.ins map Variable2BVar),
        new Trigger(applyF),
        (wf(VarExpr(HeapName), VarExpr(MaskName)) && CanAssumeFunctionDefs)
          ==>
        etran.Tr(SubstResult(post, f.apply(ExplicitThisExpr(), f.ins map { arg => new VariableExpr(arg) })))
        ))
     })
  }

  def translatePredicate(pred: Predicate): List[Decl] = {
    
    // pick new k
    val (predicateKV, predicateK) = Boogie.NewBVar("predicateK", tint, true)
    val predicateKStmts = BLocal(predicateKV) :: bassume(0 < predicateK && 1000*predicateK < permissionOnePercent)
    
    // const unique class.name: HeapType;
    Const(pred.FullName, true, FieldType(theap)) ::
    // axiom PredicateField(f);
    Axiom(PredicateField(pred.FullName)) ::
    // check definedness of predicate body
    Proc(pred.FullName + "$checkDefinedness",
      List(NewBVarWhere("this", new Type(currentClass))),
      Nil,
      GlobalNames,
      DefaultPrecondition(),
      predicateKStmts :::
      DefinePreInitialState :::
      InhaleWithChecking(List(DefinitionOf(pred)), "predicate definition", predicateK))
  }

  def translateMethod(method: Method): List[Decl] = {
    // pick new k for this method, that represents the fraction for read permissions
    val (methodKV, methodK) = Boogie.NewBVar("methodK", tint, true)
    val methodKStmts = BLocal(methodKV) :: bassume(0 < methodK && 1000*methodK < permissionOnePercent)
    
    // check definedness of the method contract
    Proc(method.FullName + "$checkDefinedness", 
      NewBVarWhere("this", new Type(currentClass)) :: (method.ins map {i => Variable2BVarWhere(i)}),
      method.outs map {i => Variable2BVarWhere(i)},
      GlobalNames,
      DefaultPrecondition(),
        methodKStmts :::
        DefinePreInitialState :::
        bassume(CanAssumeFunctionDefs) ::
        // check precondition
        InhaleWithChecking(Preconditions(method.spec), "precondition", methodK) :::
        DefineInitialState :::
        (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
        Havoc(etran.Heap) ::
        // check postcondition
        InhaleWithChecking(Postconditions(method.spec), "postcondition", methodK) :::
        // check lockchange
        (LockChanges(method.spec) flatMap { lc => isDefined(lc)})) ::
    // check that method body satisfies the method contract
    Proc(method.FullName,
      NewBVarWhere("this", new Type(currentClass)) :: (method.ins map {i => Variable2BVarWhere(i)}),
      method.outs map {i => Variable2BVarWhere(i)},
      GlobalNames,
      DefaultPrecondition(),
        methodKStmts :::
        bassume(CurrentModule ==@ Boogie.VarExpr(ModuleName(currentClass))) ::
        bassume(CanAssumeFunctionDefs) ::
        DefinePreInitialState :::
        Inhale(Preconditions(method.spec) map { p => (if(0 < Chalice.defaults) UnfoldPredicatesWithReceiverThis(p) else p)}, "precondition", methodK) :::
        DefineInitialState :::
        translateStatements(method.body, methodK) :::
        Exhale(Postconditions(method.spec) map { p => ((if(0 < Chalice.defaults) UnfoldPredicatesWithReceiverThis(p) else p), ErrorMessage(method.pos, "The postcondition at " + p.pos + " might not hold."))}, "postcondition", methodK, true) :::
        (if(Chalice.checkLeaks) isLeaking(method.pos, "Method " + method.FullName + " might leak references.") else Nil) :::
        bassert(LockFrame(LockChanges(method.spec), etran), method.pos, "Method might lock/unlock more than allowed.") :::
        bassert(DebtCheck, method.pos, "Method body is not allowed to leave any debt."))
  }

  // TODO: This method has not yet been updated to the new permission model
  def translateMethodTransform(mt: MethodTransform): List[Decl] = {
    // extract coupling invariants
    def Invariants(e: Expression): Expression = desugar(e) match {
      case And(a,b) => And(Invariants(a), Invariants(b))
      case Implies(a,b) => Implies(a, Invariants(b))
      case Access(ma, Full) if ! ma.isPredicate =>
        val cis = for (ci <- mt.Parent.CouplingInvariants; if (ci.fields.contains(ma.f))) yield FractionOf(ci.e, ci.fraction(ma.f));
        cis.foldLeft(BoolLiteral(true):Expression)(And(_,_))
      case _: PermissionExpr => throw new NotSupportedException("not supported")
      case _ => BoolLiteral(true)
    }

    val preCI = if (mt.Parent.CouplingInvariants.size > 0) Preconditions(mt.Spec).map(Invariants) else Nil
    val postCI = if (mt.Parent.CouplingInvariants.size > 0) Postconditions(mt.refines.Spec).map(Invariants) else Nil

    // check definedness of refinement specifications
    Proc(mt.FullName + "$checkDefinedness",
      NewBVarWhere("this", new Type(currentClass)) :: (mt.Ins map {i => Variable2BVarWhere(i)}),
      mt.Outs map {i => Variable2BVarWhere(i)},
      GlobalNames,
      DefaultPrecondition(),
        DefinePreInitialState :::
        bassume(CanAssumeFunctionDefs) ::
        // check precondition
        InhaleWithChecking(Preconditions(mt.Spec) ::: preCI, "precondition", todoiparam) :::
        DefineInitialState :::
        (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
        Havoc(etran.Heap) ::
        // check postcondition
        InhaleWithChecking(Postconditions(mt.refines.Spec), "postcondition", todoiparam) :::
        tag(InhaleWithChecking(postCI ::: Postconditions(mt.spec), "postcondition", todoiparam), keepTag)
      ) ::
    // check correctness of refinement
    Proc(mt.FullName,
      NewBVarWhere("this", new Type(currentClass)) :: (mt.Ins map {i => Variable2BVarWhere(i)}),
      mt.Outs map {i => Variable2BVarWhere(i)},
      GlobalNames,
      DefaultPrecondition(),
        assert2assume {
          bassume(CurrentModule ==@ Boogie.VarExpr(ModuleName(currentClass))) ::
          bassume(CanAssumeFunctionDefs) ::
          DefinePreInitialState :::
          Inhale(Preconditions(mt.Spec) ::: preCI, "precondition", todoiparam) :::
          DefineInitialState :::
          translateStatements(mt.body, todoiparam) :::
          Exhale(Postconditions(mt.refines.Spec) map {p => (p, ErrorMessage(p.pos, "The postcondition at " + p.pos + " might not hold."))}, "postcondition", todoiparam, todobparam) :::
          tag(Exhale(
            (postCI map {p => (p, ErrorMessage(mt.pos, "The coupling invariant might not be preserved."))}) :::
            (Postconditions(mt.spec) map {p => (p, ErrorMessage(p.pos, "The postcondition at " + p.pos + " might not hold."))}), "postcondition", todoiparam, todobparam), keepTag)
        }
      )

  }

  def DebtCheck() = {
    // (forall ch :: ch == null || 0 <= Credits[ch])
    val (chV, ch) = NewBVar("ch", tref, false)
    new Boogie.Forall(chV, (ch ==@ bnull) || (0 <= new MapSelect(etran.Credits, ch)))
  }

  def DefaultPrecondition() = {
    "requires this!=null;" ::
    "free requires wf(Heap, Mask);" ::
    Nil
  }

  def DefinePreInitialState = {
    Comment("define pre-initial state") ::
    (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits)
  }
  def DefineInitialState = {
    Comment("define initial state") ::
    bassume(etran.Heap ==@ Boogie.Old(etran.Heap)) ::
    bassume(etran.Mask ==@ Boogie.Old(etran.Mask)) ::
    bassume(etran.Credits ==@ Boogie.Old(etran.Credits))
  }

  /**********************************************************************
  *****************           STATEMENTS                *****************
  **********************************************************************/
  def translateStatements(statements: List[Statement], methodK: Expr): List[Stmt] = statements flatMap (v => translateStatement(v, methodK))

  def translateStatement(s: Statement, methodK: Expr): List[Stmt] = {
    s match {
      case Assert(e) =>
        val newGlobals = etran.FreshGlobals("assert");
        val tmpHeap = Boogie.NewBVar(HeapName, theap, true);
        val tmpMask = Boogie.NewBVar(MaskName, tmask, true); 
        val tmpCredits = Boogie.NewBVar(CreditsName, tcredits, true); 
        val tmpTranslator = new ExpressionTranslator(List(tmpHeap._1.id, tmpMask._1.id, tmpCredits._1.id), List(etran.ChooseEtran(true).Heap, etran.ChooseEtran(true).Mask, etran.ChooseEtran(true).Credits), currentClass);        
        Comment("assert") ::
        // exhale e in a copy of the heap/mask/credits
        BLocal(tmpHeap._1) :: (tmpHeap._2 := etran.Heap) ::
        BLocal(tmpMask._1) :: (tmpMask._2 := etran.Mask) ::
        BLocal(tmpCredits._1) :: (tmpCredits._2 := etran.Credits) ::
        tmpTranslator.Exhale(List((e, ErrorMessage(s.pos, "Assertion might not hold."))), "assert", true, methodK, true)
      case Assume(e) =>
        Comment("assume") ::
        isDefined(e) :::
        bassume(e)
      case BlockStmt(ss) =>
        translateStatements(ss, methodK)
      case IfStmt(guard, then, els) =>
        val tt = translateStatement(then, methodK)
        val et = els match {
          case None => Nil
          case Some(els) => translateStatement(els, methodK) }
        Comment("if") ::
        isDefined(guard) :::
        Boogie.If(guard, tt, et)
      case w: WhileStmt =>
        translateWhile(w, methodK)
      case Assign(lhs, rhs) =>
        def assignOrAssumeEqual(r: Boogie.Expr): List[Boogie.Stmt] = {
          if (lhs.v.isImmutable) {
            // this must be a "ghost const"
            val name = lhs.v.UniqueName
            bassert(! VarExpr("assigned$" + name), lhs.pos, "Const variable can be assigned to only once.") ::
            bassume(lhs ==@ r) ::
            (VarExpr("assigned$" + name) := true)
          } else {
            lhs := r
          }
        }
        Comment("assigment to " + lhs.id) ::
        (rhs match {
          case rhs@NewRhs(c, initialization, lower, upper) => // x := new C;
            val (nw, ss) = translateAllocation(rhs.typ, initialization, lower, upper, rhs.pos);
            ss ::: assignOrAssumeEqual(new VarExpr(nw)) 
          case rhs: Expression => // x := E;
            isDefined(rhs) ::: assignOrAssumeEqual(rhs)
        })
      case FieldUpdate(lhs@MemberAccess(target, f), rhs) =>
        val (statements, toStore : Expr) = 
          (rhs match {
            case rhs @ NewRhs(c, initialization, lower, upper) =>
              // e.f := new C;
              val (nw,ss) = translateAllocation(rhs.typ, initialization, lower, upper, rhs.pos)
              (ss, new VarExpr(nw))
            case rhs : Expression =>
              // e.f := E; 
              (isDefined(rhs), TrExpr(rhs))
           });
        Comment("update field " + f) ::
        isDefined(target) :::
        bassert(CanWrite(target, lhs.f), s.pos, "Location might not be writable") ::
        statements ::: etran.Heap.store(target, lhs.f, toStore) :: bassume(wf(VarExpr(HeapName), VarExpr(MaskName)))
      case lv : LocalVar =>
        translateLocalVarDecl(lv.v, false) :::
        { lv.rhs match {
          //update the local, provided a rhs was provided
          case None => Nil
          case Some(rhs) => translateStatement(Assign(new VariableExpr(lv.v), rhs), methodK) }}
      case s: SpecStmt => translateSpecStmt(s)
      case c: Call => translateCall(c, methodK)
      case Install(obj, lowerBounds, upperBounds) =>
        Comment("install") ::
        isDefined(obj) :::
        bassert(nonNull(obj), s.pos, "The target of the install statement might be null.") ::
        bassert(isHeld(obj), s.pos, "The lock of the target of the install statement might not be held.") ::
        // assert CanWrite(obj.mu); assume lowerbounds < obj.mu < upperBounds;
        UpdateMu(obj, false, false, lowerBounds, upperBounds, ErrorMessage(s.pos, "Install might fail."))
      case Share(obj, lowerBounds, upperBounds) =>
        val (preShareMaskV, preShareMask) = Boogie.NewBVar("preShareMask", tmask, true)    
        Comment("share") ::
        // remember the mask immediately before the share
        BLocal(preShareMaskV) :: Boogie.Assign(preShareMask, etran.Mask) ::
        isDefined(obj) :::
        bassert(nonNull(obj), s.pos, "The target of the share statement might be null.") ::
        UpdateMu(obj, true, false, lowerBounds, upperBounds, ErrorMessage(s.pos, "Share might fail.")) :::
        bassume(!isHeld(obj) && ! isRdHeld(obj)) :: // follows from o.mu==lockbottom
        // exhale the monitor invariant (using the current state as the old state)
        ExhaleInvariants(obj, false, ErrorMessage(s.pos, "Monitor invariant might not hold."), etran.UseCurrentAsOld(), methodK) :::
        // assume a seen state is the one right before the share
        bassume(LastSeenHeap(etran.Heap.select(obj, "mu"), etran.Heap.select(obj, "held")) ==@ etran.Heap) ::
        bassume(LastSeenMask(etran.Heap.select(obj, "mu"), etran.Heap.select(obj, "held")) ==@ preShareMask) ::
        bassume(LastSeenCredits(etran.Heap.select(obj, "mu"), etran.Heap.select(obj, "held")) ==@ etran.Credits)
      case Unshare(obj) =>
        val (heldV, held) = Boogie.NewBVar("held", Boogie.NamedType("int"), true)
        val o = TrExpr(obj)
        Comment("unshare") ::
        isDefined(obj) :::
        bassert(nonNull(o), s.pos, "The target of the unshare statement might be null.") ::
        bassert(CanWrite(o, "mu"), s.pos, "The mu field of the target of the unshare statement might not be writable.") ::
        bassert(isShared(o), s.pos, "The target of the unshare statement might not be shared.") ::
        bassert(isHeld(o), s.pos, "The target of the unshare statement might not be locked by the current thread.") :: // locked or read-locked
        etran.Heap.store(o, "mu", bLockBottom) ::
        // havoc o.held where 0<=o.held 
        BLocal(heldV) :: Boogie.Havoc(held) :: bassume(held <= 0) ::
        etran.Heap.store(o, "held", held) ::
        // set o.rdheld to false
        etran.Heap.store(o, "rdheld", false)
      case Acquire(obj) =>
        Comment("acquire") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), s.pos, "The target of the acquire statement might be null.") ::
        TrAcquire(s, obj, methodK)
      case Release(obj) =>
        Comment("release") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), s.pos, "The target of the release statement might be null.") ::
        TrRelease(s, obj, methodK)
      case Lock(e, body, readonly) =>
        val objV = new Variable("lock", new Type(e.typ))
        val obj = new VariableExpr(objV)
        val sname = if (readonly) "rd lock" else "lock"
        val o = TrExpr(obj)
        Comment(sname) ::
        isDefined(e) :::
        BLocal(Variable2BVar(objV)) :: (o := TrExpr(e)) ::
        bassert(nonNull(o), s.pos, "The target of the " + sname + " statement might be null.") ::
        { if (readonly) {
            TrRdAcquire(s, obj, methodK) :::
            translateStatement(body, methodK) :::
            TrRdRelease(s, obj, methodK)
          } else {
            TrAcquire(s, obj, methodK) :::
            translateStatement(body, methodK) :::
            TrRelease(s, obj, methodK)
          }
        }
      case RdAcquire(obj) =>
        Comment("rd acquire") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), s.pos, "The target of the read-acquire statement might be null.") ::
        TrRdAcquire(s, obj, methodK)
      case rdrelease@RdRelease(obj) =>
        Comment("rd release") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), obj.pos, "The target of the read-release statement might be null.") ::
        TrRdRelease(s, obj, methodK)
      case downgrade@Downgrade(obj) =>
        val o = TrExpr(obj);
        val prevHeapV = new Boogie.BVar("prevHeap", theap, true)
        Comment("downgrade") ::
        isDefined(obj) :::
        bassert(nonNull(o), s.pos, "The target of the downgrade statement might be null.") ::
        bassert(isHeld(o), s.pos, "The lock of the target of the downgrade statement might not be held by the current thread.") ::
        bassert(! isRdHeld(o), s.pos, "The current thread might hold the read lock.") ::
        ExhaleInvariants(obj, false, ErrorMessage(downgrade.pos, "Monitor invariant might not hold."), methodK) :::
        BLocal(prevHeapV) ::
        InhaleInvariants(obj, true, methodK) :::
        bassume(etran.Heap ==@ new Boogie.VarExpr(prevHeapV)) ::
        etran.Heap.store(o, "rdheld", true)
      case Free(obj) =>
        val o = TrExpr(obj);
        isDefined(obj) :::
        bassert(nonNull(o), s.pos, "The target of the free statement might be null.") ::
        (for (f <- obj.typ.Fields ++ RootClass.MentionableFields) yield
          bassert(CanWrite(o, f.FullName), s.pos, "The field " + f.id + " of the target of the free statement might not be writable.")) :::
        (for (f <- obj.typ.Fields ++ RootClass.MentionableFields) yield
          etran.SetNoPermission(o, f.FullName, etran.Mask))
        // probably need to havoc all the fields! Do we check enough?
      case fold@Fold(acc@Access(pred@MemberAccess(e, f), perm)) =>
        val o = TrExpr(e);
        var definition = scaleExpressionByPermission(SubstThis(DefinitionOf(pred.predicate), e), perm, fold.pos)
        
        // pick new k
        val (foldKV, foldK) = Boogie.NewBVar("foldK", tint, true)
        Comment("fold") ::
        BLocal(foldKV) :: bassume(0 < foldK && 1000*foldK < permissionFull) ::
        isDefined(e) :::
        isDefined(perm) :::
        bassert(nonNull(o), s.pos, "The target of the fold statement might be null.") ::
        // remove the definition from the current state, and replace by predicate itself
        Exhale(List((definition, ErrorMessage(s.pos, "Fold might fail because the definition of " + pred.predicate.FullName + " does not hold."))), "fold", foldK, false) :::
        Inhale(List(acc), "fold", foldK) :::
        etran.Heap.store(o, pred.predicate.FullName, etran.Heap) :: // Is this necessary?      
        bassume(wf(etran.Heap, etran.Mask))
      case unfld@Unfold(acc@Access(pred@MemberAccess(e, f), perm:Permission)) =>
        val o = TrExpr(e);
        val definition = scaleExpressionByPermission(SubstThis(DefinitionOf(pred.predicate), e), perm, unfld.pos)
        
        // pick new k
        val (unfoldKV, unfoldK) = Boogie.NewBVar("unfoldK", tint, true)
        Comment("unfold") ::
        BLocal(unfoldKV) :: bassume(0 < unfoldK && unfoldK < permissionFull) ::
        isDefined(e) :::
        bassert(nonNull(o), s.pos, "The target of the fold statement might be null.") ::
        isDefined(perm) :::
        Exhale(List((acc, ErrorMessage(s.pos, "unfold might fail because the predicate " + pred.predicate.FullName + " does not hold."))), "unfold", unfoldK, false) :::
        etran.InhaleFrom(List(definition), "unfold", false, etran.Heap.select(o, pred.predicate.FullName), unfoldK)
      case c@CallAsync(declaresLocal, token, obj, id, args) =>
        val formalThisV = new Variable("this", new Type(c.m.Parent))
        val formalThis = new VariableExpr(formalThisV)
        val formalInsV = for (p <- c.m.ins) yield new Variable(p.id, p.t)
        val formalIns = for (v <- formalInsV) yield new VariableExpr(v)

        val (tokenV,tokenId) = NewBVar("token", tref, true)
        val (asyncStateV,asyncState) = NewBVar("asyncstate", tint, true)
        val (preCallHeapV, preCallHeap) = NewBVar("preCallHeap", theap, true)
        val (preCallMaskV, preCallMask) = NewBVar("preCallMask", tmask, true)
        val (preCallCreditsV, preCallCredits) = NewBVar("preCallCredits", tcredits, true)
        val (argsSeqV, argsSeq) = NewBVar("argsSeq", tArgSeq, true)
        val argsSeqLength = 1 + args.length;
        
        // pick new k for this fork
        val (asyncMethodCallKV, asyncMethodCallK) = Boogie.NewBVar("asyncMethodCallK", tint, true)
        BLocal(asyncMethodCallKV) ::
        bassume(0 < asyncMethodCallK) :: // upper bounds are later provided by the exhale
        Comment("call " + id) ::
        // declare the local variable, if needed
        { if (c.local == null)
            List[Stmt]()
          else
            List(BLocal(Variable2BVarWhere(c.local))) } :::
        // remember the value of the heap/mask/credits
        BLocal(preCallHeapV) :: (preCallHeap := etran.Heap) ::
        BLocal(preCallMaskV) :: (preCallMask := etran.Mask) ::
        BLocal(preCallCreditsV) :: (preCallCredits := etran.Credits) ::
        BLocal(argsSeqV) ::
        // introduce formal parameters and pre-state globals
        (for (v <- formalThisV :: formalInsV) yield BLocal(Variable2BVarWhere(v))) :::
        // check definedness of arguments
        isDefined(obj) :::
        bassert(nonNull(obj), c.pos, "The target of the method call might be null.") ::
        (args flatMap { e: Expression => isDefined(e)}) :::
        // assign actual ins to formal ins
        (formalThis := obj) ::
        (for ((v,e) <- formalIns zip args) yield (v := e)) :::
        // insert all arguments in the argument sequence
        Boogie.AssignMap(argsSeq, 0, formalThis) ::
        { var i = 1
          for (v <- formalIns) yield { val r = Boogie.AssignMap(argsSeq, i, v); i += 1; r }
        } :::
        // exhale preconditions
        Exhale(Preconditions(c.m.spec) map
          (p => SubstVars(p, formalThis, c.m.ins, formalIns)) zip (Preconditions(c.m.spec) map { p => ErrorMessage(c.pos, "The precondition at " + p.pos + " might not hold.")}), "precondition", asyncMethodCallK, false) :::
        // create a new token
        BLocal(tokenV) :: Havoc(tokenId) :: bassume(nonNull(tokenId)) ::
        // the following assumes help in proving that the token is fresh
        bassume(etran.Heap.select(tokenId, "joinable") ==@ 0) ::
        bassume(new Boogie.MapSelect(etran.Mask, tokenId, "joinable", "perm$N")==@ 0) ::
        bassume(new Boogie.MapSelect(etran.Mask, tokenId, "joinable", "perm$R")==@ 0) ::
        etran.IncPermission(tokenId, "joinable", permissionFull) :::
        // create a fresh value for the joinable field
        BLocal(asyncStateV) :: Boogie.Havoc(asyncState) :: bassume(asyncState !=@ 0) ::
        etran.Heap.store(tokenId, "joinable", asyncState) ::
        // also store the k used for this fork, such that the same k can be used in the join
        etran.Heap.store(tokenId, forkK, asyncMethodCallK) ::
        // assume the pre call state for the token is the state before inhaling the precondition
        bassume(CallHeap(asyncState) ==@ preCallHeap) ::
        bassume(CallMask(asyncState) ==@ preCallMask) ::
        bassume(CallCredits(asyncState) ==@ preCallCredits) ::
        bassume(CallArgs(asyncState) ==@ argsSeq) :::
        // assign the returned token to the variable
        { if (token != null) List(token := tokenId) else List() }
      case jn@JoinAsync(lhs, token) =>
        val formalThisV = new Variable("this", new Type(jn.m.Parent))
        val formalThis = new VariableExpr(formalThisV)
        val formalInsV = for (p <- jn.m.ins) yield new Variable(p.id, p.t)
        val formalIns = for (v <- formalInsV) yield new VariableExpr(v)
        val formalOutsV = for (p <- jn.m.outs) yield new Variable(p.id, p.t)
        val formalOuts = for (v <- formalOutsV) yield new VariableExpr(v)

        val (argsSeqV, argsSeq) = NewBVar("argsSeq", tArgSeq, true)
        val (preCallHeapV, preCallHeap) = NewBVar("preCallHeap", theap, true);
        val (preCallMaskV, preCallMask) = NewBVar("preCallMask", tmask, true);
        val (preCallCreditsV, preCallCredits) = NewBVar("preCallCredits", tcredits, true);
        val preGlobals = List(preCallHeap, preCallMask, preCallCredits);
        val postEtran = new ExpressionTranslator(List(etran.Heap, etran.Mask, etran.Credits), preGlobals, currentClass);
        val (asyncJoinKV, asyncJoinK) = Boogie.NewBVar("asyncJoinK", tint, true)
        
        Comment("join async") :: 
        // pick new k for this join
        BLocal(asyncJoinKV) ::
        bassume(0 < asyncJoinK) ::
        // try to use the same k as for the fork
        bassume(asyncJoinK ==@ etran.Heap.select(token, forkK)) :: 
        // check that token is well-defined
        isDefined(token) :::
        // check that we did not join yet
        bassert(CanWrite(token, "joinable"), jn.pos, "The joinable field might not be writable.") ::
        bassert(etran.Heap.select(token, "joinable") !=@ 0, jn.pos, "The joinable field might not be true.") ::
        // lookup token.joinable
        BLocal(argsSeqV) :: (argsSeq := CallArgs(etran.Heap.select(token, "joinable"))) ::
        // retrieve the call's pre-state from token.joinable
        BLocal(preCallHeapV) :: (preCallHeap := CallHeap(etran.Heap.select(token, "joinable"))) :: 
        BLocal(preCallMaskV) :: (preCallMask := CallMask(etran.Heap.select(token, "joinable"))) ::
        BLocal(preCallCreditsV) :: (preCallCredits := CallCredits(etran.Heap.select(token, "joinable"))) ::
        // introduce locals for the out parameters
        (for (v <- formalThisV :: formalInsV ::: formalOutsV) yield BLocal(Variable2BVarWhere(v))) :::
        // initialize the in parameters
        (formalThis := new MapSelect(argsSeq, 0)) ::
        { var i = 1
          (formalIns map { v => val r = (v := new MapSelect(argsSeq, i)); i += 1; r })
        } :::
        // havoc formal outs
        (for (v <- formalOuts) yield Havoc(v)) :::
        // set joinable to false
        etran.Heap.store(token, "joinable", 0) ::
        etran.SetNoPermission(token, "joinable", etran.Mask) ::
        // inhale postcondition of the call
        postEtran.Inhale(Postconditions(jn.m.spec) map
                         { p => SubstVars(p, formalThis, jn.m.ins ++ jn.m.outs, formalIns ++ formalOuts)}, "postcondition", false, asyncJoinK) :::
        // assign formal outs to actual outs
        (for ((v,e) <- lhs zip formalOuts) yield (v := e))
      case s@Send(ch, args) =>
        val channel = ch.typ.asInstanceOf[ChannelClass].ch
        val formalThisV = new Variable("this", new Type(ch.typ))
        val formalThis = new VariableExpr(formalThisV)
        val formalParamsV = for (p <- channel.parameters) yield new Variable(p.id, p.t)
        val formalParams = for (v <- formalParamsV) yield new VariableExpr(v)
        Comment("send") ::
        // introduce formal parameters
        (for (v <- formalThisV :: formalParamsV) yield BLocal(Variable2BVarWhere(v))) :::
        // check definedness of arguments
        isDefined(ch) :::
        bassert(nonNull(ch), ch.pos, "The channel might be null.") ::
        (args flatMap { e: Expression => isDefined(e)}) :::
        // assign actual ins to formal parameters
        (formalThis := ch) ::
        (for ((v,e) <- formalParams zip args) yield (v := e)) :::
        // increase credits
        new Boogie.MapUpdate(etran.Credits, TrExpr(ch), new Boogie.MapSelect(etran.Credits, TrExpr(ch)) + 1) ::
        // exhale where clause
        Exhale(List(
          (SubstVars(channel.where, formalThis, channel.parameters, formalParams),
           ErrorMessage(s.pos, "The where clause at " + channel.where.pos + " might not hold."))),
          "channel where clause", methodK, false)
      case r@Receive(_, ch, outs) =>
        val channel = ch.typ.asInstanceOf[ChannelClass].ch
        val formalThisV = new Variable("this", new Type(ch.typ))
        val formalThis = new VariableExpr(formalThisV)
        val formalParamsV = for (p <- channel.parameters) yield new Variable(p.id, p.t)
        val formalParams = for (v <- formalParamsV) yield new VariableExpr(v)
        Comment("receive") ::
        // check definedness of arguments
        isDefined(ch) :::
        bassert(nonNull(ch), ch.pos, "The channel might be null.") ::
        // check that credits are positive
        bassert(0 < new Boogie.MapSelect(etran.Credits, TrExpr(ch)), r.pos, "receive operation requires a credit") ::
        // ...and check: waitlevel << ch.mu
        bassert(CanRead(ch, "mu"), r.pos, "The mu field of the channel in the receive statement might not be readable.") ::
        bassert(etran.MaxLockIsBelowX(etran.Heap.select(ch, "mu")), r.pos, "The channel must lie above waitlevel in the wait order") ::
        // introduce locals for the parameters
        (for (v <- formalThisV :: formalParamsV) yield BLocal(Variable2BVarWhere(v))) :::
        // initialize the parameters; that is, set "this" to the channel and havoc the other formal parameters
        (formalThis := ch) ::
        (for (v <- formalParams) yield Havoc(v)) :::
        // inhale where clause
        Inhale(List(SubstVars(channel.where, formalThis, channel.parameters, formalParams)), "channel where clause", methodK) :::
        // declare any new local variables among the actual outs
        (for (v <- r.locals) yield BLocal(Variable2BVarWhere(v))) :::
        // assign formal outs to actual outs
        (for ((v,e) <- outs zip formalParams) yield (v := e)) :::
        // decrease credits
        new Boogie.MapUpdate(etran.Credits, TrExpr(ch), new Boogie.MapSelect(etran.Credits, TrExpr(ch)) - 1)
      case r: RefinementBlock =>
        translateRefinement(r)
      case _: Signal => throw new NotSupportedException("not implemented")
      case _: Wait => throw new NotSupportedException("not implemented")      
    }
  }

  def translateLocalVarDecl(v: Variable, assignConst: Boolean) = {
    val bv = Variable2BVarWhere(v)
    Comment("local " + v) ::
    BLocal(bv) ::
    { if (v.isImmutable) {
        val isAssignedVar = new Boogie.BVar("assigned$" + bv.id, BoolClass)
        // havoc x; var assigned$x: bool; assigned$x := false;
        Havoc(new Boogie.VarExpr(bv)) ::
        BLocal(isAssignedVar) ::
        (new Boogie.VarExpr(isAssignedVar) := assignConst)
      } else
        Nil }
  }

  def translateAllocation(cl: Class, initialization: List[Init], lowerBounds: List[Expression], upperBounds: List[Expression], pos: Position): (Boogie.BVar, List[Boogie.Stmt]) = {
    val (nw, nwe) = NewBVar("nw", cl, true)
    val (ttV,tt) = Boogie.NewTVar("T")
    val f = new Boogie.BVar("f", FieldType(tt))
    (nw,
      Comment("new") ::
      BLocal(nw) :: Havoc(nwe) ::
      bassume(nonNull(nwe) && (dtype(nwe) ==@ className(cl))) ::
      bassume(new Boogie.Forall(ttV, f, etran.HasNoPermission(nwe, f.id))) ::
      // initial values of fields:
      (if (cl.IsChannel)
         UpdateMu(nwe, false, true, lowerBounds, upperBounds, ErrorMessage(pos, "new might fail."))
       else
         List(bassume(etran.Heap.select(nwe, "mu") ==@ bLockBottom))) :::
      bassume(etran.Heap.select(nwe, "held") <= 0) ::
      bassume(etran.Heap.select(nwe, "rdheld") ==@ false) ::
      // give access to user-defined fields and special fields:
      (for (f <- cl.Fields ++ RootClass.MentionableFields) yield
        etran.IncPermission(nwe, f.FullName, permissionFull)).flatten :::
      // initialize fields according to the initialization
      (initialization flatMap { init => isDefined(init.e) ::: etran.Heap.store(nwe, init.f.FullName, init.e) })
    )
  }

  def TrAcquire(s: Statement, nonNullObj: Expression, currentK: Expr) = {
    val o = TrExpr(nonNullObj);
    val (lastAcquireVar, lastAcquire) = Boogie.NewBVar("lastAcquire", IntClass, true)
    val (lastSeenHeldV, lastSeenHeld) = Boogie.NewBVar("lastSeenHeld", tint, true)
    val (lastSeenMuV, lastSeenMu) = Boogie.NewBVar("lastSeenMu", tmu, true)
    (if (Chalice.skipDeadlockChecks)
       bassume(CanRead(o, "mu")) ::
       bassume(etran.MaxLockIsBelowX(etran.Heap.select(o,"mu")))
     else
       bassert(CanRead(o, "mu"), s.pos, "The mu field of the target of the acquire statement might not be readable.") ::
       bassert(etran.MaxLockIsBelowX(etran.Heap.select(o,"mu")), s.pos, "The mu field of the target of the acquire statement might not be above waitlevel.")) :::
    bassume(etran.Heap.select(o,"mu") !=@ bLockBottom) ::  // this isn't strictly necessary, it seems; but we might as well include it
    // remember the state right before releasing
    BLocal(lastSeenMuV) :: (lastSeenMu := etran.Heap.select(o, "mu")) ::
    BLocal(lastSeenHeldV) :: Havoc(lastSeenHeld) :: (lastSeenHeld := etran.Heap.select(o, "held")) ::
    bassume(! isHeld(o) && ! isRdHeld(o)) :: // this assume follows from the previous assert
    // update the thread's locking state
    BLocal(lastAcquireVar) :: Havoc(lastAcquire) :: bassume(0 < lastAcquire) ::
    etran.Heap.store(o, "held", lastAcquire) ::
    InhaleInvariants(nonNullObj, false, etran.WhereOldIs(
      LastSeenHeap(lastSeenMu, lastSeenHeld),
      LastSeenMask(lastSeenMu, lastSeenHeld),
      LastSeenCredits(lastSeenMu, lastSeenHeld)), currentK) :::
    // remember values of Heap/Mask/Credits globals (for proving history constraint at release)
    bassume(AcquireHeap(lastAcquire) ==@ etran.Heap) ::
    bassume(AcquireMask(lastAcquire) ==@ etran.Mask) ::
    bassume(AcquireCredits(lastAcquire) ==@ etran.Credits)
  }
  def TrRelease(s: Statement, nonNullObj: Expression, currentK: Expr) = {
    val (heldV, held) = Boogie.NewBVar("held", tint, true) 
    val (prevLmV, prevLm) = Boogie.NewBVar("prevLM", tref, true)
    val (preReleaseHeapV, preReleaseHeap) = NewBVar("preReleaseHeap", theap, true)
    val (preReleaseMaskV, preReleaseMask) = NewBVar("preReleaseMask", tmask, true)
    val (preReleaseCreditsV, preReleaseCredits) = NewBVar("preReleaseCredits", tcredits, true)
    val o = TrExpr(nonNullObj);
    BLocal(preReleaseHeapV) :: (preReleaseHeap := etran.Heap) ::
    BLocal(preReleaseMaskV) :: (preReleaseMask := etran.Mask) ::
    BLocal(preReleaseCreditsV) :: (preReleaseCredits := etran.Credits) ::
    bassert(isHeld(o), s.pos, "The target of the release statement might not be locked by the current thread.") ::
    bassert(!isRdHeld(o), s.pos, "Release might fail because the current thread might hold the read lock.") ::
    ExhaleInvariants(nonNullObj, false, ErrorMessage(s.pos, "Monitor invariant might hot hold."), etran.WhereOldIs(
      AcquireHeap(etran.Heap.select(o, "held")),
      AcquireMask(etran.Heap.select(o, "held")),
      AcquireCredits(etran.Heap.select(o, "held"))), currentK) :::
    // havoc o.held where 0<=o.held 
    BLocal(heldV) :: Havoc(held) :: bassume(held <= 0) ::
    etran.Heap.store(o, "held", held) ::
    // assume a seen state is the one right before the share
    bassume(LastSeenHeap(etran.Heap.select(o, "mu"), held) ==@ preReleaseHeap) ::
    bassume(LastSeenMask(etran.Heap.select(o, "mu"), held) ==@ preReleaseMask) ::
    bassume(LastSeenCredits(etran.Heap.select(o, "mu"), held) ==@ preReleaseCredits)
  }
  def TrRdAcquire(s: Statement, nonNullObj: Expression, currentK: Expr) = {
    val (heldV, held) = Boogie.NewBVar("held", tint, true)
    val o = TrExpr(nonNullObj)
    bassert(CanRead(o, "mu"), s.pos, "The mu field of the target of the read-acquire statement might not be readable.") ::
    bassert(etran.MaxLockIsBelowX(etran.Heap.select(o, "mu")), s.pos, "The mu field of the target of the read-acquire statement might not be above waitlevel.") ::
    bassume(etran.Heap.select(o,"mu") !=@ bLockBottom) ::  // this isn't strictly necessary, it seems; but we might as well include it
    bassume(! isHeld(o) && ! isRdHeld(o)) ::
    BLocal(heldV) :: Havoc(held) :: bassume(held <= 0) ::
    etran.Heap.store(o, "held", held) ::
    etran.Heap.store(o, "rdheld", true) ::
    InhaleInvariants(nonNullObj, true, currentK)
  }
  def TrRdRelease(s: Statement, nonNullObj: Expression, currentK: Expr) = {
    val (heldV, held) = Boogie.NewBVar("held", tint, true)
    val o = TrExpr(nonNullObj);
    bassert(isRdHeld(o), s.pos, "The current thread might not hold the read-lock of the object being released.") ::
    ExhaleInvariants(nonNullObj, true, ErrorMessage(s.pos, "Monitor invariant might not hold."), currentK) :::
    BLocal(heldV) :: Havoc(held) :: bassume(held <= 0) ::
    etran.Heap.store(o, "held", held) ::
    etran.Heap.store(o, "rdheld", false)
  }

  // TODO: This method has not yet been updated to the new permission model
  def translateSpecStmt(s: SpecStmt): List[Stmt] = {
    val preGlobals = etran.FreshGlobals("pre")

    // declare new local variables
    s.locals.flatMap(v => translateLocalVarDecl(v, true)) :::
    Comment("spec statement") ::
    (for (v <- preGlobals) yield BLocal(v)) :::
    // remember values of globals
    (for ((o,g) <- preGlobals zip etran.Globals) yield (new Boogie.VarExpr(o) := g)) :::
    // exhale preconditions
    etran.Exhale(List((s.pre, ErrorMessage(s.pos, "The specification statement precondition at " + s.pos + " might not hold."))), "spec stmt precondition", true, todoiparam, todobparam) :::
    // havoc locals
    (s.lhs.map(l => Boogie.Havoc(l))) :::
    // inhale postconditions (using the state before the call as the "old" state)
    etran.FromPreGlobals(preGlobals).Inhale(List(s.post), "spec stmt postcondition", true, todoiparam)
  }

  def translateCall(c: Call, methodK: Expr): List[Stmt] = {
    val obj = c.obj;
    val lhs = c.lhs;
    val id = c.id;
    val args = c.args;
    val formalThisV = new Variable("this", new Type(c.m.Parent))
    val formalThis = new VariableExpr(formalThisV)
    val formalInsV = for (p <- c.m.Ins) yield new Variable(p.id, p.t)
    val formalIns = for (v <- formalInsV) yield new VariableExpr(v)
    val formalOutsV = for (p <- c.m.Outs) yield new Variable(p.id, p.t)
    val formalOuts = for (v <- formalOutsV) yield new VariableExpr(v)
    val preGlobals = etran.FreshGlobals("call")
    val postEtran = etran.FromPreGlobals(preGlobals)
    
    // pick new k for this method call
    val (methodCallKV, methodCallK) = Boogie.NewBVar("methodCallK", tint, true)
    BLocal(methodCallKV) ::
    bassume(0 < methodCallK) :: // upper bounds are later provided by the exhale
    Comment("call " + id) ::
    // introduce formal parameters and pre-state globals
    (for (v <- formalThisV :: formalInsV ::: formalOutsV) yield BLocal(Variable2BVarWhere(v))) :::
    (for (v <- preGlobals) yield BLocal(v)) :::
    // remember values of globals
    (for ((o,g) <- preGlobals zip etran.Globals) yield (new Boogie.VarExpr(o) := g)) :::
    // check definedness of arguments
    isDefined(obj) :::
    bassert(nonNull(obj), c.pos, "The target of the method call might be null.") ::
    (args flatMap { e: Expression => isDefined(e)}) :::
    // assign actual ins to formal ins
    (formalThis := obj) ::
    (for ((v,e) <- formalIns zip args) yield (v := e)) :::
    // exhale preconditions
    Exhale(Preconditions(c.m.Spec) map
          (p => SubstVars(p, formalThis, c.m.Ins, formalIns)) zip (Preconditions(c.m.Spec) map { p => ErrorMessage(c.pos, "The precondition at " + p.pos + " might not hold.")}), "precondition", methodCallK, false) :::
    // havoc formal outs
    (for (v <- formalOuts) yield Havoc(v)) :::
    // havoc lockchanges
    LockHavoc(for (e <- LockChanges(c.m.Spec) map (p => SubstVars(p, formalThis, c.m.Ins ++ c.m.Outs, formalIns ++ formalOuts))) yield etran.Tr(e), postEtran) :::
    // inhale postconditions (using the state before the call as the "old" state)
    postEtran.Inhale(Postconditions(c.m.Spec) map
                     (p => SubstVars(p, formalThis, c.m.Ins ++ c.m.Outs, formalIns ++ formalOuts)) , "postcondition", false, methodCallK) :::
    // declare any new local variables among the actual outs
    (for (v <- c.locals) yield BLocal(Variable2BVarWhere(v))) :::
    // assign formal outs to actual outs
    (for ((v,e) <- lhs zip formalOuts) yield (v :=e))
  }

  def translateWhile(w: WhileStmt, methodK: Expr): List[Stmt] = {
    val guard = w.guard;
    val lkch = w.lkch;
    val body = w.body;

    val preLoopGlobals = etran.FreshGlobals("while")
    val loopEtran = etran.FromPreGlobals(preLoopGlobals)
    val iterStartGlobals = etran.FreshGlobals("iterStart")
    val iterStartEtran = etran.FromPreGlobals(iterStartGlobals)
    val saveLocalsV = for (v <- w.LoopTargets) yield new Variable(v.id, v.t)
    val iterStartLocalsV = for (v <- w.LoopTargets) yield new Variable(v.id, v.t)
    val lkchOld = lkch map (e => SubstVars(e, w.LoopTargets,
                                             for (v <- saveLocalsV) yield new VariableExpr(v)))
    val lkchIterStart = lkch map (e => SubstVars(e, w.LoopTargets,
                                                   for (v <- iterStartLocalsV) yield new VariableExpr(v)))
    val oldLocks = lkchOld map (e => loopEtran.oldEtran.Tr(e))
    val iterStartLocks = lkchIterStart map (e => iterStartEtran.oldEtran.Tr(e))
    val newLocks = lkch map (e => loopEtran.Tr(e));
    val (whileKV, whileK) = Boogie.NewBVar("whileK", tint, true)
    
    Comment("while") ::
    // pick new k for this method call
    BLocal(whileKV) ::
    bassume(0 < whileK) :: // upper bounds are later provided by the exhale
    // save globals
    (for (v <- preLoopGlobals) yield BLocal(v)) :::
    (loopEtran.oldEtran.Heap := loopEtran.Heap) ::
    (loopEtran.oldEtran.Mask := loopEtran.Mask) ::  // oldMask is not actually used below
    (loopEtran.oldEtran.Credits := loopEtran.Credits) ::  // is oldCredits?
    // check invariant on entry to the loop
    Exhale(w.oldInvs map { inv => (inv, ErrorMessage(inv.pos, "The loop invariant might not hold on entry to the loop."))}, "loop invariant, initially", whileK, false) :::
    tag(Exhale(w.newInvs map { inv => (inv, ErrorMessage(inv.pos, "The loop invariant might not hold on entry to the loop."))}, "loop invariant, initially", whileK, false), keepTag) :::
    List(bassert(DebtCheck, w.pos, "Loop invariant must consume all debt on entry to the loop.")) :::
    // check lockchange on entry to the loop
    Comment("check lockchange on entry to the loop") ::
    (bassert(LockFrame(lkch, etran), w.pos, "Method execution before loop might lock/unlock more than allowed by lockchange clause of loop.")) ::
    // save values of local-variable loop targets
    (for (sv <- saveLocalsV) yield BLocal(Variable2BVarWhere(sv))) :::
    (for ((v,sv) <- w.LoopTargets zip saveLocalsV) yield (new VariableExpr(sv) := new VariableExpr(v))) :::
    // havoc local-variable loop targets
    (w.LoopTargets :\ List[Boogie.Stmt]()) ( (v,vars) => (v match {
      case v: Variable if v.isImmutable => Boogie.Havoc(Boogie.VarExpr("assigned$" + v.id))
      case _ => Boogie.Havoc(Boogie.VarExpr(v.UniqueName)) }) :: vars) :::
    Boogie.If(null,
    // 1. CHECK  DEFINEDNESS OF INVARIANT
      Comment("check loop invariant definedness") ::
      //(w.LoopTargets.toList map { v: Variable => Boogie.Havoc(Boogie.VarExpr(v.id)) }) :::
      Boogie.Havoc(etran.Heap) :: Boogie.Assign(etran.Mask, ZeroMask) :: Boogie.Assign(etran.Credits, ZeroCredits) ::
      InhaleWithChecking(w.oldInvs, "loop invariant definedness", whileK) :::
      tag(InhaleWithChecking(w.newInvs, "loop invariant definedness", whileK), keepTag) :::                  
      bassume(false)
    , Boogie.If(null,
    // 2. CHECK LOOP BODY
      // Renew state: set Mask to ZeroMask and Credits to ZeroCredits, and havoc Heap everywhere except
      // at {old(local),local}.{held,rdheld}
      Havoc(etran.Heap) :: (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
      Inhale(w.Invs, "loop invariant, body", whileK) :::
      // assume lockchange at the beginning of the loop iteration
      Comment("assume lockchange at the beginning of the loop iteration") ::
      (bassume(LockFrame(lkch, etran))) ::
      // this is the state at the beginning of the loop iteration; save these values
      (for (v <- iterStartGlobals) yield BLocal(v)) :::
      (iterStartEtran.oldEtran.Heap := iterStartEtran.Heap) ::
      (iterStartEtran.oldEtran.Mask := iterStartEtran.Mask) ::  // oldMask is not actually used below
      (iterStartEtran.oldEtran.Credits := iterStartEtran.Credits) ::  // is oldCredits?
      (for (isv <- iterStartLocalsV) yield BLocal(Variable2BVarWhere(isv))) :::
      (for ((v,isv) <- w.LoopTargets zip iterStartLocalsV) yield
         (new VariableExpr(isv) := new VariableExpr(v))) :::
      // evaluate the guard
      isDefined(guard) ::: List(bassume(guard)) :::
      translateStatement(body, whileK) ::: 
      // check invariant
      Exhale(w.oldInvs map { inv => (inv, ErrorMessage(inv.pos, "The loop invariant at " + inv.pos + " might not be preserved by the loop."))}, "loop invariant, maintained", whileK, true) :::
      tag(Exhale(w.newInvs map { inv => (inv, ErrorMessage(inv.pos, "The loop invariant at " + inv.pos + " might not be preserved by the loop."))}, "loop invariant, maintained", whileK, true), keepTag) :::
      isLeaking(w.pos, "The loop might leak refereces.") :::
      // check lockchange after loop iteration
      Comment("check lockchange after loop iteration") ::
        (bassert(LockFrame(lkch, etran), w.pos, "The loop might lock/unlock more than the lockchange clause allows.")) ::
      // perform debt check
      bassert(DebtCheck, w.pos, "Loop body is not allowed to leave any debt.") :::
      bassume(false),
   // 3. AFTER LOOP
     LockHavoc(oldLocks ++ newLocks, loopEtran) :::
     // assume lockchange after the loop
     Comment("assume lockchange after the loop") ::
     (bassume(LockFrame(lkch, etran))) ::
     Inhale(w.Invs, "loop invariant, after loop", whileK) :::
     bassume(!guard)))
  }

  // TODO: This method has not yet been updated to the new permission model
  def translateRefinement(r: RefinementBlock): List[Stmt] = {
    // abstract expression translator
    val absTran = etran;
    // concrete expression translate
    val conGlobals = etran.FreshGlobals("concrete")
    val conTran = new ExpressionTranslator(conGlobals map {v => new VarExpr(v)}, etran.oldEtran.Globals, currentClass);
    // shared locals before block (excluding immutable)
    val before = for (v <- r.before; if (! v.isImmutable)) yield v;
    // shared locals in block
    val (duringA, duringC) = r.during;
    // save locals before (to restore for abstract block)
    val beforeV = for (v <- before) yield new Variable(v.id, v.t)
    // save locals after (to compare with abstract block)
    val afterV = for (v <- before) yield new Variable(v.id, v.t)

    Comment("refinement block") ::
    // save heap
    (for (c <- conGlobals) yield BLocal(c)) :::
    (for ((c, a) <- conGlobals zip etran.Globals) yield (new VarExpr(c) := a)) :::
    // save shared local variables
    (for (v <- beforeV) yield BLocal(Variable2BVarWhere(v))) :::            
    (for ((v, w) <- beforeV zip before) yield (new VariableExpr(v) := new VariableExpr(w))) :::
    // run concrete C on the fresh heap
    {
      etran = conTran;
      Comment("run concrete program:") ::
      tag(translateStatements(r.con, todoiparam), keepTag)
    } :::
    // run angelically A on the old heap
    Comment("run abstract program:") ::
    { etran = absTran;
    r.abs match {
      case List(s: SpecStmt) =>
        var (m, me) = NewBVar("specMask", tmask, true)

        tag(
          Comment("give witnesses to declared local variables") ::
          (for (v <- duringA) yield BLocal(Variable2BVarWhere(v))) :::
          (for ((v, w) <- duringA zip duringC) yield (new VariableExpr(v) := new VariableExpr(w))) :::
          BLocal(m) ::
          (me := absTran.Mask) ::
          absTran.Exhale(s.post, me, absTran.Heap, ErrorMessage(r.pos, "Refinement may fail to satisfy specification statement post-condition."), false, todoiparam, todobparam) :::
          (for ((v, w) <- beforeV zip before; if (! s.lhs.exists(ve => ve.v == w))) yield
             bassert(new VariableExpr(v) ==@ new VariableExpr(w), r.pos, "Refinement may change a variable not in frame of the specification statement: " + v.id)),
          keepTag)
      case _ =>
        // save locals after
        (for (v <- afterV) yield BLocal(Variable2BVarWhere(v))) :::
        (for ((v, w) <- afterV zip before) yield (new VariableExpr(v) := new VariableExpr(w))) :::
        // restore locals before
        (for ((v, w) <- before zip beforeV) yield (new VariableExpr(v) := new VariableExpr(w))) :::
        translateStatements(r.abs, todoiparam) :::
        // assert equality on shared locals
        tag(
          (for ((v, w) <- afterV zip before) yield
            bassert(new VariableExpr(v) ==@ new VariableExpr(w), r.pos, "Refinement may produce different value for pre-state local variable: " + v.id)) :::
          (for ((v, w) <- duringA zip duringC) yield
            bassert(new VariableExpr(v) ==@ new VariableExpr(w), r.pos, "Refinement may produce different value for a declared local variable: " + v.id)),
          keepTag)
    }} :::
    {
      val (v,ve) = NewBVar("this", tref, true)
      // TODO: check for mask coupling
      // TODO: we only inhale concrete values for "This"

      def copy(e: Expression):List[Stmt] = e match {
        case And(a,b) => copy(a) ::: copy(b)
        case Implies(a,b) => Boogie.If(absTran.Tr(a), copy(b), Nil)
        case Access(ma, _) if ! ma.isPredicate => absTran.Heap.store(absTran.Tr(ma.e), new VarExpr(ma.f.FullName), conTran.Heap.select(absTran.Tr(ma.e), ma.f.FullName))
        case _: PermissionExpr => throw new NotSupportedException("not implemented")
        case _ => Nil
      }

      // copy variables in the coupling invariants to the abstract heap (to preserve their values across refinement blocks and establish invariant)
      (for (ci <- currentClass.CouplingInvariants)
        yield Boogie.If((ci.fields.map(f => absTran.CanRead(new VarExpr("this"), f.FullName)).reduceLeft(_ || _)),
          copy(ci.e), Nil)) :::
      // assert equality on shared globals (except those that are replaced)
      tag(
        for (f <- currentClass.refines.Fields; if ! currentClass.CouplingInvariants.exists(_.fields.contains(f)))
          yield bassert((absTran.Heap.select(ve, f.FullName) ==@ conTran.Heap.select(ve, f.FullName)).forall(v), r.pos, "Refinement may change value of field " + f.FullName),
        keepTag)            
    } :::
    Comment("end of refinement block")
  }

  def UpdateMu(o: Expr, allowOnlyFromBottom: Boolean, justAssumeValue: Boolean,
               lowerBounds: List[Expression], upperBounds: List[Expression], error: ErrorMessage): List[Stmt] = {
    def BoundIsNullObject(b: Expression): Boogie.Expr = {
      if (b.typ.IsMu) false else b ==@ bnull
    }
    def MuValue(b: Expression): Expr = {
      if (b.typ.IsMu) b else etran.Heap.select(b, "mu")
    }
    def Below(a: Expr, b: Expr) = {
      new FunctionApp("MuBelow", a, b)
    }
    val (muV, mu) = Boogie.NewBVar("mu", Boogie.NamedType("Mu"), true)
    // check that bounds are well-defined
    ((lowerBounds ++ upperBounds) flatMap { bound => isDefined(bound)}) :::
    // check that we have full access to o.mu
    (if (!justAssumeValue)
      List(bassert(CanWrite(o, "mu"), error.pos, error.message + " The mu field of the target might not be writable."))
     else
       List()) :::
    // ...and that o.mu starts off as lockbottom, if desired
    (if (allowOnlyFromBottom)
      List(bassert(etran.Heap.select(o,"mu") ==@ bLockBottom,
                   error.pos, error.message + " The object may already be shared (i.e., mu may not be LockBottom)"))
     else
      List()) :::
    // check for each bound that if it is a non-null object, then its mu field is readable
    (for (bound <- lowerBounds ++ upperBounds if !bound.typ.IsMu) yield
      bassert((bound ==@ bnull) || CanRead(bound, "mu"), bound.pos, "The mu field of bound at " + bound.pos + " might not be readable." )) :::
    // check that each lower bound is smaller than each upper bound
    (for (lb <- lowerBounds; ub <- upperBounds) yield
      bassert( (etran.ShaveOffOld(lb), etran.ShaveOffOld(ub)) match {
        case ((MaxLockLiteral(),o0), (MaxLockLiteral(),o1)) =>
          if (o0 == o1)
            false
          else
            etran.TemporalMaxLockComparison(etran.ChooseEtran(o0), etran.ChooseEtran(o1))
        case ((MaxLockLiteral(),o), _) => etran.ChooseEtran(o).MaxLockIsBelowX(MuValue(ub))
        case (_, (MaxLockLiteral(),o)) => etran.ChooseEtran(o).MaxLockIsAboveX(MuValue(lb))
        case _ => BoundIsNullObject(lb) ||
                  BoundIsNullObject(ub) ||
                  Below(MuValue(lb), MuValue(ub)) }, lb.pos, "The lower bound at " + lb.pos + " might not be smaller than the upper bound at " + ub.pos + ".")) :::
    // havoc mu
    BLocal(muV) :: Havoc(mu) :: bassume(mu !=@ bLockBottom) ::
    // assume that mu is between the given bounds (or above waitlevel if no bounds are given)
    (if (lowerBounds == Nil && upperBounds == Nil) {
      // assume waitlevel << mu
      List(bassume(etran.MaxLockIsBelowX(mu)))
    } else {
      (for (lb <- lowerBounds) yield
        // assume lb << mu
        bassume(
          if (etran.IsMaxLockLit(lb)) {
            val (f,o) = etran.ShaveOffOld(lb)
            etran.ChooseEtran(o).MaxLockIsBelowX(mu)
          } else
            (BoundIsNullObject(lb) || Below(MuValue(lb), mu)))) :::
      (for (ub <- upperBounds) yield
        // assume mu << ub
        bassume(
          if (etran.IsMaxLockLit(ub)) {
            val (f,o) = etran.ShaveOffOld(ub)
            etran.ChooseEtran(o).MaxLockIsAboveX(mu)
          } else
            (BoundIsNullObject(ub) || Below(mu, MuValue(ub)))))
    }) :::
    // store the mu field
    (if (justAssumeValue) bassume(etran.Heap.select(o, "mu") ==@ mu) else etran.Heap.store(o, "mu", mu))
  }

  def isLeaking(pos: Position, msg: String): List[Boogie.Stmt] = {
    if(Chalice.checkLeaks) {
      var o = Boogie.VarExpr("$o");
      var f = "$f";
      val (ttV,tt) = Boogie.NewTVar("T")
      List(
        bassert(new Boogie.Forall(
          List(ttV),
          List(Boogie.BVar("$o", tref), Boogie.BVar("$f", FieldType(tt))),
          Nil,
          (o ==@ bnull) || ((new MapSelect(etran.Mask, o, f, "perm$R") ==@ 0) && (new MapSelect(etran.Mask, o, f, "perm$N") ==@ 0))
        ), pos, msg)
      )
    } else {
      Nil
    }
  }

  def LockFrame(lkch: List[Expression], etran: ExpressionTranslator) =
    LocksUnchanged(for (l <- lkch) yield etran.Tr(l), etran)
  def LocksUnchanged(exceptions: List[Boogie.Expr], etran: ExpressionTranslator) = {
    val (lkV, lk) = Boogie.NewBVar("lk", tref, true)
    val b: Boogie.Expr = false
    Boogie.Forall(Nil, List(lkV),
                  List(new Trigger(etran.Heap.select(lk, "held")), new Trigger(etran.Heap.select(lk, "rdheld"))),
                  (((0 < etran.Heap.select(lk, "held")) ==@
                    (0 < etran.oldEtran.Heap.select(lk, "held"))) &&
                   (new Boogie.MapSelect(etran.Heap, lk, "rdheld") ==@
                    new Boogie.MapSelect(etran.oldEtran.Heap, lk, "rdheld"))) ||
          // It seems we should exclude newly-allocated objects from lockchange. Since Chalice does not have an "alloc" field,
          // we could use the "mu" field as an approximation, but that breaks the HandOverHand example. So we leave it for now.
          // (new Boogie.MapSelect(etran.oldEtran.Heap, lk, "mu") ==@ bLockBottom) ||
                  ((exceptions :\ b) ((e,ll) => ll || (lk ==@ e))))
  }
  def LockHavoc(locks: List[Boogie.Expr], etran: ExpressionTranslator) = {
    val (heldV, held) = NewBVar("isHeld", IntClass, true)
    val (rdheldV, rdheld) = NewBVar("isRdHeld", BoolClass, true)
    BLocal(heldV) :: BLocal(rdheldV) ::
    (for (o <- locks) yield {  // todo: somewhere we should worry about Df(l)
      Havoc(held) :: Havoc(rdheld) ::
      bassume(rdheld ==> (0 < held)) ::
      new MapUpdate(etran.Heap, o, VarExpr("held"), held) ::
      new MapUpdate(etran.Heap, o, VarExpr("rdheld"), rdheld) }).flatten
  }
  def NumberOfLocksHeldIsInvariant(oldLocks: List[Boogie.Expr], newLocks: List[Boogie.Expr],
                                   etran: ExpressionTranslator) = {
    (for ((o,n) <- oldLocks zip newLocks) yield {
      // oo.held == nn.held && oo.rdheld == nn.rdheld
      (((0 < new Boogie.MapSelect(etran.oldEtran.Heap, o, "held")) ==@
        (0 < new Boogie.MapSelect(etran.Heap, n, "held"))) &&
       (new Boogie.MapSelect(etran.oldEtran.Heap, o, "rdheld") ==@
        new Boogie.MapSelect(etran.Heap, n, "rdheld"))) ::
      // no.held == on.held && no.rdheld == on.rdheld
      (((0 < new Boogie.MapSelect(etran.Heap, o, "held")) ==@
        (0 < new Boogie.MapSelect(etran.oldEtran.Heap, n, "held"))) &&
       (new Boogie.MapSelect(etran.Heap, o, "rdheld") ==@
        new Boogie.MapSelect(etran.oldEtran.Heap, n, "rdheld"))) ::
      // o == n || (oo.held != no.held && (!oo.rdheld || !no.rdheld))
      ((o ==@ n) ||
       (((0 < new Boogie.MapSelect(etran.oldEtran.Heap, o, "held")) !=@ (0 < new Boogie.MapSelect(etran.Heap, o, "held"))) &&
        ((! new Boogie.MapSelect(etran.oldEtran.Heap, o, "rdheld")) ||
         (! new Boogie.MapSelect(etran.Heap, o, "rdheld"))))) ::
      Nil
    }).flatten
  }

  implicit def lift(s: Stmt): List[Stmt] = List(s)
  def isDefined(e: Expression) = etran.isDefined(e)(true)
  def TrExpr(e: Expression) = etran.Tr(e)

  def InhaleInvariants(obj: Expression, readonly: Boolean, tran: ExpressionTranslator, currentK: Expr) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    tran.Inhale(obj.typ.MonitorInvariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv)), "monitor invariant", false, currentK)
  }
  def ExhaleInvariants(obj: Expression, readonly: Boolean, msg: ErrorMessage, tran: ExpressionTranslator, currentK: Expr) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    tran.Exhale(obj.typ.MonitorInvariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv, msg)), "monitor invariant", false, currentK, false)
  }
  def InhaleInvariants(obj: Expression, readonly: Boolean, currentK: Expr) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    Inhale(obj.typ.MonitorInvariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv)), "monitor invariant", currentK)
  }
  def ExhaleInvariants(obj: Expression, readonly: Boolean, msg: ErrorMessage, currentK: Expr) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    Exhale(obj.typ.MonitorInvariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv, msg)), "monitor invariant", currentK, false)
  }

  def Inhale(predicates: List[Expression], occasion: String, currentK: Expr): List[Boogie.Stmt] = etran.Inhale(predicates, occasion, false, currentK)
  def Exhale(predicates: List[(Expression, ErrorMessage)], occasion: String, currentK: Expr, exactchecking: Boolean): List[Boogie.Stmt] = etran.Exhale(predicates, occasion, false, currentK, exactchecking)
  def InhaleWithChecking(predicates: List[Expression], occasion: String, currentK: Expr): List[Boogie.Stmt] = etran.Inhale(predicates, occasion, true, currentK)
  def ExhaleWithChecking(predicates: List[(Expression, ErrorMessage)], occasion: String, currentK: Expr, exactchecking: Boolean): List[Boogie.Stmt] = etran.Exhale(predicates, occasion, true, currentK, exactchecking)

  def CanRead(obj: Boogie.Expr, field: Boogie.Expr): Boogie.Expr = etran.CanRead(obj, field)
  def CanWrite(obj: Boogie.Expr, field: Boogie.Expr): Boogie.Expr = etran.CanWrite(obj, field)


/**********************************************************************
*****************          EXPRESSIONS                *****************
**********************************************************************/

object ExpressionTranslator {
  val Globals = {
    ("Heap", theap) ::
    ("Mask", tmask) ::
    ("Credits", tcredits) ::
    Nil
  }
}

class ExpressionTranslator(globals: List[Boogie.Expr], preGlobals: List[Boogie.Expr], currentClass: Class, checkTermination: Boolean) {
  assert(globals.size == 3)
  assert(preGlobals.size == 3)

  import TranslationHelper._

  val Heap = globals(0);
  val Mask = globals(1);
  val Credits = globals(2);
  lazy val oldEtran = new ExpressionTranslator(preGlobals, preGlobals, currentClass, checkTermination)

  def this(globals: List[Boogie.Expr], preGlobals: List[Boogie.Expr], currentClass: Class) = this(globals, preGlobals, currentClass, false)
  def this(globals: List[Boogie.Expr], cl: Class) = this(globals, globals map (g => Boogie.Old(g)), cl)
  def this(cl: Class) = this(for ((id,t) <- ExpressionTranslator.Globals) yield Boogie.VarExpr(id), cl)

  def Globals = List(Heap, Mask, Credits)
  def ChooseEtran(chooseOld: Boolean) = if (chooseOld) oldEtran else this

  /**
   * Create a list of fresh global variables
   */
  def FreshGlobals(prefix: String):List[Boogie.BVar] = {
    new Boogie.BVar(prefix + HeapName, theap, true) ::
    new Boogie.BVar(prefix + MaskName, tmask, true) ::
    new Boogie.BVar(prefix + CreditsName, tcredits, true) ::
    Nil
  }

  def FromPreGlobals(preGlobals: List[Boogie.BVar]) = {
    val pg = preGlobals map (g => new VarExpr(g))
    new ExpressionTranslator(globals, pg, currentClass, checkTermination)
  }

  def UseCurrentAsOld() = {
    new ExpressionTranslator(globals, globals, currentClass, checkTermination);
  }

  def WhereOldIs(h: Boogie.Expr, m: Boogie.Expr, c: Boogie.Expr) = {
    new ExpressionTranslator(globals, List(h, m, c), currentClass, checkTermination);
  }

  def CheckTermination(check: Boolean) = {
    new ExpressionTranslator(globals, preGlobals, currentClass, check);
  }

  /**********************************************************************
  *****************              TR/DF                  *****************
  **********************************************************************/

  def isDefined(e: Expression)(implicit assumption: Expr): List[Boogie.Stmt] = {
    def prove(goal: Expr, pos: Position, msg: String)(implicit assumption: Expr) =
      bassert(assumption ==> goal, pos, msg)
    
    desugar(e) match {
      case IntLiteral(n) => Nil
      case BoolLiteral(b) => Nil
      case NullLiteral() => Nil
      case MaxLockLiteral() => Nil
      case LockBottomLiteral() => Nil
      case _:ThisExpr => Nil
      case _:Result => Nil
      case _:VariableExpr => Nil
      case fs @ MemberAccess(e, f) =>       
        assert(!fs.isPredicate);
        isDefined(e) ::: 
        prove(nonNull(Tr(e)), e.pos, "Receiver might be null.") ::
        prove(CanRead(Tr(e), fs.f.FullName), fs.pos, "Location might not be readable.")
      case Full | Star | Epsilon | MethodEpsilon => Nil
      case ForkEpsilon(token) => isDefined(token)
      case MonitorEpsilon(Some(monitor)) => isDefined(monitor)
      case ChannelEpsilon(Some(channel)) => isDefined(channel)
      case PredicateEpsilon(_) => Nil
      case ChannelEpsilon(None) | MonitorEpsilon(None) => Nil
      case PermPlus(l,r) => isDefined(l) ::: isDefined(r)
      case PermMinus(l,r) => isDefined(l) ::: isDefined(r)
      case PermTimes(l,r) => isDefined(l) ::: isDefined(r)
      case IntPermTimes(l,r) => isDefined(l) ::: isDefined(r)
      case Frac(perm) => isDefined(perm)
      case Epsilons(p) => isDefined(p)
      case _:PermissionExpr => throw new InternalErrorException("permission expression unexpected here: " + e.pos + " (" + e + ")")
      case c@Credit(e, n) =>
        isDefined(e) :::
        isDefined(c.N)
      case Holds(e) =>
        isDefined(e)
      case RdHolds(e) =>
        isDefined(e)
      case _: Assigned => Nil
      case Old(e) =>
        oldEtran.isDefined(e)
      case IfThenElse(con, then, els) =>
        isDefined(con) ::: Boogie.If(Tr(con), isDefined(then), isDefined(els))
      case Not(e) =>
        isDefined(e)
      case func@FunctionApplication(obj, id, args) =>
        val newGlobals = FreshGlobals("checkPre");
        val (tmpHeapV, tmpHeap) = Boogie.NewBVar("Heap", theap, true);
        val (tmpMaskV, tmpMask) = Boogie.NewBVar("Mask", tmask, true); 
        val (tmpCreditsV, tmpCredits) = Boogie.NewBVar("Credits", tcredits, true); 
        val tmpTranslator = new ExpressionTranslator(List(tmpHeap,tmpMask,tmpCredits), etran.oldEtran.Globals, currentClass);
        
        // pick new k
        val (funcappKV, funcappK) = Boogie.NewBVar("funcappK", tint, true)
        
        // check definedness of receiver + arguments
        (obj :: args flatMap { arg => isDefined(arg) }) :::
        // check that receiver is not null
        List(prove(nonNull(Tr(obj)), obj.pos, "Receiver might be null.")) :::
        // check precondition of the function by exhaling the precondition in tmpHeap/tmpMask/tmpCredits
        Comment("check precondition of call") ::
        BLocal(funcappKV) :: bassume(0 < funcappK && 1000*funcappK < permissionFull) ::
        bassume(assumption) ::
        BLocal(tmpHeapV) :: (tmpHeap := Heap) ::
        BLocal(tmpMaskV) :: (tmpMask := Mask) :::
        BLocal(tmpCreditsV) :: (tmpCredits := Credits) :::
        tmpTranslator.Exhale(Preconditions(func.f.spec) map { pre=> (SubstVars(pre, obj, func.f.ins, args), ErrorMessage(func.pos, "Precondition at " + pre.pos + " might not hold."))},
                             "function call",
                             false, funcappK, false) :::
        // size of the heap of callee must be strictly smaller than size of the heap of the caller
        (if(checkTermination) { List(prove(NonEmptyMask(tmpMask), func.pos, "The heap of the callee might not be strictly smaller than the heap of the caller.")) } else Nil)
      case unfolding@Unfolding(acc@Access(pred@MemberAccess(obj, f), perm), e) =>
        val newGlobals = FreshGlobals("checkPre");
        val (tmpHeapV, tmpHeap) = Boogie.NewBVar("Heap", theap, true);
        val (tmpMaskV, tmpMask) = Boogie.NewBVar("Mask", tmask, true);
        val (tmpCreditsV, tmpCredits) = Boogie.NewBVar("Credits", tcredits, true);
        val tmpTranslator = new ExpressionTranslator(List(tmpHeap, tmpMask, tmpCredits), etran.oldEtran.Globals, currentClass);
        
        val receiverOk = isDefined(obj) ::: prove(nonNull(Tr(obj)), obj.pos, "Receiver might be null.");
        val definition = scaleExpressionByPermission(SubstThis(DefinitionOf(pred.predicate), obj), perm, unfolding.pos)
        
        // pick new k
        val (unfoldingKV, unfoldingK) = Boogie.NewBVar("unfoldingK", tint, true)
        
        Comment("unfolding") ::
        BLocal(unfoldingKV) :: bassume(0 < unfoldingK && 1000*unfoldingK < permissionFull) ::
        // check definedness
        receiverOk ::: isDefined(perm) :::
        // copy state into temporary variables
        BLocal(tmpHeapV) :: Boogie.Assign(tmpHeap, Heap) ::
        BLocal(tmpMaskV) :: Boogie.Assign(tmpMask, Mask) ::
        BLocal(tmpCreditsV) :: Boogie.Assign(tmpCredits, Credits) ::
        // exhale the predicate
        tmpTranslator.Exhale(List((acc, ErrorMessage(unfolding.pos, "Unfolding might fail."))), "unfolding", false, unfoldingK, false) :::
        // inhale the definition of the predicate
        tmpTranslator.InhaleFrom(List(definition), "unfolding", false, Heap.select(Tr(obj), pred.predicate.FullName), unfoldingK) :::
        // check definedness of e in state where the predicate is unfolded
        tmpTranslator.isDefined(e)
      case Iff(e0,e1) =>
        isDefined(e0) ::: isDefined(e1)
      case Implies(e0,e1) =>
        isDefined(e0) ::: isDefined(e1)(assumption && Tr(e0))
      case And(e0,e1) =>
        isDefined(e0) ::: isDefined(e1)(assumption && Tr(e0))
      case Or(e0,e1) =>
        isDefined(e0) ::: isDefined(e1)(assumption && Boogie.UnaryExpr("!", Tr(e0)))
      case LockBelow(e0,e1) =>
        var df = isDefined(e0) ::: isDefined(e1);
        if (e0.typ.IsRef) {
          df = df ::: List(prove(nonNull(Tr(e0)), e0.pos, "Receiver might be null."), prove(CanRead(Tr(e0),"mu"), e0.pos, "The mu field might not be readable."));
        }
         if (e1.typ.IsRef) {
          df = df ::: List(prove(nonNull(Tr(e1)), e1.pos, "Receiver might be null."), prove(CanRead(Tr(e1),"mu"), e1.pos, "The mu field might not be readable."));
        }
        df
      case e: CompareExpr =>
        isDefined(e.E0) ::: isDefined(e.E1)
      case Div(e0,e1) =>
        isDefined(e0) ::: isDefined(e1) :::
        List(prove(Tr(e1) !=@ 0, e1.pos, "Denominator might be zero."))
      case Mod(e0,e1) =>
        isDefined(e0) ::: isDefined(e1) ::: List(prove(Tr(e1) !=@ 0, e1.pos, "Denominator might be zero."))
      case e: ArithmeticExpr =>
        isDefined(e.E0) ::: isDefined(e.E1)
      case EmptySeq(t) => Nil
      case ExplicitSeq(es) =>
        es flatMap { e => isDefined(e) }
      case Range(min, max) =>
        isDefined(min) ::: isDefined(max) :::
        prove(Tr(min) <= Tr(max), e.pos, "Range minimum might not be smaller or equal to range maximum.")
      case Append(e0, e1) =>
        isDefined(e0) ::: isDefined(e1)
      case at@At(e0, e1) =>
        isDefined(e0) ::: isDefined(e1) :::
        prove(0 <= Tr(e1), at.pos, "Sequence index might be negative.") ::
        prove(Tr(e1) < SeqLength(Tr(e0)), at.pos, "Sequence index might be larger than or equal to the length of the sequence.")
      case Drop(e0, e1) => 
        isDefined(e0) ::: isDefined(e1) :::
        prove(0 <= Tr(e1), e.pos, "Cannot drop less than zero elements.") ::
        prove(Tr(e1) <= SeqLength(Tr(e0)), e.pos, "Cannot drop more than elements than the length of the sequence.")
      case Take(e0, e1) => 
        isDefined(e0) ::: isDefined(e1) :::
        prove(0 <= Tr(e1), e.pos, "Cannot take less than zero elements.") ::
        prove(Tr(e1) <= SeqLength(Tr(e0)), e.pos, "Cannot take more than elements than the length of the sequence.")
      case Length(e) =>
        isDefined(e)
      case Contains(e0, e1) =>
        isDefined(e0) ::: isDefined(e1)
      case Eval(h, e) =>
        val (evalHeap, evalMask, evalCredits, checks, assumptions) = fromEvalState(h);
        val evalEtran = new ExpressionTranslator(List(evalHeap, evalMask, evalCredits), etran.oldEtran.Globals, currentClass);
        evalEtran.isDefined(e)
      case _ : SeqQuantification => throw new InternalErrorException("should be desugared")
      case tq @ TypeQuantification(_, _, _, e, (min, max)) =>
        // replace variables since we need locals
        val vars = tq.variables map {v => val result = new Variable(v.id, v.t); result.pos = v.pos; result;}
        prove(Tr(min) <= Tr(max), e.pos, "Range minimum might not be smaller or equal to range maximum.") :::
        (vars map {v => BLocal(Variable2BVarWhere(v))}) :::
        isDefined(SubstVars(e, tq.variables, vars map {v => new VariableExpr(v);}))
      case tq @ TypeQuantification(_, _, _, e, _) =>
        // replace variables since we need locals
        val vars = tq.variables map {v => val result = new Variable(v.id, v.t); result.pos = v.pos; result;}
        (vars map {v => BLocal(Variable2BVarWhere(v))}) :::
        isDefined(SubstVars(e, tq.variables, vars map {v => new VariableExpr(v);}))
    }
  }

  def Tr(e: Expression): Boogie.Expr = desugar(e) match {
    case IntLiteral(n) => n
    case BoolLiteral(b) => b
    case NullLiteral() => bnull
    case MaxLockLiteral() => throw new InternalErrorException("waitlevel case should be handled in << and == and !=")
    case LockBottomLiteral() => bLockBottom
    case _:ThisExpr => VarExpr("this")
    case _:Result => VarExpr("result")
    case ve : VariableExpr => VarExpr(ve.v.UniqueName)
    case fs @ MemberAccess(e,_) =>
      assert(! fs.isPredicate);
      var r = Heap.select(Tr(e), fs.f.FullName);
      if (fs.f.isInstanceOf[SpecialField] && fs.f.id == "joinable")
        r !=@ 0 // joinable is encoded as an integer
      else
        r
    case _:Permission => throw new InternalErrorException("permission unexpected here")
    case _:PermissionExpr => throw new InternalErrorException("permission expression unexpected here: " + e.pos)
    case _:Credit => throw new InternalErrorException("credit expression unexpected here")
    case Holds(e) =>
      (0 < Heap.select(Tr(e), "held")) &&
      !Heap.select(Tr(e), "rdheld")
    case RdHolds(e) =>
      Heap.select(Tr(e), "rdheld")
    case a: Assigned =>
      VarExpr("assigned$" + a.v.UniqueName)
    case Old(e) =>
      oldEtran.Tr(e)
    case IfThenElse(con, then, els) =>
      Boogie.Ite(Tr(con), Tr(then), Tr(els))  // of type: VarExpr(TrClass(then.typ))
    case Not(e) =>
      ! Tr(e)
    case func@FunctionApplication(obj, id, args) =>
      FunctionApp(functionName(func.f), Heap :: Mask :: (obj :: args map { arg => Tr(arg)}))
    case uf@Unfolding(_, e) =>
      Tr(e)
    case Iff(e0,e1) =>
      Tr(e0) <==> Tr(e1)
    case Implies(e0,e1) =>
      Tr(e0) ==> Tr(e1)
    case And(e0,e1) =>
      Tr(e0) && Tr(e1)
    case Or(e0,e1) =>
      Tr(e0) || Tr(e1)
    case Eq(e0,e1) =>
      (ShaveOffOld(e0), ShaveOffOld(e1)) match {
        case ((MaxLockLiteral(),o0), (MaxLockLiteral(),o1)) =>
          if (o0 == o1)
            true
          else
            MaxLockPreserved
        case ((MaxLockLiteral(),o), _) => ChooseEtran(o).IsHighestLock(Tr(e1))
        case (_, (MaxLockLiteral(),o)) => ChooseEtran(o).IsHighestLock(Tr(e0))
        case _ => if(e0.typ.IsSeq) FunctionApp("Seq#Equal", List(Tr(e0), Tr(e1))) else (Tr(e0) ==@ Tr(e1))
      }
    case Neq(e0,e1) =>
      Tr(Not(Eq(e0,e1)))
    case Less(e0,e1) =>
      Tr(e0) < Tr(e1)
    case AtMost(e0,e1) =>
      Tr(e0) <= Tr(e1)
    case AtLeast(e0,e1) =>
      Tr(e0) >= Tr(e1)
    case Greater(e0,e1) =>
      Tr(e0) > Tr(e1)
    case LockBelow(e0,e1) => {
      def MuValue(b: Expression): Boogie.Expr =
        if (b.typ.IsRef) new Boogie.MapSelect(Heap, Tr(b), "mu") else Tr(b)
      (ShaveOffOld(e0), ShaveOffOld(e1)) match {
        case ((MaxLockLiteral(),o0), (MaxLockLiteral(),o1)) =>
          if (o0 == o1)
            false
          else
            TemporalMaxLockComparison(ChooseEtran(o0), ChooseEtran(o1))
        case ((MaxLockLiteral(),o), _) => ChooseEtran(o).MaxLockIsBelowX(MuValue(e1))
        case (_, (MaxLockLiteral(),o)) => ChooseEtran(o).MaxLockIsAboveX(MuValue(e0))
        case _ => new FunctionApp("MuBelow", MuValue(e0), MuValue(e1)) }
    }
    case Plus(e0,e1) =>
      Tr(e0) + Tr(e1)
    case Minus(e0,e1) =>
      Tr(e0) - Tr(e1)
    case Times(e0,e1) =>
      Tr(e0) * Tr(e1)
    case Div(e0,e1) =>
      Tr(e0) / Tr(e1)
    case Mod(e0,e1) =>
      Tr(e0) % Tr(e1)
    case EmptySeq(t) =>
      createEmptySeq
    case ExplicitSeq(es) =>
      es match {
        case Nil => createEmptySeq
        case h :: Nil => createSingletonSeq(Tr(h))
        case h :: t => createAppendSeq(createSingletonSeq(Tr(h)), Tr(ExplicitSeq(t)))
      }
    case Range(min, max) =>
      createRange(Tr(min), Tr(max))
    case Append(e0, e1) =>
      createAppendSeq(Tr(e0), Tr(e1))
    case at@At(e0, e1) =>SeqIndex(Tr(e0), Tr(e1))
    case Drop(e0, e1) =>
      Boogie.FunctionApp("Seq#Drop", List(Tr(e0), Tr(e1)))
    case Take(e0, e1) =>
      Boogie.FunctionApp("Seq#Take", List(Tr(e0), Tr(e1)))
    case Length(e) => SeqLength(Tr(e))
    case Contains(e0, e1) => SeqContains(Tr(e1), Tr(e0))
    case Eval(h, e) =>
      val (evalHeap, evalMask, evalCredits, checks, assumptions) = fromEvalState(h);
      val evalEtran = new ExpressionTranslator(List(evalHeap, evalMask, evalCredits), etran.oldEtran.Globals, currentClass);
      evalEtran.Tr(e)
    case _:SeqQuantification => throw new InternalErrorException("should be desugared")
    case tq @ TypeQuantification(Forall, _, _, e, _) =>
      Boogie.Forall(Nil, tq.variables map { v => Variable2BVar(v)}, Nil, Tr(e))
    case tq @ TypeQuantification(Exists, _, _, e, _) =>
      Boogie.Exists(Nil, tq.variables map { v => Variable2BVar(v)}, Nil, Tr(e))
  }

  def ShaveOffOld(e: Expression): (Expression, Boolean) = e match {
    case Old(e) =>
      val (f,o) = ShaveOffOld(e)
      (f,true)
    case _ => (e,false)
  }
  def IsMaxLockLit(e: Expression) = {
    val (f,o) = ShaveOffOld(e)
    f.isInstanceOf[MaxLockLiteral]
  }

  /**********************************************************************
  *****************          INHALE/EXHALE              *****************
  **********************************************************************/

  def Inhale(predicates: List[Expression], occasion: String, check: Boolean, currentK: Expr): List[Boogie.Stmt] = {
    if (predicates.size == 0) return Nil;
    
    val (ihV, ih) = Boogie.NewBVar("inhaleHeap", theap, true)
    Comment("inhale (" + occasion + ")") ::
    BLocal(ihV) :: Boogie.Havoc(ih) ::
    bassume(IsGoodInhaleState(ih, Heap, Mask)) ::
    (for (p <- predicates) yield Inhale(p, ih, check, currentK)).flatten :::
    bassume(IsGoodMask(Mask)) ::
    bassume(wf(Heap, Mask)) ::
    Comment("end inhale")
  }

  def InhaleFrom(predicates: List[Expression], occasion: String, check: Boolean, useHeap: Boogie.Expr, currentK: Expr): List[Boogie.Stmt] = {
    if (predicates.size == 0) return Nil;
    
    val (ihV, ih) = Boogie.NewBVar("inhaleHeap", theap, true)
    Comment("inhale (" + occasion + ")") ::
    BLocal(ihV) :: Boogie.Assign(ih, useHeap) ::
    bassume(IsGoodInhaleState(ih, Heap, Mask)) ::
    (for (p <- predicates) yield Inhale(p,ih, check, currentK)).flatten :::
    bassume(IsGoodMask(Mask)) ::
    bassume(wf(Heap, Mask)) ::
    Comment("end inhale")
  }
  
  def InhalePermission(perm: Permission, obj: Expr, memberName: String, currentK: Expr): List[Boogie.Stmt] = {
    
    val (f, stmts) = extractKFromPermission(perm, currentK)
    val n = extractEpsilonsFromPermission(perm);
    
    stmts :::
    (perm.permissionType match {
      case PermissionType.Mixed =>
        bassume(f > 0 || (f == 0 && n > 0)) ::
        IncPermission(obj, memberName, f) :::
        IncPermissionEpsilon(obj, memberName, n)
      case PermissionType.Epsilons =>
        bassume(n > 0) ::
        IncPermissionEpsilon(obj, memberName, n)
      case PermissionType.Fraction =>
        bassume(f > 0) ::
        IncPermission(obj, memberName, f)
    })
  }

  def Inhale(p: Expression, ih: Boogie.Expr, check: Boolean, currentK: Expr): List[Boogie.Stmt] = desugar(p) match {
    case pred@MemberAccess(e, p) if pred.isPredicate => 
      val chk = (if (check) {
        isDefined(e)(true) ::: 
        bassert(nonNull(Tr(e)), e.pos, "Receiver might be null.") :: Nil
      } else Nil)
      val tmp = Access(pred, Full);
      tmp.pos = pred.pos;
      chk ::: Inhale(tmp, ih, check, currentK)
    case AccessAll(obj, perm) => throw new InternalErrorException("should be desugared")
    case AccessSeq(s, None, perm) => throw new InternalErrorException("should be desugared")
    case acc@Access(e,perm) =>
      val trE = Tr(e.e)
      val module = currentClass.module;
      val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;

      // List(bassert(nonNull(trE), acc.pos, "The target of the acc predicate might be null."))
      (if(check) isDefined(e.e)(true) ::: isDefined(perm)(true)
      else Nil) :::
      bassume(nonNull(trE)) ::
      new MapUpdate(Heap, trE, VarExpr(memberName), new Boogie.MapSelect(ih, trE, memberName)) ::
      bassume(wf(Heap, Mask)) ::
      (if(e.isPredicate && e.predicate.Parent.module.equals(currentClass.module)) List(bassume(new Boogie.MapSelect(ih, trE, memberName) ==@ Heap)) else Nil) :::
      (if(e.isPredicate) Nil else List(bassume(TypeInformation(new Boogie.MapSelect(Heap, trE, memberName), e.f.typ.typ)))) :::
      InhalePermission(perm, trE, memberName, currentK) :::
      bassume(IsGoodMask(Mask)) ::
      bassume(IsGoodState(new Boogie.MapSelect(ih, trE, memberName))) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(ih, Mask))
    case acc @ AccessSeq(s, Some(member), perm) =>
      if (member.isPredicate) throw new NotSupportedException("not yet implemented");
      val e = Tr(s);
      val memberName = member.f.FullName;
      val (refV, ref) = Boogie.NewBVar("ref", tref, true);
      
      val (r, stmts) = extractKFromPermission(perm, currentK)
      val n = extractEpsilonsFromPermission(perm);

      stmts :::
      // assume that the permission is positive
      bassume((SeqContains(e, ref) ==>
      (perm.permissionType match {
        case PermissionType.Fraction => r > 0
        case PermissionType.Mixed    => r > 0 || (r == 0 && n > 0)
        case PermissionType.Epsilons => n > 0
      })).forall(refV)) ::
      (if (check) isDefined(s)(true) ::: isDefined(perm)(true) else Nil) :::
      {
        val (aV,a) = Boogie.NewTVar("alpha");
        val (refV, ref) = Boogie.NewBVar("ref", tref, true);
        val (fV, f) = Boogie.NewBVar("f", FieldType(a), true);
        (Heap := Lambda(List(aV), List(refV, fV),
          (SeqContains(e, ref) && f ==@ memberName).thenElse
            (ih(ref, f), Heap(ref, f)))) ::
        bassume((SeqContains(e, ref) ==> TypeInformation(Heap(ref, memberName), member.f.typ.typ)).forall(refV))
      } :::
      bassume(wf(Heap, Mask)) ::
      // update the map
      {
        val (aV,a) = Boogie.NewTVar("alpha");
        val (fV, f) = Boogie.NewBVar("f", FieldType(a), true);
        val (pcV,pc) = Boogie.NewBVar("p", tperm, true);
        Mask := Lambda(List(aV), List(refV, fV),
          (SeqContains(e, ref) && f ==@ memberName).thenElse
            (Lambda(List(), List(pcV),
              Boogie.Ite(pc ==@ "perm$R",
                Mask(ref, f)("perm$R") + r,
                Mask(ref, f)("perm$N") + n)),
            Mask(ref, f)))
      } :::
      bassume(IsGoodMask(Mask)) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(ih, Mask))
    case cr@Credit(ch, n) =>
      val trCh = Tr(ch)
      (if (check)
         isDefined(ch)(true) :::
         bassert(nonNull(trCh), ch.pos, "The target of the credit predicate might be null.") :::
         isDefined(cr.N)(true)
       else
         Nil) :::
      new Boogie.MapUpdate(Credits, trCh, new Boogie.MapSelect(Credits, trCh) + Tr(cr.N))
    case Implies(e0,e1) =>
      (if(check) isDefined(e0)(true) else Nil) :::
      Boogie.If(Tr(e0), Inhale(e1, ih, check, currentK), Nil)
    case IfThenElse(con, then, els) =>
      (if(check) isDefined(con)(true) else Nil) :::
      Boogie.If(Tr(con), Inhale(then, ih, check, currentK), Inhale(els, ih, check, currentK))
    case And(e0,e1) =>
      Inhale(e0, ih, check, currentK) ::: Inhale(e1, ih, check, currentK)
    case holds@Holds(e) =>
      val trE = Tr(e);
      (if(check)
         isDefined(e)(true) :::
         bassert(nonNull(trE), holds.pos, "The target of the holds predicate might be null.")
       else Nil) :::
      bassume(IsGoodMask(Mask)) ::
      bassume(IsGoodState(new Boogie.MapSelect(ih, trE, "held"))) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(ih, Mask)) ::
      new Boogie.MapUpdate(Heap, trE, VarExpr("held"),
                      new Boogie.MapSelect(ih, trE, "held")) ::
      bassume(0 < new Boogie.MapSelect(ih, trE, "held")) ::
      bassume(! new Boogie.MapSelect(ih, trE, "rdheld")) ::
      bassume(wf(Heap, Mask)) ::
      bassume(IsGoodMask(Mask)) ::
      bassume(IsGoodState(new Boogie.MapSelect(ih, trE, "held"))) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(ih, Mask))
    case Eval(h, e) => 
      val (evalHeap, evalMask, evalCredits, checks, proofOrAssume) = fromEvalState(h);
      val preGlobals = etran.FreshGlobals("eval")
      val preEtran = new ExpressionTranslator(preGlobals map (v => new Boogie.VarExpr(v)), currentClass)
      BLocal(preGlobals(0)) :: BLocal(preGlobals(1)) :: BLocal(preGlobals(2)) ::
      (new VarExpr(preGlobals(1)) := ZeroMask) ::
      // Should we start from ZeroMask instead of an arbitrary mask? In that case, assume submask(preEtran.Mask, evalMask); at the end!
      (if(check) checks else Nil) :::
      // havoc the held field when inhaling eval(o.release, ...)
      (if(h.isInstanceOf[ReleaseState]) {
        val (freshHeldV, freshHeld) = NewBVar("freshHeld", tint, true);
        val obj = Tr(h.target());
        List(BLocal(freshHeldV), bassume((0<Heap.select(obj, "held")) <==> (0<freshHeld)), (Heap.select(obj, "held") := freshHeld))
      } else Nil) :::
      bassume(IsGoodMask(preEtran.Mask)) ::
      bassume(wf(preEtran.Heap, preEtran.Mask)) ::
      bassume(proofOrAssume) ::
      preEtran.Inhale(e, ih, check, currentK) :::
      bassume(preEtran.Heap ==@ evalHeap) ::
      bassume(submask(preEtran.Mask, evalMask))
    case e => (if(check) isDefined(e)(true) else Nil) ::: bassume(Tr(e))
  }
  
  def Exhale(predicates: List[(Expression, ErrorMessage)], occasion: String, check: Boolean, currentK: Expr, exactchecking: Boolean): List[Boogie.Stmt] = {
    if (predicates.size == 0) return Nil;
    
    val (emV, em) = NewBVar("exhaleMask", tmask, true)
    Comment("begin exhale (" + occasion + ")") ::
    BLocal(emV) :: (em := Mask) ::
    (for (p <- predicates) yield Exhale(p._1, em, null, p._2, check, currentK, exactchecking)).flatten :::
    (Mask := em) ::
    bassume(wf(Heap, Mask)) ::
    Comment("end exhale")
  }
  
  def ExhalePermission(perm: Permission, obj: Expr, memberName: String, currentK: Expr, pos: Position, error: ErrorMessage, em: Boogie.Expr, exactchecking: Boolean): List[Boogie.Stmt] = {
    val ec = needExactChecking(perm, exactchecking);
    
    val (f, stmts) = extractKFromPermission(perm, currentK)
    val n = extractEpsilonsFromPermission(perm);
    
    stmts :::
    (perm.permissionType match {
      case PermissionType.Mixed =>
        bassert(f > 0 || (f == 0 && n > 0), error.pos, error.message + " The permission at " + pos + " might not be positive.") ::
        DecPermissionBoth(obj, memberName, f, n, em, error, pos, ec)
      case PermissionType.Epsilons =>
        bassert(n > 0, error.pos, error.message + " The permission at " + pos + " might not be positive.") ::
        DecPermissionEpsilon(obj, memberName, n, em, error, pos)
      case PermissionType.Fraction =>
        bassert(f > 0, error.pos, error.message + " The permission at " + pos + " might not be positive.") ::
        DecPermission(obj, memberName, f, em, error, pos, ec)
    })
  }
  
  // does this permission require exact checking, or is it enough to check that we have any permission > 0?
  def needExactChecking(perm: Permission, default: Boolean): Boolean = {
    perm match {
      case Full => true
      case Frac(_) => true
      case Epsilon => default
      case PredicateEpsilon(_) | MonitorEpsilon(_) | ChannelEpsilon(_) | ForkEpsilon(_) => true
      case MethodEpsilon => default
      case Epsilons(p) => true
      case Star => false
      case IntPermTimes(lhs, rhs) => needExactChecking(rhs, default)
      case PermTimes(lhs, rhs) => {
        val l = needExactChecking(lhs, default);
        val r = needExactChecking(rhs, default);
        if (l == false || r == false) false else true // if one side doesn't need exact checking, the whole multiplication doesn't
      }
      case PermPlus(lhs, rhs) => {
        val l = needExactChecking(lhs, default);
        val r = needExactChecking(rhs, default);
        if (l == true || r == true) true else false // if one side needs exact checking, use exact
      }
      case PermMinus(lhs, rhs) => {
        val l = needExactChecking(lhs, default);
        val r = needExactChecking(rhs, default);
        if (l == true || r == true) true else false // if one side needs exact checking, use exact
      }
    }
  }
  
  def Exhale(p: Expression, em: Boogie.Expr, eh: Boogie.Expr, error: ErrorMessage, check: Boolean, currentK: Expr, exactchecking: Boolean): List[Boogie.Stmt] = desugar(p) match {
    case pred@MemberAccess(e, p) if pred.isPredicate =>
      val tmp = Access(pred, Full);
      tmp.pos = pred.pos;
      Exhale(tmp, em , eh, error, check, currentK, exactchecking)
    case AccessAll(obj, perm) => throw new InternalErrorException("should be desugared")
    case AccessSeq(s, None, perm) => throw new InternalErrorException("should be desugared")
    case acc@Access(e,perm) =>
      val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;
      val (starKV, starK) = NewBVar("starK", tint, true);

      // check definedness
      (if(check) isDefined(e.e)(true) :::
                 bassert(nonNull(Tr(e.e)), error.pos, error.message + " The target of the acc predicate at " + acc.pos + " might be null.") else Nil) :::
      // if the mask does not contain sufficient permissions, try folding acc(e, fraction)
      // TODO: include automagic again
      // check that the necessary permissions are there and remove them from the mask
      ExhalePermission(perm, Tr(e.e), memberName, currentK, acc.pos, error, em, exactchecking) :::
      bassume(IsGoodMask(Mask)) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(Heap, em))
    case acc @ AccessSeq(s, Some(member), perm) =>
      if (member.isPredicate) throw new NotSupportedException("not yet implemented");
      val e = Tr(s);
      val memberName = member.f.FullName;
      
      val (r, stmts) = extractKFromPermission(perm, currentK)
      val n = extractEpsilonsFromPermission(perm);
      val ec = needExactChecking(perm, exactchecking);

      stmts :::
      (if (check) isDefined(s)(true) ::: isDefined(perm)(true) else Nil) :::
      {
        val (aV,a) = Boogie.NewTVar("alpha");
        val (refV, ref) = Boogie.NewBVar("ref", tref, true);
        val (fV, f) = Boogie.NewBVar("f", FieldType(a), true);
        val (pcV,pc) = Boogie.NewBVar("p", tperm, true);
        val mr = em(ref, memberName)("perm$R");
        val mn = em(ref, memberName)("perm$N");
        
        // assert that the permission is positive
        bassert((SeqContains(e, ref) ==>
          (perm.permissionType match {
            case PermissionType.Fraction => r > 0
            case PermissionType.Mixed    => r > 0 || (r == 0 && n > 0)
            case PermissionType.Epsilons => n > 0
          })).forall(refV), error.pos, error.message + " The permission at " + acc.pos + " might not be positive.") ::
        // make sure enough permission is available
        bassert((SeqContains(e, ref) ==>
          ((perm,perm.permissionType) match {
            case _ if !ec     => mr > 0
            case (Star,_)     => mr > 0
            case (_,PermissionType.Fraction) => r <= mr && (r ==@ mr ==> 0 <= mn)
            case (_,PermissionType.Mixed)    => r <= mr && (r ==@ mr ==> n <= mn)
            case (_,PermissionType.Epsilons) => mr ==@ 0 ==> n <= mn
          })).forall(refV), error.pos, error.message + " Insufficient permission at " + acc.pos + " for " + member.f.FullName) ::
        // additional assumption on k if we have a star permission or use inexact checking
        ( perm match {
            case _ if !ec => bassume((SeqContains(e, ref) ==> (r < mr)).forall(refV)) :: Nil
            case Star => bassume((SeqContains(e, ref) ==> (r < mr)).forall(refV)) :: Nil
            case _ => Nil
        }) :::
        // update the map
        (em := Lambda(List(aV), List(refV, fV),
          (SeqContains(e, ref) && f ==@ memberName).thenElse(
            Lambda(List(), List(pcV), (pc ==@ "perm$R").thenElse(mr - r, mn - n)),
            em(ref, f))))
      } :::
      bassume(IsGoodMask(Mask)) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(Heap, em))

    case cr@Credit(ch, n) =>
      val trCh = Tr(ch)
      (if (check)
         isDefined(ch)(true) :::
         bassert(nonNull(trCh), ch.pos, "The target of the credit predicate might be null.") :::
         isDefined(cr.N)(true)
       else
         Nil) :::
      new Boogie.MapUpdate(Credits, trCh, new Boogie.MapSelect(Credits, trCh) - Tr(cr.N))
    case Implies(e0,e1) =>
      (if(check) isDefined(e0)(true) else Nil) :::
      Boogie.If(Tr(e0), Exhale(e1, em, eh, error, check, currentK, exactchecking), Nil)
    case IfThenElse(con, then, els) =>
      (if(check) isDefined(con)(true) else Nil) :::
      Boogie.If(Tr(con), Exhale(then, em, eh, error, check, currentK, exactchecking), Exhale(els, em, eh, error, check, currentK, exactchecking))
    case And(e0,e1) =>
      Exhale(e0, em, eh, error, check, currentK, exactchecking) ::: Exhale(e1, em, eh, error, check, currentK, exactchecking)
    case holds@Holds(e) => 
      (if(check) isDefined(e)(true) :::
      bassert(nonNull(Tr(e)), error.pos, error.message + " The target of the holds predicate at " + holds.pos + " might be null.") :: Nil else Nil) :::
      bassert(0 < new Boogie.MapSelect(Heap, Tr(e), "held"), error.pos, error.message + " The current thread might not hold lock at " + holds.pos + ".") ::
      bassert(! new Boogie.MapSelect(Heap, Tr(e), "rdheld"), error.pos, error.message + " The current thread might hold the read lock at " + holds.pos + ".") ::
      bassume(IsGoodMask(Mask)) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(Heap, em))
    case Eval(h, e) =>
      val (evalHeap, evalMask, evalCredits, checks, proofOrAssume) = fromEvalState(h);
      val preGlobals = etran.FreshGlobals("eval")
      val preEtran = new ExpressionTranslator(List(Boogie.VarExpr(preGlobals(0).id), Boogie.VarExpr(preGlobals(1).id), Boogie.VarExpr(preGlobals(2).id)), currentClass);
      BLocal(preGlobals(0)) :: (VarExpr(preGlobals(0).id) := evalHeap) ::
      BLocal(preGlobals(1)) :: (VarExpr(preGlobals(1).id) := evalMask) ::
      BLocal(preGlobals(2)) :: (VarExpr(preGlobals(2).id) := evalCredits) ::
      (if(check) checks else Nil) :::
      bassume(IsGoodMask(preEtran.Mask)) ::
      bassume(wf(preEtran.Heap, preEtran.Mask)) ::
      bassert(proofOrAssume, p.pos, "Arguments for joinable might not match up.") ::
      preEtran.Exhale(List((e, error)), "eval", check, currentK, exactchecking)
    case e => (if(check) isDefined(e)(true) else Nil) ::: List(bassert(Tr(e), error.pos, error.message + " The expression at " + e.pos + " might not evaluate to true."))
  }
  
  def extractKFromPermission(expr: Permission, currentK: Expr): (Expr, List[Boogie.Stmt]) = expr match {
    case Full => (permissionFull, Nil)
    case Epsilon => (currentK, Nil)
    case Epsilons(_) => (0, Nil)
    case PredicateEpsilon(_) => (predicateK, Nil)
    case MonitorEpsilon(_) => (monitorK, Nil)
    case ChannelEpsilon(_) => (channelK, Nil)
    case MethodEpsilon => (currentK, Nil)
    case ForkEpsilon(token) =>
      val fk = etran.Heap.select(Tr(token), forkK)
      (fk, bassume(0 < fk && fk < permissionFull) /* this is always true for forkK */)
    case Star =>
      val (starKV, starK) = NewBVar("starK", tint, true);
      (starK, BLocal(starKV) :: bassume(starK > 0 /* an upper bound is provided later by DecPermission */) :: Nil)
    case Frac(p) => (percentPermission(Tr(p)), Nil)
    case IntPermTimes(lhs, rhs) => {
      val (r, rs) = extractKFromPermission(rhs, currentK)
      (lhs * r, rs)
    }
    case PermTimes(lhs, rhs) => {
      val (l, ls) = extractKFromPermission(lhs, currentK)
      val (r, rs) = extractKFromPermission(rhs, currentK)
      val (resV, res) = Boogie.NewBVar("productK", tint, true)
      (res, ls ::: rs ::: BLocal(resV) :: bassume(permissionFull * res ==@ l * r) :: Nil)
    }
    case PermPlus(lhs, rhs) => {
      val (l, ls) = extractKFromPermission(lhs, currentK)
      val (r, rs) = extractKFromPermission(rhs, currentK)
      (l + r, Nil)
    }
    case PermMinus(lhs, rhs) => {
      val (l, ls) = extractKFromPermission(lhs, currentK)
      val (r, rs) = extractKFromPermission(rhs, currentK)
      (l - r, Nil)
    }
  }
  
  def extractEpsilonsFromPermission(expr: Permission): Expr = expr match {
    case _:Write => 0
    case Epsilons(n) => Tr(n)
    case PermTimes(lhs, rhs) => 0 // multiplication cannot give epsilons
    case IntPermTimes(lhs, rhs) => lhs * extractEpsilonsFromPermission(rhs)
    case PermPlus(lhs, rhs) => {
      val l = extractEpsilonsFromPermission(lhs)
      val r = extractEpsilonsFromPermission(rhs)
      l + r
    }
    case PermMinus(lhs, rhs) => {
      val l = extractEpsilonsFromPermission(lhs)
      val r = extractEpsilonsFromPermission(rhs)
      l - r
    }
  }

  def fromEvalState(h: EvalState): (Expr, Expr, Expr, List[Stmt], Expr) = {
    h match {
      case AcquireState(obj) =>
        (AcquireHeap(Heap.select(Tr(obj), "held")),
         AcquireMask(Heap.select(Tr(obj), "held")),
         AcquireCredits(Heap.select(Tr(obj), "held")),
         isDefined(obj)(true), true)
      case ReleaseState(obj) =>
        (LastSeenHeap(Heap.select(Tr(obj), "mu"), Heap.select(Tr(obj), "held")),
         LastSeenMask(Heap.select(Tr(obj), "mu"), Heap.select(Tr(obj), "held")),
         LastSeenCredits(Heap.select(Tr(obj), "mu"), Heap.select(Tr(obj), "held")),
         isDefined(obj)(true), true)
      case CallState(token, obj, id, args) =>
        val argsSeq = CallArgs(Heap.select(Tr(token), "joinable"));

        var f: ((Expression, Int)) => Expr =
            (a: (Expression, Int)) => a match {
                case (VariableExpr("?"),_) => true: Expr
                case _ => new MapSelect(argsSeq, a._2) ==@ Tr(a._1)
              }
        var ll: List[(Expression, Int)] = null
        ll = (args zip (1 until args.length+1).toList);
        
        var i = 0;
        (CallHeap(Heap.select(Tr(token), "joinable")), 
         CallMask(Heap.select(Tr(token), "joinable")),
         CallCredits(Heap.select(Tr(token), "joinable")),
         isDefined(token)(true) :::
         isDefined(obj)(true) :::
         (args flatMap { a => isDefined(a)(true)}) :::
         bassert(CanRead(Tr(token), "joinable"), obj.pos, "Joinable field of the token might not be readable.") ::
         bassert(Heap.select(Tr(token), "joinable") !=@ 0, obj.pos, "Token might not be active."),
         (new MapSelect(argsSeq, 0) ==@ Tr(obj) ) &&
         ((ll map { 
            f
         }).foldLeft(true: Expr){ (a: Expr, b: Expr) => a && b})
        )
    }
  }

  /**********************************************************************
  *****************          PERMISSIONS                *****************
  **********************************************************************/

  def CanRead(obj: Boogie.Expr, field: Boogie.Expr): Boogie.Expr = new Boogie.FunctionApp("CanRead", Mask, obj, field)
  def CanRead(obj: Boogie.Expr, field: String): Boogie.Expr = CanRead(obj, new Boogie.VarExpr(field))
  def CanWrite(obj: Boogie.Expr, field: Boogie.Expr): Boogie.Expr = new Boogie.FunctionApp("CanWrite", Mask, obj, field)
  def CanWrite(obj: Boogie.Expr, field: String): Boogie.Expr = CanWrite(obj, new Boogie.VarExpr(field))
  def HasNoPermission(obj: Boogie.Expr, field: String) =
    (new Boogie.MapSelect(Mask, obj, field, "perm$R") ==@ Boogie.IntLiteral(0)) &&
    (new Boogie.MapSelect(Mask, obj, field, "perm$N") ==@ Boogie.IntLiteral(0))
  def SetNoPermission(obj: Boogie.Expr, field: String, mask: Boogie.Expr) =
    Boogie.Assign(new Boogie.MapSelect(mask, obj, field), Boogie.VarExpr("Permission$Zero"))
  def HasFullPermission(obj: Boogie.Expr, field: String, mask: Boogie.Expr) =
    (new Boogie.MapSelect(mask, obj, field, "perm$R") ==@ permissionFull) &&
    (new Boogie.MapSelect(mask, obj, field, "perm$N") ==@ Boogie.IntLiteral(0))
  def SetFullPermission(obj: Boogie.Expr, field: String) =
    Boogie.Assign(new Boogie.MapSelect(Mask, obj, field), Boogie.VarExpr("Permission$Full"))

  def IncPermission(obj: Boogie.Expr, field: String, howMuch: Boogie.Expr): List[Boogie.Stmt] = {
    MapUpdate3(Mask, obj, field, "perm$R", new Boogie.MapSelect(Mask, obj, field, "perm$R") + howMuch) :: Nil
  }
  def IncPermissionEpsilon(obj: Boogie.Expr, field: String, epsilons: Boogie.Expr): List[Boogie.Stmt] = {
    MapUpdate3(Mask, obj, field, "perm$N", new Boogie.MapSelect(Mask, obj, field, "perm$N") + epsilons) ::
    bassume(Boogie.FunctionApp("wf", List(Heap, Mask))) :: Nil
  }
  def DecPermission(obj: Boogie.Expr, field: String, howMuch: Boogie.Expr, mask: Boogie.Expr, error: ErrorMessage, pos: Position, exactchecking: Boolean): List[Boogie.Stmt] = {
    val fP: Boogie.Expr = new Boogie.MapSelect(mask, obj, field, "perm$R")
    val fC: Boogie.Expr = new Boogie.MapSelect(mask, obj, field, "perm$N")
    (if (exactchecking) bassert(howMuch <= fP && (howMuch ==@ fP ==> 0 <= fC), error.pos, error.message + " Insufficient fraction at " + pos + " for " + field + ".") :: Nil
    else bassert(fP > 0, error.pos, error.message + " Insufficient fraction at " + pos + " for " + field + ".") :: bassume(howMuch < fP)) :::
    MapUpdate3(mask, obj, field, "perm$R", new Boogie.MapSelect(mask, obj, field, "perm$R") - howMuch)
  }
  def DecPermissionEpsilon(obj: Boogie.Expr, field: String, epsilons: Boogie.Expr, mask: Boogie.Expr, error: ErrorMessage, pos: Position): List[Boogie.Stmt] = {
    val xyz = new Boogie.MapSelect(mask, obj, field, "perm$N")
    bassert((new Boogie.MapSelect(mask, obj, field, "perm$R") ==@ Boogie.IntLiteral(0)) ==> (epsilons <= xyz), error.pos, error.message + " Insufficient epsilons at " + pos + "  for " + field + ".") ::
    MapUpdate3(mask, obj, field, "perm$N", new Boogie.MapSelect(mask, obj, field, "perm$N") - epsilons) ::
    bassume(Boogie.FunctionApp("wf", List(Heap, Mask))) :: Nil
  }
  def DecPermissionBoth(obj: Boogie.Expr, field: String, howMuch: Boogie.Expr, epsilons: Boogie.Expr, mask: Boogie.Expr, error: ErrorMessage, pos: Position, exactchecking: Boolean): List[Boogie.Stmt] = {
    val fP: Boogie.Expr = new Boogie.MapSelect(mask, obj, field, "perm$R")
    val fC: Boogie.Expr = new Boogie.MapSelect(mask, obj, field, "perm$N")

    (if (exactchecking) bassert(howMuch <= fP && (howMuch ==@ fP ==> epsilons <= fC), error.pos, error.message + " Insufficient permission at " + pos + " for " + field + ".") :: Nil
    else bassert(fP > 0, error.pos, error.message + " Insufficient permission at " + pos + " for " + field + ".") :: bassume(howMuch < fP)) :::
    MapUpdate3(mask, obj, field, "perm$N", fC - epsilons) ::
    bassume(Boogie.FunctionApp("wf", List(Heap, Mask))) ::
    MapUpdate3(mask, obj, field, "perm$R", fP - howMuch) :: Nil
  }

  def MapUpdate3(m: Boogie.Expr, arg0: Boogie.Expr, arg1: String, arg2: String, rhs: Boogie.Expr) = {
    // m[a,b,c] := rhs
    // m[a,b][c] := rhs
    // m[a,b] := map[a,b][c := rhs]
    val m01 = new Boogie.MapSelect(m, arg0, arg1)
    Boogie.Assign(m01, Boogie.MapStore(m01, arg2, rhs))
  }

  def DecPerm(m: Expr, e: Expr, f: Expr, i: Expr) = FunctionApp("DecPerm", List(m, e, f, i))
  def DecEpsilons(m: Expr, e: Expr, f: Expr, i: Expr) = FunctionApp("DecEpsilons", List(m, e, f, i))
  def IncPerm(m: Expr, e: Expr, f: Expr, i: Expr) = FunctionApp("IncPerm", List(m, e, f, i))
  def IncEpsilons(m: Expr, e: Expr, f: Expr, i: Expr) = FunctionApp("IncEpsilons", List(m, e, f, i))


  def MaxLockIsBelowX(x: Boogie.Expr) = {  // waitlevel << x
    val (oV, o) = Boogie.NewBVar("o", tref, true)
    new Boogie.Forall(oV,
                      (contributesToWaitLevel(o, Heap, Credits)) ==>
                      new Boogie.FunctionApp("MuBelow", new Boogie.MapSelect(Heap, o, "mu"), x))
  }
  def MaxLockIsAboveX(x: Boogie.Expr) = {  // x << waitlevel
    val (oV, o) = Boogie.NewBVar("o", tref, true)
    new Boogie.Exists(oV,
                      (contributesToWaitLevel(o, Heap, Credits)) &&
                      new Boogie.FunctionApp("MuBelow", x, new Boogie.MapSelect(Heap, o, "mu")))
  }
  def IsHighestLock(x: Boogie.Expr) = {
    // (forall r :: r.held ==> r.mu << x || r.mu == x)
    val (rV, r) = Boogie.NewBVar("r", tref, true)
    new Boogie.Forall(rV,
                      contributesToWaitLevel(r, Heap, Credits) ==>
                        (new Boogie.FunctionApp("MuBelow", new MapSelect(Heap, r, "mu"), x) ||
                        (new Boogie.MapSelect(Heap, r, "mu") ==@ x)))
  }
  def MaxLockPreserved = {  // old(waitlevel) == waitlevel
    // I don't know what the best encoding of this conding is, so I'll try a disjunction.
    // Disjunct b0 is easier to prove, but it is stronger than b1.

    // (forall r: ref ::
    //     old(Heap)[r,held] == Heap[r,held] &&
    //     (Heap[r,held] ==> old(Heap)[r,mu] == Heap[r,mu]))
    val (rV, r) = Boogie.NewBVar("r", tref, true)
    val b0 = new Boogie.Forall(rV,
                      ((0 < new Boogie.MapSelect(oldEtran.Heap, r, "held")) ==@
                       (0 < new Boogie.MapSelect(Heap, r, "held"))) &&
                      ((0 < new Boogie.MapSelect(Heap, r, "held")) ==>
                        (new Boogie.MapSelect(oldEtran.Heap, r, "mu") ==@
                         new Boogie.MapSelect(Heap, r, "mu"))))

    // (forall o, p ::
    //     old(o.held) && (forall r :: old(r.held) ==> old(r.mu) << old(o.mu) || old(r.mu)==old(o.mu)) &&
    //         p.held  && (forall r ::     r.held  ==>     r.mu  <<     p.mu  ||     r.mu ==    p.mu )
    //     ==>
    //     old(o.mu) == p.mu)
    val (oV, o) = Boogie.NewBVar("o", tref, true)
    val (pV, p) = Boogie.NewBVar("p", tref, true)
    val b1 = Boogie.Forall(Nil, List(oV,pV), Nil,
                  ((0 < new Boogie.MapSelect(oldEtran.Heap, o, "held")) &&
                   oldEtran.IsHighestLock(new Boogie.MapSelect(oldEtran.Heap, o, "mu")) &&
                   (0 < new Boogie.MapSelect(Heap, p, "held")) &&
                   IsHighestLock(new Boogie.MapSelect(Heap, p, "mu")))
                  ==>
                  (new Boogie.MapSelect(oldEtran.Heap, o, "mu") ==@ new Boogie.MapSelect(Heap, p, "mu")))
    b0 || b1
  }
  def TemporalMaxLockComparison(e0: ExpressionTranslator, e1: ExpressionTranslator) = {  // e0(waitlevel) << e1(waitlevel)
    // (exists o ::
    //     e1(o.held) &&
    //     (forall r :: e0(r.held) ==> e0(r.mu) << e1(o.mu)))
    val (oV, o) = Boogie.NewBVar("o", tref, true)
    new Boogie.Exists(oV,
                      (0 < new Boogie.MapSelect(e1.Heap, o, "held")) &&
                      e0.MaxLockIsBelowX(new Boogie.MapSelect(e1.Heap, o, "mu")))
  }
}

  // implicit (uses etran)

  implicit def expression2Expr(e: Expression) = etran.Tr(e);

  // prelude (uses etran)
  def isHeld(e: Expr): Expr = (0 < etran.Heap.select(e, "held"))
  def isRdHeld(e: Expr): Expr = etran.Heap.select(e, "rdheld")
  def isShared(e: Expr): Expr = etran.Heap.select(e, "mu") !=@ bLockBottom

object TranslationHelper {
  // implicit conversions

  implicit def string2VarExpr(s: String) = VarExpr(s);
  implicit def field2Expr(f: Field) = VarExpr(f.FullName);
  implicit def bool2Bool(b: Boolean): Boogie.BoolLiteral = Boogie.BoolLiteral(b)
  implicit def int2Int(n: Int): Boogie.IntLiteral = Boogie.IntLiteral(n)
  implicit def lift(s: Boogie.Stmt): List[Boogie.Stmt] = List(s)
  implicit def type2BType(cl: Class): BType = {
    if(cl.IsRef) {
      tref
    } else if(cl.IsBool) {
      tbool
    } else if(cl.IsMu) {
      tmu
    } else if(cl.IsInt) {
      tint
    } else if(cl.IsSeq) {
      tseq(type2BType(cl.asInstanceOf[SeqClass].parameter))
    } else {
      assert(false, "unexpected type: " + cl.FullName); null
    }
  }
  implicit def decl2DeclList(decl: Decl): List[Decl] = List(decl)
  implicit def function2RichFunction(f: Function) = RichFunction(f);

  case class RichFunction(f: Function) {
    def apply(args: List[Expr]) = {
      FunctionApp(functionName(f), args)
    }
  }
  
  // prelude definitions

  def todoiparam: Expr = IntLiteral(-1); // This value is used as parameter at places where Chalice has not been updated to the new permission model.
  def todobparam: Boolean = true; // This value is used as parameter at places where Chalice has not been updated to the new permission model.
  
  def ModuleType = NamedType("ModuleName");
  def ModuleName(cl: Class) = "module#" + cl.module.id;
  def TypeName = NamedType("TypeName");
  def FieldType(tp: BType) = IndexedType("Field", tp);
  def bassert(e: Expr, pos: Position, msg: String) = new Boogie.Assert(e, pos, msg)
  def bassume(e: Expr) = Boogie.Assume(e)
  def BLocal(id: String, tp: BType) = new Boogie.LocalVar(id, tp)
  def BLocal(x: Boogie.BVar) = Boogie.LocalVar(x)
  def tArgSeq = NamedType("ArgSeq");
  def tref = NamedType("ref");
  def tbool = NamedType("bool");
  def tmu  = NamedType("Mu");
  def tint = NamedType("int");
  def tseq(arg: BType) = IndexedType("Seq", arg)
  def theap = NamedType("HeapType");
  def tmask = NamedType("MaskType");
  def tcredits = NamedType("CreditsType");
  def tperm = NamedType("PermissionComponent");
  def ZeroMask = VarExpr("ZeroMask");
  def ZeroCredits = VarExpr("ZeroCredits");
  def HeapName = "Heap";
  def MaskName = "Mask";
  def CreditsName = "Credits";
  def GlobalNames = List(HeapName, MaskName, CreditsName);
  def CanAssumeFunctionDefs = VarExpr("CanAssumeFunctionDefs");
  def permissionFull = percentPermission(100);
  def permissionOnePercent = percentPermission(1);
  def percentPermission(e: Expr) = {
    Chalice.percentageSupport match {
      case 0 | 1 => e*VarExpr("Permission$denominator")
      case 2 | 3 => FunctionApp("Fractions", List(e))
    }
  }
  def forkK = "forkK";
  def channelK = "channelK";
  def monitorK = "monitorK";
  def predicateK = "predicateK";
  def CurrentModule = VarExpr("CurrentModule");
  def IsGoodState(e: Expr) = FunctionApp("IsGoodState", List(e));
  def dtype(e: Expr) = FunctionApp("dtype", List(e))
  def functionName(f: Function) = "#" + f.FullName;
  def className(cl: Class) = Boogie.VarExpr(cl.id + "#t")
  def bnull = Boogie.Null();
  def bLockBottom = VarExpr("$LockBottom")
  def nonNull(e: Expr): Expr = e !=@ bnull
  def LastSeenHeap(sharedBit: Expr, heldBit: Expr) = FunctionApp("LastSeen$Heap", List(sharedBit, heldBit))
  def LastSeenMask(sharedBit: Expr, heldBit: Expr) = FunctionApp("LastSeen$Mask", List(sharedBit, heldBit))
  def LastSeenCredits(sharedBit: Expr, heldBit: Expr) = FunctionApp("LastSeen$Credits", List(sharedBit, heldBit))
  def AcquireHeap(heldBit: Expr) = FunctionApp("Acquire$Heap", List(heldBit))
  def AcquireMask(heldBit: Expr) = FunctionApp("Acquire$Mask", List(heldBit))
  def AcquireCredits(heldBit: Expr) = FunctionApp("Acquire$Credits", List(heldBit))
  def CallHeap(joinableBit: Expr) = FunctionApp("Call$Heap", List(joinableBit))
  def CallMask(joinableBit: Expr) = FunctionApp("Call$Mask", List(joinableBit))
  def CallCredits(joinableBit: Expr) = FunctionApp("Call$Credits", List(joinableBit))
  def CallArgs(joinableBit: Expr) = FunctionApp("Call$Args", List(joinableBit))
  def submask(m0: Expr, m1: Expr) = FunctionApp("submask", List(m0, m1))

  def wf(h: Expr, m: Expr) = FunctionApp("wf", List(h, m));
  def IsGoodMask(m: Expr) = FunctionApp("IsGoodMask", List(m))
  def IsGoodInhaleState(a: Expr, b: Expr, c: Expr) = FunctionApp("IsGoodInhaleState", List(a, b, c))
  def contributesToWaitLevel(e: Expr, h: Expr, c: Expr) =
    (0 < h.select(e, "held")) || h.select(e, "rdheld")  || (new Boogie.MapSelect(c, e) < 0)
  def NonEmptyMask(m: Expr) = ! FunctionApp("EmptyMask", List(m))
  def NonPredicateField(f: String) = FunctionApp("NonPredicateField", List(VarExpr(f)))
  def PredicateField(f: String) = FunctionApp("PredicateField", List(VarExpr(f)))
  def cast(a: Expr, b: Expr) = FunctionApp("cast", List(a, b))

  // sequences

  def createEmptySeq = FunctionApp("Seq#Empty", List())
  def createSingletonSeq(e: Expr) = FunctionApp("Seq#Singleton", List(e)) 
  def createAppendSeq(a: Expr, b: Expr) = FunctionApp("Seq#Append", List(a, b)) 
  def createRange(min: Expr, max: Expr) = FunctionApp("Seq#Range", List(min, max))
  def SeqLength(s: Expr) = FunctionApp("Seq#Length", List(s))
  def SeqContains(s: Expr, elt: Expr) = FunctionApp("Seq#Contains", List(s, elt))
  def SeqIndex(s: Expr, idx: Expr) = FunctionApp("Seq#Index", List(s, idx))

  def Variable2BVar(v: Variable) = new Boogie.BVar(v.UniqueName, v.t.typ)
  def Variable2BVarWhere(v: Variable) = NewBVarWhere(v.UniqueName, v.t)
  def NewBVarWhere(id: String, tp: Type) = {
    new Boogie.BVar(id, tp.typ){
      override val where = TypeInformation(new Boogie.VarExpr(id), tp.typ) }
  }

  // scale an expression (such as the definition of a predicate) by a permission
  def scaleExpressionByPermission(expr: Expression, perm1: Permission, pos: Position): Expression = {
    val result = expr match {
      case pred@MemberAccess(o, p) if pred.isPredicate => Access(pred, perm1)
      case Access(e, perm2) => Access(e, multiplyPermission(perm1, perm2, pos))
      case AccessSeq(e, f, perm2) => AccessSeq(e, f, multiplyPermission(perm1, perm2, pos))
      case And(lhs, rhs) => And(scaleExpressionByPermission(lhs, perm1, pos), scaleExpressionByPermission(rhs, perm1, pos))
      case Implies(lhs, rhs) => Implies(lhs, scaleExpressionByPermission(rhs, perm1, pos))
      case _ if ! expr.isInstanceOf[PermissionExpr] => expr
      case _ => throw new InternalErrorException("Unexpected expression, unable to scale.");
    }
    result.pos = expr.pos;
    result
  }
  
  // multiply two permissions
  def multiplyPermission(perm1: Permission, perm2: Permission, pos: Position): Permission = {
    val result = (perm1,perm2) match {
      case (Full,p2) => p2
      case (p1,Full) => p1
      case (Epsilons(_),_) => throw new NotSupportedException(pos + ": Scaling epsilon permissions with non-full permissions is not possible.")
      case (_,Epsilons(_)) => throw new NotSupportedException(pos + ": Scaling epsilon permissions with non-full permissions is not possible.")
      case (p1,p2) => PermTimes(p1,p2)
    }
    result
  }
  
  // TODO: this method is used by the method tranform extension, which has not yet been updated to the new permission model
  def FractionOf(expr: Expression, fraction: Expression) : Expression = {
    throw new NotSupportedException("Not supported")
  }

  def TypeInformation(e: Boogie.Expr, cl: Class): Boogie.Expr = {
    if (cl.IsRef) {
      (e ==@ Boogie.Null()) || (dtype(e) ==@ className(cl))
    } else if (cl.IsSeq && cl.parameters(0).IsRef) {
      val (v,ve) = Boogie.NewBVar("$i", tint, true);
      (0 <= ve && ve < SeqLength(e)
        ==> TypeInformation(SeqIndex(e,ve), cl.parameters(0))).forall(v);
    } else {
      true
    }
  }

  def Version(expr: Expression, etran: ExpressionTranslator): Boogie.Expr = {
    val nostate = Boogie.VarExpr("nostate");
    desugar(expr) match {
      case pred@MemberAccess(e, p) if pred.isPredicate =>
        Version(Access(pred, Full), etran)
      case acc@Access(e, _) =>
        val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;
        new Boogie.MapSelect(etran.Heap, etran.Tr(e.e), memberName)
      case Implies(e0,e1) =>
        Boogie.Ite(etran.Tr(e0), Version(e1, etran), nostate)
      case And(e0,e1) =>
        val l = Version(e0, etran);
        val r = Version(e1, etran);
        if (l == nostate) r
        else if (r == nostate) l
        else Boogie.FunctionApp("combine", List(l, r))
      case IfThenElse(con, then, els) =>
        Boogie.Ite(etran.Tr(con), Version(then, etran), Version(els, etran))
      case _: PermissionExpr => throw new InternalErrorException("unexpected permission expression")
      case e =>
        e visit {_ match { case _ : PermissionExpr => throw new InternalErrorException("unexpected permission expression"); case _ =>}}
        nostate
    }
  }

  // conservative for Implies and IfThenElse
  // returns an expression of Boogie type bool
  def Version(expr: Expression, etran1: ExpressionTranslator, etran2: ExpressionTranslator): Boogie.Expr = {
    desugar(expr) match {
      case pred@MemberAccess(e, p) if pred.isPredicate =>
        Version(Access(pred, Full), etran1, etran2)
      case Access(e, _) =>
        val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;
        etran1.Heap.select(etran1.Tr(e.e), memberName) ==@ etran2.Heap.select(etran2.Tr(e.e), memberName)
      case AccessSeq(s, Some(e), _) =>
        val name = if(e.isPredicate) e.predicate.FullName else e.f.FullName;
        val (iV, i) = Boogie.NewBVar("i", tint, true)
        (SeqLength(etran1.Tr(s)) ==@ SeqLength(etran2.Tr(s))) &&
        ((((0 <= i) && (i < SeqLength(etran1.Tr(s)))) ==>
          (etran1.Heap.select(SeqIndex(etran1.Tr(s), i), name) ==@ etran2.Heap.select(SeqIndex(etran2.Tr(s), i), name))).forall(iV))
      case Implies(e0,e1) =>
        Boogie.Ite(etran1.Tr(e0) || etran2.Tr(e0), Version(e1, etran1, etran2), true)
      case And(e0,e1) =>
        Version(e0, etran1, etran2) && Version(e1, etran1, etran2)
      case IfThenElse(con, then, els) =>
        Version(then, etran1, etran2) && Version(els, etran1, etran2)
      case _: PermissionExpr => throw new InternalErrorException("unexpected permission expression")
      case e =>
        e visit {_ match { case _ : PermissionExpr => throw new InternalErrorException("unexpected permission expression"); case _ =>}}
        Boogie.BoolLiteral(true)
    }
  }
  
  def Preconditions(spec: List[Specification]): List[Expression] = {
    val result = spec flatMap ( s => s match {
      case Precondition(e) => List(e)
      case _ => Nil });
    if(Chalice.autoMagic) {
      automagic(result.foldLeft(BoolLiteral(true): Expression)({ (a, b) => And(a, b)}), Nil)._1 ::: result
    } else {
      result
    }
  }
  def Postconditions(spec: List[Specification]): List[Expression] = {
    val result = spec flatMap ( s => s match {
      case Postcondition(e) => List(e)
      case _ => Nil })
    if(Chalice.autoMagic) {
      automagic(result.foldLeft(BoolLiteral(true): Expression)({ (a, b) => And(a, b)}), Nil)._1 ::: result
    } else {
      result
    }
  }

  def automagic(expr: Expression, handled: List[Expression]): (/*assumptions*/ List[Expression], /*newHandled*/List[Expression]) = {
    def isHandled(e: Expression) = handled exists { ex => ex.equals(e) }
    expr match {
      case ma@MemberAccess(obj, f) =>
        val (assumptions, handled1) = automagic(obj, handled);
        if(isHandled(ma)) {
          (assumptions, handled1)
        } else {
          if(ma.isPredicate){
            // assumption: obj!=null
            (assumptions ::: Neq(obj, NullLiteral()) :: Nil, handled1 ::: List(ma))
          } else {
            // assumption: obj!=null && acc(obj, f)
            (assumptions ::: Neq(obj, NullLiteral()) :: Access(ma, Full) :: Nil, handled1 ::: List(ma))
          }
        }
      case Access(ma@MemberAccess(obj, f), perm) =>
        val (assumptions, handled1) = automagic(obj, handled ::: List(ma));
        perm match {
          case Full | Epsilon | Star | MethodEpsilon => (assumptions, handled1);
          case Frac(fraction) => val result = automagic(fraction, handled1); (assumptions ::: result._1, result._2)
          case Epsilons(epsilon) => val result = automagic(epsilon, handled1); (assumptions ::: result._1, result._2)
          case ChannelEpsilon(None) | PredicateEpsilon(None) | MonitorEpsilon(None) => (assumptions, handled1)
          case ChannelEpsilon(Some(e)) => val result = automagic(e, handled1); (assumptions ::: result._1, result._2)
          case PredicateEpsilon(Some(e)) => val result = automagic(e, handled1); (assumptions ::: result._1, result._2)
          case MonitorEpsilon(Some(e)) => val result = automagic(e, handled1); (assumptions ::: result._1, result._2)
          case ForkEpsilon(e) => val result = automagic(e, handled1); (assumptions ::: result._1, result._2)
          case IntPermTimes(e0, e1) =>
            val (assumptions1, handled2) = automagic(e0, handled1);
            val result = automagic(e1, handled2); 
            (assumptions ::: assumptions1 ::: result._1, result._2)
          case PermTimes(e0, e1) =>
            val (assumptions1, handled2) = automagic(e0, handled1);
            val result = automagic(e1, handled2); 
            (assumptions ::: assumptions1 ::: result._1, result._2)
          case PermPlus(e0, e1) =>
            val (assumptions1, handled2) = automagic(e0, handled1);
            val result = automagic(e1, handled2); 
            (assumptions ::: assumptions1 ::: result._1, result._2)
          case PermMinus(e0, e1) =>
            val (assumptions1, handled2) = automagic(e0, handled1);
            val result = automagic(e1, handled2); 
            (assumptions ::: assumptions1 ::: result._1, result._2)
        }
      case AccessAll(obj, perm) => 
        automagic(obj, handled)
      case Holds(e) =>
        automagic(e, handled)
      case RdHolds(e) =>
        automagic(e, handled)
      case a: Assigned =>
       (Nil, handled)
      case Old(e) =>
       (Nil, handled) // ??
      case IfThenElse(con, then, els) =>
        val (assumptions, handled1) = automagic(con, handled);
        val (assumptions2, handled2) = automagic(then, handled1);
        val result = automagic(els, handled2); 
        (assumptions ::: assumptions2 ::: result._1, result._2)
      case Not(e) =>
        automagic(e, handled)
      case func@FunctionApplication(obj, id, args) =>
        var assumption = Nil: List[Expression];
        var newHandled = handled;
        for(a <- obj :: args) {
          val (ass, hd) = automagic(a, handled);
          assumption = assumption ::: ass;
          newHandled = hd;
        }
        (assumption, newHandled)
      case uf@Unfolding(_, e) =>
        (Nil, handled)
      case bin: BinaryExpr =>
        val (assumptions, handled1) = automagic(bin.E0, handled);
        val result = automagic(bin.E1, handled1); 
        (assumptions ::: result._1, result._2)
      case EmptySeq(t) =>
        (Nil, handled)
      case ExplicitSeq(es) =>
        var assumption = Nil: List[Expression];
        var newHandled = handled;
        for(a <- es) {
          val (ass, hd) = automagic(a, handled);
          assumption = assumption ::: ass;
          newHandled = hd;
        }
        (assumption, newHandled)
      case Range(min, max) =>
        val (assumptions, handled1) = automagic(min, handled);
        val result = automagic(max, handled1); 
        (assumptions ::: result._1, result._2)
      case Length(e) =>
        automagic(e, handled)
      case Eval(h, e) =>
        (Nil, handled)
      case _ => (Nil, handled)
    }
  }

  def DefinitionOf(predicate: Predicate): Expression = {
    if(Chalice.autoMagic) {
      And(automagic(predicate.definition, Nil)._1.foldLeft(BoolLiteral(true): Expression)({ (a, b) => And(a, b)}), predicate.definition)
    } else {
      predicate.definition
    }
  }

  def LockChanges(spec: List[Specification]): List[Expression] = {
    spec flatMap ( s => s match {
      case LockChange(ee) => ee
      case _ => Nil })
  }

  def SubstRd(e: Expression): Expression = e match {
    case Access(e, _:Permission) =>
      //val r = Access(e,MonitorEpsilon(None)); r.pos = e.pos; r.typ = BoolClass; r
      val r = Access(e,Epsilons(IntLiteral(1))); r.pos = e.pos; r.typ = BoolClass; r
    case Implies(e0,e1) =>
      val r = Implies(e0, SubstRd(e1)); r.pos = e.pos; r.typ = BoolClass; r
    case And(e0,e1) =>
      val r = And(SubstRd(e0), SubstRd(e1)); r.pos = e.pos; r.typ = BoolClass; r
    case _ => e
  }

  def UnfoldPredicatesWithReceiverThis(expr: Expression): Expression = {
    val func = (e:Expression) =>
      e match {
        case pred@MemberAccess(o, f) if pred.isPredicate && o.isInstanceOf[ThisExpr] =>
          Some(SubstThis(DefinitionOf(pred.predicate), o))
        case Access(pred@MemberAccess(o, f), p) if pred.isPredicate && o.isInstanceOf[ThisExpr] =>
          val definition = scaleExpressionByPermission(SubstThis(DefinitionOf(pred.predicate), o), p, e.pos)
          Some(definition)
        case func@FunctionApplication(obj: ThisExpr, name, args) if 2<=Chalice.defaults && func.f.definition.isDefined =>
          Some(SubstVars(func.f.definition.get, obj, func.f.ins, args))
        case _ => None
      }
    AST.transform(expr, func)
  }

  // needed to do a _simultaneous_ substitution!
  def SubstVars(expr: Expression, x:Expression, vs:List[Variable], es:List[Expression]): Expression =
    SubstVars(expr, Some(x), Map() ++ (vs zip es));
  def SubstVars(expr: Expression, vs:List[Variable], es:List[Expression]): Expression =
    SubstVars(expr, None, Map() ++ (vs zip es));
  def SubstVars(expr: Expression, t: Option[Expression], vs: Map[Variable, Expression]): Expression = expr.transform {
    case _: ThisExpr if t.isDefined => t
    case e: VariableExpr =>
      if (vs.contains(e.v)) Some(vs(e.v)) else None;
    case q: Quantification =>
      q.variables foreach { (v) => if (vs.contains(v)) throw new InternalErrorException("cannot substitute a variable bound in the quantifier")}
      None;
    case _ => None;
  }

  def SubstThis(expr: Expression, x: Expression): Expression = expr.transform {
    case _: ThisExpr => Some(x)
    case _ => None
  }

  def SubstResult(expr: Expression, x: Expression): Expression = expr.transform {
    case _: Result => Some(x)
    case _ => None
  }

  // De-sugar expression (idempotent)
  // * unroll wildcard pattern (for objects) in permission expression
  // * convert sequence quantification into type quantification
  // * perform simple permission expression optimizations (e.g. Frac(1)+Frac(1) = Frac(1+1) or Frac(100) = Full)
  // * simplify quantification over empty sequences
  def desugar(expr: Expression): Expression = expr transform {
    _ match {
      case Frac(IntLiteral(100)) => Some(Full)
      case PermTimes(Full, r) => Some(r)
      case PermTimes(l, Full) => Some(l)
      case PermPlus(lhs, rhs) =>
        val ll = desugar(lhs)
        val rr = desugar(rhs)
        (ll, rr) match {
          case (Frac(l), Frac(r)) => Some(Frac(Plus(l,r)))
          case _ => Some(PermPlus(ll.asInstanceOf[Permission], rr.asInstanceOf[Permission]))
        }
      case PermMinus(lhs, rhs) =>
        val ll = desugar(lhs)
        val rr = desugar(rhs)
        (ll, rr) match {
          case (Frac(l), Frac(r)) => Some(Frac(Minus(l,r)))
          case _ => Some(PermMinus(ll.asInstanceOf[Permission], rr.asInstanceOf[Permission]))
        }
      case PermTimes(lhs, rhs) =>
        val ll = desugar(lhs)
        val rr = desugar(rhs)
        (ll, rr) match {
          case (Frac(l), Frac(r)) => Some(Frac(Times(l,r)))
          case _ => Some(PermTimes(ll.asInstanceOf[Permission], rr.asInstanceOf[Permission]))
        }
      case AccessAll(obj, perm) =>
        Some(obj.typ.Fields.map({f =>
          val ma = MemberAccess(desugar(obj), f.id);
          ma.f = f; ma.pos = expr.pos; ma.typ = f.typ.typ;
          val acc = Access(ma, perm);
          acc.pos = expr.pos; acc.typ = acc.typ; acc
        }).foldLeft(BoolLiteral(true): Expression){(e1, e2) =>
          val and = And(e1, e2);
          and.pos = expr.pos; and.typ = BoolClass; and
        })
      case AccessSeq(s, None, perm) =>
        Some(s.typ.parameters(0).Fields.map({(f) =>
          val ma = MemberAccess(At(desugar(s), IntLiteral(0)), f.id);
          ma.f = f; ma.pos = expr.pos; ma.typ = f.typ.typ;
          val acc = AccessSeq(s, Some(ma), perm);
          acc.pos = expr.pos; acc.typ = acc.typ; acc
        }).foldLeft(BoolLiteral(true): Expression){(e1, e2) =>
          val and = And(e1, e2);
          and.pos = expr.pos; and.typ = BoolClass; and
        })
      case qe @ SeqQuantification(q, is, Range(min, max), e) =>
        val dmin = desugar(min);
        val dmax = desugar(max);
        val dis = qe.variables;
        val disx = dis map {v => new VariableExpr(v)};
        val de = desugar(e);

        val assumption = disx map {x =>
          And(AtMost(dmin, x), Less(x, dmax))
        } reduceLeft {(e0, e1) =>
          And(e0, e1)
        };
        assumption transform {e => e.pos = expr.pos; None};
        val body = q match {
          case Forall => Implies(assumption, de);
          case Exists => And(assumption, de);
        }
        body.pos = expr.pos;
        val result = TypeQuantification(q, is, new Type(IntClass), body, (dmin,dmax));
        result.variables = dis;
        Some(result);
      case qe @ SeqQuantification(Forall, is, ExplicitSeq(List()), e) => Some(BoolLiteral(true))
      case qe @ SeqQuantification(Exists, is, ExplicitSeq(List()), e) => Some(BoolLiteral(false))
      case qe @ SeqQuantification(Forall, is, EmptySeq(_), e) => Some(BoolLiteral(true))
      case qe @ SeqQuantification(Exists, is, EmptySeq(_), e) => Some(BoolLiteral(false))
      case qe @ SeqQuantification(q, is, seq, e) =>
        val dseq = desugar(seq);
        val min = IntLiteral(0);
        val max = Length(dseq);
        val dis = qe.variables map {v => new Variable(v.UniqueName, new Type(IntClass))};
        val disx = dis map {v => new VariableExpr(v)};
        val de = SubstVars(desugar(e), qe.variables, disx map {x => At(dseq, x)});

        val assumption = disx map {x =>
          And(AtMost(min, x), Less(x, max))
        } reduceLeft {(e0, e1) =>
          And(e0, e1)
        };
        assumption transform {e => e.pos = expr.pos; None};
        val body = q match {
          case Forall => Implies(assumption, de);
          case Exists => And(assumption, de);
        }
        body.pos = expr.pos;
        val result = new TypeQuantification(q, is, new Type(IntClass), body);
        result.variables = dis;
        Some(result);
      case _ => None;
    }
  }

  // tags statements to be preserved
  val keepTag = Boogie.Tag("keep")
  
  // Assume the only composite statement in Boogie is If
  def tag(l: List[Stmt], t: Boogie.Tag):List[Stmt] =
    for (s <- l) yield {
      s.tags = t :: s.tags;
      s match {
        case Boogie.If(_, thn, els) => tag(thn, t); tag(els, t);
        case _ => 
      }
      s
    }
  // Assume the only composite statement in Boogie is If
  def assert2assume(l: List[Stmt]):List[Stmt] =
    if (Chalice.noFreeAssume) l else
      l flatMap {
        case Boogie.If(guard, thn, els) => Boogie.If(guard, assert2assume(thn), assert2assume(els))
        case ba @ Boogie.Assert(e) =>
          if (ba.tags contains keepTag) ba else Comment(" assert " + ba.pos + ": " + ba.message) :: Boogie.Assume(e)
        case s => s
      }
}

}
