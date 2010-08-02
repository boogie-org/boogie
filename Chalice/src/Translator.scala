//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

import Boogie.Proc, Boogie.NamedType, Boogie.NewBVar, Boogie.Havoc, Boogie.Stmt, Boogie.Const,
       Boogie.Decl, Boogie.Expr, Boogie.FunctionApp, Boogie.Axiom, Boogie.BVar, Boogie.BType,
       Boogie.VarExpr, Boogie.IndexedType, Boogie.Comment, Boogie.MapUpdate, Boogie.MapSelect,
       Boogie.If, Boogie.Lambda, Boogie.Trigger;

case class ErrorMessage(pos: Position, message: String)

object TranslationOptions {
  // note: the initial values should match those Chalice.scala

  var defaults = 0: Int;
  var autoFold = false: Boolean;
  var checkLeaks = false: Boolean;
  var autoMagic = false: Boolean;
  var skipDeadlockChecks = false: Boolean;
  var skipTermination = false: Boolean;
}

class Translator {
  import TranslationHelper._;
  import TranslationOptions._;
  var currentClass = null: Class;
  var currentMethod = null: Method;
  var modules = Nil: List[String]
  var etran = new ExpressionTranslator(null);

  def translateProgram(decls: List[TopLevelDecl]): List[Decl] = {
    decls flatMap {
      case cl: Class => translateClass(cl)
      case ch: Channel => translateClass(ChannelClass(ch)) /* TODO: admissibility check of where clause */
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
    declarations = declarations ::: translateMonitorInvariant(cl.Invariants, cl.pos);
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
    }
  }

  def translateMonitorInvariant(invs: List[MonitorInvariant], pos: Position): List[Decl] = {
    val (h0V, h0) = NewBVar("h0", theap, true); val (m0V, m0) = NewBVar("m0", tmask, true);
    val (c0V, c0) = NewBVar("c0", tcredits, true);
    val (h1V, h1) = NewBVar("h1", theap, true); val (m1V, m1) = NewBVar("m1", tmask, true);
    val (c1V, c1) = NewBVar("c1", tcredits, true);
    val (lkV, lk) = NewBVar("lk", tref, true);
    val oldTranslator = new ExpressionTranslator(List(h1, m1, c1), List(h0, m0, c0), currentClass);
    Proc(currentClass.id + "$monitorinvariant$checkDefinedness",
      List(NewBVarWhere("this", new Type(currentClass))),
      Nil,
      GlobalNames,
      DefaultPrecondition(),
        BLocal(h0V) :: BLocal(m0V) :: BLocal(c0V) :: BLocal(h1V) :: BLocal(m1V) :: BLocal(c1V) :: BLocal(lkV) ::
        bassume(wf(h0, m0)) :: bassume(wf(h1, m1)) ::
        (oldTranslator.Mask := ZeroMask) :: (oldTranslator.Credits := ZeroCredits) ::
        oldTranslator.Inhale(invs map { mi => mi.e}, "monitor invariant", false) :::
        (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
        Havoc(etran.Heap) ::
        // check that invariant is well-defined
        etran.WhereOldIs(h1, m1, c1).Inhale(invs map { mi => mi.e}, "monitor invariant", true) :::
        (if (!checkLeaks || invs.length == 0) Nil else
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
        etran.UseCurrentAsOld().Exhale(invs map {mi => (mi.e, ErrorMessage(mi.pos, "Monitor invariant might not be reflexive."))}, "invariant reflexive?", false) :::
        bassert(DebtCheck(), pos, "Monitor invariant is not allowed to contain debt.")
    )
  }

  def translateField(f: Field): List[Decl] = {
    Const(f.FullName, true, FieldType(f.typ.typ)) ::
    Axiom(NonPredicateField(f.FullName))
    // TODO: add typeinformation as an axiom
  }

  def translateFunction(f: Function): List[Decl] = {
    val myresult = BVar("result", f.out.typ);
    etran.checkTermination = !skipTermination;
    val checkBody = isDefined(f.definition);
    etran.checkTermination = false;
    // Boogie function that represents the Chalice function
    Boogie.Function(functionName(f), BVar("heap", theap) :: BVar("mask", tmask) :: BVar("this", tref) :: (f.ins map Variable2BVar), BVar("$myresult", f.out.typ)) ::
    // check definedness of the function's precondition and body
    Proc(f.FullName + "$checkDefinedness", 
      NewBVarWhere("this", new Type(currentClass)) :: (f.ins map {i => Variable2BVarWhere(i)}),
      Nil,
      GlobalNames,
      DefaultPrecondition(),
      DefinePreInitialState :::
      // check definedness of the precondition
      InhaleWithChecking(Preconditions(f.spec) map { p => (if(0<defaults) UnfoldPredicatesWithReceiverThis(p) else p)}, "precondition") :::
      bassume(CurrentModule ==@ VarExpr(ModuleName(currentClass))) :: // verify the body assuming that you are in the module
      // check definedness of function body
      checkBody :::
      BLocal(myresult) ::
      (Boogie.VarExpr("result") := etran.Tr(f.definition)) ::
      // check that postcondition holds
      ExhaleWithChecking(Postconditions(f.spec) map { post => ((if(0<defaults) UnfoldPredicatesWithReceiverThis(post) else post),
              ErrorMessage(f.pos, "Postcondition at " + post.pos + " might not hold."))}, "function postcondition")) ::
    // definition axiom
    definitionAxiom(f) :::
    // framing axiom (+ frame function)
    framingAxiom(f) :::
    // postcondition axiom(s)
    postconditionAxiom(f)
  }

  def definitionAxiom(f: Function): List[Decl] = {
    val inArgs = (f.ins map {i => Boogie.VarExpr(i.UniqueName)});
    val frameFunctionName = "##" + f.FullName;

    /* axiom (forall h: HeapType, m: MaskType, this: ref, x_1: t_1, ..., x_n: t_n ::
         wf(h, m) && CurrentModule == module#C ==> #C.f(h, m, this, x_1, ..., x_n) == tr(body))
    */
    val args = VarExpr("this") :: inArgs;
    var formals = BVar(HeapName, theap) :: BVar(MaskName, tmask) :: BVar("this", tref) :: (f.ins map Variable2BVar);
    val applyF = FunctionApp(functionName(f), List(etran.Heap, etran.Mask) ::: args);

    /** Limit application of the function by introducing a second limited function */
    val body = etran.Tr(if (f.isRecursive) {
      val limited = Map() ++ (f.SCC zip (f.SCC map {f =>
        val result = Function(f.id + "#limited", f.ins, f.out, f.spec, f.definition);
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
      f.definition transform limit;
    } else
      f.definition);

    Axiom(new Boogie.Forall(
      formals, new Trigger(applyF),
        (wf(VarExpr(HeapName), VarExpr(MaskName)) && (CurrentModule ==@ ModuleName(currentClass)))
        ==>
        (applyF ==@ body))) ::
    (if (f.isRecursive)
      // define the limited function
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
      val frameFunctionName = "##" + f.FullName;

      val args = VarExpr("this") :: inArgs;
      val applyF = FunctionApp(functionName(f), List(etran.Heap, etran.Mask) ::: args);
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
      // Encoding with two heap quantification
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
    /* function ##C.f(state, ref, t_1, ..., t_n) returns (t);       
       axiom (forall h: HeapType, m: MaskType, this: ref, x_1: t_1, ..., x_n: t_n ::
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
      DefinePreInitialState :::
      InhaleWithChecking(List(DefinitionOf(pred)), "predicate definition"))
  }

  def translateMethod(method: Method): List[Decl] = {
    // check definedness of the method contract
    Proc(method.FullName + "$checkDefinedness", 
      NewBVarWhere("this", new Type(currentClass)) :: (method.ins map {i => Variable2BVarWhere(i)}),
      method.outs map {i => Variable2BVarWhere(i)},
      GlobalNames,
      DefaultPrecondition(),
        DefinePreInitialState :::
        bassume(CanAssumeFunctionDefs) ::
        // check precondition
        InhaleWithChecking(Preconditions(method.spec), "precondition") :::
        DefineInitialState :::
        (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
        Havoc(etran.Heap) ::
        // check postcondition
        InhaleWithChecking(Postconditions(method.spec), "postcondition") :::
        // check lockchange
        (LockChanges(method.spec) flatMap { lc => isDefined(lc)})) ::
    // check that method body satisfies the method contract
    Proc(method.FullName,
      NewBVarWhere("this", new Type(currentClass)) :: (method.ins map {i => Variable2BVarWhere(i)}),
      method.outs map {i => Variable2BVarWhere(i)},
      GlobalNames,
      DefaultPrecondition(),
        bassume(CurrentModule ==@ Boogie.VarExpr(ModuleName(currentClass))) ::
        bassume(CanAssumeFunctionDefs) ::
        DefinePreInitialState :::
        Inhale(Preconditions(method.spec) map { p => (if(0<defaults) UnfoldPredicatesWithReceiverThis(p) else p)}, "precondition") :::
        DefineInitialState :::
        translateStatements(method.body) :::
        Exhale(Postconditions(method.spec) map { p => ((if(0<defaults) UnfoldPredicatesWithReceiverThis(p) else p), ErrorMessage(method.pos, "The postcondition at " + p.pos + " might not hold."))}, "postcondition") :::
        (if(checkLeaks) isLeaking(method.pos, "Method " + method.FullName + " might leak refereces.") else Nil) :::
        bassert(LockFrame(LockChanges(method.spec), etran), method.pos, "Method might lock/unlock more than allowed.") :::
        bassert(DebtCheck, method.pos, "Method body is not allowed to leave any debt."))
  }

  def DebtCheck() = {
    // (forall ch :: ch == null || 0 <= Credits[ch])
    val (chV, ch) = NewBVar("ch", tref, false)
    new Boogie.Forall(chV, (ch ==@ bnull) || (0 <= new MapSelect(etran.Credits, ch)))
  }

  def DefaultPrecondition() : List[String] = 
  {
    List("requires this!=null;", "free requires wf(Heap, Mask);")
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
  def translateStatements(statements: List[Statement]): List[Stmt] = {
    statements flatMap translateStatement
  }

  def translateStatement(s: Statement): List[Stmt] = {
    s match {
      case Assert(e) =>
        val newGlobals = etran.FreshGlobals("assert");
        val tmpHeap = Boogie.NewBVar(HeapName, theap, true);
        val tmpMask = Boogie.NewBVar(MaskName, tmask, true); 
        val tmpCredits = Boogie.NewBVar(CreditsName, tcredits, true); 
        val tmpTranslator = new ExpressionTranslator(List(tmpHeap._1.id, tmpMask._1.id, tmpCredits._1.id), List(etran.ChooseEtran(true).Heap, etran.ChooseEtran(true).Mask, etran.ChooseEtran(true).Credits), currentClass);        
        Comment("assert") ::
        // exhale e in a copy of the heap/mask/credits
        BLocal(tmpHeap._1) :: (tmpHeap._2 := VarExpr(HeapName)) ::
        BLocal(tmpMask._1) :: (tmpMask._2 := VarExpr(MaskName)) ::
        BLocal(tmpCredits._1) :: (tmpCredits._2 := VarExpr(CreditsName)) ::
        tmpTranslator.Exhale(List((e, ErrorMessage(s.pos, "Assertion might not hold."))), "assert", true)
      case Assume(e) =>
        Comment("assume") ::
        isDefined(e) :::
        bassume(e)
      case BlockStmt(ss) =>
        translateStatements(ss)
      case IfStmt(guard, then, els) =>
        val tt = translateStatement(then)
        val et = els match {
          case None => Nil
          case Some(els) => translateStatement(els) }
        Comment("if") ::
        isDefined(guard) :::
        Boogie.If(guard, tt, et)
      case w: WhileStmt =>
        translateWhile(w)
      case Assign(lhs, rhs) =>
        def assignOrAssumeEqual(r: Boogie.Expr): List[Boogie.Stmt] = {
          if (lhs.v.isInstanceOf[ImmutableVariable]) {
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
      case lv @ LocalVar(id, t, const, ghost, rhs) =>
        val bv = Variable2BVarWhere(lv.v)
        val isAssignedVar = if (const) new Boogie.BVar("assigned$" + bv.id, BoolClass) else null
        Comment("local " + (if (ghost) "ghost " else "") + (if (const) "const " else "var ") + id) ::
        BLocal(bv) :: 
        { if (const)
            // havoc x; var assigned$x: bool; assigned$x := false; 
            Havoc(new Boogie.VarExpr(bv)) ::
            BLocal(isAssignedVar) :: (new Boogie.VarExpr(isAssignedVar) := false)
          else
            List() } :::
        { rhs match {
          //update the local, provided a rhs was provided
          case None => List()
          case Some(rhs) => translateStatement(Assign(new VariableExpr(lv.v), rhs)) }}
      case c: Call =>
        translateCall(c)
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
        ExhaleInvariants(obj, false, ErrorMessage(s.pos, "Monitor invariant might not hold."), etran.UseCurrentAsOld()) :::
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
        TrAcquire(s, obj)
      case Release(obj) =>
        Comment("release") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), s.pos, "The target of the release statement might be null.") ::
        TrRelease(s, obj)
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
            TrRdAcquire(s, obj) :::
            translateStatement(body) :::
            TrRdRelease(s, obj)
          } else {
            TrAcquire(s, obj) :::
            translateStatement(body) :::
            TrRelease(s, obj)
          }
        }
      case RdAcquire(obj) =>
        Comment("rd acquire") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), s.pos, "The target of the read-acquire statement might be null.") ::
        TrRdAcquire(s, obj)
      case rdrelease@RdRelease(obj) =>
        Comment("rd release") ::
        isDefined(obj) :::
        bassert(nonNull(TrExpr(obj)), obj.pos, "The target of the read-release statement might be null.") ::
        TrRdRelease(s, obj)
      case downgrade@Downgrade(obj) =>
        val o = TrExpr(obj);
        val prevHeapV = new Boogie.BVar("prevHeap", theap, true)
        Comment("downgrade") ::
        isDefined(obj) :::
        bassert(nonNull(o), s.pos, "The target of the downgrade statement might be null.") ::
        bassert(isHeld(o), s.pos, "The lock of the target of the downgrade statement might not be held by the current thread.") ::
        bassert(! isRdHeld(o), s.pos, "The current thread might hold the read lock.") ::
        ExhaleInvariants(obj, false, ErrorMessage(downgrade.pos, "Monitor invariant might not hold.")) :::
        BLocal(prevHeapV) ::
        InhaleInvariants(obj, true) :::
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
      case fold@Fold(acc@Access(pred@MemberAccess(e, f), fraction:Write)) =>
        val o = TrExpr(e);
        var definition = fraction match {
          case Frac(p) => FractionOf(SubstThis(DefinitionOf(pred.predicate), e), p);
          case Full => SubstThis(DefinitionOf(pred.predicate), e);
        }
        Comment("fold") ::
        isDefined(e) :::
        bassert(nonNull(o), s.pos, "The target of the fold statement might be null.") ::
        (fraction match {
          case Frac(p) => isDefined(p) :::
            bassert(0 <= etran.Tr(p), s.pos, "Fraction might be negative.") ::
            bassert(etran.Tr(p) <= 100, s.pos, "Fraction might be larger than 100.") :: Nil;
          case Full => Nil}) :::
        // remove the definition from the current state, and replace by predicate itself
        Exhale(List((definition, ErrorMessage(s.pos, "Fold might fail because the definition of " + pred.predicate.FullName + " does not hold."))), "fold") :::
        Inhale(List(acc), "fold") :::
        etran.Heap.store(o, pred.predicate.FullName, etran.Heap) :: // Is this necessary?      
        bassume(wf(etran.Heap, etran.Mask))
      case fld@Fold(acc@Access(pred@MemberAccess(e, f), nbEpsilons:Read)) =>
        val o = TrExpr(e);
        var (definition, checkEpsilons) = nbEpsilons match {
          case Epsilon => (EpsilonsOf(SubstThis(pred.predicate.definition, e), IntLiteral(1)), Nil)
          case Star => throw new Exception("Not supported yet!");
          case Epsilons(i) => (EpsilonsOf(SubstThis(DefinitionOf(pred.predicate), e), i), isDefined(i) ::: bassert(Boogie.IntLiteral(0) <= i, s.pos, "Number of epsilons might be negative.") :: Nil)
        }
        Comment("fold") ::
        isDefined(e) :::
        bassert(nonNull(o), s.pos, "The target of the fold statement might be null.") ::
        checkEpsilons :::
        Exhale(List((definition, ErrorMessage(fld.pos, "Fold might fail because the definition of " + pred.predicate.FullName + " does not hold."))), "fold") :::
        Inhale(List(acc), "fold") :::
        etran.Heap.store(e, pred.predicate.FullName, etran.Heap) ::
        bassume(wf(etran.Heap, etran.Mask))
      case unfld@Unfold(acc@Access(pred@MemberAccess(e, f), fraction:Write)) =>
        val o = TrExpr(e);
        var definition = fraction match {
          case Frac(p) => FractionOf(SubstThis(DefinitionOf(pred.predicate), e), p);
          case Full => SubstThis(DefinitionOf(pred.predicate), e);
        }
        Comment("unfold") ::
        isDefined(e) :::
        bassert(nonNull(o), s.pos, "The target of the fold statement might be null.") ::
        (fraction match {
          case Frac(p) => isDefined(p) :::
            bassert(Boogie.IntLiteral(0) <= p, s.pos, "Fraction might be negative.") ::
            bassert(p <= 100, s.pos, "Fraction might be larger than 100.") :: Nil
          case Full => Nil}) :::
        Exhale(List((acc, ErrorMessage(s.pos, "unfold might fail because the predicate " + pred.predicate.FullName + " does not hold."))), "unfold") :::
        etran.InhaleFrom(List(definition), "unfold", false, etran.Heap.select(o, pred.predicate.FullName))
      case unfld@Unfold(acc@Access(pred@MemberAccess(e, f), nbEpsilons:Read)) =>
        val o = TrExpr(e);
        var (definition, checkEpsilons) = nbEpsilons match {
          case Epsilon => (EpsilonsOf(SubstThis(DefinitionOf(pred.predicate), e), IntLiteral(1)), Nil)
          case Star => throw new Exception("Not supported yet!");
          case Epsilons(i) => (EpsilonsOf(SubstThis(DefinitionOf(pred.predicate), e), i), isDefined(i) ::: bassert(Boogie.IntLiteral(0) <= i, s.pos, "Number of epsilons might be negative.") :: Nil)
        }
        Comment("unfold") ::
        isDefined(e) :::
        bassert(nonNull(o), s.pos, "The target of the fold statement might be null.") ::
        checkEpsilons :::
        Exhale(List((acc, ErrorMessage(s.pos, "Unold might fail because the predicate " + pred.predicate.FullName + " does not hold."))), "unfold") :::
        etran.InhaleFrom(List(definition), "unfold", false, etran.Heap.select(o, pred.predicate.FullName))
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
          (p => SubstVars(p, formalThis, c.m.ins, formalIns)) zip (Preconditions(c.m.spec) map { p => ErrorMessage(c.pos, "The precondition at " + p.pos + " might not hold.")}), "precondition") :::
        // create a new token
        BLocal(tokenV) :: Havoc(tokenId) :: bassume(nonNull(tokenId)) ::
        // the following assumes help in proving that the token is fresh
        bassume(etran.Heap.select(tokenId, "joinable") ==@ 0) ::
        bassume(new Boogie.MapSelect(etran.Mask, tokenId, "joinable", "perm$N")==@ 0) ::
        bassume(new Boogie.MapSelect(etran.Mask, tokenId, "joinable", "perm$R")==@ 0) ::
        etran.IncPermission(tokenId, "joinable", 100) ::
        // create a fresh value for the joinable field
        BLocal(asyncStateV) :: Boogie.Havoc(asyncState) :: bassume(asyncState !=@ 0) ::
        etran.Heap.store(tokenId, "joinable", asyncState) ::
        // assume the pre call state for the token is the state before inhaling the precondition
        bassume(CallHeap(asyncState) ==@ preCallHeap) ::
        bassume(CallMask(asyncState) ==@ preCallMask) ::
        bassume(CallCredits(asyncState) ==@ preCallCredits) ::
        bassume(CallArgs(asyncState) ==@ argsSeq) ::
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
        Comment("join async") :: 
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
                         { p => SubstVars(p, formalThis, jn.m.ins ++ jn.m.outs, formalIns ++ formalOuts)}, "postcondition", false) :::
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
          "channel where clause")
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
        Inhale(List(SubstVars(channel.where, formalThis, channel.parameters, formalParams)), "channel where clause") :::
        // declare any new local variables among the actual outs
        (for (v <- r.locals) yield BLocal(Variable2BVarWhere(v))) :::
        // assign formal outs to actual outs
        (for ((v,e) <- outs zip formalParams) yield (v := e)) :::
        // decrease credits
        new Boogie.MapUpdate(etran.Credits, TrExpr(ch), new Boogie.MapSelect(etran.Credits, TrExpr(ch)) - 1)
    }
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
        etran.IncPermission(nwe, f.FullName, 100)) :::
      // initialize fields according to the initialization
      (initialization flatMap { init => isDefined(init.e) ::: etran.Heap.store(nwe, init.f.FullName, init.e) })
    )
  }

  def TrAcquire(s: Statement, nonNullObj: Expression) = {
    val o = TrExpr(nonNullObj);
    val (lastAcquireVar, lastAcquire) = Boogie.NewBVar("lastAcquire", IntClass, true)
    val (lastSeenHeldV, lastSeenHeld) = Boogie.NewBVar("lastSeenHeld", tint, true)
    val (lastSeenMuV, lastSeenMu) = Boogie.NewBVar("lastSeenMu", tmu, true)
    (if (skipDeadlockChecks)
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
      LastSeenCredits(lastSeenMu, lastSeenHeld))) :::
    // remember values of Heap/Mask/Credits globals (for proving history constraint at release)
    bassume(AcquireHeap(lastAcquire) ==@ etran.Heap) ::
    bassume(AcquireMask(lastAcquire) ==@ etran.Mask) ::
    bassume(AcquireCredits(lastAcquire) ==@ etran.Credits)
  }
  def TrRelease(s: Statement, nonNullObj: Expression) = {
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
      AcquireCredits(etran.Heap.select(o, "held")))) :::
    // havoc o.held where 0<=o.held 
    BLocal(heldV) :: Havoc(held) :: bassume(held <= 0) ::
    etran.Heap.store(o, "held", held) ::
    // assume a seen state is the one right before the share
    bassume(LastSeenHeap(etran.Heap.select(o, "mu"), held) ==@ preReleaseHeap) ::
    bassume(LastSeenMask(etran.Heap.select(o, "mu"), held) ==@ preReleaseMask) ::
    bassume(LastSeenCredits(etran.Heap.select(o, "mu"), held) ==@ preReleaseCredits)
  }
  def TrRdAcquire(s: Statement, nonNullObj: Expression) = {
    val (heldV, held) = Boogie.NewBVar("held", tint, true)
    val o = TrExpr(nonNullObj)
    bassert(CanRead(o, "mu"), s.pos, "The mu field of the target of the read-acquire statement might not be readable.") ::
    bassert(etran.MaxLockIsBelowX(etran.Heap.select(o, "mu")), s.pos, "The mu field of the target of the read-acquire statement might not be above waitlevel.") ::
    bassume(etran.Heap.select(o,"mu") !=@ bLockBottom) ::  // this isn't strictly necessary, it seems; but we might as well include it
    bassume(! isHeld(o) && ! isRdHeld(o)) ::
    BLocal(heldV) :: Havoc(held) :: bassume(held <= 0) ::
    etran.Heap.store(o, "held", held) ::
    etran.Heap.store(o, "rdheld", true) ::
    InhaleInvariants(nonNullObj, true)
  }
  def TrRdRelease(s: Statement, nonNullObj: Expression) = {
    val (heldV, held) = Boogie.NewBVar("held", tint, true)
    val o = TrExpr(nonNullObj);
    bassert(isRdHeld(o), s.pos, "The current thread might not hold the read-lock of the object being released.") ::
    ExhaleInvariants(nonNullObj, true, ErrorMessage(s.pos, "Monitor invariant might not hold.")) :::
    BLocal(heldV) :: Havoc(held) :: bassume(held <= 0) ::
    etran.Heap.store(o, "held", held) ::
    etran.Heap.store(o, "rdheld", false)
  }

  def translateCall(c: Call): List[Stmt] = {
    val obj = c.obj;
    val lhs = c.lhs;
    val id = c.id;
    val args = c.args;
    val formalThisV = new Variable("this", new Type(c.m.Parent))
    val formalThis = new VariableExpr(formalThisV)
    val formalInsV = for (p <- c.m.ins) yield new Variable(p.id, p.t)
    val formalIns = for (v <- formalInsV) yield new VariableExpr(v)
    val formalOutsV = for (p <- c.m.outs) yield new Variable(p.id, p.t)
    val formalOuts = for (v <- formalOutsV) yield new VariableExpr(v)
    val preGlobals = etran.FreshGlobals("call")
    val postEtran = etran.FromPreGlobals(preGlobals)
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
    Exhale(Preconditions(c.m.spec) map
          (p => SubstVars(p, formalThis, c.m.ins, formalIns)) zip (Preconditions(c.m.spec) map { p => ErrorMessage(c.pos, "The precondition at " + p.pos + " might not hold.")}), "precondition") :::
    // havoc formal outs
    (for (v <- formalOuts) yield Havoc(v)) :::
    // havoc lockchanges
    LockHavoc(for (e <- LockChanges(c.m.spec) map (p => SubstVars(p, formalThis, c.m.ins, formalIns))) yield etran.Tr(e), postEtran) :::
    // inhale postconditions (using the state before the call as the "old" state)
    postEtran.Inhale(Postconditions(c.m.spec) map
                     (p => SubstVars(p, formalThis, c.m.ins ++ c.m.outs, formalIns ++ formalOuts)) , "postcondition", false) :::
    // declare any new local variables among the actual outs
    (for (v <- c.locals) yield BLocal(Variable2BVarWhere(v))) :::
    // assign formal outs to actual outs
    (for ((v,e) <- lhs zip formalOuts) yield (v :=e))
  }

  def translateWhile(w: WhileStmt): List[Stmt] = {
    val guard = w.guard;
    val invs = w.invs;
    val lkch = w. lkch;
    val body = w.body;

    val preLoopGlobals = etran.FreshGlobals("while")
    val loopEtran = etran.FromPreGlobals(preLoopGlobals)
    val iterStartGlobals = etran.FreshGlobals("iterStart")
    val iterStartEtran = etran.FromPreGlobals(iterStartGlobals)
    val saveLocalsV = for (v <- w.LoopTargetsList) yield new Variable(v.id, v.t)
    val iterStartLocalsV = for (v <- w.LoopTargetsList) yield new Variable(v.id, v.t)
    val lkchOld = lkch map (e => SubstVars(e, w.LoopTargetsList,
                                             for (v <- saveLocalsV) yield new VariableExpr(v)))
    val lkchIterStart = lkch map (e => SubstVars(e, w.LoopTargetsList,
                                                   for (v <- iterStartLocalsV) yield new VariableExpr(v)))
    val oldLocks = lkchOld map (e => loopEtran.oldEtran.Tr(e))
    val iterStartLocks = lkchIterStart map (e => iterStartEtran.oldEtran.Tr(e))
    val newLocks = lkch map (e => loopEtran.Tr(e));
    Comment("while") ::
    // save globals
    (for (v <- preLoopGlobals) yield BLocal(v)) :::
    (loopEtran.oldEtran.Heap := loopEtran.Heap) ::
    (loopEtran.oldEtran.Mask := loopEtran.Mask) ::  // oldMask is not actually used below
    (loopEtran.oldEtran.Credits := loopEtran.Credits) ::  // is oldCredits?
    // check invariant on entry to the loop
    Exhale(invs map { inv => (inv, ErrorMessage(inv.pos, "The loop invariant might not hold on entry to the loop."))}, "loop invariant, initially") :::
     List(bassert(DebtCheck, w.pos, "Loop invariant must consume all debt on entry to the loop.")) :::
    // check lockchange on entry to the loop
    Comment("check lockchange on entry to the loop") ::
    (bassert(LockFrame(lkch, etran), w.pos, "Method execution before loop might lock/unlock more than allowed by lockchange clause of loop.")) ::
    // save values of local-variable loop targets
    (for (sv <- saveLocalsV) yield BLocal(Variable2BVarWhere(sv))) :::
    (for ((v,sv) <- w.LoopTargetsList zip saveLocalsV) yield
      (new VariableExpr(sv) := new VariableExpr(v))) :::
    // havoc local-variable loop targets
    (w.LoopTargets :\ List[Boogie.Stmt]()) ( (v,vars) => (v match {
      case v: ImmutableVariable => Boogie.Havoc(Boogie.VarExpr("assigned$" + v.id))
      case _ => Boogie.Havoc(Boogie.VarExpr(v.UniqueName)) }) :: vars) :::
    Boogie.If(null,
    // 1. CHECK  DEFINEDNESS OF INVARIANT
      Comment("check loop invariant definedness") ::
      //(w.LoopTargets.toList map { v: Variable => Boogie.Havoc(Boogie.VarExpr(v.id)) }) :::
      Boogie.Havoc(etran.Heap) :: Boogie.Assign(etran.Mask, ZeroMask) :: Boogie.Assign(etran.Credits, ZeroCredits) ::
      InhaleWithChecking(invs, "loop invariant definedness") :::
      bassume(false)
    , Boogie.If(null,
    // 2. CHECK LOOP BODY
      // Renew state: set Mask to ZeroMask and Credits to ZeroCredits, and havoc Heap everywhere except
      // at {old(local),local}.{held,rdheld}
      Havoc(etran.Heap) :: (etran.Mask := ZeroMask) :: (etran.Credits := ZeroCredits) ::
      Inhale(invs, "loop invariant, body") :::
      // assume lockchange at the beginning of the loop iteration
      Comment("assume lockchange at the beginning of the loop iteration") ::
      (bassume(LockFrame(lkch, etran))) ::
      // this is the state at the beginning of the loop iteration; save these values
      (for (v <- iterStartGlobals) yield BLocal(v)) :::
      (iterStartEtran.oldEtran.Heap := iterStartEtran.Heap) ::
      (iterStartEtran.oldEtran.Mask := iterStartEtran.Mask) ::  // oldMask is not actually used below
      (iterStartEtran.oldEtran.Credits := iterStartEtran.Credits) ::  // is oldCredits?
      (for (isv <- iterStartLocalsV) yield BLocal(Variable2BVarWhere(isv))) :::
      (for ((v,isv) <- w.LoopTargetsList zip iterStartLocalsV) yield
         (new VariableExpr(isv) := new VariableExpr(v))) :::
      // evaluate the guard
      isDefined(guard) ::: List(bassume(guard)) :::
      translateStatement(body) ::: 
      // check invariant
      Exhale(invs map { inv => (inv, ErrorMessage(w.pos, "The loop invariant at " + inv.pos + " might not be preserved by the loop."))}, "loop invariant, maintained") :::
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
     Inhale(invs, "loop invariant, after loop") :::
     bassume(!guard)))
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
    if(checkLeaks) {
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
    List.flatten (for (o <- locks) yield {  // todo: somewhere we should worry about Df(l)
      Havoc(held) :: Havoc(rdheld) ::
      bassume(rdheld ==> (0 < held)) ::
      new MapUpdate(etran.Heap, o, VarExpr("held"), held) ::
      new MapUpdate(etran.Heap, o, VarExpr("rdheld"), rdheld) })
  }
  def NumberOfLocksHeldIsInvariant(oldLocks: List[Boogie.Expr], newLocks: List[Boogie.Expr],
                                   etran: ExpressionTranslator) = {
    List.flatten (for ((o,n) <- oldLocks zip newLocks) yield {
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
    })
  }

  implicit def lift(s: Stmt): List[Stmt] = List(s)
  def isDefined(e: Expression) = etran.isDefined(e)(true)
  def TrExpr(e: Expression) = etran.Tr(e)

  def InhaleInvariants(obj: Expression, readonly: Boolean, tran: ExpressionTranslator) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    tran.Inhale(obj.typ.Invariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv)), "monitor invariant", false)
  }
  def ExhaleInvariants(obj: Expression, readonly: Boolean, msg: ErrorMessage, tran: ExpressionTranslator) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    tran.Exhale(obj.typ.Invariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv, msg)), "monitor invariant", false)
  }
  def InhaleInvariants(obj: Expression, readonly: Boolean) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    Inhale(obj.typ.Invariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv)), "monitor invariant")
  }
  def ExhaleInvariants(obj: Expression, readonly: Boolean, msg: ErrorMessage) = {
    val shV = new Variable("sh", new Type(obj.typ))
    val sh = new VariableExpr(shV)
    BLocal(Variable2BVar(shV)) :: Boogie.Assign(TrExpr(sh), TrExpr(obj)) ::
    Exhale(obj.typ.Invariants map
           (inv => SubstThis(inv.e, sh)) map
           (inv => (if (readonly) SubstRd(inv) else inv, msg)), "monitor invariant")
  }

  def Inhale(predicates: List[Expression], occasion: String): List[Boogie.Stmt] = etran.Inhale(predicates, occasion, false)
  def Exhale(predicates: List[(Expression, ErrorMessage)], occasion: String): List[Boogie.Stmt] = etran.Exhale(predicates, occasion, false)
  def InhaleWithChecking(predicates: List[Expression], occasion: String): List[Boogie.Stmt] = etran.Inhale(predicates, occasion, true)
  def ExhaleWithChecking(predicates: List[(Expression, ErrorMessage)], occasion: String): List[Boogie.Stmt] = etran.Exhale(predicates, occasion, true)

  def CanRead(obj: Boogie.Expr, field: Boogie.Expr): Boogie.Expr = etran.CanRead(obj, field)
  def CanWrite(obj: Boogie.Expr, field: Boogie.Expr): Boogie.Expr = etran.CanWrite(obj, field)


  /**********************************************************************
  *****************          EXPRESSIONS                *****************
  **********************************************************************/

class ExpressionTranslator(globals: List[Boogie.Expr], preGlobals: List[Boogie.Expr], currentClass: Class) {
  import TranslationHelper._
  import TranslationOptions._

  val Heap = globals(0);
  val Mask = globals(1);
  val Credits = globals(2);
  lazy val oldEtran = new ExpressionTranslator(preGlobals, preGlobals, currentClass)
  var checkTermination = false; 

  def this(globals: List[Boogie.Expr], cl: Class) = this(globals, globals map (g => Boogie.Old(g)), cl)
  def this(cl: Class) = this(for ((id,t) <- ExpressionTranslator.Globals) yield Boogie.VarExpr(id), cl)

  def Globals = List(Heap, Mask, Credits)
  def ChooseEtran(chooseOld: Boolean) = if (chooseOld) oldEtran else this
  // Create a list of fresh global variables
  def FreshGlobals(prefix: String) = {
    new Boogie.BVar(prefix + HeapName, theap, true) ::
    new Boogie.BVar(prefix + MaskName, tmask, true) ::
    new Boogie.BVar(prefix + CreditsName, tcredits, true) ::
    Nil
  }

  // Create a new ExpressionTranslator that is a copy of the receiver, but with
  // preGlobals as the old global variables 
  def FromPreGlobals(preGlobals: List[Boogie.BVar]) = {
    val g = for ((id,t) <- ExpressionTranslator.Globals) yield VarExpr(id)
    val pg = preGlobals map (g => new VarExpr(g))
    new ExpressionTranslator(g, pg, currentClass)
  }

  def UseCurrentAsOld() = {
    new ExpressionTranslator(globals, globals, currentClass);
  }

  def WhereOldIs(h: Boogie.Expr, m: Boogie.Expr, c: Boogie.Expr) = {
    new ExpressionTranslator(globals, List(h, m, c), currentClass);
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
      case Full | Epsilon | Star => Nil
      case Frac(perm) => isDefined(perm) ::: bassert(Boogie.IntLiteral(0)<=Tr(perm), perm.pos, "Fraction might be negative.") :: Nil
      case Epsilons(p) => isDefined(p) ::: bassert(Boogie.IntLiteral(0)<=Tr(p), p.pos, "Number of epsilons might be negative.")
      case _:PermissionExpr => throw new Exception("permission expression unexpected here: " + e.pos)
      case c@Credit(e, n) =>
        isDefined(e);
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
        val tmpTranslator = new ExpressionTranslator(List(tmpHeap,tmpMask,tmpCredits), currentClass);
        // check definedness of receiver + arguments
        (obj :: args flatMap { arg => isDefined(arg) }) :::
        // check that receiver is not null
        List(prove(nonNull(Tr(obj)), obj.pos, "Receiver might be null.")) :::
        // check precondition of the function by exhaling the precondition in tmpHeap/tmpMask/tmpCredits
        Comment("check precondition of call") ::
        bassume(assumption) ::
        BLocal(tmpHeapV) :: (tmpHeap := Heap) ::
        BLocal(tmpMaskV) :: (tmpMask := Mask) :::
        BLocal(tmpCreditsV) :: (tmpCredits := Credits) :::
        tmpTranslator.Exhale(Preconditions(func.f.spec) map { pre=> (SubstVars(pre, obj, func.f.ins, args), ErrorMessage(func.pos, "Precondition at " + pre.pos + " might not hold."))},
                             "function call",
                             false) :::
        // size of the heap of callee must be strictly smaller than size of the heap of the caller
        (if(checkTermination) { List(prove(NonEmptyMask(tmpMask), func.pos, "The heap of the callee might not be strictly smaller than the heap of the caller.")) } else Nil)
      case unfolding@Unfolding(access, e) =>
        val (checks, predicate, definition, from) = access match {
          case acc@Access(pred@MemberAccess(obj, f), perm) =>
           val receiverOk = isDefined(obj) ::: prove(nonNull(Tr(obj)), obj.pos, "Receiver might be null.");
           val body = SubstThis(DefinitionOf(pred.predicate), obj);
            perm match {           
              case Full => (receiverOk, acc, body, Heap.select(Tr(obj), pred.predicate.FullName))
              case Frac(fraction) => (receiverOk ::: isDefined(fraction) ::: prove(0 <= Tr(fraction), fraction.pos, "Fraction might be negative") :: prove(Tr(fraction) <= 100, fraction.pos, "Fraction might exceed 100."), acc, FractionOf(body, fraction), Heap.select(Tr(obj), pred.predicate.FullName))
              case Epsilon => (receiverOk, acc, EpsilonsOf(body, IntLiteral(1)), Heap.select(Tr(obj), pred.predicate.FullName))
              case Star => assert(false); (null, null, null, Heap.select(Tr(obj), pred.predicate.FullName))
              case Epsilons(epsilons) => (receiverOk ::: isDefined(epsilons) ::: prove(0 <= Tr(epsilons), epsilons.pos, "Number of epsilons might be negative"), acc, EpsilonsOf(body, epsilons), Heap.select(Tr(obj), pred.predicate.FullName))
            }
        }
        val newGlobals = FreshGlobals("checkPre");
        val (tmpHeapV, tmpHeap) = Boogie.NewBVar("Heap", theap, true);
        val (tmpMaskV, tmpMask) = Boogie.NewBVar("Mask", tmask, true);
        val (tmpCreditsV, tmpCredits) = Boogie.NewBVar("Credits", tcredits, true);
        val tmpTranslator = new ExpressionTranslator(List(tmpHeap, tmpMask, tmpCredits), currentClass);
        Comment("unfolding") ::
        // check definedness
        checks :::
        // copy state into temporary variables
        BLocal(tmpHeapV) :: Boogie.Assign(tmpHeap, Heap) ::
        BLocal(tmpMaskV) :: Boogie.Assign(tmpMask, Mask) ::
        BLocal(tmpCreditsV) :: Boogie.Assign(tmpCredits, Credits) ::
        // exhale the predicate
        tmpTranslator.Exhale(List((predicate, ErrorMessage(unfolding.pos, "Unfolding might fail."))), "unfolding", false) :::
        // inhale the definition of the predicate
        tmpTranslator.InhaleFrom(List(definition), "unfolding", false, from) :::
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
        isDefined(min) ::: isDefined(max)
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
        val evalEtran = new ExpressionTranslator(List(evalHeap, evalMask, evalCredits), currentClass);
        evalEtran.isDefined(e)
      case _ : SeqQuantification => throw new Exception("should be desugared")
      case tq @ TypeQuantification(_, _, _, e) =>
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
    case MaxLockLiteral() => throw new Exception("waitlevel case should be handled in << and == and !=")
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
    case _:Permission => throw new Exception("permission unexpected here")
    case _:PermissionExpr => throw new Exception("permission expression unexpected here: " + e.pos)
    case _:Credit => throw new Exception("credit expression unexpected here")
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
      if (IsMaxLockLit(e0) || IsMaxLockLit(e1))
        Tr(Not(Eq(e0,e1)))
      else
        (Tr(e0) !=@ Tr(e1))
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
    case Length(e) => SeqLength(e)
    case Contains(e0, e1) => SeqContains(Tr(e1), Tr(e0))
    case Eval(h, e) =>
      val (evalHeap, evalMask, evalCredits, checks, assumptions) = fromEvalState(h);
      val evalEtran = new ExpressionTranslator(List(evalHeap, evalMask, evalCredits), currentClass);
      evalEtran.Tr(e)
    case _:SeqQuantification => throw new Exception("should be desugared")
    case tq @ TypeQuantification(Forall, _, _, e) =>
      Boogie.Forall(Nil, tq.variables map { v => Variable2BVar(v)}, Nil, Tr(e))
    case tq @ TypeQuantification(Exists, _, _, e) =>
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

  def Inhale(predicates: List[Expression], occasion: String, check: Boolean): List[Boogie.Stmt] = {
    val (ihV, ih) = Boogie.NewBVar("inhaleHeap", theap, true)
    Comment("inhale (" + occasion + ")") ::
    BLocal(ihV) :: Boogie.Havoc(ih) ::
    bassume(IsGoodInhaleState(ih, Heap, Mask)) ::
    List.flatten (for (p <- predicates) yield Inhale(p, ih, check)) :::
    bassume(IsGoodMask(Mask)) ::
    bassume(wf(Heap, Mask)) ::
    Comment("end inhale")
  }

  def InhaleFrom(predicates: List[Expression], occasion: String, check: Boolean, useHeap: Boogie.Expr): List[Boogie.Stmt] = {
    val (ihV, ih) = Boogie.NewBVar("inhaleHeap", theap, true)
    Comment("inhale (" + occasion + ")") ::
    BLocal(ihV) :: Boogie.Assign(ih, useHeap) ::
    bassume(IsGoodInhaleState(ih, Heap, Mask)) ::
    List.flatten (for (p <- predicates) yield Inhale(p,ih, check)) :::
    bassume(IsGoodMask(Mask)) ::
    bassume(wf(Heap, Mask)) ::
    Comment("end inhale")
  }

  def Inhale(p: Expression, ih: Boogie.Expr, check: Boolean): List[Boogie.Stmt] = desugar(p) match {
    case pred@MemberAccess(e, p) if pred.isPredicate => 
      val tmp = Access(pred, Full);
      tmp.pos = pred.pos;
      Inhale(tmp, ih, check)
    case AccessAll(obj, perm) => throw new Exception("should be desugared")
    case AccessSeq(s, None, perm) => throw new Exception("should be desugared")
    case acc@Access(e,perm) =>
      val trE = Tr(e.e)
      val module = currentClass.module;
      val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;

      // List(bassert(nonNull(trE), acc.pos, "The target of the acc predicate might be null."))
      (if(check) isDefined(e.e)(true) ::: isDefined(perm)(true) ::: (perm match {case Frac(p) if(! e.isPredicate) => bassert(Tr(p) <= 100, p.pos, "Fraction might exceed 100.") :: Nil; case _ => Nil})
      else Nil) :::
      bassume(nonNull(trE)) ::
      new MapUpdate(Heap, trE, VarExpr(memberName), new Boogie.MapSelect(ih, trE, memberName)) ::
      bassume(wf(Heap, Mask)) ::
      (if(e.isPredicate && e.predicate.Parent.module.equals(currentClass.module)) List(bassume(new Boogie.MapSelect(ih, trE, memberName) ==@ Heap)) else Nil) :::
      (if(e.isPredicate) Nil else List(bassume(TypeInformation(new Boogie.MapSelect(Heap, trE, memberName), e.f.typ.typ)))) :::
      (perm match {
        case Full => IncPermission(trE, memberName, 100)
        case Frac(perm) => IncPermission(trE, memberName, Tr(perm))
        case Epsilon => IncPermissionEpsilon(trE, memberName, 1)
        case Epsilons(p) => IncPermissionEpsilon(trE, memberName, Tr(p))
        case Star => IncPermissionEpsilon(trE, memberName, null)
      }) ::
      bassume(IsGoodMask(Mask)) ::
      bassume(IsGoodState(new Boogie.MapSelect(ih, trE, memberName))) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(ih, Mask))
    case acc @ AccessSeq(s, Some(member), perm) =>
      if (member.isPredicate) throw new Exception("not yet implemented");
      val e = Tr(s);
      val memberName = member.f.FullName;
      val (r, n) = perm match {
        case Full => (100, 0) : (Expr, Expr)
        case Frac(p) => (Tr(p), 0) : (Expr, Expr)
        case Epsilon => (0, 1) : (Expr, Expr)        // TODO: check for infinity bounds -- or perhaps just wait till epsilons are gone
        case Epsilons(p) => (0, Tr(p)) : (Expr, Expr)
      };

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
      {
        val (aV,a) = Boogie.NewTVar("alpha");
        val (refV, ref) = Boogie.NewBVar("ref", tref, true);
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
      Boogie.If(Tr(e0), Inhale(e1, ih, check), Nil)
    case IfThenElse(con, then, els) =>
      (if(check) isDefined(con)(true) else Nil) :::
      Boogie.If(Tr(con), Inhale(then, ih, check), Inhale(els, ih, check))
    case And(e0,e1) =>
      Inhale(e0, ih, check) ::: Inhale(e1, ih, check)
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
      preEtran.Inhale(e, ih, check) :::
      bassume(preEtran.Heap ==@ evalHeap) ::
      bassume(submask(preEtran.Mask, evalMask))
    case e => (if(check) isDefined(e)(true) else Nil) ::: bassume(Tr(e))
  }

  def Exhale(predicates: List[(Expression, ErrorMessage)], occasion: String, check: Boolean): List[Boogie.Stmt] = {
    val (emV, em) = NewBVar("exhaleMask", tmask, true)
    Comment("begin exhale (" + occasion + ")") ::
    BLocal(emV) :: (em := Mask) ::
    (List.flatten (for (p <- predicates) yield Exhale(p._1, em, null, p._2, check))) :::
    (Mask := em) ::
    bassume(wf(Heap, Mask)) ::
    Comment("end exhale")
  }

  def Exhale(p: Expression, em: Boogie.Expr, eh: Boogie.Expr, error: ErrorMessage, check: Boolean): List[Boogie.Stmt] = desugar(p) match {
    case pred@MemberAccess(e, p) if pred.isPredicate =>
      val tmp = Access(pred, Full);
      tmp.pos = pred.pos;
      Exhale(tmp, em , eh, error, check)
    case AccessAll(obj, perm) => throw new Exception("should be desugared")
    case AccessSeq(s, None, perm) => throw new Exception("should be desugared")
    case acc@Access(e,perm:Write) =>
      val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;

      // look up the fraction
      val (fraction, checkFraction) = perm match {
        case Full => (IntLiteral(100), Nil)
        case Frac(fr) => (fr, bassert(0<=Tr(fr), fr.pos, "Fraction might be negative.") :: (if(! e.isPredicate) bassert(Tr(fr)<=100, fr.pos, "Fraction might exceed 100.") :: Nil else Nil) ::: Nil)
      }

      val (fractionV, frac) = NewBVar("fraction", tint, true);
      // check definedness
      (if(check) isDefined(e.e)(true) :::
                 checkFraction :::
                 bassert(nonNull(Tr(e.e)), error.pos, error.message + " The target of the acc predicate at " + acc.pos + " might be null.") else Nil) :::
      BLocal(fractionV) :: (frac := Tr(fraction)) ::
      // if the mask does not contain sufficient permissions, try folding acc(e, fraction)
      (if(e.isPredicate && autoFold && (perm == Full || canTakeFractionOf(DefinitionOf(e.predicate)))) {
         val inhaleTran = new ExpressionTranslator(List(Heap, em, Credits), currentClass);
         val sourceVar = new Variable("fraction", new Type(IntClass));
         val bplVar = Variable2BVar(sourceVar);
         BLocal(bplVar) :: (VarExpr(sourceVar.UniqueName) := frac) ::
         If(new MapSelect(em, Tr(e.e), memberName, "perm$R") < frac,
           Exhale(perm match {
              case Frac(p) => FractionOf(SubstThis(DefinitionOf(e.predicate), e.e), new VariableExpr(sourceVar));
              case Full => SubstThis(DefinitionOf(e.predicate), e.e)}, em, eh, ErrorMessage(error.pos, error.message + " Automatic fold might fail."), false) :::
           inhaleTran.Inhale(List(perm match {
              case Full => Access(e, Full);
              case Frac(p) => Access(e, Frac(new VariableExpr(sourceVar)))}), "automatic fold", false)
         , Nil) :: Nil}
       else Nil) :::
      // check that the necessary permissions are there and remove them from the mask
      DecPermission(Tr(e.e), memberName, frac, em, error, acc.pos) :::
      bassume(IsGoodMask(Mask)) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(Heap, em))
    case rd@Access(e,perm:Read) =>
      val memberName = if(e.isPredicate) e.predicate.FullName else e.f.FullName;
      val (epsilonsV, eps) = NewBVar("epsilons", tint, true);
      val (dfP, epsilons) = perm match {
        case Epsilon => (List(), IntLiteral(1))
        case Star => (List(), null)
        case Epsilons(p) => (isDefined(p)(true) ::: List(bassert(0 <= Tr(p), error.pos, error.message + " The number of epsilons at " + rd.pos + " might be negative.")) , p)
      }
      // check definedness
      (if(check) isDefined(e.e)(true) :::
        bassert(nonNull(Tr(e.e)), error.pos, error.message + " The target of the rd predicate at " + rd.pos + " might be null.") ::
        dfP else Nil) :::
      BLocal(epsilonsV) :: (if(epsilons!=null) (eps := Tr(epsilons)) :: Nil else Nil) :::
      // if the mask does not contain sufficient permissions, try folding rdacc(e, epsilons)
      (if(e.isPredicate && autoFold && canTakeEpsilonsOf(DefinitionOf(e.predicate)) && epsilons!=null) {
          val inhaleTran = new ExpressionTranslator(List(Heap, em, Credits), currentClass);
          val sourceVar = new Variable("epsilons", new Type(IntClass));
          val bplVar = Variable2BVar(sourceVar);
          BLocal(bplVar) :: (VarExpr(sourceVar.UniqueName) := eps) ::
          If(new MapSelect(em, Tr(e.e), memberName, "perm$N") < eps,
            Exhale(EpsilonsOf(SubstThis(DefinitionOf(e.predicate), e.e), new VariableExpr(sourceVar)), em, eh, ErrorMessage(error.pos, error.message + " Automatic fold might fail."), false) :::
            inhaleTran.Inhale(List(Access(e, Epsilons(new VariableExpr(sourceVar)))), "automatic fold", false)
          , Nil) :: Nil}
       else Nil) :::
      // check that the necessary permissions are there and remove them from the mask
      DecPermissionEpsilon(Tr(e.e), memberName, if(epsilons != null) eps else null, em, error, rd.pos) :::
      bassume(IsGoodMask(Mask)) ::
      bassume(wf(Heap, Mask)) ::
      bassume(wf(Heap, em))
    case acc @ AccessSeq(s, Some(member), perm) =>
      if (member.isPredicate) throw new Exception("not yet implemented");
      val e = Tr(s);
      val memberName = member.f.FullName;
      val (r, n) = perm match {
        case Full => (100, 0) : (Expr, Expr)
        case Frac(p) => (p, 0) : (Expr, Expr)
        case Epsilon => (0, 1) : (Expr, Expr)        // TODO: check for infinity bounds -- or perhaps just wait till epsilons are gone
        case Epsilons(p) => (0, p) : (Expr, Expr)
      };

      (if (check) isDefined(s)(true) ::: isDefined(perm)(true) else Nil) :::
      {
        val (aV,a) = Boogie.NewTVar("alpha");
        val (refV, ref) = Boogie.NewBVar("ref", tref, true);
        val (fV, f) = Boogie.NewBVar("f", FieldType(a), true);
        val (pcV,pc) = Boogie.NewBVar("p", tperm, true);
        val mr = em(ref, memberName)("perm$R");
        val mn = em(ref, memberName)("perm$N");

        bassert((SeqContains(e, ref) ==>
          (perm match {
            case _: Read => mr ==@ 0 ==> n <= mn
            case _: Write => r <= mr && (r ==@ mr ==> 0 <= mn)
          })).forall(refV), error.pos, error.message + " Insufficient permissions") ::
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
      Boogie.If(Tr(e0), Exhale(e1, em, eh, error, check), Nil)
    case IfThenElse(con, then, els) =>
      (if(check) isDefined(con)(true) else Nil) :::
      Boogie.If(Tr(con), Exhale(then, em, eh, error, check), Exhale(els, em, eh, error, check))
    case And(e0,e1) =>
      Exhale(e0, em, eh, error, check) ::: Exhale(e1, em, eh, error, check)
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
      preEtran.Exhale(List((e, error)), "eval", check)
    case e => (if(check) isDefined(e)(true) else Nil) ::: List(bassert(Tr(e), error.pos, error.message + " The expression at " + e.pos + " might not evaluate to true."))
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
         (((args zip (1 until args.length+1).toList) map { a => new MapSelect(argsSeq, a._2) ==@ Tr(a._1)}).foldLeft(true: Expr){ (a: Expr, b: Expr) => a && b})
        )
    }
  }

  // permissions

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
    (new Boogie.MapSelect(mask, obj, field, "perm$R") ==@ Boogie.IntLiteral(100)) &&
    (new Boogie.MapSelect(mask, obj, field, "perm$N") ==@ Boogie.IntLiteral(0))
  def SetFullPermission(obj: Boogie.Expr, field: String) =
    Boogie.Assign(new Boogie.MapSelect(Mask, obj, field), Boogie.VarExpr("Permission$Full"))

  def IncPermission(obj: Boogie.Expr, field: String, howMuch: Boogie.Expr) =
    MapUpdate3(Mask, obj, field, "perm$R", new Boogie.MapSelect(Mask, obj, field, "perm$R") + howMuch)
  def IncPermissionEpsilon(obj: Boogie.Expr, field: String, epsilons: Boogie.Expr) =
    if (epsilons != null) {
      val g = (new Boogie.MapSelect(Mask, obj, field, "perm$N") !=@ Boogie.VarExpr("Permission$MinusInfinity")) &&
              (new Boogie.MapSelect(Mask, obj, field, "perm$N") !=@ Boogie.VarExpr("Permission$PlusInfinity"))
      Boogie.If(g, 
        MapUpdate3(Mask, obj, field, "perm$N", new Boogie.MapSelect(Mask, obj, field, "perm$N") + epsilons) ::
          bassume(Boogie.FunctionApp("wf", List(Heap, Mask))) :: Nil
        , Nil)
    } else {
      val g = (new Boogie.MapSelect(Mask, obj, field, "perm$N") !=@ Boogie.VarExpr("Permission$MinusInfinity"))
      Boogie.If(g, MapUpdate3(Mask, obj, field, "perm$N", Boogie.VarExpr("Permission$PlusInfinity")), Nil)
    }
  def DecPermission(obj: Boogie.Expr, field: String, howMuch: Boogie.Expr, mask: Boogie.Expr, error: ErrorMessage, pos: Position) = {
    val fP: Boogie.Expr = new Boogie.MapSelect(mask, obj, field, "perm$R")
    val fC: Boogie.Expr = new Boogie.MapSelect(mask, obj, field, "perm$N")
    bassert(howMuch <= fP && (howMuch ==@ fP ==> 0 <= fC), error.pos, error.message + " Insufficient fraction at " + pos + " for " + field + ".") ::
    MapUpdate3(mask, obj, field, "perm$R", new Boogie.MapSelect(mask, obj, field, "perm$R") - howMuch)
  }
  def DecPermissionEpsilon(obj: Boogie.Expr, field: String, epsilons: Boogie.Expr, mask: Boogie.Expr, error: ErrorMessage, pos: Position) =
    if (epsilons != null) {
      val g = (new Boogie.MapSelect(mask, obj, field, "perm$N") !=@ Boogie.VarExpr("Permission$MinusInfinity")) &&
              (new Boogie.MapSelect(mask, obj, field, "perm$N") !=@ Boogie.VarExpr("Permission$PlusInfinity"))
      val xyz = new Boogie.MapSelect(mask, obj, field, "perm$N")
      bassert((new Boogie.MapSelect(mask, obj, field, "perm$R") ==@ Boogie.IntLiteral(0)) ==> (epsilons <= xyz), error.pos, error.message + " Insufficient epsilons at " + pos + "  for " + field + ".") ::
      Boogie.If(g,
         MapUpdate3(mask, obj, field, "perm$N", new Boogie.MapSelect(mask, obj, field, "perm$N") - epsilons) ::
           bassume(Boogie.FunctionApp("wf", List(Heap, Mask))) :: Nil
        , Nil)
    } else {
      val g = (new Boogie.MapSelect(mask, obj, field, "perm$N") !=@ Boogie.VarExpr("Permission$PlusInfinity"))
      bassert((new Boogie.MapSelect(mask, obj, field, "perm$R") ==@ Boogie.IntLiteral(0)) ==>
                    (new Boogie.MapSelect(mask, obj, field, "perm$N") ==@ Boogie.VarExpr("Permission$PlusInfinity")),  error.pos, error.message + " Insufficient epsilons at " + pos + " for " + field + ".") ::
      Boogie.If(g, MapUpdate3(mask, obj, field, "perm$N", Boogie.VarExpr("Permission$MinusInfinity")), Nil)
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
    val (oV, o) = Boogie.NewBVar("o", tref, false)
    new Boogie.Forall(oV,
                      (contributesToWaitLevel(o, Heap, Credits)) ==>
                      new Boogie.FunctionApp("MuBelow", new Boogie.MapSelect(Heap, o, "mu"), x))
  }
  def MaxLockIsAboveX(x: Boogie.Expr) = {  // x << waitlevel
    val (oV, o) = Boogie.NewBVar("o", tref, false)
    new Boogie.Exists(oV,
                      (contributesToWaitLevel(o, Heap, Credits)) &&
                      new Boogie.FunctionApp("MuBelow", x, new Boogie.MapSelect(Heap, o, "mu")))
  }
  def IsHighestLock(x: Boogie.Expr) = {
    // (forall r :: r.held ==> r.mu << x || r.mu == x)
    val (rV, r) = Boogie.NewBVar("r", tref, false)
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
    val (rV, r) = Boogie.NewBVar("r", tref, false)
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
    val (oV, o) = Boogie.NewBVar("o", tref, false)
    val (pV, p) = Boogie.NewBVar("p", tref, false)
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
    val (oV, o) = Boogie.NewBVar("o", tref, false)
    new Boogie.Exists(oV,
                      (0 < new Boogie.MapSelect(e1.Heap, o, "held")) &&
                      e0.MaxLockIsBelowX(new Boogie.MapSelect(e1.Heap, o, "mu")))
  }

  def fractionOk(expr: Expression) = {
    bassert(0<=Tr(expr), expr.pos, "Fraction might be negative.") :: 
    bassert(Tr(expr) <= 100, expr.pos, "Fraction might exceed 100.")
  }
}

  // implicit (uses etran)

  implicit def expression2Expr(e: Expression) = etran.Tr(e);

  // prelude (uses etran)
  def isHeld(e: Expr): Expr = (0 < etran.Heap.select(e, "held"))
  def isRdHeld(e: Expr): Expr = etran.Heap.select(e, "rdheld")
  def isShared(e: Expr): Expr = etran.Heap.select(e, "mu") !=@ bLockBottom

object ExpressionTranslator {
  val Globals = {
    ("Heap", theap) ::
    ("Mask", tmask) ::
    ("Credits", tcredits) ::
    Nil
  }
}

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
      assert(false, "unexpectected type: " + cl.FullName); null
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

  def ModuleType = NamedType("ModuleName");
  def ModuleName(cl: Class) = "module#" + cl.module.id;
  def TypeName = NamedType("TypeName");
  def FieldType(tp: BType) = IndexedType("Field", tp);
  def bassert(e: Expr, pos: Position, msg: String) = {
    val result = Boogie.Assert(e); result.pos = pos; result.message = msg; result
  }
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

  // Sequences

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

  // scale an expression by a fraction
  def FractionOf(expr: Expression, fraction: Expression) : Expression = {
    val result = expr match {
      case Access(e, Full) => Access(e, Frac(fraction))
      case And(lhs, rhs) => And(FractionOf(lhs, fraction), FractionOf(rhs, fraction))
      case _ if ! expr.isInstanceOf[PermissionExpr] => expr
      case _ => throw new Exception("  " + expr.pos + ": Scaling non-full permissions is not supported yet." + expr);
    }
    result.pos = expr.pos;
    result
  }

  def canTakeFractionOf(expr: Expression): Boolean = {
    expr match {
      case Access(e, Full) => true
      case And(lhs, rhs) => canTakeFractionOf(lhs) && canTakeFractionOf(rhs)
      case _ if ! expr.isInstanceOf[PermissionExpr] => true
      case _ => false
    }
  }

  // scale an expression by a number of epsilons
  def EpsilonsOf(expr: Expression, nbEpsilons: Expression) : Expression = {
    val result = expr match {
      case Access(e, _:Write) => Access(e, Epsilons(nbEpsilons))
      case And(lhs, rhs) => And(FractionOf(lhs, nbEpsilons), FractionOf(rhs, nbEpsilons))
      case _ if ! expr.isInstanceOf[PermissionExpr] => expr
      case _ => throw new Exception("  " + expr.pos + ": Scaling non-full permissions is not supported yet." + expr);
    }
    result.pos = expr.pos;
    result
  }

  def canTakeEpsilonsOf(expr: Expression): Boolean = {
    expr match {
      case Access(e, _:Write) => true
      case And(lhs, rhs) => canTakeEpsilonsOf(lhs) && canTakeEpsilonsOf(rhs)
      case _ if ! expr.isInstanceOf[PermissionExpr] => true
      case _ => false
    }
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
      case _: PermissionExpr => throw new Exception("unexpected permission expression")
      case e =>
        e visit {_ match { case _ : PermissionExpr => throw new Exception("unexpected permission expression"); case _ =>}}
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
      case _: PermissionExpr => throw new Exception("unexpected permission expression")
      case e =>
        e visit {_ match { case _ : PermissionExpr => throw new Exception("unexpected permission expression"); case _ =>}}
        Boogie.BoolLiteral(true)
    }
  }
  
  def Preconditions(spec: List[Specification]): List[Expression] = {
    val result = spec flatMap ( s => s match {
      case Precondition(e) => List(e)
      case _ => Nil });
    if(autoMagic) {
     automagic(result.foldLeft(BoolLiteral(true): Expression)({ (a, b) => And(a, b)}), Nil)._1 ::: result
    } else {
      result
    }
  }
  def Postconditions(spec: List[Specification]): List[Expression] = {
    val result = spec flatMap ( s => s match {
      case Postcondition(e) => List(e)
      case _ => Nil })
    if(autoMagic) {
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
          case Full | Epsilon | Star => (assumptions, handled1);
          case Frac(fraction) => val result = automagic(fraction, handled1); (assumptions ::: result._1, result._2)
          case Epsilons(epsilon) => val result = automagic(epsilon, handled1); (assumptions ::: result._1, result._2)
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
    if(autoMagic) {
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
    case Access(e, _:Write) =>
      val r = Access(e,Epsilon); r.pos = e.pos; r.typ = BoolClass; r
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
          Some(p match {
            case Full => SubstThis(DefinitionOf(pred.predicate), o)
            case Frac(p) => FractionOf(SubstThis(DefinitionOf(pred.predicate), o), p)
            case Epsilon => EpsilonsOf(SubstThis(DefinitionOf(pred.predicate), o), IntLiteral(1))
            case Star => throw new Exception("not supported yet")
            case Epsilons(p) => EpsilonsOf(SubstThis(DefinitionOf(pred.predicate), o), p)
          })
        case func@FunctionApplication(obj: ThisExpr, name, args) if 2<=TranslationOptions.defaults =>
          Some(SubstVars(func.f.definition, obj, func.f.ins, args))
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
    _ match {
      case _: ThisExpr if t.isDefined => t
      case e: VariableExpr =>
        if (vs.contains(e.v)) Some(vs(e.v)) else None;
      case q: Quantification =>
        q.variables foreach { (v) => if (vs.contains(v)) throw new Exception("cannot substitute a variable bound in the quantifier")}
        None;
      case _ => None;
    }
  }

  def SubstThis(expr: Expression, x: Expression): Expression = expr.transform {
    _ match {
      case _: ThisExpr => Some(x)
      case _ => None
    }
  }

  def SubstResult(expr: Expression, x: Expression): Expression = expr.transform {
    _ match {
      case _: Result => Some(x)
      case _ => None
    }
  }  

  // De-sugar expression (idempotent)
  // * unroll wildcard pattern (for objects) in permission expression
  // * convert sequence quantification into type quantification
  def desugar(expr: Expression): Expression = expr transform {
    _ match {
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
        val result = TypeQuantification(q, is, new Type(IntClass), body);
        result.variables = dis;
        Some(result);
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
        val result = TypeQuantification(q, is, new Type(IntClass), body);
        result.variables = dis;
        Some(result);
      case _ => None;
    }
  }
}
}
