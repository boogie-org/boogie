
package chalice;

import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

/** SmokeTest allows to perform 'smoke testing' on any given Chalice program.
 *  The prover is instructed to try proving 'false' at various places in the
 *  program to find unreachable code, precondition that are equivalent to false
 *  or assumptions that introduce a contradiction.
 *
 *  @author Stefan Heule
 */
object SmokeTest {

  /** SmokeAssert is used to keep track of the position and real error message
   *  associated with a certain assert statement. Also, we build a DAG of
   *  SmokeAssert that essentially corresponds to the control flow graph (the
   *  member prev is used to record the in-edges of every SmokeAssert). This
   *  graph is then used to omit certain warnings (e.g., if the precondition is
   *  already false, we do not need to report that the method end cannot be
   *  reached, too).
   */
  case class SmokeAssert(id: Int, pos: Position, msg: String, prev: Set[SmokeAssert], chaliceAssert: Assert) {
    var warning: Boolean = false // did this "assert false" generate a warning? (i.e. did it not generate a Boogie error?)
  }
  /** Serves as a sentinel for the first assert (which should always cause a
   *  warning, thus SmokeAssertSentinel.warning = false
   */
  object SmokeAssertSentinel extends SmokeAssert(-1, NoPosition, "", Set(), null)

  /** Map from error message ID's to their SmokeAssert object */
  private var smokeAssertions: Map[Int,SmokeAssert] = Map()
  private var count: Int = 0 // current error message id
  
  /** Process the output of Boogie and generate the correct warnings from smoke testing */
  def processBoogieOutput(out: List[String]): String = {
    var errorCount: Map[String, Int] = Map()
    val SmokePattern = ".*: SMOKE-TEST-([0-9]+).".r
    val SummaryPattern = "Boogie program verifier finished with ([0-9]+) verified, ([0-9]+) errors".r
    var verificationResult = "";
    var smokeErrors: Set[Int] = Set()
    var outcome: Option[(Int,Int)] = None
    for (s <- out) s match {
      case SmokePattern(id) => smokeErrors += id.toInt
      case SummaryPattern(verified, errors) => outcome = Some((verified.toInt,errors.toInt))
      case _ => verificationResult += s + "\n"
    }
    
    // check which smoke assertions failed
    for ((errNr, s@SmokeAssert(_, pos, msg, prev, _)) <- smokeAssertions) yield {
      s.warning = !smokeErrors.contains(errNr)
    }
    
    var smokeTestWarnings = 0
    val smokeResult = {
      var t = "";
      for (s@SmokeAssert(_, pos, msg, prev, _) <- smokeAssertions.values.toList.sortWith((a,b) => a.pos < b.pos)) yield {
        if (s.warning) {
          if (s.prev.exists(a => !a.warning)) { // omit warning if all ancestors created a warning
            t += "  " + pos + ": " + msg + "\n"
            smokeTestWarnings += 1
          }
        }
      }
      t
    }
    
    var realErrors = -1
    val status = (outcome match {
      case None => ""
      case Some((verified,errors)) =>
        realErrors = errors-smokeErrors.size
        "Boogie program verifier finished with " + realErrors + " errors and " + smokeTestWarnings + " smoke test warnings."
    })
    
    verificationResult +
    (if (realErrors > 0) "The program did not fully verify; the smoke warnings might be misleading if contradictions are introduced by failing proof attempts of the verification.\n" else "") + 
    smokeResult + (if (smokeResult != "") "\n" else "") +
    status
  }
  
  /** Add smoke assertions for to a program. */
  def smokeProgram(prog: List[TopLevelDecl]): List[TopLevelDecl] = {
    for (decl <- prog) yield decl match {
      case cl: Class =>
        val newmembers = for (m <- cl.members) yield m match {
          case MonitorInvariant(e) => m
          case f@ Field(id, t, ghost) => m
          case method: Method =>
            copyPosition(method, smokeMethod(method))
          case Condition(id, optE) => m
          case Predicate(id, definition) => m
          case Function(id, ins, out, specs, e) => m
          case m: MethodTransform => m
          case CouplingInvariant(ids, e) => m
        }
        copyPosition(cl, Class(cl.classId, cl.parameters, cl.module, newmembers))
      case ch: Channel => ch
    }
  }
  
  /** Add smoke assertions for a method (if necessary). */
  private def smokeMethod(method: Method) = {
    val preassert = initSmokeAssert(method.pos, "Precondition of method " + method.Id + " is equivalent to false.")
    var (newbody, bodyout) = smokeStmt(method.body, Set(preassert))
    val postassert = initSmokeAssert(method.pos, "The end of method " + method.Id + " is unreachable.", bodyout)
    newbody = preassert.chaliceAssert :: newbody ::: postassert.chaliceAssert :: Nil
    Method(method.id, method.ins, method.outs, method.spec, newbody)
  }
  
  /** Add smoke assertions for multiple statements (if necessary). */
  private def smokeStmt(stmts: List[Statement], in: Set[SmokeAssert]): (List[Statement], Set[SmokeAssert]) = {
    var tmp = in
    val newstmts = (for (s <- stmts) yield {
      val (sstmts, sout) = smokeStmt(s, tmp)
      tmp = sout
      copyPosition(s, sstmts)
    }).flatten
    (newstmts, tmp)
  }
  
  /** Add smoke assertions for a statement (if necessary). */
  private def smokeStmt(stmt: Statement, in: Set[SmokeAssert]): (List[Statement], Set[SmokeAssert]) = {
    var out = in
    val result = stmt match {
      // composite statements
      case BlockStmt(ss) =>
        val (smokestmts, blocksmoke) = smokeStmt(ss, in)
        out = blocksmoke
        smokestmts
      case ifs@IfStmt(guard, BlockStmt(then), els) =>
        val thensmoke = initSmokeAssert(ifs.pos, "The begging of the if-branch is unreachable.", in)
        val (thensmokestmts, thenout) = smokeStmt(then, Set(thensmoke))
        out = thenout
        val newthen = thensmoke.chaliceAssert :: thensmokestmts
        val newelse = els match {
          case None =>
            out ++= in
            None
          case Some(s) =>
            val elsesmoke = initSmokeAssert(ifs.pos, "The begging of the else-branch is unreachable.", in)
            val (blocksmokestmts, blockout) = smokeStmt(s, Set(elsesmoke))
            out ++= blockout
            Some(BlockStmt(elsesmoke.chaliceAssert :: blocksmokestmts))
        }
        IfStmt(guard, BlockStmt(newthen), newelse) :: Nil
      case WhileStmt(guard, oldInvs, newInvs, lkch, BlockStmt(body)) =>
        val whilesmoke = initSmokeAssert(stmt.pos, "The begging of the while-body is unreachable.", in)
        val (whilesmokestmts, whileout) = smokeStmt(body, Set(whilesmoke))
        val whileaftersmoke = initSmokeAssert(stmt.pos, "The statements after the while-loop are unreachable.", in)
        val whileendsmoke = initSmokeAssert(stmt.pos, "The end of the while-loop is unreachable.", whileout)
        out = Set(whileaftersmoke)
        val newbody = whilesmoke.chaliceAssert :: whilesmokestmts ::: whileendsmoke.chaliceAssert :: Nil
        WhileStmt(guard, oldInvs, newInvs, lkch, BlockStmt(newbody)) :: whileaftersmoke.chaliceAssert :: Nil
      case Lock(obj, BlockStmt(body), rdLock) =>
        val locksmoke = initSmokeAssert(stmt.pos, "The begging of the lock-block is unreachable.", in)
        val (blocksmokestmts, blockout) = smokeStmt(body, Set(locksmoke))
        out = blockout
        Lock(obj, BlockStmt(locksmoke.chaliceAssert :: blocksmokestmts), rdLock) :: Nil
      case _: RefinementBlock =>
        // TODO
        stmt :: Nil
      
      // assumption
      case Assume(_) =>
        val assumeSmoke = initSmokeAssert(stmt.pos, "Assumption introduces a contradiction.", in)
        out = Set(assumeSmoke)
        stmt :: assumeSmoke.chaliceAssert :: Nil
      
      // simple statements that inhale something
      case Unfold(_) => val (stmts, sout) = smokeSimpleStmt(stmt, in, "unfold"); out = sout; stmts
      case JoinAsync(_, _) => val (stmts, sout) = smokeSimpleStmt(stmt, in, "join"); out = sout; stmts
      case _: Call => val (stmts, sout) = smokeSimpleStmt(stmt, in, "method call"); out = sout; stmts
      case _: SpecStmt => val (stmts, sout) = smokeSimpleStmt(stmt, in, "specification"); out = sout; stmts
      case Receive(_, _, _) => val (stmts, sout) = smokeSimpleStmt(stmt, in, "receive"); out = sout; stmts
      case Acquire(_) => val (stmts, sout) = smokeSimpleStmt(stmt, in, "acquire"); out = sout; stmts
      case RdAcquire(_) => val (stmts, sout) = smokeSimpleStmt(stmt, in, "rd acquire"); out = sout; stmts
      
      // any other simple statements
      case Assert(_) => stmt :: Nil
      case Assign(_, _) => stmt :: Nil
      case FieldUpdate(_, _) => stmt :: Nil
      case _: LocalVar => stmt :: Nil
      case Install(_, _, _) => stmt :: Nil
      case Share(_, _, _) => stmt :: Nil
      case Unshare(_) => stmt :: Nil
      case Release(_) => stmt :: Nil
      case RdRelease(_) => stmt :: Nil
      case Downgrade(_) => stmt :: Nil
      case Free(_) => stmt :: Nil
      case Fold(_) => stmt :: Nil
      case CallAsync(_, _, _, _, _) => stmt :: Nil
      case Send(_, _) => stmt :: Nil
      case _: Signal => stmt :: Nil
      case _: Wait => stmt :: Nil
    }
    (result, out)
  }
  
  /** Helper method to add a smoke assertion after a simple (non-compound)
   *  statement.
   */
  def smokeSimpleStmt(stmt: Statement, in: Set[SmokeAssert], msg: String): (List[Statement], Set[SmokeAssert]) = {
    val smoke = initSmokeAssert(stmt.pos, "The statements after the " + msg + " statement are unreachable.", in)
    (stmt :: smoke.chaliceAssert :: Nil, Set(smoke))
  }
  
  /** Generate an "assert false" with a certain position and a certain error
   *  message. Note: We generate "assert 1!=1" instead of "assert false", as
   *  Boogie seems to perform some weird optimization for false, which does
   *  not generate warnings for all failing assertions (even if the command
   *  line switch /subsumption:0 is used).
   */
  def initSmokeAssert(pos: Position, error: String): SmokeAssert = initSmokeAssert(pos, error, Set(SmokeAssertSentinel))
  def initSmokeAssert(pos: Position, error: String, prev: Set[SmokeAssert]): SmokeAssert = {
    count += 1
    val i = IntLiteral(1); i.typ = IntClass
    val n = Neq(i, i); n.typ = BoolClass
    val assert = Assert(n)
    assert.smokeErrorNr = Some(count)
    assert.pos = pos
    val sm = SmokeAssert(count, pos, error, prev, assert)
    smokeAssertions += count -> sm
    sm
  }
  
  /** Copy the position of an old AST node to a new node (if not already
   *  present).
   */
  private def copyPosition[A <: ASTNode](oldNode: A, newNode: A): A = {
    if (newNode.pos == NoPosition) newNode.pos = oldNode.pos
    newNode
  }
  /** Copy the position from one old AST node to multiple new nodes. */
  private def copyPosition[A <: ASTNode](oldNode: A, newNodes: List[A]): List[A] = {
    for (newNode <- newNodes) yield copyPosition(oldNode, newNode)
  }
}