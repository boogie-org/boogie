
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

  /** Map from error message ID's to their position and error message */
  private var errorMessages: scala.collection.SortedMap[Int, (Position, String)] = scala.collection.SortedMap()
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
    val smokeTestAssertions = errorMessages.size
    val smokeTestWarnings = smokeTestAssertions - smokeErrors.size
    
    val smokeResult = {
      var t = "";
      for ((errNr, (pos, msg)) <- errorMessages) yield {
        if (!smokeErrors.contains(errNr)) {
          t += "  " + pos + ": " + msg + "\n"
        }
      }
      t
    }
    
    verificationResult +
    smokeResult + (if (smokeResult != "") "\n" else "") +
    (outcome match {
      case None => ""
      case Some((verified,errors)) =>
        "Boogie program verifier finished with " + (errors-smokeErrors.size) + " errors and " + smokeTestWarnings + " smoke test warnings."
    })
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
    var newbody = smokeStmt(method.body)
    val preassert = smokeAssert(method.pos, "Precondition of method " + method.Id + " is equivalent to false.")
    val postassert = smokeAssert(method.pos, "The end of method " + method.Id + " is unreachable.")
    newbody = preassert :: newbody ::: postassert :: Nil
    Method(method.id, method.ins, method.outs, method.spec, newbody)
  }
  
  /** Add smoke assertions for multiple statements (if necessary). */
  private def smokeStmt(stmts: List[Statement]): List[Statement] = {
    (for (s <- stmts) yield copyPosition(s, smokeStmt(s))).flatten
  }
  
  /** Add smoke assertions for a statement (if necessary). */
  private def smokeStmt(stmt: Statement): List[Statement] = {
    stmt match {
      case Assume(_) => stmt :: smokeAssert(stmt.pos, "Assumption might introduce a contradiction.") :: Nil
      case BlockStmt(ss) => smokeStmt(ss)
      case ifs@IfStmt(guard, BlockStmt(then), els) =>
        val newthen = smokeStmt(then) ::: smokeAssert(ifs.pos, "The end of the if-branch is unreachable.") :: Nil
        val newelse = els match {
          case None => None
          case Some(s) => Some(BlockStmt(smokeStmt(s) ::: smokeAssert(ifs.pos, "The end of the else-branch is unreachable.") :: Nil))
        }
        IfStmt(guard, BlockStmt(newthen), newelse) :: Nil
      case WhileStmt(guard, oldInvs, newInvs, lkch, BlockStmt(body)) =>
        val newbody = smokeStmt(body) ::: smokeAssert(stmt.pos, "The end of the while-body is unreachable.") :: Nil
        WhileStmt(guard, oldInvs, newInvs, lkch, BlockStmt(newbody)) :: Nil
      case Lock(obj, BlockStmt(body), rdLock) =>
        Lock(obj, BlockStmt(smokeStmt(body)), rdLock) :: Nil
      case _: RefinementBlock => stmt :: Nil
      
      case Assert(_) => stmt :: Nil
      case Assign(_, _) => stmt :: Nil
      case FieldUpdate(_, _) => stmt :: Nil
      case _: LocalVar => stmt :: Nil
      case _: SpecStmt => stmt :: Nil
      case _: Call => stmt :: Nil
      case Install(_, _, _) => stmt :: Nil
      case Share(_, _, _) => stmt :: Nil
      case Unshare(_) => stmt :: Nil
      case Acquire(_) => stmt :: Nil
      case Release(_) => stmt :: Nil
      case RdAcquire(_) => stmt :: Nil
      case RdRelease(_) => stmt :: Nil
      case Downgrade(_) => stmt :: Nil
      case Free(_) => stmt :: Nil
      case Fold(_) => stmt :: Nil
      case Unfold(_) => stmt :: Nil
      case CallAsync(_, _, _, _, _) => stmt :: Nil
      case JoinAsync(_, _) => stmt :: Nil
      case Send(_, _) => stmt :: Nil
      case Receive(_, _, _) => stmt :: Nil
      case _: Signal => stmt :: Nil
      case _: Wait => stmt :: Nil
    }
  }
  
  /** Generate an "assert false" with a certain position and a certain error
   *  message. Note: We generate "assert 1!=1" instead of "assert false", as
   *  Boogie seems to perform some weird optimization for false, which does
   *  not generate warnings for all failing assertions (even if the command
   *  line switch /subsumption:0 is used).
   */
  private def smokeAssert(pos: Position, error: String) = {
    count += 1
    errorMessages += count -> (pos, error)
    val assert = Assert(Neq(IntLiteral(1), IntLiteral(1)))
    assert.smokeErrorNr = Some(count)
    assert.pos = pos
    assert
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