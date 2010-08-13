//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional
import scala.util.parsing.input.NoPosition
import java.io.File

class Parser extends StandardTokenParsers {

  def parseStdin = phrase(programUnit)(new lexical.Scanner(new PagedSeqReader(PagedSeq fromReader Console.in)))
  def parseFile(file: File) = phrase(programUnit)(new lexical.Scanner(new PagedSeqReader(PagedSeq fromFile file)))
 
  case class PositionedString(v: String) extends Positional

  lexical.reserved += ("class", "ghost", "var", "const", "method", "channel", "condition",
                       "assert", "assume", "new", "this", "reorder",
                       "between", "and", "above", "below", "share", "unshare", "acquire", "release", "downgrade",
                       "lock", "fork", "join", "rd", "acc", "credit", "holds", "old", "assigned",
                       "call", "if", "else", "while", "invariant", "lockchange",
                       "returns", "requires", "ensures", "where",
                       "int", "bool", "false", "true", "null", "waitlevel", "lockbottom",
                       "module", "external",
                       "predicate", "function", "free", "send", "receive",
                       "ite", "fold", "unfold", "unfolding", "in", "forall", "exists",
                       "seq", "nil", "result", "eval", "token",
                       "wait", "signal")
  // todo: can we remove "nil"?
  lexical.delimiters += ("(", ")", "{", "}", "[[", "]]",
                         "<==>", "==>", "&&", "||",
                         "==", "!=", "<", "<=", ">=", ">", "<<", "in", "!in",
                         "+", "-", "*", "/", "%", "!", ".", "..",
                         ";", ":", ":=", ",", "?", "|", "[", "]", "++", "::")

  def programUnit = (classDecl | channelDecl)*
  def Semi = ";" ?
  var currentLocalVariables = Set[String]() // used in the method context

  /**
   * Top level declarations
   */

  def classDecl =
        positioned(("external" ?) ~ ("class" ~> ident) ~ opt("module" ~> ident) ~ "{" ~ (memberDecl*) <~ "}" ^^ {
          case ext ~ id ~ module ~ _ ~ members =>
            val cl = Class(id, Nil, module.getOrElse("default"), members)
            ext match { case None => case Some(t) => cl.IsExternal = true }
            cl
        })
  def channelDecl =
    "channel" ~> ident ~ formalParameters(true) ~ ("where" ~> expression ?) <~ Semi ^^ {
      case id ~ ins ~ None => Channel(id, ins, BoolLiteral(true))
      case id ~ ins ~ Some(e) => Channel(id, ins, e)
    }

  /**
   * Member declarations
   */

  def memberDecl = positioned(fieldDecl | invariantDecl | methodDecl | conditionDecl | predicateDecl | functionDecl)
  def fieldDecl =
        ( "var" ~> idType <~ Semi ^^ { case (id,t) => Field(id.v, t, false) }
        | "ghost" ~> "var" ~> idType <~ Semi ^^ { case (id,t) => Field(id.v, t, true) }
        )
  def invariantDecl = positioned("invariant" ~> expression <~ Semi ^^ MonitorInvariant)
  def methodDecl = {
    currentLocalVariables = Set[String]()
    "method" ~> ident ~ formalParameters(true) ~ ("returns" ~> formalParameters(false) ?) ~
    (methodSpec*) ~ blockStatement ^^ {
      case id ~ ins ~ outs ~ spec ~ body =>
        outs match {
          case None => Method(id, ins, Nil, spec, body)
          case Some(outs) => Method(id, ins, outs, spec, body) }}
  }
  def predicateDecl: Parser[Predicate] =
    ("predicate" ~> ident) ~ ("{" ~> expression <~ "}") ^^ { case id ~ definition => Predicate(id, definition) }
  def functionDecl = 
    ("function" ~> ident) ~ formalParameters(true) ~ (":" ~> typeDecl) ~ (methodSpec*) ~ opt("{" ~> expression <~ "}") ^^ {
      case id ~ ins ~ out ~ specs ~ body => Function(id, ins, out, specs, body)
    }
  def conditionDecl =
    "condition" ~> ident ~ ("where" ~> expression ?) <~ Semi ^^ {
      case id ~ optE => Condition(id, optE) }
  
  def formalParameters(immutable: Boolean) =
    "(" ~> (formalList(immutable) ?) <~ ")" ^^ {
      case None => Nil
      case Some(ids) => ids }
  def formalList(immutable: Boolean) = repsep(formal(immutable), ",")  
  def formal(immutable: Boolean): Parser[Variable] =
    idType ^^ {case (id,t) =>
      currentLocalVariables = currentLocalVariables + id.v;
      new Variable(id.v,t,false,immutable) 
    }
  def Ident = positioned(ident ^^ PositionedString)
  def idType = idTypeOpt ^^ {
      case (id, None) => (id, Type("int", Nil))
      case (id, Some(t)) => (id, t) }
  def idTypeOpt =
    Ident ~ (":" ~> typeDecl ?) ^^ { case id ~ optT => (id, optT) }
  def typeDecl: Parser[Type] =
      positioned(("int" | "bool" | ident | "seq") ~ opt("<" ~> repsep(typeDecl, ",") <~ ">") ^^ { case t ~ parameters => Type(t, parameters.getOrElse(Nil)) }
      | ("token" ~ "<") ~> (typeDecl <~ ".") ~ ident <~ ">" ^^ { case c ~ m => TokenType(c, m) }
      )

  /**
   * Pre and post conditions
   */
  
  def methodSpec =
    positioned( "requires" ~> expression <~ Semi ^^ Precondition
    | "ensures" ~> expression <~ Semi ^^ Postcondition
    | "lockchange" ~> expressionList <~ Semi ^^ LockChange
    )

  /**
   * Statements
   */

  def blockStatement: Parser[List[Statement]] = "{" ~> blockStatementBody <~ "}"
  def blockStatementBody: Parser[List[Statement]] = {
    val prev = currentLocalVariables
    (statement*) ^^ {
      case x => currentLocalVariables = prev; x }
  }
  def statement: Parser[Statement] =
    positioned( "assert" ~> expression <~ Semi ^^ Assert
    | "assume" ~> expression <~ Semi ^^ Assume
    | blockStatement ^^ BlockStmt
    | "var" ~> localVarStmt(false, false)
    | "const" ~> localVarStmt(true, false)
    | "ghost" ~> "const" ~> localVarStmt(true, true)
    | "ghost" ~> "var" ~> localVarStmt(false, true)
    | "call" ~> callStmt
    | "if" ~> ifStmtThen
    | "while" ~> "(" ~> expression ~ ")" ~ loopSpec ~ blockStatement ^^ {
        case guard ~ _ ~ lSpec ~ body =>
          lSpec match { case (invs,lkch) => WhileStmt(guard, invs, lkch, BlockStmt(body)) }}
    | "reorder" ~> expression ~ (installBounds ?) <~ Semi ^^ {
        case obj ~ None => Install(obj, List(), List())
        case obj ~ Some(bounds) => Install(obj, bounds._1, bounds._2) }
    | "share" ~> expression ~ (installBounds ?) <~ Semi ^^ {
        case obj ~ None => Share(obj, List(), List())
        case obj ~ Some(bounds) => Share(obj, bounds._1, bounds._2) }
    | "unshare" ~> expression <~ Semi ^^ Unshare
    | "acquire" ~> expression <~ Semi ^^ Acquire
    | "release" ~> expression <~ Semi ^^ Release
    | "lock" ~> "(" ~> expression ~ ")" ~ blockStatement ^^ {
        case e ~ _ ~ b => Lock(e, BlockStmt(b), false) }
    | "[[" ~> blockStatementBody <~ "]]" ^^ {
        case b => Lock(ExplicitThisExpr(), BlockStmt(b), false) }
    | "rd" ~>
        ( "lock" ~> "(" ~> expression ~ ")" ~ blockStatement ^^ {
            case e ~ _ ~ b => Lock(e, BlockStmt(b), true) }
        | "acquire" ~> expression <~ Semi ^^ RdAcquire
        | "release" ~> expression <~ Semi ^^ RdRelease
        )
    | "downgrade" ~> expression <~ Semi ^^ Downgrade
    | "free" ~> expression <~ Semi ^^ Free
    | Ident ~ ":=" ~ Rhs <~ Semi ^^ {
        case lhs ~ _ ~ rhs =>
          if (currentLocalVariables contains lhs.v) {
            val varExpr = VariableExpr(lhs.v); varExpr.pos = lhs.pos;
            Assign(varExpr, rhs)
          } else {
            val implicitThis = ImplicitThisExpr();
            val select = MemberAccess(implicitThis, lhs.v);
            implicitThis.pos = lhs.pos;
            select.pos = lhs.pos;
            FieldUpdate(select, rhs)
          }}
    | selectExprFerSure ~ ":=" ~ Rhs <~ Semi ^^ {
        case lhs ~ _ ~ rhs => FieldUpdate(lhs, rhs) }
    | ("fold" ~> expression <~ Semi) ^? { 
        case pred: MemberAccess => Fold(Access(pred, Full))
        case perm: Access => Fold(perm)
      }
    | ("unfold" ~> expression <~ Semi) ^? { 
        case pred: MemberAccess => Unfold(Access(pred, Full))
        case perm: Access => Unfold(perm)
      }
    | ("fork") ~> callSignature ^? ({
        case None ~ target ~ args =>
          val (receiver, name) = target match { 
            case VariableExpr(id) => (new ImplicitThisExpr, id)
            case MemberAccess(obj, id) => (obj, id) 
          }
          CallAsync(false, null, receiver, name, args)
        case Some(List(tok)) ~ target ~ args => 
          val (receiver, name) = target match { 
            case VariableExpr(id) => (new ImplicitThisExpr, id)
            case MemberAccess(obj, id) => (obj, id) 
          }
          if (currentLocalVariables contains tok.id) {
            CallAsync(false, tok, receiver, name, args)
          } else {
            currentLocalVariables = currentLocalVariables + tok.id;
            CallAsync(true, tok, receiver, name, args)
          }
        }, t => "fork statement cannot take more than 1 left-hand side")
    | (("join") ~> ( identList <~ ":=" ?)) ~ expression <~ Semi ^^ 
        { case results ~ token => JoinAsync(ExtractList(results), token) }
    | "wait" ~> memberAccess <~ Semi ^^ {
        case MemberAccess(obj, id) => Wait(obj, id) }
    | "signal" ~> ("forall" ?) ~ memberAccess <~ Semi ^^ {
        case None ~ MemberAccess(obj, id) => Signal(obj, id, false)
        case _ ~ MemberAccess(obj, id) => Signal(obj, id, true) }
    | ("send" ~> suffixPlusExpr into { e => e match {
        case FunctionApplication(obj, name, args) => Semi ^^^ Send(MemberAccess(obj,name), args)
        case e => "(" ~> expressionList <~ ")" <~ Semi ^^ { case args => Send(e, args) }}})
    | ("send" ~> atom into { e => e match {
        case fa@FunctionApplication(ImplicitThisExpr(), name, args) => Semi ^^^ {val va = VariableExpr(name); va.pos = fa.pos; Send(va, args)}
        case e => "(" ~> expressionList <~ ")" <~ Semi ^^ { case args => Send(e, args) }}})
    | "receive" ~> (identList <~ ":=" ?) ~ expression <~ Semi ^^ {
        case outs ~ e =>
          val lhs = ExtractList(outs)
          Receive(declareImplicitLocals(lhs), e, lhs) }
    )
  def localVarStmt(const: Boolean, ghost: Boolean) =
    ( (rep1sep(idType, ",") into {decls:List[(PositionedString,Type)] => {
        val locals = for ((id, t) <- decls; if (! currentLocalVariables.contains(id.v))) yield {
          currentLocalVariables = currentLocalVariables + id.v
          new Variable(id.v, t, ghost, const)
        }
        val lhs = for ((id, _) <- decls) yield {
          val v = VariableExpr(id.v); v.pos = id.pos; v
        }
        "[" ~> expression <~ "]" <~ Semi ^^ {e => SpecStmt(lhs, locals, e)};
     } })
    | idTypeOpt ~ (":=" ~> Rhs ?) <~ Semi ^^ {
        case (id,optT) ~ rhs =>
          currentLocalVariables = currentLocalVariables + id.v
          LocalVar(id.v,
                   optT match {
                     case Some(t) => t
                     case None =>
                       // do a cheap (and hokey) type inference of the RHS
                       rhs match {
                         case Some(NewRhs(tid, _, _, _)) => Type(tid, Nil)
                         case Some(BoolLiteral(b)) => Type("bool", Nil)
                         case Some(x:BinaryExpr) if x.ResultType != null => new Type(x.ResultType);
                         case _ => Type("int", Nil)
                       }
                   },
                   const, ghost, rhs) }
    )
  def ifStmtThen: Parser[IfStmt] =
    "(" ~> expression ~ ")" ~ blockStatement ~ ("else" ~> ifStmtElse ?) ^^ {
      case guard ~ _ ~ thenClause ~ elseClause => IfStmt(guard, BlockStmt(thenClause), elseClause) }
  def ifStmtElse =
    ( "if" ~> ifStmtThen
    | statement
    )
  def loopSpec: Parser[(List[Expression], List[Expression])] =
    (loopSpecX *) ^^ {
      case pp => (pp :\ (List[Expression](), List[Expression]())) ( (p,list) =>
        (p,list) match {
          case ((null,ee),(e0,e1)) => (e0, ee ++ e1)
          case ((e,ee),(e0,e1)) => (e :: e0, ee ++ e1)
        })
    }
  def loopSpecX =
    ( "invariant" ~> expression <~ Semi ^^ { case e => (e,Nil) }
    | "lockchange" ~> expressionList <~ Semi ^^ { case ee => (null,ee) }
    )
  def declareImplicitLocals(lhs: List[VariableExpr]) =
    for (v <- lhs) yield
      if (currentLocalVariables contains v.id)
        false
      else {
        currentLocalVariables = currentLocalVariables + v.id
        true
      }
  def callStmt =
    callSignature ^? ({
      case outs ~ VariableExpr(id) ~ args =>
        val lhs = ExtractList(outs)
        Call(declareImplicitLocals(lhs), lhs, new ImplicitThisExpr, id, args)
      case outs ~ MemberAccess(obj,id) ~ args =>
        val lhs = ExtractList(outs)
        Call(declareImplicitLocals(lhs), lhs, obj, id, args)
    }, t => "bad call statement")
  def callSignature =
    (identList <~ ":=" ?) ~ callTarget ~ expressionList <~ ")" <~ Semi
  def callTarget =  // returns a VariableExpr or a FieldSelect
      ( ident <~ "(" ^^ VariableExpr
      | selectExprFerSure <~ "("
      )
  def memberAccess =  // returns a MemberAccess
      ( selectExprFerSure
      | ident ^^ { case id => MemberAccess(ImplicitThisExpr(), id) }
      )
  def ExtractList[T](a: Option[List[T]]): List[T] = a match {
    case None => Nil
    case Some(list) => list }
  def identList =
    ( Ident ^^ { case t => val v = VariableExpr(t.v); v.pos = t.pos; v }) ~
    (("," ~> Ident ^^ { case t => val v = VariableExpr(t.v); v.pos = t.pos; v }) *) ^^ { case e ~ ee => e::ee }
  def Rhs : Parser[RValue] =
    positioned(
      "new" ~> ident ~ opt("{" ~> repsep(FieldInit, ",") <~ "}") ~ opt(installBounds) ^^ {
        case id ~ None ~ None => NewRhs(id, Nil, Nil, Nil)
        case id ~ Some(inits) ~ None => NewRhs(id, inits, Nil, Nil)
        case id ~ None ~ Some(bounds) => NewRhs(id, Nil, bounds._1, bounds._2)
        case id ~ Some(inits) ~ Some(bounds) => NewRhs(id, inits, bounds._1, bounds._2)
      }
    | expression
    )
  def FieldInit: Parser[Init] =
    positioned( (ident <~ ":=") ~ expression ^^ { case id ~ e => Init(id, e) } )
  def installBounds: Parser[(List[Expression], List[Expression])] =
    ( "between" ~> expressionList ~ "and" ~ expressionList ^^ { case l ~ _ ~ u => (l,u) }
    | "below" ~> expressionList ~ ("above" ~> expressionList ?) ^^ {
        case u ~ None => (Nil,u)
        case u ~ Some(l) => (l,u) }
    | "above" ~> expressionList ~ ("below" ~> expressionList ?) ^^ {
        case l ~ None => (l,Nil)
        case l ~ Some(u) => (l,u) }
    )

  /**
   * Expressions
   */
  
  def expressionList =
    repsep(expression, ",")
  def expression = positioned(iteExpr)

  def iteExpr: Parser[Expression] =
        positioned(iffExpr ~ (("?" ~> iteExpr) ~ (":" ~> iteExpr) ?) ^^ {
          case e ~ None => e
          case e0 ~ Some(e1 ~ e2) => IfThenElse(e0,e1,e2) })
  def iffExpr: Parser[Expression] =
        positioned(implExpr ~ ("<==>" ~> iffExpr ?) ^^ {
          case e ~ None => e
          case e0 ~ Some(e1) => Iff(e0,e1) })
  def implExpr: Parser[Expression] =
        positioned(logicalExpr ~ ("==>" ~> implExpr ?) ^^ {
          case e ~ None => e
          case e0 ~ Some(e1) => Implies(e0,e1) })
  def logicalExpr =
        positioned(cmpExpr ~ (( ("&&" ~ cmpExpr +) | ("||" ~ cmpExpr +) )?) ^^ {
          case e ~ None => e
          case e0 ~ Some(rest) => (rest foldLeft e0) {
            case (a, "&&" ~ b) => And(a,b)
            case (a, "||" ~ b) => Or(a,b) }})
  def cmpExpr = 
        positioned(concatExpr ~ ((CompareOp ~ concatExpr)?) ^^ {
          case e ~ None => e
          case e0 ~ Some("==" ~ e1) => Eq(e0,e1)
          case e0 ~ Some("!=" ~ e1) => Neq(e0,e1)
          case e0 ~ Some("<" ~ e1) => Less(e0,e1)
          case e0 ~ Some("<=" ~ e1) => AtMost(e0,e1)
          case e0 ~ Some(">=" ~ e1) => AtLeast(e0,e1)
          case e0 ~ Some(">" ~ e1) => Greater(e0,e1)
          case e0 ~ Some("<<" ~ e1) => LockBelow(e0,e1)
          case e0 ~ Some("in" ~ e1) => Contains(e0, e1)
          case e0 ~ Some("!in" ~ e1) => val c = Contains(e0, e1); c.pos = e0.pos; Not(c)
        })
  def CompareOp = "==" | "!=" | "<" | "<=" | ">=" | ">" | "<<" | "in" | "!in"
  def concatExpr =
        positioned(addExpr ~ ("++" ~> addExpr *) ^^ {
          case e0 ~ rest => (rest foldLeft e0) {
            case (a, b) => Append(a, b) }})
  def addExpr =
        positioned(multExpr ~ (AddOp ~ multExpr *) ^^ {
          case e0 ~ rest => (rest foldLeft e0) {
            case (a, "+" ~ b) => Plus(a,b)
            case (a, "-" ~ b) => Minus(a,b) }})
  def AddOp = "+" | "-"
  def multExpr: Parser[Expression] =
        unaryExpr ~ (MulOp ~ unaryExpr *) ^^ {
          case e0 ~ rest => (rest foldLeft e0) {
            case (a, "*" ~ b) => Times(a,b)
            case (a, "/" ~ b) => Div(a,b)
            case (a, "%" ~ b) => Mod(a,b) }}
  def MulOp = "*" | "/" | "%"
  def unaryExpr: Parser[Expression] =
        ( "!" ~> unaryExpr ^^ Not
        | "-" ~> unaryExpr ^^ { Minus(IntLiteral(0),_) }
        | suffixExpr
        )
  def suffixExpr =
    atom ~ (suffixThing *) ^^ {
      case e ~ sfxs => sfxs.foldLeft(e) { (t, a) => val result = a(t); result.pos = t.pos; result } }
  def suffixPlusExpr =
    atom ~ (suffixThing +) ^^ {
      case e ~ sfxs => sfxs.foldLeft(e) { (t, a) => val result = a(t); result.pos = t.pos; result } }
  def suffixThing: Parser[(Expression => Expression)] =
    ( "[" ~> expression <~ "]" ^^ { case e1 => { e0: Expression => At(e0, e1) }} 
    | "[" ~> expression <~ (".." ~ "]") ^^ { case e1 => { e0: Expression => Drop(e0, e1)}} 
    | "[" ~> ".." ~> expression <~ "]" ^^ { case e1 => { e0: Expression => Take(e0, e1)}}
    | "[" ~> (expression <~ "..") ~ expression <~ "]" ^^ {
        case e1 ~ e2 => {e0: Expression => val tak = Take(e0, e2); tak.pos = e0.pos; Drop(tak, e1)} }
    | "." ~> ident ~ opt("(" ~> expressionList <~ ")") ^^ {
        case name ~ None => { e0: Expression => MemberAccess(e0, name) }
        case name ~ Some(es) => { e0: Expression => FunctionApplication(e0, name, es) } }
    | "." ~> "acquire" ~> exprBody ^^ { case eb => { e0: Expression => Eval(AcquireState(e0), eb) }}
    | "." ~> "release" ~> exprBody ^^ { case eb => { e0: Expression => Eval(ReleaseState(e0), eb) }}
    | "." ~> "fork" ~> (callTarget ~ expressionList <~ ")") ~ exprBody ^^ {
        case MemberAccess(obj,id) ~ args ~ eb => { e0: Expression => Eval(CallState(e0, obj, id, args), eb) }}
    )
  def exprBody =
    "{" ~> expression <~ "}"

  def selectExprFerSure: Parser[MemberAccess] =
    positioned(atom ~ "." ~ ident ~ ("." ~> ident *) ^^ {
      case e ~ _ ~ field ~ moreFields =>
        (moreFields foldLeft MemberAccess(e,field)) { (target, f) =>
          val result = MemberAccess(target, f); result.pos = target.pos; result }})
  def selectExprFerSureX: Parser[MemberAccess] =
    positioned(atom ~ identOrSpecial ~ ("." ~> ident *) ^^ {
      case e ~ field ~ moreFields =>
        (moreFields foldLeft MemberAccess(e,field)) { (target, f) =>
          val result = MemberAccess(target, f); result.pos = target.pos; result }})
  def identOrSpecial: Parser[String] =
    ( "." ~> ident ^^ { case s => s }
    | "." ~> "acquire" ^^^ "acquire"
    | "." ~> "release" ^^^ "release"
    | "." ~> "fork" ^^^ "fork"
    | "." ~> "*" ^^^ "*"
    | "["~"*"~"]"~"."~"*" ^^^ "[*].*"
    | "["~"*"~"]" ^^^ "[*]"
    )

  def atom : Parser[Expression] =
    positioned(
      numericLit ^^ { case n => IntLiteral(n.toInt) }
    | "false" ^^^ BoolLiteral(false)
    | "true" ^^^ BoolLiteral(true)
    | "null" ^^^ NullLiteral()
    | "waitlevel" ^^^ MaxLockLiteral()
    | "lockbottom" ^^^ LockBottomLiteral()
    | "this" ^^^ ExplicitThisExpr()
    | "result" ^^^ Result()
    | positioned(Ident) ~ opt("(" ~> expressionList <~ ")") ^^ {
        case id ~ None =>
          val r =
          if (currentLocalVariables contains id.v) {
            VariableExpr(id.v)
          } else {
            val implicitThis = ImplicitThisExpr(); implicitThis.pos = id.pos
            MemberAccess(implicitThis, id.v)
          }
          r.pos = id.pos; r
        case id ~ Some(args) =>
          val implicitThis = ImplicitThisExpr(); implicitThis.pos = id.pos
          val r = FunctionApplication(implicitThis, id.v, args)
          r.pos = id.pos; r
        }
    | "rd" ~> "(" ~>
      ( (Ident ^^ (e => { val result = MemberAccess(ImplicitThisExpr(),e.v); result.pos = e.pos; result})) ~ rdPermArg <~ ")"
      | selectExprFerSureX ~ rdPermArg <~ ")"
      ) ^^ {
        case MemberAccess(obj, "*") ~ p => AccessAll(obj, p);
        case MemberAccess(obj, "[*].*") ~ p => AccessSeq(obj, None, p);
        case MemberAccess(MemberAccess(obj, "[*]"), f) ~ p => AccessSeq(obj, Some(MemberAccess(At(obj, IntLiteral(0)), f)), p);
        case e ~ p => Access(e, p)
      }
    | "acc" ~> "(" ~>
      ( (Ident ^^ (e => { val result = MemberAccess(ImplicitThisExpr(),e.v); result.pos = e.pos; result} )) ~ accPermArg <~ ")"
      | selectExprFerSureX ~ accPermArg <~ ")"
      ) ^^ {
        case MemberAccess(obj, "*") ~ p => AccessAll(obj, p);
        case MemberAccess(obj, "[*].*") ~ p => AccessSeq(obj, None, p);
        case MemberAccess(MemberAccess(obj, "[*]"), f) ~ p => AccessSeq(obj, Some(MemberAccess(At(obj, IntLiteral(0)), f)), p);
        case e ~ p => Access(e, p)
      }
    | "credit" ~> "(" ~> expression ~ ("," ~> expression ?) <~ ")" ^^ {
        case ch ~ n => Credit(ch, n) }
    | "holds" ~> "(" ~> expression <~ ")" ^^ Holds
    | "rd" ~> "holds" ~> "(" ~> expression <~ ")" ^^ RdHolds
    | "assigned" ~> "(" ~> ident <~ ")" ^^ Assigned
    | "old" ~> "(" ~> expression <~ ")" ^^ Old
    | ("unfolding" ~> suffixExpr <~ "in") ~ expression ^? { 
        case (pred: MemberAccess) ~ e => val acc = Access(pred, Full); acc.pos = pred.pos; Unfolding(acc, e)
        case (perm: Access) ~ e => Unfolding(perm, e)
      }
    | "|" ~> expression <~ "|" ^^ Length
    | ("eval" ~ "(") ~> (evalstate <~ ",") ~ (expression <~ ")") ^^ { case h ~ e => Eval(h, e) }
    | ("ite" ~> "(" ~> expression <~ ",") ~ (expression <~ ",") ~ (expression <~ ")") ^^ {
        case con ~ then ~ els => IfThenElse (con, then, els) }
    | "(" ~> expression <~ ")"
    | quantifierType
    | quantifierSeq
    | ("[" ~> expression) ~ (".." ~> expression <~ "]") ^^ { case from ~ to => Range(from, to) }
    | ("nil" ~> "<") ~> (typeDecl <~ ">") ^^ EmptySeq
    | ("[" ~> expressionList <~ "]") ^^ { case es => ExplicitSeq(es) }
    )

  def quantifierSeq: Parser[Quantification] =
    (quant ~ repsep(ident, ",")) into {case q ~ is => quantifierSeqBody(q, is)}
  def quantifierSeqBody(q: Quant, is: List[String]) : Parser[Quantification] =
    (("in" ~> expression <~ "::") ~ (exprWithLocals(is))) ^^
      { case seq ~ e =>
        currentLocalVariables = currentLocalVariables -- is;
        SeqQuantification(q, is, seq, e);
      }
  def quantifierType: Parser[Quantification] =
    (quant ~ repsep(ident, ",")) into {case q ~ is => quantifierTypeBody(q, is)}
  def quantifierTypeBody(q: Quant, is: List[String]) : Parser[Quantification] =
    ((":" ~> typeDecl <~ "::") ~ (exprWithLocals(is))) ^^
      { case t ~ e =>
        currentLocalVariables = currentLocalVariables -- is;
        TypeQuantification(q, is, t, e);
      }
  def quant: Parser[Quant] =
    ( "forall" ^^^ Forall | "exists" ^^^ Exists)

  def exprWithLocals(i: List[String]) : Parser[Expression] = {
    currentLocalVariables = currentLocalVariables ++ i;
    val result = ((expression) ^^ { case e => e});
    result
  }

  def evalstate: Parser[EvalState] =
    (suffixExpr <~ ".") into { e =>
      ( "acquire" ^^^ AcquireState(e)
      | "release" ^^^ ReleaseState(e)
      | "fork" ~> callTarget ~ expressionList <~ ")" ^^ {
          case MemberAccess(obj,id) ~ args => CallState(e, obj, id, args) }
      )}

  def rdPermArg : Parser[Read] =
      opt( "," ~> "*" ^^^ Star
      | "," ~> expression ^^ { case e => Epsilons(e) }) ^^ { case None => Epsilon; case Some(p) => p}

  def accPermArg : Parser[Write] =
      opt( "," ~> expression ^^ { case e => Frac(e) }) ^^ { case None => Full; case Some(p) => p}
}
