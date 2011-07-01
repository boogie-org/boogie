//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
class ChaliceToCSharp {
    
  def convertProgram(decls: List[TopLevelDecl]): String = {
    "using Chalice;" + nl + nl +
    rep(decls map convertTopLevelDecl)
  }

  def convertTopLevelDecl(decl: TopLevelDecl): String = {
    decl match {
      case cl: Class => convertClass(cl)
      case ch: Channel => convertChannel(ch)
    }
  }
  
  def convertChannel(ch: Channel): String = {
    "public class " + ch.channelId + " {" + nl +
    indentMore {
      indent + "class " + ch.channelId + "_args " + "{" + nl + 
      indentMore {
        repsep(ch.parameters map { variable => indent + "internal " + convertType(variable.t) + " " + variable.id + ";"}, nl)
      } + nl + indent + "}" + nl +
      indent + "ChannelBuffer<" + ch.channelId + "_args" + ">" + " buffer = new ChannelBuffer<" + ch.channelId + "_args" + ">();" + nl +
      indent + "public void Send(" + repsep(ch.parameters map { variable => convertType(variable.t) + " " + variable.id }, ", ") + ") {" + nl +
      indentMore {
        indent + ch.channelId + "_args " + "entry = new " + ch.channelId + "_args" + "();" + nl + 
        repsep(ch.parameters map { p => indent + "entry." + p.id + " = " + p.id + ";"}, nl) + nl +
        indent + "buffer.Add(entry);" + nl
      } + 
      indent + "}" + nl + 
      indent + "public void Receive(" + repsep(ch.parameters map { variable => "out " + convertType(variable.t) + " " + variable.id }, ", ") + ") {" + nl +
      indentMore {
        indent + ch.channelId + "_args " + "entry = buffer.Remove();" + nl +
        repsep(ch.parameters map { p => indent + p.id + " = entry." + p.id + ";"}, nl) + nl
      } +
      indent + "}" + nl
    } +
    "}" + nl + nl
  }
  
  def convertClass(cl: Class): String = if (cl.IsExternal) "" else {
    "public class " + cl.id + " {" + nl +
    indentMore { indent + "public " + cl.id + "() " + "{" + nl + indent + "}" } + nl + nl +
    (if(0 < cl.Fields.length) {
      indentMore { indent + "public " + cl.id + "(" + repsep(cl.Fields map { f => convertType(f.typ) + " " + f.Id }, ", ") + ") " + "{" + nl +
      indentMore { rep(cl.Fields map { f => indent + "this." + f.Id + " = " + f.Id + ";" + nl}) } + 
      indent + "}" } + nl + nl 
    } else  "") +
    indentMore { repsep(cl.members map convertMember, nl) } +
    "}" + nl + nl
  }
  
  def convertMember(member: Member): String = {
    member match {
      case Field(id, tp, false) =>
        indent + "public " + convertType(tp) + " " + id + ";" + nl
      case meth@Method(id, ins, outs, spec, body) =>
        var csharpmain = if(id.equals("Start") && ins.length == 0 && outs.length == 0) {
          indent + "public static void Main() { " + nl +
          indentMore { 
            indent + meth.Parent.id + " newObject = new " + meth.Parent.id + "();" + nl +
            indent + "newObject.Start();" + nl
          } + 
          indent + "}" + nl + nl
        } else { "" };
        var params = repsep(ins map { variable => convertType(variable.t) + " " + variable.id }, ", ") + (if(ins.length > 0 && outs.length > 0) ", " else "") +
        repsep(outs map { variable => "out " + convertType(variable.t) + " " + variable.id }, ", ");
        csharpmain + 
        indent + "public " + "void " + id + "(" + params + ") " + "{" + nl +
        indentMore { 
          rep(outs map { x => indent + x.id + " = " + defaultValue(x.t) + ";" + nl } ) + 
          rep(body map convertStatement) 
        } +
        indent + "}" + nl + nl +
        indent + "public delegate " + "void " + id + "_delegate" + "(" + params + ");"  + nl + nl +
        indent + "public class " + "Token_" + id + " { " + nl + 
        (indentMore {
          indent + "public " + id + "_delegate " + "del;" + nl +
          indent + "public " + "System.IAsyncResult " + "async;" + nl +
          (rep(outs map { o: Variable => indent + "public " + convertType(o.t) + " " + o.id + ";" + nl  }))
        }) +
        indent + "}"  + nl
      case Function(id, ins, out, spec, definition) if definition.isDefined =>
        indent + "public " + convertType(out) + " " + id + "(" + 
         repsep(ins map { variable => convertType(variable.t) + " " + variable.id }, ", ") + 
         ") " + "{" + nl +
         indentMore { indent + "return " + convertExpression(definition.get) + ";" + nl } +
        indent +  "}" + nl
      case MonitorInvariant(_) => indent + "// monitor invariant" + nl
      case Predicate(_, _) => indent + "//predicate" + nl
	  case _ => throw new NotSupportedException("unsupportet construct")
    }
  }

  def convertStatement(statement: Statement): String = {
    statement match {
      case Assert(e) => indent + "// assert" + nl
      case Assume(e) => indent + {e match {
        case BoolLiteral(false) => "assert false;" + nl // abort since we made a wrong choice...
        case _ => // TODO: what to do with assume expressions that contain old, result, ghost variables, etc.
          "// assume" + nl}}
      case BlockStmt(ss) => indent + "{" + nl + (indentMore { rep(ss map convertStatement) }) + indent + "}" + nl
      case IfStmt(guard, thn, els) => indent + "if (" + convertExpression(guard) + ")" + nl + convertStatement(thn) + 
        (if(els.isDefined) (indent + "else" + nl + convertStatement(els.get)) else { "" }) + nl
      case LocalVar(v, rhs) =>
        indent + convertType(v.t) + " " + v.id + " = " +
        (if(rhs.isDefined) convertExpression(rhs.get) else defaultValue(v.t)) + 
        ";" + nl
      case FieldUpdate(MemberAccess(target, f), rhs) =>
        indent + convertExpression(target) + "." + f + " = " + convertExpression(rhs) + ";" + nl
      case Assign(VariableExpr(x), rhs) =>
        indent + x + " = " + convertExpression(rhs) + ";" + nl
      case WhileStmt(guard, _, _, _, body) =>
        indent + "while (" + convertExpression(guard) + ")" + nl + convertStatement(body) + nl
      case c@Call(_, lhs, target, id, args) =>
        declareLocals(c.locals) +
        indent + convertExpression(target) + "." + id + "(" + 
          repsep(args map convertExpression, ", ") + 
          (if(args.length > 0 && lhs.length > 0) ", " else "") +
          repsep(lhs map { l => "out " + convertExpression(l) }, ", ") +
          ")" + ";" + nl
      case Install(_, _, _) => indent + "// install" + nl
      case Share(_, _, _) => indent + "// share" + nl
      case Unshare(_) => indent + "// unshare" + nl
      case Downgrade(_) => indent + "// downgrade" + nl
      case Acquire(obj) => indent + "System.Threading.Monitor.Enter(" + convertExpression(obj) + ")" + ";" + nl
      case Release(obj) => indent + "System.Threading.Monitor.Exit(" + convertExpression(obj) + ")" + ";" + nl
      case Lock(obj, body, false) => indent + "lock(" + convertExpression(obj) + ") " + nl + convertStatement(body) + nl
      case Free(_) => indent + "// free" + nl   
      case Fold(_) => indent + "// fold" + nl  
      case Unfold(_) => indent + "// unfold" + nl    
      case RdAcquire(obj) => assert(false); ""
      case RdRelease(obj) => assert(false); ""
      case Lock(_, _, true) => assert(false); ""
      case ca@CallAsync(declaresLocal, lhs, obj, id, args) => 
        val tokenName = if(declaresLocal) lhs.id else { uniqueInt += 1; "tok_" + uniqueInt };
        val call = convertExpression(obj) + "." + id;
        val tokenClass = ca.m.Parent.id + ".Token_" + id;
        val delegateName = ca.m.Parent.id + "." + id + "_delegate";
        indent + tokenClass + " " + tokenName + " = new " + tokenClass + "();" + nl + 
        indent + tokenName + "." + "del" + " = new " + delegateName + "(" + call + ");" + nl +
        indent + tokenName + "." + "async" + " = " + tokenName + "." + "del" + "." + "BeginInvoke(" + repsep(args map convertExpression, ", ") +
        (if(args.length > 0 && ca.m.outs.length > 0) ", " else "") + repsep(ca.m.outs map { o => "out " + tokenName + "." + o.id }, ", ") +
        (if(args.length > 0 || ca.m.outs.length > 0) ", " else "") + "null, null" +
        ");" + nl
      case ja@JoinAsync(lhs, token) =>
        indent + convertExpression(token) + "." + "del.EndInvoke(" + 
        repsep(lhs map { x => "out " + x.id}, ", ") +
        (if(lhs.length > 0) ", " else "") + convertExpression(token) + "." + "async" + ");" + nl
      case s@Send(ch, args) =>
        indent + convertExpression(ch) + ".Send(" + repsep(args map convertExpression, ", ") + ")" + ";" + nl
      case r@Receive(_, ch, outs) =>
        declareLocals(r.locals) +
        indent + convertExpression(ch) + ".Receive(" + repsep(outs map { out => "out " + convertExpression(out)}, ", ") + ")" + ";" + nl
	  case _ => throw new NotSupportedException("unsupportet construct")
    }
  }
  
  def declareLocals(locals: List[Variable]) = {
    var s = ""
    for (v <- locals)
      s = s + indent + convertType(v.t) + " " + v.id + ";" + nl
    s
  }

  def convertExpression(expression: RValue): String = {
    expression match {
      case IntLiteral(n) => "" + n
      case BoolLiteral(b) => "" + b
      case NullLiteral() => "null"
      case th: ThisExpr => "this"
      case VariableExpr(id) => id
      case MemberAccess(target, f) => convertExpression(target) + "." + f
      case newrhs@NewRhs(c, initialization, lower, upper) => 
        if(initialization.length == 0) { "new " + c + "()" } else {
          val init = repsep(newrhs.typ.Fields map { f => (initialization.find { i => i.f == f}) match {
              case None => defaultValue(f.typ)
              case Some(init) => convertExpression(init.e);
            }
          }, ", ");
          "new " + c + "(" + init + ")";
        }
      case At(s, i) => convertExpression(s) + ".At(" + convertExpression(i) + ")" 
      case Append(s1, s2) => convertExpression(s1) + ".Append(" + convertExpression(s2) + ")" 
      case Take(s, i) => convertExpression(s) + ".Take(" + convertExpression(i) + ")"
      case Drop(s, i) => convertExpression(s) + ".Drop(" + convertExpression(i) + ")" 
      case LockBelow(_, _) => "true"
      case bin: BinaryExpr => "(" + convertExpression(bin.E0) + " " + bin.OpName + " " + convertExpression(bin.E1) + ")"// todo: <==> and ==>
      case Unfolding(p, e) => convertExpression(e)
      case FunctionApplication(target, id, args) => convertExpression(target) + "." + id + "(" + repsep(args map convertExpression, ", ") + ")"
      case Not(e) => "(! " + convertExpression(e) + ")"
      case EmptySeq(tp) => "new Chalice.ImmutableList<" + convertType(tp) + ">()"
      case es@ExplicitSeq(elems) => 
        val elemType = new Type(es.typ.asInstanceOf[SeqClass].parameter);
        "new Chalice.ImmutableList<" + convertType(elemType) + ">(" +
          "new " + convertType(elemType) + "[] {" + repsep(elems map convertExpression, ", ") + "}" + 
        ")"
      case Range(min, max) => "Chalice.ImmutableList.Range(" + convertExpression(min) + ", " + convertExpression(max) + ")"
      case Length(s) => convertExpression(s) + ".Length"
      case IfThenElse(c, thn, els) => "(" + convertExpression(c) + " ? " + convertExpression(thn) + " : " + convertExpression(els) + ")"
      case _ => throw new NotSupportedException("Expression not supported yet!");
    }
  }
  
  def convertType(tp: Type): String = {
    tp.typ match {
      case t: TokenClass => t.c.FullName + ".Token_" + t.m
      case s: SeqClass => "Chalice.ImmutableList<" + convertType(new Type(s.parameter)) + ">"
      case IntClass => "int"
      case BoolClass => "bool"
      case NullClass => "object"
      case Class(id, _, _, _) => id
    }
  }
  
  def defaultValue(tp: Type) = {
     tp.typ match {
      case t: TokenClass => "null"
      case s: SeqClass => "new Chalice.ImmutableList<" + convertType(new Type(s.parameter)) + ">()"
      case IntClass => "0"
      case BoolClass => "false"
      case NullClass => "null"
      case Class(id, _, _, _) => "null"
    }
  }
  
  // utility methods below
  
  var uniqueInt: Int = 0;
  val nl = System.getProperty("line.separator");
  var indentLevel = 0
  
  def rep(strings: List[String]): String = {
    strings.foldLeft("")({ (a, b) => a + b })
  }
  
  def repsep(strings: List[String], separator: String): String = {
    if(strings.length == 0) {
      ""
    } else {
      strings.reduceLeft({ (a, b) => a + separator + b })
    }
  }
  
  def indent: String = {
    def doIndent(i: Int): String = {
      if(i==0) { "" } else { "  " + doIndent(i-1) }
    }
    doIndent(indentLevel);
  }

  def indentMore(what: => String) = {
    val prev = indentLevel
    indentLevel = indentLevel + 1
    val result = what
    indentLevel = prev
    result
  }
}
