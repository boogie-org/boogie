//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;


namespace BytecodeTranslator
{
  public class MostNestedTryStatementTraverser : BaseCodeTraverser {
    Dictionary<IName, ITryCatchFinallyStatement> mostNestedTryStatement = new Dictionary<IName, ITryCatchFinallyStatement>();
    ITryCatchFinallyStatement currStatement = null;
    public override void Visit(ILabeledStatement labeledStatement) {
      if (currStatement != null)
        mostNestedTryStatement.Add(labeledStatement.Label, currStatement);
      base.Visit(labeledStatement);
    }
    public override void Visit(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      ITryCatchFinallyStatement savedStatement = currStatement;
      currStatement = tryCatchFinallyStatement;
      base.Visit(tryCatchFinallyStatement);
      currStatement = savedStatement;
    }
    public ITryCatchFinallyStatement MostNestedTryStatement(IName label) {
      if (!mostNestedTryStatement.ContainsKey(label))
        return null;
      return mostNestedTryStatement[label];
    }
  }

  public class StatementTraverser : BaseCodeTraverser {

    public readonly TraverserFactory factory;

    readonly Sink sink;

    public readonly PdbReader/*?*/ PdbReader;

    public readonly Bpl.StmtListBuilder StmtBuilder = new Bpl.StmtListBuilder();
    private bool contractContext;
    internal readonly Stack<IExpression> operandStack = new Stack<IExpression>();

    #region Constructors
    public StatementTraverser(Sink sink, PdbReader/*?*/ pdbReader, bool contractContext, List<Tuple<ITryCatchFinallyStatement,TryCatchFinallyContext>> nestedTryCatchFinallyStatements) {
      this.sink = sink;
      this.factory = sink.Factory;
      PdbReader = pdbReader;
      this.contractContext = contractContext;
      this.nestedTryCatchFinallyStatements = nestedTryCatchFinallyStatements;
    }
    #endregion

    #region Helper Methods

    Bpl.Expr ExpressionFor(IExpression expression) {
      ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      etrav.Visit(expression);
      Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      return etrav.TranslatedExpressions.Pop();
    }

    public ICollection<ITypeDefinition>/*?*/ TranslateMethod(IMethodDefinition method) {
      var methodBody = method.Body as ISourceMethodBody;
      if (methodBody == null) return null;
      var block = methodBody.Block as BlockStatement;
      // TODO: Error if cast fails?

      ICollection<ITypeDefinition> newTypes = null;
      if (block != null) {
        var remover = new AnonymousDelegateRemover(this.sink.host, this.PdbReader);
        newTypes = remover.RemoveAnonymousDelegates(methodBody.MethodDefinition, block);
      }
      this.Visit(methodBody);
      return newTypes;
    }

    public void GenerateDispatchContinuation() {
      // Iterate over all labels in sink.cciLabels and sink.boogieLabels and generate dispatch based on sink.LabelVariable
      this.StmtBuilder.AddLabelCmd("DispatchContinuation");
      Bpl.IfCmd elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(true), TranslationHelper.BuildStmtList(new Bpl.AssumeCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(false))), null, null);
      Bpl.IdentifierExpr labelExpr = Bpl.Expr.Ident(this.sink.LabelVariable);
      foreach (IName name in sink.cciLabels.Keys) {
        Bpl.GotoCmd gotoCmd = new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(name.Value));
        Bpl.Expr targetExpr = Bpl.Expr.Literal(sink.cciLabels[name]);
        elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, labelExpr, targetExpr), TranslationHelper.BuildStmtList(gotoCmd), elseIfCmd, null);
      }
      this.StmtBuilder.Add(elseIfCmd);
    }
    #endregion

    //public override void Visit(ISourceMethodBody methodBody) {
    //  var block = methodBody.Block as BlockStatement;
    //  // TODO: Error if cast fails?

    //  if (block != null) {
    //    var remover = new AnonymousDelegateRemover(this.sink.host, this.PdbReader);
    //    var newTypes = remover.RemoveAnonymousDelegates(methodBody.MethodDefinition, block);
    //  }
    //  base.Visit(methodBody);
    //}

    public override void Visit(IBlockStatement block) {
      foreach (var s in block.Statements) {
        this.Visit(s);
      }
    }

    public override void Visit(IStatement statement) {
      EmitSourceContext(statement);
      base.Visit(statement);
    }

    private void EmitSourceContext(IStatement statement) {
      if (statement is IEmptyStatement) return;
      var tok = statement.Token();
      string fileName = null;
      int lineNumber = 0;
      if (this.PdbReader != null) {
        var slocs = this.PdbReader.GetClosestPrimarySourceLocationsFor(statement.Locations);
        foreach (var sloc in slocs) {
          fileName = sloc.Document.Location;
          lineNumber = sloc.StartLine;
          break;
        }
        if (fileName != null) {
          var attrib = new Bpl.QKeyValue(tok, "sourceLine", new List<object> { Bpl.Expr.Literal((int)lineNumber) }, null);
          attrib = new Bpl.QKeyValue(tok, "sourceFile", new List<object> { fileName }, attrib);
          StmtBuilder.Add(
            new Bpl.AssertCmd(tok, Bpl.Expr.True, attrib)
            );
        }
      }
    }

    #region Basic Statements

    public override void Visit(IAssertStatement assertStatement) {
      StmtBuilder.Add(
        new Bpl.AssertCmd(assertStatement.Token(), ExpressionFor(assertStatement.Condition))
        );
    }

    public override void Visit(IAssumeStatement assumeStatement) {
      StmtBuilder.Add(
        new Bpl.AssumeCmd(assumeStatement.Token(), ExpressionFor(assumeStatement.Condition))
        );
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub</remarks>
    /// <param name="conditionalStatement"></param>
    public override void Visit(IConditionalStatement conditionalStatement) {
      StatementTraverser thenTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext, this.nestedTryCatchFinallyStatements);
      StatementTraverser elseTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext, this.nestedTryCatchFinallyStatements);

      ExpressionTraverser condTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      condTraverser.Visit(conditionalStatement.Condition);
      thenTraverser.Visit(conditionalStatement.TrueBranch);
      elseTraverser.Visit(conditionalStatement.FalseBranch);

      Bpl.IfCmd ifcmd = new Bpl.IfCmd(conditionalStatement.Token(),
          condTraverser.TranslatedExpressions.Pop(),
          thenTraverser.StmtBuilder.Collect(conditionalStatement.TrueBranch.Token()),
          null,
          elseTraverser.StmtBuilder.Collect(conditionalStatement.FalseBranch.Token())
          );

      StmtBuilder.Add(ifcmd);

    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="expressionStatement"></param>
    /// <remarks> TODO: might be wrong for the general case</remarks>
    public override void Visit(IExpressionStatement expressionStatement) {

      ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      etrav.Visit(expressionStatement.Expression);
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Not Implemented</remarks>
    /// <param name="breakStatement"></param>
    public override void Visit(IBreakStatement breakStatement) {
      StmtBuilder.Add(new Bpl.BreakCmd(breakStatement.Token(), "I dont know"));
    }

    /// <summary>
    /// If the local declaration has an initial value, then generate the
    /// statement "loc := e" from it. Otherwise ignore it.
    /// </summary>
    public override void Visit(ILocalDeclarationStatement localDeclarationStatement) {
      var initVal = localDeclarationStatement.InitialValue;
      if (initVal == null) return;
      var boogieLocal = this.sink.FindOrCreateLocalVariable(localDeclarationStatement.LocalVariable);
      var boogieLocalExpr = Bpl.Expr.Ident(boogieLocal);
      var tok = localDeclarationStatement.Token();
      var e = ExpressionFor(initVal);

      var typ = initVal.Type;
      var structCopy = TranslationHelper.IsStruct(typ) && !(initVal is IDefaultValue);
      // then a struct value of type S is being assigned: "lhs := s"
      // model this as the statement "call lhs := S..#copy_ctor(s)" that does the bit-wise copying
      Bpl.DeclWithFormals proc = null;
      if (structCopy) {
        var defaultValue = new DefaultValue() {
          DefaultValueType = typ,
          Locations = new List<ILocation>(localDeclarationStatement.Locations),
          Type = typ,
        };
        var e2 = ExpressionFor(defaultValue);
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, boogieLocalExpr, e2));
        proc = this.sink.FindOrCreateProcedureForStructCopy(typ);
        StmtBuilder.Add(new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { e, boogieLocalExpr, }, new List<Bpl.IdentifierExpr>()));
      } else {
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, boogieLocalExpr, e));
      }
      return;
    }

    public override void Visit(IPushStatement pushStatement) {
      var tok = pushStatement.Token();
      var val = pushStatement.ValueToPush;
      var dup = val as IDupValue;
      IExpression e;
      if (dup != null) {
        e = this.operandStack.Peek();
      } else {
        e = val;
      }
      this.operandStack.Push(e);
      return;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) not implemented</remarks>
    /// <param name="returnStatement"></param>
    public override void Visit(IReturnStatement returnStatement) {
      Bpl.IToken tok = returnStatement.Token();

      if (returnStatement.Expression != null) {
        ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
        etrav.Visit(returnStatement.Expression);

        if (this.sink.ReturnVariable == null || etrav.TranslatedExpressions.Count < 1) {
          throw new TranslationException(String.Format("{0} returns a value that is not supported by the function", returnStatement.ToString()));
        }

        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
            new Bpl.IdentifierExpr(tok, this.sink.ReturnVariable), etrav.TranslatedExpressions.Pop()));
      }
      StmtBuilder.Add(new Bpl.ReturnCmd(returnStatement.Token()));
    }
    #endregion

    #region Goto and Labels

    /// <summary>
    /// 
    /// </summary>
    /// <remarks> STUB </remarks>
    /// <param name="gotoStatement"></param>
    public override void Visit(IGotoStatement gotoStatement) {
      IName target = gotoStatement.TargetStatement.Label;
      ITryCatchFinallyStatement targetContext = this.sink.MostNestedTryStatement(target);
      int count = 0;
      while (count < this.nestedTryCatchFinallyStatements.Count) {
        int index = this.nestedTryCatchFinallyStatements.Count - count - 1;
        ITryCatchFinallyStatement nestedContext = this.nestedTryCatchFinallyStatements[index].Item1;
        if (targetContext == nestedContext)
          break;
        count++;
      }
      System.Diagnostics.Debug.Assert((count == nestedTryCatchFinallyStatements.Count) == (targetContext == null));
      if (count > 0) {
        int id = this.sink.FindOrCreateCciLabelIdentifier(target);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(id)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.FinallyStackCounterVariable), Bpl.Expr.Literal(count-1)));
        string finallyLabel = this.sink.FindOrCreateFinallyLabel(this.nestedTryCatchFinallyStatements[this.nestedTryCatchFinallyStatements.Count - 1].Item1);
        StmtBuilder.Add(new Bpl.GotoCmd(gotoStatement.Token(), new Bpl.StringSeq(finallyLabel)));
      }
      else {
        StmtBuilder.Add(new Bpl.GotoCmd(gotoStatement.Token(), new Bpl.StringSeq(target.Value)));
      }
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks> (mschaef) not sure if there is more work to do</remarks>
    /// <param name="labeledStatement"></param>
    public override void Visit(ILabeledStatement labeledStatement) {
      StmtBuilder.AddLabelCmd(labeledStatement.Label.Value);
      base.Visit(labeledStatement.Statement);
    }

    #endregion

    #region Looping Statements

    public override void Visit(IWhileDoStatement whileDoStatement) {
      throw new NotImplementedException("While Statements are not implemented");
    }



    #endregion

    public enum TryCatchFinallyContext { InTry, InCatch, InFinally };
    List<Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext>> nestedTryCatchFinallyStatements;
    
    private void RaiseExceptionHelper(Bpl.StmtListBuilder builder) {
      int count = nestedTryCatchFinallyStatements.Count;
      if (count == 0) {
        builder.Add(new Bpl.ReturnCmd(Bpl.Token.NoToken));
      }
      else {
        Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext> topOfStack = nestedTryCatchFinallyStatements[count - 1];
        string exceptionTarget; 
        if (topOfStack.Item2 == TryCatchFinallyContext.InTry) {
          exceptionTarget = this.sink.FindOrCreateCatchLabel(topOfStack.Item1);
        }
        else if (topOfStack.Item2 == TryCatchFinallyContext.InCatch) {
          builder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
          exceptionTarget = this.sink.FindOrCreateFinallyLabel(topOfStack.Item1);
        }
        else {
          exceptionTarget = this.sink.FindOrCreateContinuationLabel(topOfStack.Item1);
        }
        builder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(exceptionTarget)));
      }
    }

    public void RaiseException() {
      RaiseExceptionHelper(StmtBuilder);
    }
    
    public void RaiseException(Bpl.Expr e) {
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      RaiseExceptionHelper(builder);
      Bpl.IfCmd ifCmd = new Bpl.IfCmd(Bpl.Token.NoToken, e, builder.Collect(Bpl.Token.NoToken), null, null);
      StmtBuilder.Add(ifCmd);
    }

    public override void Visit(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext>(tryCatchFinallyStatement, TryCatchFinallyContext.InTry));
      this.Visit(tryCatchFinallyStatement.TryBody);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
      StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement))));
      nestedTryCatchFinallyStatements.RemoveAt(nestedTryCatchFinallyStatements.Count - 1);

      StmtBuilder.AddLabelCmd(this.sink.FindOrCreateCatchLabel(tryCatchFinallyStatement));
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LocalExcVariable), Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable)));
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef)));
      List<Bpl.StmtList> catchStatements = new List<Bpl.StmtList>();
      List<Bpl.Expr> typeReferences = new List<Bpl.Expr>();
      this.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext>(tryCatchFinallyStatement, TryCatchFinallyContext.InCatch));
      foreach (ICatchClause catchClause in tryCatchFinallyStatement.CatchClauses) {
        typeReferences.Insert(0, this.sink.FindOrCreateType(catchClause.ExceptionType));
        StatementTraverser catchTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext, this.nestedTryCatchFinallyStatements);
        if (catchClause.ExceptionContainer != Dummy.LocalVariable) {
          Bpl.Variable catchClauseVariable = this.sink.FindOrCreateLocalVariable(catchClause.ExceptionContainer);
          catchTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(catchClauseVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
        }
        catchTraverser.Visit(catchClause.Body);
        catchTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
        catchTraverser.StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement))));
        catchStatements.Insert(0, catchTraverser.StmtBuilder.Collect(catchClause.Token()));
      }
      Bpl.IfCmd elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(false), TranslationHelper.BuildStmtList(new Bpl.ReturnCmd(Bpl.Token.NoToken)), null, null);
      Bpl.Expr dynTypeOfOperand = this.sink.Heap.DynamicType(Bpl.Expr.Ident(this.sink.LocalExcVariable));
      for (int i = 0; i < catchStatements.Count; i++) {
        Bpl.Expr expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, dynTypeOfOperand, typeReferences[i]);
        elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, expr, catchStatements[i], elseIfCmd, null);
      }
      this.StmtBuilder.Add(elseIfCmd);
      this.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
      RaiseException();
      nestedTryCatchFinallyStatements.RemoveAt(nestedTryCatchFinallyStatements.Count - 1);

      this.StmtBuilder.AddLabelCmd(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement));
      if (tryCatchFinallyStatement.FinallyBody != null) {
        nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext>(tryCatchFinallyStatement, TryCatchFinallyContext.InFinally));
        Bpl.Variable savedExcVariable = this.sink.CreateFreshLocal(this.sink.Heap.RefType);
        Bpl.Variable savedLabelVariable = this.sink.CreateFreshLocal(Bpl.Type.Int);
        Bpl.Variable savedFinallyStackCounterVariable = this.sink.CreateFreshLocal(Bpl.Type.Int);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedExcVariable), Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedLabelVariable), Bpl.Expr.Ident(this.sink.LabelVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedFinallyStackCounterVariable), Bpl.Expr.Ident(this.sink.FinallyStackCounterVariable)));
        Visit(tryCatchFinallyStatement.FinallyBody);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(savedExcVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Ident(savedLabelVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.FinallyStackCounterVariable), Bpl.Expr.Ident(savedFinallyStackCounterVariable)));
        nestedTryCatchFinallyStatements.RemoveAt(nestedTryCatchFinallyStatements.Count - 1);
      }
      Bpl.GotoCmd dispatchCmd = new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq("DispatchContinuation"));
      Bpl.GotoCmd continuationCmd = new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(this.sink.FindOrCreateContinuationLabel(tryCatchFinallyStatement)));
      Bpl.IfCmd ifCmd = new Bpl.IfCmd(
        Bpl.Token.NoToken,
        Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)),
        TranslationHelper.BuildStmtList(continuationCmd),
        new Bpl.IfCmd(
          Bpl.Token.NoToken,
          Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, Bpl.Expr.Ident(this.sink.FinallyStackCounterVariable), Bpl.Expr.Literal(0)),
          TranslationHelper.BuildStmtList(dispatchCmd), 
          null, 
          null),
        null);
      this.StmtBuilder.Add(ifCmd);
      int count = this.nestedTryCatchFinallyStatements.Count;
      if (count == 0) {
        this.StmtBuilder.Add(new Bpl.AssertCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(false)));
      }
      else {
        Bpl.IdentifierExpr fsv = Bpl.Expr.Ident(this.sink.FinallyStackCounterVariable);
        Bpl.AssignCmd decrementCmd = TranslationHelper.BuildAssignCmd(fsv, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, fsv, Bpl.Expr.Literal(1)));
        this.StmtBuilder.Add(decrementCmd);
        string parentFinallyLabel = this.sink.FindOrCreateFinallyLabel(this.nestedTryCatchFinallyStatements[count - 1].Item1);
        Bpl.GotoCmd parentCmd = new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(parentFinallyLabel));
        this.StmtBuilder.Add(parentCmd);
      }
      StmtBuilder.AddLabelCmd(this.sink.FindOrCreateContinuationLabel(tryCatchFinallyStatement));
      Bpl.Expr raiseExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef));
      RaiseException(raiseExpr);
    }

    public override void Visit(IThrowStatement throwStatement) {
      ExpressionTraverser exceptionTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      exceptionTraverser.Visit(throwStatement.Exception);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), exceptionTraverser.TranslatedExpressions.Pop()));
      RaiseException();
    }

    public override void Visit(IRethrowStatement rethrowStatement) {
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
      RaiseException();
    }
  }

}
