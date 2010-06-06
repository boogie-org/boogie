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
  internal class StatementTraverser : BaseCodeTraverser {
    public readonly MethodTraverser MethodTraverser;

    public readonly Bpl.Variable HeapVariable;

    public readonly Bpl.StmtListBuilder StmtBuilder = new Bpl.StmtListBuilder();

    #region Constructors
    public StatementTraverser(MethodTraverser mt) {
      HeapVariable = mt.HeapVariable;
      MethodTraverser = mt;
    }

    public StatementTraverser(MethodTraverser mt, Bpl.Variable heapvar) {
      HeapVariable = heapvar;
      MethodTraverser = mt;
    }
    #endregion

    #region Helper Methods

    Bpl.IToken TokenFor(IStatement statement) {
      return TranslationHelper.CciLocationToBoogieToken(statement.Locations);
    }

    Bpl.Expr ExpressionFor(IExpression expression) {
      ExpressionTraverser etrav = new ExpressionTraverser(this);
      etrav.Visit(expression);
      Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      return etrav.TranslatedExpressions.Pop();
    }

    #endregion

    public override void Visit(IBlockStatement block) {
      Bpl.StmtListBuilder slb = new Bpl.StmtListBuilder();

      foreach (IStatement st in block.Statements) {
        this.Visit(st);
      }
    }

    #region Basic Statements

    public override void Visit(IAssertStatement assertStatement) {

      StmtBuilder.Add(
        new Bpl.AssertCmd(TokenFor(assertStatement), ExpressionFor(assertStatement.Condition))
        );

      //ExpressionTraverser etrav = new ExpressionTraverser(this);
      //etrav.Visit(assertStatement.Condition);
      //Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      //var tok = TranslationHelper.CciLocationToBoogieToken(assertStatement.Locations);
      //var a = new Bpl.AssertCmd(tok, etrav.TranslatedExpressions.Pop());
      //StmtBuilder.Add(a);
    }

    public override void Visit(IAssumeStatement assumeStatement) {
      ExpressionTraverser etrav = new ExpressionTraverser(this);
      etrav.Visit(assumeStatement.Condition);
      Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      var tok = TranslationHelper.CciLocationToBoogieToken(assumeStatement.Locations);
      var a = new Bpl.AssumeCmd(tok, etrav.TranslatedExpressions.Pop());
      StmtBuilder.Add(a);
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub</remarks>
    /// <param name="conditionalStatement"></param>
    public override void Visit(IConditionalStatement conditionalStatement) {
      StatementTraverser thenTraverser = new StatementTraverser(this.MethodTraverser);
      StatementTraverser elseTraverser = new StatementTraverser(this.MethodTraverser);

      ExpressionTraverser condTraverser = new ExpressionTraverser(this);
      condTraverser.Visit(conditionalStatement.Condition);
      thenTraverser.Visit(conditionalStatement.TrueBranch);
      elseTraverser.Visit(conditionalStatement.FalseBranch);

      Bpl.IfCmd ifcmd = new Bpl.IfCmd(TranslationHelper.CciLocationToBoogieToken(conditionalStatement.Locations),
          condTraverser.TranslatedExpressions.Pop(),
          thenTraverser.StmtBuilder.Collect(TranslationHelper.CciLocationToBoogieToken(conditionalStatement.TrueBranch.Locations)),
          null,
          elseTraverser.StmtBuilder.Collect(TranslationHelper.CciLocationToBoogieToken(conditionalStatement.FalseBranch.Locations))
          );

      StmtBuilder.Add(ifcmd);

    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="expressionStatement"></param>
    /// <remarks> TODO: might be wrong for the general case</remarks>
    public override void Visit(IExpressionStatement expressionStatement) {

      ExpressionTraverser etrav = new ExpressionTraverser(this);
      etrav.Visit(expressionStatement.Expression);
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Not Implemented</remarks>
    /// <param name="breakStatement"></param>
    public override void Visit(IBreakStatement breakStatement) {
      StmtBuilder.Add(new Bpl.BreakCmd(TranslationHelper.CciLocationToBoogieToken(breakStatement.Locations), "I dont know"));
    }

    /// <summary>
    /// If the local declaration has an initial value, then generate the
    /// statement "loc := e" from it. Otherwise ignore it.
    /// </summary>
    public override void Visit(ILocalDeclarationStatement localDeclarationStatement) {
      if (localDeclarationStatement.InitialValue == null) return;
      var loc = this.MethodTraverser.FindOrCreateLocalVariable(localDeclarationStatement.LocalVariable);
      var tok = TokenFor(localDeclarationStatement);
      var e = ExpressionFor(localDeclarationStatement.InitialValue);
      StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, loc), e));
      return;

      //if (localDeclarationStatement.InitialValue == null) return;
      //ExpressionTraverser etrav = new ExpressionTraverser(this);
      //etrav.Visit(localDeclarationStatement.InitialValue);
      //Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(localDeclarationStatement.Locations);
      //Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      //var loc = this.MethodTraverser.FindOrCreateLocalVariable(localDeclarationStatement.LocalVariable);
      //var e = etrav.TranslatedExpressions.Pop();
      //StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, loc), e));
      //return;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) not implemented</remarks>
    /// <param name="returnStatement"></param>
    public override void Visit(IReturnStatement returnStatement) {
      Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(returnStatement.Locations);

      #region Copy values of all out parameters to outvariables
      foreach (MethodTraverser.MethodParameter mp in MethodTraverser.OutVars) {
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
          new Bpl.IdentifierExpr(tok, mp.outParameterCopy), new Bpl.IdentifierExpr(tok, mp.localParameter)));
      }
      #endregion

      if (returnStatement.Expression != null) {
        ExpressionTraverser etrav = new ExpressionTraverser(this);
        etrav.Visit(returnStatement.Expression);

        if (this.MethodTraverser.RetVariable == null || etrav.TranslatedExpressions.Count < 1) {
          throw new TranslationException(String.Format("{0} returns a value that is not supported by the function", returnStatement.ToString()));
        }

        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
            new Bpl.IdentifierExpr(tok, this.MethodTraverser.RetVariable), etrav.TranslatedExpressions.Pop()));
      }
      StmtBuilder.Add(new Bpl.ReturnCmd(TranslationHelper.CciLocationToBoogieToken(returnStatement.Locations)));
    }
    #endregion

    #region Goto and Labels

    /// <summary>
    /// 
    /// </summary>
    /// <remarks> STUB </remarks>
    /// <param name="gotoStatement"></param>
    public override void Visit(IGotoStatement gotoStatement) {
      String[] target = new String[1];
      target[0] = gotoStatement.TargetStatement.Label.Value;

      Bpl.GotoCmd gotocmd = new Microsoft.Boogie.GotoCmd(TranslationHelper.CciLocationToBoogieToken(gotoStatement.Locations),
          new Bpl.StringSeq(target));

      StmtBuilder.Add(gotocmd);
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

  }
}
