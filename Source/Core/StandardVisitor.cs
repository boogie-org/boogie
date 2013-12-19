//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// BoogiePL - StandardVisitor.cs
//---------------------------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {
  [ContractClass(typeof(VisitorContracts))]
  /// <summary>
  /// Base for all classes that process the Absy using the visitor pattern.
  /// </summary>
  public abstract class Visitor {
    /// <summary>
    /// Switches on node.NodeType to call a visitor method that has been specialized for node.
    /// </summary>
    /// <param name="a">The Absy node to be visited.</param>
    /// <returns> Returns null if node is null. Otherwise returns an updated node (possibly a different object).</returns>
    public abstract Absy/*!*/ Visit(Absy/*!*/ node);

    /// <summary>
    /// Transfers the state from one visitor to another. This enables separate visitor instances to cooperative process a single IR.
    /// </summary>
    public virtual void TransferStateTo(Visitor targetVisitor) {
    }

    public virtual List<Expr> VisitExprSeq(List<Expr> list) {
      Contract.Requires(list != null);
      Contract.Ensures(Contract.Result<List<Expr>>() != null);
      lock (list)
      {
        for (int i = 0, n = list.Count; i < n; i++)
          list[i] = (Expr)this.Visit(cce.NonNull(list[i]));
      }
      return list;
    }
  }
  [ContractClassFor(typeof(Visitor))]
  abstract class VisitorContracts : Visitor {
    public override Absy Visit(Absy node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Absy>() != null);

      throw new System.NotImplementedException();
    }
  }

  /// <summary>
  /// Walks an IR, mutating it into a new form
  /// </summary>   
  public abstract class StandardVisitor : Visitor {
    public Visitor callingVisitor;

    public StandardVisitor() {
    }
    public StandardVisitor(Visitor callingVisitor) {
      this.callingVisitor = callingVisitor;
    }
    public override Absy Visit(Absy node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return node.StdDispatch(this);
    }
    public virtual Cmd VisitAssertCmd(AssertCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
    public virtual Cmd VisitAssignCmd(AssignCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      for (int i = 0; i < node.Lhss.Count; ++i) {
        node.Lhss[i] = cce.NonNull((AssignLhs)this.Visit(node.Lhss[i]));
        node.Rhss[i] = cce.NonNull((Expr/*!*/)this.Visit(node.Rhss[i]));
      }
      return node;
    }
    public virtual Cmd VisitAssumeCmd(AssumeCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
    public virtual AtomicRE VisitAtomicRE(AtomicRE node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AtomicRE>() != null);
      node.b = this.VisitBlock(node.b);
      return node;
    }
    public virtual Axiom VisitAxiom(Axiom node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Axiom>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
    public virtual Type VisitBasicType(BasicType node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }
    public virtual BvConcatExpr VisitBvConcatExpr(BvConcatExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BvConcatExpr>() != null);
      node.E0 = this.VisitExpr(node.E0);
      node.E1 = this.VisitExpr(node.E1);
      return node;
    }
    public virtual Type VisitBvType(BvType node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }
    public virtual Type VisitBvTypeProxy(BvTypeProxy node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
        return (Type)this.Visit(node.ProxyFor);
      return this.VisitType(node);
    }
    public virtual Block VisitBlock(Block node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Block>() != null);
      node.Cmds = this.VisitCmdSeq(node.Cmds);
      node.TransferCmd = (TransferCmd)this.Visit(cce.NonNull(node.TransferCmd));
      return node;
    }
    public virtual Expr VisitCodeExpr(CodeExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.LocVars = this.VisitVariableSeq(node.LocVars);
      node.Blocks = this.VisitBlockList(node.Blocks);
      return node;
    }
    public virtual List<Block> VisitBlockSeq(List<Block> blockSeq) {
      Contract.Requires(blockSeq != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);
      lock (blockSeq)
      {
        for (int i = 0, n = blockSeq.Count; i < n; i++)
          blockSeq[i] = this.VisitBlock(cce.NonNull(blockSeq[i]));
      }
      return blockSeq;
    }
    public virtual List<Block/*!*/>/*!*/ VisitBlockList(List<Block/*!*/>/*!*/ blocks) {
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      for (int i = 0, n = blocks.Count; i < n; i++) {
        blocks[i] = this.VisitBlock(blocks[i]);
      }
      return blocks;
    }
    public virtual BoundVariable VisitBoundVariable(BoundVariable node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BoundVariable>() != null);
      node = (BoundVariable)this.VisitVariable(node);
      return node;
    }
    public virtual Cmd VisitCallCmd(CallCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      for (int i = 0; i < node.Ins.Count; ++i)
        if (node.Ins[i] != null)
          node.Ins[i] = this.VisitExpr(cce.NonNull(node.Ins[i]));
      for (int i = 0; i < node.Outs.Count; ++i)
        if (node.Outs[i] != null)
          node.Outs[i] = (IdentifierExpr)this.VisitIdentifierExpr(cce.NonNull(node.Outs[i]));
      return node;
    }
    public virtual Cmd VisitParCallCmd(ParCallCmd node)
    {
        Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Cmd>() != null);
        for (int i = 0; i < node.CallCmds.Count; i++)
        {
            if (node.CallCmds[i] != null)
                node.CallCmds[i] = (CallCmd)this.VisitCallCmd(node.CallCmds[i]);
        }
        return node;
    }
    public virtual List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq) {
      Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      lock (cmdSeq)
      {
        for (int i = 0, n = cmdSeq.Count; i < n; i++)
          cmdSeq[i] = (Cmd)this.Visit(cce.NonNull(cmdSeq[i])); // call general Visit so subtypes of Cmd get visited by their particular visitor
      }
      return cmdSeq;
    }
    public virtual Choice VisitChoice(Choice node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Choice>() != null);
      node.rs = this.VisitRESeq(node.rs);
      return node;
    }
    public virtual Cmd VisitCommentCmd(CommentCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return node;
    }
    public virtual Constant VisitConstant(Constant node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Constant>() != null);
      return node;
    }
    public virtual CtorType VisitCtorType(CtorType node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<CtorType>() != null);
      lock (node)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
          node.Arguments[i] = cce.NonNull((Type/*!*/)this.Visit(node.Arguments[i]));
      }
      return node;
    }
    public virtual Declaration VisitDeclaration(Declaration node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return node;
    }
    public virtual List<Declaration/*!*/>/*!*/ VisitDeclarationList(List<Declaration/*!*/>/*!*/ declarationList) {
      Contract.Requires(cce.NonNullElements(declarationList));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Declaration>>()));
      for (int i = 0, n = declarationList.Count; i < n; i++)
        declarationList[i] = cce.NonNull((Declaration/*!*/)this.Visit(declarationList[i]));
      return declarationList;
    }
    public virtual DeclWithFormals VisitDeclWithFormals(DeclWithFormals node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<DeclWithFormals>() != null);
      node.InParams = this.VisitVariableSeq(node.InParams);
      node.OutParams = this.VisitVariableSeq(node.OutParams);
      return node;
    }
    public virtual ExistsExpr VisitExistsExpr(ExistsExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ExistsExpr>() != null);
      node = (ExistsExpr)this.VisitQuantifierExpr(node);
      return node;
    }
    public virtual BvExtractExpr VisitBvExtractExpr(BvExtractExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BvExtractExpr>() != null);
      node.Bitvector = this.VisitExpr(node.Bitvector);
      return node;
    }
    public virtual Expr VisitExpr(Expr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Expr e = (Expr)this.Visit(node);
      return e;
    }
    public override List<Expr> VisitExprSeq(List<Expr> exprSeq) {
      //Contract.Requires(exprSeq != null);
      Contract.Ensures(Contract.Result<List<Expr>>() != null);
      for (int i = 0, n = exprSeq.Count; i < n; i++)
        exprSeq[i] = this.VisitExpr(cce.NonNull(exprSeq[i]));
      return exprSeq;
    }
    public virtual Requires VisitRequires(Requires @requires) {
      Contract.Requires(@requires != null);
      Contract.Ensures(Contract.Result<Requires>() != null);
      @requires.Condition = this.VisitExpr(@requires.Condition);
      return @requires;
    }
    public virtual List<Requires> VisitRequiresSeq(List<Requires> requiresSeq) {
      Contract.Requires(requiresSeq != null);
      Contract.Ensures(Contract.Result<List<Requires>>() != null);
      for (int i = 0, n = requiresSeq.Count; i < n; i++)
        requiresSeq[i] = this.VisitRequires(requiresSeq[i]);
      return requiresSeq;
    }
    public virtual Ensures VisitEnsures(Ensures @ensures) {
      Contract.Requires(@ensures != null);
      Contract.Ensures(Contract.Result<Ensures>() != null);
      @ensures.Condition = this.VisitExpr(@ensures.Condition);
      return @ensures;
    }
    public virtual List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq) {
      Contract.Requires(ensuresSeq != null);
      Contract.Ensures(Contract.Result<List<Ensures>>() != null);
      for (int i = 0, n = ensuresSeq.Count; i < n; i++)
        ensuresSeq[i] = this.VisitEnsures(ensuresSeq[i]);
      return ensuresSeq;
    }
    public virtual ForallExpr VisitForallExpr(ForallExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ForallExpr>() != null);
      node = (ForallExpr)this.VisitQuantifierExpr(node);
      return node;
    }
    public virtual LambdaExpr VisitLambdaExpr(LambdaExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LambdaExpr>() != null);
      node = (LambdaExpr)this.VisitBinderExpr(node);
      return node;
    }
    public virtual Formal VisitFormal(Formal node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Formal>() != null);
      return node;
    }
    public virtual Function VisitFunction(Function node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      node = (Function)this.VisitDeclWithFormals(node);
      if (node.Body != null)
        node.Body = this.VisitExpr(node.Body);
      return node;
    }
    public virtual GlobalVariable VisitGlobalVariable(GlobalVariable node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GlobalVariable>() != null);
      node = (GlobalVariable)this.VisitVariable(node);
      return node;
    }
    public virtual GotoCmd VisitGotoCmd(GotoCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GotoCmd>() != null);
      // do not visit the labelTargets, or control-flow loops will lead to a looping visitor
      return node;
    }
    public virtual Cmd VisitHavocCmd(HavocCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Vars = this.VisitIdentifierExprSeq(node.Vars);
      return node;
    }
    public virtual Expr VisitIdentifierExpr(IdentifierExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (node.Decl != null)
        node.Decl = this.VisitVariable(node.Decl);
      return node;
    }
    public virtual List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq) {
      Contract.Requires(identifierExprSeq != null);
      Contract.Ensures(Contract.Result<List<IdentifierExpr>>() != null);
      lock (identifierExprSeq)
      {
        for (int i = 0, n = identifierExprSeq.Count; i < n; i++)
          identifierExprSeq[i] = (IdentifierExpr)this.VisitIdentifierExpr(cce.NonNull(identifierExprSeq[i]));
      }
      return identifierExprSeq;
    }
    public virtual Implementation VisitImplementation(Implementation node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      node.LocVars = this.VisitVariableSeq(node.LocVars);
      node.Blocks = this.VisitBlockList(node.Blocks);
      node.Proc = this.VisitProcedure(cce.NonNull(node.Proc));
      node = (Implementation)this.VisitDeclWithFormals(node); // do this first or last?
      return node;
    }
    public virtual LiteralExpr VisitLiteralExpr(LiteralExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return node;
    }

    public virtual LocalVariable VisitLocalVariable(LocalVariable node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LocalVariable>() != null);
      return node;
    }

    public virtual AssignLhs VisitMapAssignLhs(MapAssignLhs node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      node.Map = cce.NonNull((AssignLhs)this.Visit(node.Map));
      for (int i = 0; i < node.Indexes.Count; ++i)
        node.Indexes[i] = cce.NonNull((Expr)this.Visit(node.Indexes[i]));
      return node;
    }
    public virtual MapType VisitMapType(MapType node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<MapType>() != null);
      // not doing anything about the bound variables ... maybe
      // these should be visited as well ...
      //
      // NOTE: when overriding this method, you have to make sure that
      // the bound variables of the map type are updated correctly
      lock (node.Arguments)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
          node.Arguments[i] = cce.NonNull((Type/*!*/)this.Visit(node.Arguments[i]));
      }
      node.Result = cce.NonNull((Type/*!*/)this.Visit(node.Result));
      return node;
    }
    public virtual Type VisitMapTypeProxy(MapTypeProxy node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
        return (Type)this.Visit(node.ProxyFor);
      return this.VisitType(node);
    }

    public virtual Expr VisitNAryExpr(NAryExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.Args = this.VisitExprSeq(node.Args);
      return node;
    }
    public virtual Expr VisitOldExpr(OldExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
    public virtual Procedure VisitProcedure(Procedure node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Procedure>() != null);
      node.Ensures = this.VisitEnsuresSeq(node.Ensures);
      node.InParams = this.VisitVariableSeq(node.InParams);
      node.Modifies = this.VisitIdentifierExprSeq(node.Modifies);
      node.OutParams = this.VisitVariableSeq(node.OutParams);
      node.Requires = this.VisitRequiresSeq(node.Requires);
      return node;
    }
    public virtual Program VisitProgram(Program node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Program>() != null);
      node.TopLevelDeclarations = this.VisitDeclarationList(node.TopLevelDeclarations);
      return node;
    }
    public virtual BinderExpr VisitBinderExpr(BinderExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BinderExpr>() != null);
      node.Body = this.VisitExpr(node.Body);
      node.Dummies = this.VisitVariableSeq(node.Dummies);
      //node.Type = this.VisitType(node.Type);
      return node;
    }
    public virtual QuantifierExpr VisitQuantifierExpr(QuantifierExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<QuantifierExpr>() != null);
      node = cce.NonNull((QuantifierExpr)this.VisitBinderExpr(node));
      if (node.Triggers != null) {
        node.Triggers = this.VisitTrigger(node.Triggers);
      }
      return node;
    }
    public virtual Cmd VisitRE(RE node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd)this.Visit(node); // Call general visit so subtypes get visited by their particular visitor
    }
    public virtual List<RE> VisitRESeq(List<RE> reSeq) {
      Contract.Requires(reSeq != null);
      Contract.Ensures(Contract.Result<List<RE>>() != null);
      for (int i = 0, n = reSeq.Count; i < n; i++)
        reSeq[i] = (RE)this.VisitRE(cce.NonNull(reSeq[i]));
      return reSeq;
    }
    public virtual ReturnCmd VisitReturnCmd(ReturnCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnCmd>() != null);
      return (ReturnCmd)this.VisitTransferCmd(node);
    }
    public virtual ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnExprCmd>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
    public virtual Sequential VisitSequential(Sequential node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Sequential>() != null);
      node.first = (RE)this.VisitRE(node.first);
      node.second = (RE)this.VisitRE(node.second);
      return node;
    }
    public virtual AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      node.AssignedVariable =
        (IdentifierExpr)this.VisitIdentifierExpr(node.AssignedVariable);
      return node;
    }
    public virtual Cmd VisitStateCmd(StateCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Locals = this.VisitVariableSeq(node.Locals);
      node.Cmds = this.VisitCmdSeq(node.Cmds);
      return node;
    }
    public virtual TransferCmd VisitTransferCmd(TransferCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      return node;
    }
    public virtual Trigger VisitTrigger(Trigger node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Trigger>() != null);
      Trigger origNext = node.Next;
      if (origNext != null) {
        Trigger newNext = this.VisitTrigger(origNext);
        if (newNext != origNext) {
          node = new Trigger(node.tok, node.Pos, node.Tr);  // note: this creates sharing between the old and new Tr sequence
          node.Next = newNext;
        }
      }
      node.Tr = this.VisitExprSeq(node.Tr);
      return node;
    }
    // called by default for all nullary type constructors and type variables
    public virtual Type VisitType(Type node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return node;
    }
    public virtual TypedIdent VisitTypedIdent(TypedIdent node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TypedIdent>() != null);
      node.Type = (Type)this.Visit(node.Type);
      return node;
    }
    public virtual Declaration VisitTypeCtorDecl(TypeCtorDecl node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return this.VisitDeclaration(node);
    }
    public virtual Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      node.ExpandedType = cce.NonNull((Type/*!*/)this.Visit(node.ExpandedType));
      lock (node.Arguments)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
          node.Arguments[i] = cce.NonNull((Type/*!*/)this.Visit(node.Arguments[i]));
      }
      return node;
    }
    public virtual Declaration VisitTypeSynonymDecl(TypeSynonymDecl node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return this.VisitDeclaration(node);
    }
    public virtual Type VisitTypeVariable(TypeVariable node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }
    public virtual Type VisitTypeProxy(TypeProxy node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
        return cce.NonNull((Type/*!*/)this.Visit(node.ProxyFor));
      return this.VisitType(node);
    }
    public virtual Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }
    public virtual Variable VisitVariable(Variable node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      node.TypedIdent = this.VisitTypedIdent(node.TypedIdent);
      return node;
    }
    public virtual List<Variable> VisitVariableSeq(List<Variable> variableSeq) {
      Contract.Requires(variableSeq != null);
      Contract.Ensures(Contract.Result<List<Variable>>() != null);
      lock (variableSeq)
      {
        for (int i = 0, n = variableSeq.Count; i < n; i++)
          variableSeq[i] = this.VisitVariable(cce.NonNull(variableSeq[i]));
      }
      return variableSeq;
    }
    public virtual YieldCmd VisitYieldCmd(YieldCmd node)
    {
        Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<YieldCmd>() != null);
        return node;
    }
    public virtual Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Ensures = this.VisitEnsures(node.Ensures);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
    public virtual Cmd VisitAssertRequiresCmd(AssertRequiresCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Requires = this.VisitRequires(node.Requires);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
  }
}
