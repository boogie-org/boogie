using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie
{
  [ContractClass(typeof(VisitorContracts))]
  /// <summary>
  /// Base for all classes that process the Absy using the visitor pattern.
  /// </summary>
  public abstract class Visitor
  {
    /// <summary>
    /// Switches on node.NodeType to call a visitor method that has been specialized for node.
    /// </summary>
    /// <param name="a">The Absy node to be visited.</param>
    /// <returns> Returns null if node is null. Otherwise returns an updated node (possibly a different object).</returns>
    public abstract Absy Visit(Absy node);

    /// <summary>
    /// Transfers the state from one visitor to another. This enables separate visitor instances to cooperative process a single IR.
    /// </summary>
    public virtual void TransferStateTo(Visitor targetVisitor)
    {
    }

    public virtual IList<Expr> VisitExprSeq(IList<Expr> list)
    {
      
      
      lock (list)
      {
        for (int i = 0, n = list.Count; i < n; i++)
        {
          list[i] = (Expr) this.Visit(Cce.NonNull(list[i]));
        }
      }

      return list;
    }
  }

  [ContractClassFor(typeof(Visitor))]
  abstract class VisitorContracts : Visitor
  {
    public override Absy Visit(Absy node)
    {
      
      

      throw new System.NotImplementedException();
    }
  }

  /// <summary>
  /// Walks an IR, mutating it into a new form. (For a subclass that does not mutate the IR, see ReadOnlyVisitor.)
  /// </summary>   
  public abstract class StandardVisitor : Visitor
  {
    public Visitor callingVisitor;

    public StandardVisitor()
    {
    }

    public StandardVisitor(Visitor callingVisitor)
    {
      this.callingVisitor = callingVisitor;
    }

    public override Absy Visit(Absy node)
    {
      return node.StdDispatch(this);
    }

    public virtual Cmd VisitAssertCmd(AssertCmd node)
    {
      
      
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }
    
    public virtual Cmd VisitRevealCmd(HideRevealCmd node)
    {
      
      
      return node;
    }
    
    public virtual Cmd VisitChangeScopeCmd(ChangeScope node)
    {
      
      
      return node;
    }

    public virtual Cmd VisitAssignCmd(AssignCmd node)
    {
      
      
      for (int i = 0; i < node.Lhss.Count; ++i)
      {
        node.SetLhs(i, Cce.NonNull((AssignLhs) this.Visit(node.Lhss[i])));
        node.SetRhs(i, Cce.NonNull((Expr) this.VisitExpr(node.Rhss[i])));
      }
      VisitAttributes(node);
      return node;
    }

    public virtual Cmd VisitUnpackCmd(UnpackCmd node)
    {
      node.Lhs = (NAryExpr)this.Visit(node.Lhs);
      node.Rhs = (Expr)this.Visit(node.Rhs);
      VisitAttributes(node);
      return node;
    }
    
    public virtual Cmd VisitAssumeCmd(AssumeCmd node)
    {
      
      
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }

    public virtual AtomicRE VisitAtomicRE(AtomicRE node)
    {
      
      
      node.b = this.VisitBlock(node.b);
      return node;
    }

    public virtual Axiom VisitAxiom(Axiom node)
    {
      
      
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }

    public virtual Type VisitBasicType(BasicType node)
    {
      
      
      return this.VisitType(node);
    }

    public virtual Type VisitFloatType(FloatType node)
    {
      
      
      return this.VisitType(node);
    }

    public virtual Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      
      
      node.E0 = this.VisitExpr(node.E0);
      node.E1 = this.VisitExpr(node.E1);
      return node;
    }

    public virtual Type VisitBvType(BvType node)
    {
      
      
      return this.VisitType(node);
    }

    public virtual Type VisitBvTypeProxy(BvTypeProxy node)
    {
      
      
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        return (Type) this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public virtual Block VisitBlock(Block node)
    {
      
      
      node.Cmds = this.VisitCmdSeq(node.Cmds);
      node.TransferCmd = (TransferCmd) this.Visit(Cce.NonNull(node.TransferCmd));
      return node;
    }

    public virtual Expr VisitCodeExpr(CodeExpr node)
    {
      
      
      node.LocVars = this.VisitVariableSeq(node.LocVars);
      node.Blocks = this.VisitBlockList(node.Blocks);
      return node;
    }

    public virtual List<Block> VisitBlockSeq(List<Block> blockSeq)
    {
      
      
      lock (blockSeq)
      {
        for (int i = 0, n = blockSeq.Count; i < n; i++)
        {
          blockSeq[i] = this.VisitBlock(Cce.NonNull(blockSeq[i]));
        }
      }

      return blockSeq;
    }

    public virtual IList<Block> VisitBlockList(IList<Block> blocks)
    {
      
      
      for (int i = 0, n = blocks.Count; i < n; i++)
      {
        blocks[i] = this.VisitBlock(blocks[i]);
      }

      return blocks;
    }

    public virtual BoundVariable VisitBoundVariable(BoundVariable node)
    {
      
      
      node = (BoundVariable) this.VisitVariable(node);
      return node;
    }

    public virtual Cmd VisitCallCmd(CallCmd node)
    {
      
      
      for (int i = 0; i < node.Ins.Count; ++i)
      {
        if (node.Ins[i] != null)
        {
          node.Ins[i] = this.VisitExpr(Cce.NonNull(node.Ins[i]));
        }
      }

      for (int i = 0; i < node.Outs.Count; ++i)
      {
        if (node.Outs[i] != null)
        {
          node.Outs[i] = (IdentifierExpr) this.VisitIdentifierExpr(Cce.NonNull(node.Outs[i]));
        }
      }
      VisitAttributes(node);
      return node;
    }

    public virtual List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds)
    {
      for (int i = 0; i < callCmds.Count; i++)
      {
        callCmds[i] = (CallCmd)VisitCallCmd(callCmds[i]);
      }
      return callCmds;
    }

    public virtual List<AssertCmd> VisitAssertCmdSeq(List<AssertCmd> assertCmds)
    {
      for (int i = 0; i < assertCmds.Count; i++)
      {
        assertCmds[i] = (AssertCmd)VisitAssertCmd(assertCmds[i]);
      }
      return assertCmds;
    }

    public virtual Cmd VisitParCallCmd(ParCallCmd node)
    {
      
      
      for (int i = 0; i < node.CallCmds.Count; i++)
      {
        if (node.CallCmds[i] != null)
        {
          node.CallCmds[i] = (CallCmd) this.VisitCallCmd(node.CallCmds[i]);
        }
      }
      VisitAttributes(node);
      return node;
    }

    public virtual List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      
      
      lock (cmdSeq)
      {
        for (int i = 0, n = cmdSeq.Count; i < n; i++)
        {
          cmdSeq[i] = (Cmd) this.Visit(
            Cce.NonNull(cmdSeq[i])); // call general Visit so subtypes of Cmd get visited by their particular visitor
        }
      }

      return cmdSeq;
    }

    public virtual Choice VisitChoice(Choice node)
    {
      
      
      node.rs = this.VisitRESeq(node.rs);
      return node;
    }

    public virtual Cmd VisitCommentCmd(CommentCmd node)
    {
      
      
      return node;
    }

    public virtual Constant VisitConstant(Constant node)
    {
      
      
      return node;
    }

    public virtual CtorType VisitCtorType(CtorType node)
    {
      
      
      lock (node)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = Cce.NonNull((Type) this.Visit(node.Arguments[i]));
        }
      }

      return node;
    }

    public virtual Declaration VisitDeclaration(Declaration node)
    {
      
      
      return node;
    }

    public virtual List<Declaration> VisitDeclarationList(List<Declaration> declarationList)
    {
      
      
      for (int i = 0, n = declarationList.Count; i < n; i++)
      {
        declarationList[i] = Cce.NonNull((Declaration) this.Visit(declarationList[i]));
      }

      return declarationList;
    }

    public virtual DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      
      
      node.InParams = this.VisitVariableSeq(node.InParams);
      node.OutParams = this.VisitVariableSeq(node.OutParams);
      return node;
    }

    public virtual Expr VisitExistsExpr(ExistsExpr node)
    {
      
      
      node = (ExistsExpr) this.VisitQuantifierExpr(node);
      return node;
    }

    public virtual Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      
      
      node.Bitvector = this.VisitExpr(node.Bitvector);
      return node;
    }

    public virtual Expr VisitExpr(Expr node)
    {
      
      
      Expr e = (Expr) this.Visit(node);
      return e;
    }

    public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
    {
      
      for (int i = 0, n = exprSeq.Count; i < n; i++)
      {
        exprSeq[i] = this.VisitExpr(Cce.NonNull(exprSeq[i]));
      }

      return exprSeq;
    }

    public virtual Requires VisitRequires(Requires @requires)
    {
      
      
      @requires.Condition = this.VisitExpr(@requires.Condition);
      return @requires;
    }

    public virtual List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      
      
      for (int i = 0, n = requiresSeq.Count; i < n; i++)
      {
        requiresSeq[i] = this.VisitRequires(requiresSeq[i]);
      }

      return requiresSeq;
    }

    public virtual Ensures VisitEnsures(Ensures @ensures)
    {
      
      
      @ensures.Condition = this.VisitExpr(@ensures.Condition);
      return @ensures;
    }

    public virtual List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      
      
      for (int i = 0, n = ensuresSeq.Count; i < n; i++)
      {
        ensuresSeq[i] = this.VisitEnsures(ensuresSeq[i]);
      }

      return ensuresSeq;
    }

    public virtual Expr VisitForallExpr(ForallExpr node)
    {
      
      
      node = (ForallExpr) this.VisitQuantifierExpr(node);
      return node;
    }

    public virtual Expr VisitLambdaExpr(LambdaExpr node)
    {
      
      
      node = (LambdaExpr) this.VisitBinderExpr(node);
      return node;
    }

    public virtual Expr VisitLetExpr(LetExpr node)
    {
      
      
      node.Rhss = this.VisitExprSeq(node.Rhss);
      node.Dummies = this.VisitVariableSeq(node.Dummies);
      node.Body = this.VisitExpr(node.Body);
      VisitAttributes(node);
      return node;
    }

    public virtual Formal VisitFormal(Formal node)
    {
      
      
      return node;
    }

    public virtual Function VisitFunction(Function node)
    {
      
      
      node = (Function) this.VisitDeclWithFormals(node);
      if (node.Body != null)
      {
        Contract.Assert(node.DefinitionBody == null);
        node.Body = this.VisitExpr(node.Body);
      }
      else if (node.DefinitionBody != null)
      {
        node.DefinitionBody = (NAryExpr) this.VisitExpr(node.DefinitionBody);
      }
      return node;
    }

    public virtual GlobalVariable VisitGlobalVariable(GlobalVariable node)
    {
      
      
      node = (GlobalVariable) this.VisitVariable(node);
      return node;
    }

    public virtual GotoCmd VisitGotoCmd(GotoCmd node)
    {
      
      
      // do not visit the labelTargets, or control-flow loops will lead to a looping visitor
      return node;
    }

    public virtual Cmd VisitHavocCmd(HavocCmd node)
    {
      
      
      node.Vars = this.VisitIdentifierExprSeq(node.Vars);
      return node;
    }

    public virtual Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      
      
      if (node.Decl != null)
      {
        node.Decl = this.VisitVariable(node.Decl);
      }

      return node;
    }

    public virtual List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq)
    {
      
      
      lock (identifierExprSeq)
      {
        for (int i = 0, n = identifierExprSeq.Count; i < n; i++)
        {
          identifierExprSeq[i] = (IdentifierExpr) this.VisitIdentifierExpr(Cce.NonNull(identifierExprSeq[i]));
        }
      }

      return identifierExprSeq;
    }

    public virtual Implementation VisitImplementation(Implementation node)
    {
      
      
      node.LocVars = this.VisitVariableSeq(node.LocVars);
      node.Blocks = this.VisitBlockList(node.Blocks);
      node.Proc = (Procedure)node.Proc.StdDispatch(this);
      node = (Implementation) this.VisitDeclWithFormals(node); // do this first or last?
      VisitAttributes(node);
      return node;
    }

    public virtual Expr VisitLiteralExpr(LiteralExpr node)
    {
      
      
      return node;
    }

    public virtual LocalVariable VisitLocalVariable(LocalVariable node)
    {
      
      
      return node;
    }

    public virtual AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      
      
      node.Map = Cce.NonNull((AssignLhs) this.Visit(node.Map));
      for (int i = 0; i < node.Indexes.Count; ++i)
      {
        node.Indexes[i] = Cce.NonNull((Expr) this.VisitExpr(node.Indexes[i]));
      }

      return node;
    }

    public virtual AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      
      
      node.Datatype = Cce.NonNull((AssignLhs) this.Visit(node.Datatype));
      return node;
    }
    
    public virtual Type VisitMapType(MapType node)
    {
      
      
      // not doing anything about the bound variables ... maybe
      // these should be visited as well ...
      //
      // NOTE: when overriding this method, you have to make sure that
      // the bound variables of the map type are updated correctly
      lock (node.Arguments)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = Cce.NonNull((Type) this.Visit(node.Arguments[i]));
        }
      }

      node.Result = Cce.NonNull((Type) this.Visit(node.Result));
      return node;
    }

    public virtual Type VisitMapTypeProxy(MapTypeProxy node)
    {
      
      
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        return (Type) this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public virtual Expr VisitNAryExpr(NAryExpr node)
    {
      
      
      node.Args = this.VisitExprSeq(node.Args);
      return node;
    }

    public virtual Expr VisitOldExpr(OldExpr node)
    {
      
      
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }

    public virtual Procedure VisitProcedure(Procedure node)
    {
      
      
      node.Ensures = this.VisitEnsuresSeq(node.Ensures);
      node.InParams = this.VisitVariableSeq(node.InParams);
      node.Modifies = this.VisitIdentifierExprSeq(node.Modifies);
      node.OutParams = this.VisitVariableSeq(node.OutParams);
      node.Requires = this.VisitRequiresSeq(node.Requires);
      node.Preserves = this.VisitRequiresSeq(node.Preserves);
      VisitAttributes(node);
      return node;
    }

    public virtual ActionDeclRef VisitActionDeclRef(ActionDeclRef node)
    {
      return node;
    }

    public virtual Procedure VisitActionDecl(ActionDecl node)
    {
      if (node.RefinedAction != null)
      {
        node.RefinedAction = VisitActionDeclRef(node.RefinedAction);
      }
      node.YieldRequires = VisitCallCmdSeq(node.YieldRequires);
      node.Asserts = VisitAssertCmdSeq(node.Asserts);
      return VisitProcedure(node);
    }

    public virtual YieldingLoop VisitYieldingLoop(YieldingLoop node)
    {
      node.YieldInvariants = VisitCallCmdSeq(node.YieldInvariants);
      return node;
    }

    public virtual Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node)
    {
      foreach (var block in node.Keys)
      {
        node[block] = VisitYieldingLoop(node[block]);
      }
      return node;
    }

    public virtual HashSet<Variable> VisitVariableSet(HashSet<Variable> node)
    {
      return node;
    }

    public virtual Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
    {
      node.YieldRequires = VisitCallCmdSeq(node.YieldRequires);
      node.YieldEnsures = VisitCallCmdSeq(node.YieldEnsures);
      node.YieldPreserves = VisitCallCmdSeq(node.YieldPreserves);
      node.RefinedAction = VisitActionDeclRef(node.RefinedAction);
      node.VisibleFormals = VisitVariableSet(node.VisibleFormals);
      node.YieldingLoops = VisitYieldingLoops(node.YieldingLoops);
      return VisitProcedure(node);
    }

    public virtual Procedure VisitYieldInvariantDecl(YieldInvariantDecl node)
    {
      return VisitProcedure(node);
    }
    
    public virtual Program VisitProgram(Program node)
    {
      
      
      var decls = node.TopLevelDeclarations.ToList();
      node.ClearTopLevelDeclarations();
      node.AddTopLevelDeclarations(this.VisitDeclarationList(decls));
      return node;
    }

    public virtual QKeyValue VisitQKeyValue(QKeyValue node)
    {
      
      
      var newParams = new List<object>();
      for (int i = 0, n = node.Params.Count; i < n; i++)
      {
        var e = node.Params[i] as Expr;
        newParams.Add(e != null ? this.Visit(e) : node.Params[i]);
      }

      node.ClearParams();
      node.AddParams(newParams);
      if (node.Next != null)
      {
        node.Next = (QKeyValue) this.Visit(node.Next);
      }

      return node;
    }

    public virtual Expr VisitBinderExpr(BinderExpr node)
    {
      
      
      node.Body = this.VisitExpr(node.Body);
      node.Dummies = this.VisitVariableSeq(node.Dummies);
      //node.Type = this.VisitType(node.Type);
      VisitAttributes(node);
      return node;
    }

    public virtual QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      
      
      node = Cce.NonNull((QuantifierExpr) this.VisitBinderExpr(node));
      if (node.Triggers != null)
      {
        node.Triggers = this.VisitTrigger(node.Triggers);
      }

      return node;
    }

    public virtual Cmd VisitRE(RE node)
    {
      
      
      return (Cmd) this.Visit(node); // Call general visit so subtypes get visited by their particular visitor
    }

    public virtual List<RE> VisitRESeq(List<RE> reSeq)
    {
      
      
      for (int i = 0, n = reSeq.Count; i < n; i++)
      {
        reSeq[i] = (RE) this.VisitRE(Cce.NonNull(reSeq[i]));
      }

      return reSeq;
    }

    public virtual ReturnCmd VisitReturnCmd(ReturnCmd node)
    {
      
      
      return (ReturnCmd) this.VisitTransferCmd(node);
    }

    public virtual ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
    {
      
      
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }

    public virtual Sequential VisitSequential(Sequential node)
    {
      
      
      node.first = (RE) this.VisitRE(node.first);
      node.second = (RE) this.VisitRE(node.second);
      return node;
    }

    public virtual AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
    {
      
      
      node.AssignedVariable =
        (IdentifierExpr) this.VisitIdentifierExpr(node.AssignedVariable);
      return node;
    }

    public virtual Cmd VisitStateCmd(StateCmd node)
    {
      
      
      node.Locals = this.VisitVariableSeq(node.Locals);
      node.Cmds = this.VisitCmdSeq(node.Cmds);
      return node;
    }

    public virtual TransferCmd VisitTransferCmd(TransferCmd node)
    {
      
      
      return node;
    }

    public virtual Trigger VisitTrigger(Trigger node)
    {
      
      
      Trigger origNext = node.Next;
      if (origNext != null)
      {
        Trigger newNext = this.VisitTrigger(origNext);
        if (newNext != origNext)
        {
          node = new Trigger(node.tok, node.Pos, node.Tr.ToList());
          node.Next = newNext;
        }
      }

      node.Tr = this.VisitExprSeq(node.Tr.ToList());
      return node;
    }

    // called by default for all nullary type constructors and type variables
    public virtual Type VisitType(Type node)
    {
      
      
      return node;
    }

    public virtual TypedIdent VisitTypedIdent(TypedIdent node)
    {
      
      
      node.Type = (Type) this.Visit(node.Type);
      return node;
    }

    public virtual Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      
      
      return this.VisitDeclaration(node);
    }

    public virtual Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      
      
      node.ExpandedType = Cce.NonNull((Type) this.Visit(node.ExpandedType));
      lock (node.Arguments)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = Cce.NonNull((Type) this.Visit(node.Arguments[i]));
        }
      }

      return node;
    }

    public virtual Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      
      
      return this.VisitDeclaration(node);
    }

    public virtual Type VisitTypeVariable(TypeVariable node)
    {
      
      
      return this.VisitType(node);
    }

    public virtual Type VisitTypeProxy(TypeProxy node)
    {
      
      
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        return Cce.NonNull((Type) this.Visit(node.ProxyFor));
      }

      return this.VisitType(node);
    }

    public virtual Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
    {
      
      
      return this.VisitType(node);
    }

    public virtual Variable VisitVariable(Variable node)
    {
      
      
      node.TypedIdent = this.VisitTypedIdent(node.TypedIdent);
      return node;
    }

    public virtual List<Variable> VisitVariableSeq(List<Variable> variableSeq)
    {
      
      
      lock (variableSeq)
      {
        for (int i = 0, n = variableSeq.Count; i < n; i++)
        {
          variableSeq[i] = this.VisitVariable(Cce.NonNull(variableSeq[i]));
        }
      }

      return variableSeq;
    }

    public virtual Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
      
      
      node.Ensures = this.VisitEnsures(node.Ensures);
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }

    public virtual Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
      
      
      node.Requires = this.VisitRequires(node.Requires);
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }

    /*
     * VisitAttributes is being called in the visitor of those subtypes of Cmd
     * and Expr that implement ICarriesAttributes. This behavior is introduced so
     * that hints for pool-based quantifier instantiation present in attributes
     * are processed naturally during monomorphization and inlining. There
     * are other subtypes of Absy that implement ICarriesAttributes; if
     * necessary, this method could be in the visitor for those types also.
     */
    private void VisitAttributes(ICarriesAttributes node)
    {
      if (node.Attributes != null)
      {
        node.Attributes = VisitQKeyValue(node.Attributes);
      }
    }
  }

  /// <summary>
  /// VarDeclOnceStandardVisitor is like StandardVisitor, except
  ///   -- it does not visit a variable's declaration when visiting an `IdentifierExpr`, and
  ///   -- it visits the `where` clause (if any) when visiting a `TypedIdent`.
  /// </summary>
  public abstract class VarDeclOnceStandardVisitor : StandardVisitor
  {
    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      return node;
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node) {
      node = base.VisitTypedIdent(node);
      if (node.WhereExpr != null) {
        node.WhereExpr = (Expr) Visit(node.WhereExpr);
      }
      return node;
    }
  }

  /// <summary>
  /// A ReadOnlyVisitor visits all the nodes of a given Absy.  The visitor may collect information from
  /// the nodes, may change fields contained in the data structure, but may not replace any nodes in the
  /// data structure.  To enforce this, all Visit...(node) methods have a postcondition that says that
  /// the return value is equal to the given "node".
  /// </summary>
  public abstract class ReadOnlyVisitor : StandardVisitor
  {
    public ReadOnlyVisitor()
    {
    }

    public ReadOnlyVisitor(Visitor callingVisitor)
    {
      this.callingVisitor = callingVisitor;
    }

    public override Absy Visit(Absy node)
    {
      
      return node.StdDispatch(this);
    }

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      
      for (int i = 0; i < node.Lhss.Count; ++i)
      {
        this.Visit(node.Lhss[i]);
        this.VisitExpr(node.Rhss[i]);
      }
      return node;
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      this.VisitExpr(node.Lhs);
      this.VisitExpr(node.Rhs);
      return node;
    }

    public override Cmd VisitAssumeCmd(AssumeCmd node)
    {
      
      this.VisitExpr(node.Expr);
      return node;
    }

    public override AtomicRE VisitAtomicRE(AtomicRE node)
    {
      
      this.VisitBlock(node.b);
      return node;
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Type VisitBasicType(BasicType node)
    {
      
      return this.VisitType(node);
    }

    public override Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      
      this.VisitExpr(node.E0);
      this.VisitExpr(node.E1);
      return node;
    }

    public override Type VisitBvType(BvType node)
    {
      
      return this.VisitType(node);
    }

    public override Type VisitBvTypeProxy(BvTypeProxy node)
    {
      
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public override Block VisitBlock(Block node)
    {
      
      this.VisitCmdSeq(node.Cmds);
      this.Visit(Cce.NonNull(node.TransferCmd));
      return node;
    }

    public override Expr VisitCodeExpr(CodeExpr node)
    {
      
      this.VisitVariableSeq(node.LocVars);
      this.VisitBlockList(node.Blocks);
      return node;
    }

    public override List<Block> VisitBlockSeq(List<Block> blockSeq)
    {
      
      for (int i = 0, n = blockSeq.Count; i < n; i++)
      {
        this.VisitBlock(Cce.NonNull(blockSeq[i]));
      }

      return blockSeq;
    }

    public override IList<Block> VisitBlockList(IList<Block> blocks)
    {
      
      foreach (var block in blocks) {
        this.VisitBlock(block);
      }
      return blocks;
    }

    public override BoundVariable VisitBoundVariable(BoundVariable node)
    {
      
      return (BoundVariable) this.VisitVariable(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      
      for (int i = 0; i < node.Ins.Count; ++i)
      {
        if (node.Ins[i] != null)
        {
          this.VisitExpr(node.Ins[i]);
        }
      }

      for (int i = 0; i < node.Outs.Count; ++i)
      {
        if (node.Outs[i] != null)
        {
          this.VisitIdentifierExpr(node.Outs[i]);
        }
      }

      return node;
    }

    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
      
      for (int i = 0; i < node.CallCmds.Count; i++)
      {
        if (node.CallCmds[i] != null)
        {
          this.VisitCallCmd(node.CallCmds[i]);
        }
      }

      return node;
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      
      for (int i = 0, n = cmdSeq.Count; i < n; i++)
      {
        this.Visit(Cce.NonNull(
          cmdSeq[i])); // call general Visit so subtypes of Cmd get visited by their particular visitor
      }

      return cmdSeq;
    }

    public override Choice VisitChoice(Choice node)
    {
      
      this.VisitRESeq(node.rs);
      return node;
    }

    public override Cmd VisitCommentCmd(CommentCmd node)
    {
      
      return node;
    }

    public override Constant VisitConstant(Constant node)
    {
      
      return node;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        this.Visit(node.Arguments[i]);
      }

      return node;
    }

    public override Declaration VisitDeclaration(Declaration node)
    {
      
      return node;
    }

    public override List<Declaration> VisitDeclarationList(List<Declaration> declarationList)
    {
      
      for (int i = 0, n = declarationList.Count; i < n; i++)
      {
        this.Visit(declarationList[i]);
      }

      return declarationList;
    }

    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      
      this.VisitVariableSeq(node.InParams);
      this.VisitVariableSeq(node.OutParams);
      return node;
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      
      return (ExistsExpr) this.VisitQuantifierExpr(node);
    }

    public override Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      
      this.VisitExpr(node.Bitvector);
      return node;
    }

    public override Expr VisitExpr(Expr node)
    {
      
      return (Expr) this.Visit(node);
    }

    public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
    {
      
      for (int i = 0, n = exprSeq.Count; i < n; i++)
      {
        this.VisitExpr(Cce.NonNull(exprSeq[i]));
      }

      return exprSeq;
    }

    public override Requires VisitRequires(Requires requires)
    {
      
      this.VisitExpr(requires.Condition);
      return requires;
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      
      for (int i = 0, n = requiresSeq.Count; i < n; i++)
      {
        this.VisitRequires(requiresSeq[i]);
      }

      return requiresSeq;
    }

    public override Ensures VisitEnsures(Ensures ensures)
    {
      
      this.VisitExpr(ensures.Condition);
      return ensures;
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      
      for (int i = 0, n = ensuresSeq.Count; i < n; i++)
      {
        this.VisitEnsures(ensuresSeq[i]);
      }

      return ensuresSeq;
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      
      return (ForallExpr) this.VisitQuantifierExpr(node);
    }

    public override Expr VisitLambdaExpr(LambdaExpr node)
    {
      
      return this.VisitBinderExpr(node);
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      this.VisitExprSeq(node.Rhss);
      this.VisitVariableSeq(node.Dummies);
      this.VisitExpr(node.Body);
      return node;
    }

    public override Formal VisitFormal(Formal node)
    {
      
      return node;
    }

    public override Function VisitFunction(Function node)
    {
      
      node = (Function) this.VisitDeclWithFormals(node);
      if (node.Body != null)
      {
        Contract.Assert(node.DefinitionBody == null);
        this.VisitExpr(node.Body);
      }
      else if (node.DefinitionBody != null)
      {
        this.VisitExpr(node.DefinitionBody);
      }

      return node;
    }

    public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
    {
      
      return (GlobalVariable) this.VisitVariable(node);
    }

    public override GotoCmd VisitGotoCmd(GotoCmd node)
    {
      
      // do not visit the labelTargets, or control-flow loops will lead to a looping visitor
      return node;
    }

    public override Cmd VisitHavocCmd(HavocCmd node)
    {
      
      this.VisitIdentifierExprSeq(node.Vars);
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      
      if (node.Decl != null)
      {
        this.VisitVariable(node.Decl);
      }

      return node;
    }

    public override List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq)
    {
      
      for (int i = 0, n = identifierExprSeq.Count; i < n; i++)
      {
        this.VisitIdentifierExpr(Cce.NonNull(identifierExprSeq[i]));
      }

      return identifierExprSeq;
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      
      this.VisitVariableSeq(node.LocVars);
      this.VisitBlockList(node.Blocks);
      node.Proc = (Procedure)node.Proc.StdDispatch(this);
      return (Implementation) this.VisitDeclWithFormals(node); // do this first or last?
    }

    public override Expr VisitLiteralExpr(LiteralExpr node)
    {
      
      return node;
    }

    public override LocalVariable VisitLocalVariable(LocalVariable node)
    {
      
      return node;
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      
      this.Visit(node.Map);
      for (int i = 0; i < node.Indexes.Count; ++i)
      {
        this.VisitExpr(node.Indexes[i]);
      }

      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      
      // not doing anything about the bound variables ... maybe
      // these should be visited as well ...
      //
      // NOTE: when overriding this method, you have to make sure that
      // the bound variables of the map type are updated correctly
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        this.Visit(node.Arguments[i]);
      }

      this.Visit(node.Result);
      return node;
    }

    public override Type VisitMapTypeProxy(MapTypeProxy node)
    {
      
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      
      this.VisitExprSeq(node.Args);
      return node;
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      
      this.VisitEnsuresSeq(node.Ensures);
      this.VisitVariableSeq(node.InParams);
      this.VisitIdentifierExprSeq(node.Modifies);
      this.VisitVariableSeq(node.OutParams);
      this.VisitRequiresSeq(node.Requires);
      return node;
    }

    public override Program VisitProgram(Program node)
    {
      
      this.VisitDeclarationList(node.TopLevelDeclarations.ToList());
      return node;
    }

    public override QKeyValue VisitQKeyValue(QKeyValue node)
    {
      
      for (int i = 0, n = node.Params.Count; i < n; i++)
      {
        var e = node.Params[i] as Expr;
        if (e != null)
        {
          this.Visit(e);
        }
      }

      if (node.Next != null)
      {
        this.Visit(node.Next);
      }

      return node;
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      
      this.VisitExpr(node.Body);
      this.VisitVariableSeq(node.Dummies);
      // this.VisitType(node.Type);
      return node;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      
      this.VisitBinderExpr(node);
      if (node.Triggers != null)
      {
        this.VisitTrigger(node.Triggers);
      }

      return node;
    }

    public override Cmd VisitRE(RE node)
    {
      
      return (Cmd) this.Visit(node); // Call general visit so subtypes get visited by their particular visitor
    }

    public override List<RE> VisitRESeq(List<RE> reSeq)
    {
      
      for (int i = 0, n = reSeq.Count; i < n; i++)
      {
        this.VisitRE(Cce.NonNull(reSeq[i]));
      }

      return reSeq;
    }

    public override ReturnCmd VisitReturnCmd(ReturnCmd node)
    {
      
      return (ReturnCmd) this.VisitTransferCmd(node);
    }

    public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
    {
      
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Sequential VisitSequential(Sequential node)
    {
      
      this.VisitRE(node.first);
      this.VisitRE(node.second);
      return node;
    }

    public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
    {
      
      this.VisitIdentifierExpr(node.AssignedVariable);
      return node;
    }

    public override Cmd VisitStateCmd(StateCmd node)
    {
      
      this.VisitVariableSeq(node.Locals);
      this.VisitCmdSeq(node.Cmds);
      return node;
    }

    public override TransferCmd VisitTransferCmd(TransferCmd node)
    {
      
      return node;
    }

    public override Trigger VisitTrigger(Trigger node)
    {
      
      Trigger origNext = node.Next;
      if (origNext != null)
      {
        this.VisitTrigger(origNext);
      }

      this.VisitExprSeq(node.Tr.ToList());
      return node;
    }

    // called by default for all nullary type constructors and type variables
    public override Type VisitType(Type node)
    {
      
      return node;
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node)
    {
      
      this.Visit(node.Type);
      return node;
    }

    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      
      return this.VisitDeclaration(node);
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      
      node.ExpandedType = Cce.NonNull((Type) this.Visit(node.ExpandedType));
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        this.Visit(node.Arguments[i]);
      }

      return node;
    }

    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      
      return this.VisitDeclaration(node);
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      
      return this.VisitType(node);
    }

    public override Type VisitTypeProxy(TypeProxy node)
    {
      
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
    {
      
      return this.VisitType(node);
    }

    public override Variable VisitVariable(Variable node)
    {
      
      this.VisitTypedIdent(node.TypedIdent);
      return node;
    }

    public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
    {
      
      for (int i = 0, n = variableSeq.Count; i < n; i++)
      {
        this.VisitVariable(Cce.NonNull(variableSeq[i]));
      }

      return variableSeq;
    }

    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
      
      this.VisitEnsures(node.Ensures);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
      
      this.VisitRequires(node.Requires);
      this.VisitExpr(node.Expr);
      return node;
    }
  }
}