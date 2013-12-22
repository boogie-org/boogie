//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// BoogiePL - Duplicator.cs
//---------------------------------------------------------------------------------------------

using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {
  public class Duplicator : StandardVisitor {
    public override Absy Visit(Absy node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      node = base.Visit(node);
      return node;
    }

    public override Cmd VisitAssertCmd(AssertCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitAssertCmd((AssertCmd)node.Clone());
    }
    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Cmd>() != null);
        return base.VisitAssertEnsuresCmd((AssertEnsuresCmd)node.Clone());
    }
    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Cmd>() != null);
        return base.VisitAssertRequiresCmd((AssertRequiresCmd)node.Clone());
    }
    public override Cmd VisitAssignCmd(AssignCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      AssignCmd clone = (AssignCmd)node.Clone();
      clone.Lhss = new List<AssignLhs/*!*/>(clone.Lhss);
      clone.Rhss = new List<Expr/*!*/>(clone.Rhss);
      return base.VisitAssignCmd(clone);
    }
    public override Cmd VisitAssumeCmd(AssumeCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitAssumeCmd((AssumeCmd)node.Clone());
    }
    public override AtomicRE VisitAtomicRE(AtomicRE node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AtomicRE>() != null);
      return base.VisitAtomicRE((AtomicRE)node.Clone());
    }
    public override Axiom VisitAxiom(Axiom node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Axiom>() != null);
      return base.VisitAxiom((Axiom)node.Clone());
    }
    public override Type VisitBasicType(BasicType node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // do /not/ clone the type recursively
      return (BasicType)node.Clone();
    }
    public override Block VisitBlock(Block node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Block>() != null);
      return base.VisitBlock((Block)node.Clone());
    }
    public override Expr VisitCodeExpr(CodeExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      CodeExpr clone = (CodeExpr)base.VisitCodeExpr((CodeExpr)node.Clone());
      // Before returning, fix up the resolved goto targets
      Contract.Assert(node.Blocks.Count == clone.Blocks.Count);
      Dictionary<Block, Block> subst = new Dictionary<Block, Block>();
      for (int i = 0; i < node.Blocks.Count; i++) {
        subst.Add(node.Blocks[i], clone.Blocks[i]);
      }
      foreach (Block/*!*/ b in clone.Blocks) {
        Contract.Assert(b != null);
        GotoCmd g = b.TransferCmd as GotoCmd;
        if (g != null) {
          List<Block> targets = new List<Block>();
          foreach (Block t in cce.NonNull(g.labelTargets)) {
            Block nt = subst[t];
            targets.Add(nt);
          }
          g.labelTargets = targets;
        }
      }
      return clone;
    }
    public override List<Block> VisitBlockSeq(List<Block> blockSeq) {
      //Contract.Requires(blockSeq != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);
      return base.VisitBlockSeq(new List<Block>(blockSeq));
    }
    public override List<Block/*!*/>/*!*/ VisitBlockList(List<Block/*!*/>/*!*/ blocks) {
      //Contract.Requires(cce.NonNullElements(blocks));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      return base.VisitBlockList(new List<Block/*!*/>(blocks));
    }
    public override BoundVariable VisitBoundVariable(BoundVariable node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BoundVariable>() != null);
      return base.VisitBoundVariable((BoundVariable)node.Clone());
    }
    public override Type VisitBvType(BvType node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // do /not/ clone the type recursively
      return (BvType)node.Clone();
    }
    public override Cmd VisitCallCmd(CallCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      CallCmd clone = (CallCmd)node.Clone();
      Contract.Assert(clone != null);
      clone.Ins = new List<Expr>(clone.Ins);
      clone.Outs = new List<IdentifierExpr>(clone.Outs);
      return base.VisitCallCmd(clone);
    }
    public override Choice VisitChoice(Choice node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Choice>() != null);
      return base.VisitChoice((Choice)node.Clone());
    }
    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq) {
      //Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      return base.VisitCmdSeq(new List<Cmd>(cmdSeq));
    }
    public override Constant VisitConstant(Constant node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Constant>() != null);
      return base.VisitConstant((Constant)node.Clone());
    }
    public override CtorType VisitCtorType(CtorType node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<CtorType>() != null);
      // do /not/ clone the type recursively
      return (CtorType)node.Clone();
    }
    public override Declaration VisitDeclaration(Declaration node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return base.VisitDeclaration((Declaration)node.Clone());
    }
    public override List<Declaration/*!*/>/*!*/ VisitDeclarationList(List<Declaration/*!*/>/*!*/ declarationList) {
      //Contract.Requires(cce.NonNullElements(declarationList));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Declaration>>()));
      return base.VisitDeclarationList(declarationList);
    }
    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<DeclWithFormals>() != null);
      return base.VisitDeclWithFormals((DeclWithFormals)node.Clone());
    }
    public override Ensures VisitEnsures(Ensures node)
    {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Ensures>() != null);
        return base.VisitEnsures((Ensures)node.Clone());
    }
    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
        //Contract.Requires(ensuresSeq != null);
        Contract.Ensures(Contract.Result<List<Ensures>>() != null);
        return base.VisitEnsuresSeq(new List<Ensures>(ensuresSeq));
    }
    public override ExistsExpr VisitExistsExpr(ExistsExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ExistsExpr>() != null);
      return base.VisitExistsExpr((ExistsExpr)node.Clone());
    }
    public override Expr VisitExpr(Expr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitExpr((Expr)node.Clone());
    }
    public override List<Expr> VisitExprSeq(List<Expr> list) {
      //Contract.Requires(list != null);
      Contract.Ensures(Contract.Result<List<Expr>>() != null);
      return base.VisitExprSeq(new List<Expr>(list));
    }
    public override ForallExpr VisitForallExpr(ForallExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ForallExpr>() != null);
      return base.VisitForallExpr((ForallExpr)node.Clone());
    }
    public override Formal VisitFormal(Formal node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Formal>() != null);
      return base.VisitFormal((Formal)node.Clone());
    }
    public override Function VisitFunction(Function node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return base.VisitFunction((Function)node.Clone());
    }
    public override GlobalVariable VisitGlobalVariable(GlobalVariable node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GlobalVariable>() != null);
      return base.VisitGlobalVariable((GlobalVariable)node.Clone());
    }
    public override GotoCmd VisitGotoCmd(GotoCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GotoCmd>() != null);
      return base.VisitGotoCmd((GotoCmd)node.Clone());
    }
    public override Cmd VisitHavocCmd(HavocCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitHavocCmd((HavocCmd)node.Clone());
    }
    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitIdentifierExpr((IdentifierExpr)node.Clone());
    }
    public override List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq) {
      //Contract.Requires(identifierExprSeq != null);
      Contract.Ensures(Contract.Result<List<IdentifierExpr>>() != null);
      return base.VisitIdentifierExprSeq(new List<IdentifierExpr>(identifierExprSeq));
    }
    public override Implementation VisitImplementation(Implementation node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      return base.VisitImplementation((Implementation)node.Clone());
    }
    public override LiteralExpr VisitLiteralExpr(LiteralExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return base.VisitLiteralExpr((LiteralExpr)node.Clone());
    }
    public override LocalVariable VisitLocalVariable(LocalVariable node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LocalVariable>() != null);
      return base.VisitLocalVariable((LocalVariable)node.Clone());
    }
    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      MapAssignLhs clone = (MapAssignLhs)node.Clone();
      clone.Indexes = new List<Expr/*!*/>(clone.Indexes);
      return base.VisitMapAssignLhs(clone);
    }
    public override MapType VisitMapType(MapType node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<MapType>() != null);
      // do /not/ clone the type recursively
      return (MapType)node.Clone();
    }
    public override Expr VisitNAryExpr(NAryExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitNAryExpr((NAryExpr)node.Clone());
    }
    public override Expr VisitOldExpr(OldExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitOldExpr((OldExpr)node.Clone());
    }
    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Cmd>() != null);
        ParCallCmd clone = (ParCallCmd)node.Clone();
        Contract.Assert(clone != null);
        clone.CallCmds = new List<CallCmd>(node.CallCmds);
        return base.VisitParCallCmd(clone);
    }
    public override Procedure VisitProcedure(Procedure node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Procedure>() != null);
      return base.VisitProcedure((Procedure)node.Clone());
    }
    public override Program VisitProgram(Program node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Program>() != null);
      return base.VisitProgram((Program)node.Clone());
    }
    public override BinderExpr VisitBinderExpr(BinderExpr node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BinderExpr>() != null);
      return base.VisitBinderExpr((BinderExpr)node.Clone());
    }
    public override Requires VisitRequires(Requires node)
    {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Requires>() != null);
        return base.VisitRequires((Requires)node.Clone());
    }
    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
        //Contract.Requires(requiresSeq != null);
        Contract.Ensures(Contract.Result<List<Requires>>() != null);
        return base.VisitRequiresSeq(new List<Requires>(requiresSeq));
    }
    public override Cmd VisitRE(RE node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitRE((RE)node.Clone());
    }
    public override List<RE> VisitRESeq(List<RE> reSeq) {
      //Contract.Requires(reSeq != null);
      Contract.Ensures(Contract.Result<List<RE>>() != null);
      return base.VisitRESeq(new List<RE>(reSeq));
    }
    public override ReturnCmd VisitReturnCmd(ReturnCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnCmd>() != null);
      return base.VisitReturnCmd((ReturnCmd)node.Clone());
    }
    public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnExprCmd>() != null);
      return base.VisitReturnExprCmd((ReturnExprCmd)node.Clone());
    }
    public override Sequential VisitSequential(Sequential node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Sequential>() != null);
      return base.VisitSequential((Sequential)node.Clone());
    }
    public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      return base.VisitSimpleAssignLhs((SimpleAssignLhs)node.Clone());
    }
    public override Cmd VisitStateCmd(StateCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitStateCmd((StateCmd)node.Clone());
    }
    public override TransferCmd VisitTransferCmd(TransferCmd node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      return base.VisitTransferCmd((TransferCmd)node.Clone());
    }
    public override Trigger VisitTrigger(Trigger node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Trigger>() != null);
      return base.VisitTrigger((Trigger)node.Clone());
    }
    public override Type VisitType(Type node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // do /not/ clone the type recursively
      return (Type)node.Clone();
    }
    public override TypedIdent VisitTypedIdent(TypedIdent node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TypedIdent>() != null);
      return base.VisitTypedIdent((TypedIdent)node.Clone());
    }
    public override Variable VisitVariable(Variable node) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      return node;
    }
    public override List<Variable> VisitVariableSeq(List<Variable> variableSeq) {
      //Contract.Requires(variableSeq != null);
      Contract.Ensures(Contract.Result<List<Variable>>() != null);
      return base.VisitVariableSeq(new List<Variable>(variableSeq));
    }
    public override YieldCmd VisitYieldCmd(YieldCmd node)
    {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Requires>() != null);
        return base.VisitYieldCmd((YieldCmd)node.Clone());
    }
  }


  #region A duplicator that also does substitutions for a set of variables
  /// <summary>
  /// A substitution is a partial mapping from Variables to Exprs.
  /// </summary>
  public delegate Expr/*?*/ Substitution(Variable/*!*/ v);

  public static class Substituter {
    public static Substitution SubstitutionFromHashtable(Dictionary<Variable, Expr> map) {
      Contract.Requires(map != null);
      Contract.Ensures(Contract.Result<Substitution>() != null);
      // TODO: With Whidbey, could use anonymous functions.
      return new Substitution(new CreateSubstitutionClosure(map).Method);
    }
    private sealed class CreateSubstitutionClosure {
      Dictionary<Variable /*!*/, Expr /*!*/>/*!*/ map;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(map != null);
      }

      public CreateSubstitutionClosure(Dictionary<Variable, Expr> map)
        : base() {
        Contract.Requires(map != null);
        this.map = map;
      }
      public Expr/*?*/ Method(Variable v) {
        Contract.Requires(v != null);
        if(map.ContainsKey(v)) {
          return map[v];
        }
        return null;
      }
    }

    /// <summary>
    /// Apply a substitution to an expression.  Any variables not in domain(subst)
    /// is not changed.  The substitutions applies within the "old", but the "old"
    /// expression remains.
    /// </summary>
    public static Expr Apply(Substitution subst, Expr expr) {
      Contract.Requires(expr != null);
      Contract.Requires(subst != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr)new NormalSubstituter(subst).Visit(expr);
    }

    /// <summary>
    /// Apply a substitution to a command.  Any variables not in domain(subst)
    /// is not changed.  The substitutions applies within the "old", but the "old"
    /// expression remains.
    /// </summary>
    public static Cmd Apply(Substitution subst, Cmd cmd) {
      Contract.Requires(cmd != null);
      Contract.Requires(subst != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd)new NormalSubstituter(subst).Visit(cmd);
    }

    /// <summary>
    /// Apply a substitution to an expression replacing "old" expressions.
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>    
    public static Expr ApplyReplacingOldExprs(Substitution always, Substitution forold, Expr expr) {
      Contract.Requires(expr != null);
      Contract.Requires(forold != null);
      Contract.Requires(always != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr)new ReplacingOldSubstituter(always, forold).Visit(expr);
    }

    /// <summary>
    /// Apply a substitution to a command replacing "old" expressions.
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "oldExpr" to
    /// variables in domain(oldExpr), apply map "always" to variables in
    /// domain(always)-domain(oldExpr), and leave variable unchanged otherwise.
    /// </summary>    
    public static Cmd ApplyReplacingOldExprs(Substitution always, Substitution forold, Cmd cmd) {
      Contract.Requires(cmd != null);
      Contract.Requires(forold != null);
      Contract.Requires(always != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd)new ReplacingOldSubstituter(always, forold).Visit(cmd);
    }

    private sealed class NormalSubstituter : Duplicator {
      private readonly Substitution/*!*/ subst;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(subst != null);
      }

      public NormalSubstituter(Substitution subst)
        : base() {
        Contract.Requires(subst != null);
        this.subst = subst;
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node) {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        Expr/*?*/ e = subst(cce.NonNull(node.Decl));
        return e == null ? base.VisitIdentifierExpr(node) : e;
      }
    }

    private sealed class ReplacingOldSubstituter : Duplicator {
      private readonly Substitution/*!*/ always;
      private readonly Substitution/*!*/ forold;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(always != null);
        Contract.Invariant(forold != null);
      }

      public ReplacingOldSubstituter(Substitution always, Substitution forold)
        : base() {
        Contract.Requires(forold != null);
        Contract.Requires(always != null);
        this.always = always;
        this.forold = forold;
      }

      private bool insideOldExpr = false;

      public override Expr VisitIdentifierExpr(IdentifierExpr node) {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        Expr/*?*/ e = null;

        if (insideOldExpr) {
          e = forold(cce.NonNull(node.Decl));
        }

        if (e == null) {
          e = always(cce.NonNull(node.Decl));
        }

        return e == null ? base.VisitIdentifierExpr(node) : e;
      }

      public override Expr VisitOldExpr(OldExpr node) {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        bool previouslyInOld = insideOldExpr;
        insideOldExpr = true;
        Expr/*!*/ e = (Expr/*!*/)cce.NonNull(this.Visit(node.Expr));
        insideOldExpr = previouslyInOld;
        return e;
      }
    }
  }
  #endregion
}