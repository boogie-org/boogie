using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using BoogiePL = Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
  public delegate void InlineCallback(Implementation impl);

  public class Inliner : Duplicator
  {
    private CoreOptions options;
    protected bool inlinedSomething;

    protected Program program;

    protected class UnrollDepthTracker
    {
      protected Dictionary<string, int> procUnrollDepth = new();
      protected Dictionary<string, CallCmd> procUnrollSrc = new();

      private string GetName (Implementation impl) {
        string procName = impl.Name;
        Contract.Assert(procName != null);
        return procName;
      }

      public int GetDepth(Implementation impl) {
        var procName = GetName(impl);
        if (procUnrollDepth.TryGetValue(procName, out var c)) {
          return c;
        }
        return -1;
      }

      public void SetDepth (CallCmd cmd, Implementation impl, int depth) {
        var procName = GetName(impl);
        procUnrollSrc[procName] = cmd;
        procUnrollDepth[procName] = depth;
      }

      public void Increment(Implementation impl) {
        var procName = GetName(impl);
        Debug.Assert (procUnrollSrc.ContainsKey(procName));
        Debug.Assert (procUnrollDepth.ContainsKey(procName));
        procUnrollDepth[procName] = procUnrollDepth[procName] + 1;
      }

      public void Decrement(Implementation impl) {
        var procName = GetName(impl);
        Debug.Assert (procUnrollSrc.ContainsKey(procName));
        Debug.Assert (procUnrollDepth.ContainsKey(procName));
        procUnrollDepth[procName] = procUnrollDepth[procName] - 1;
      }

      public void PopCmd(CallCmd cmd, Implementation impl) {
        var procName = GetName(impl);
        if (procUnrollSrc.ContainsKey(procName) && procUnrollSrc[procName] == cmd) {
          Debug.Assert (procUnrollDepth.ContainsKey(procName));
          procUnrollSrc.Remove(procName);
          procUnrollDepth.Remove(procName);
        }
      }
    }

    protected UnrollDepthTracker depthTracker;

    protected Dictionary<string, int> /* Procedure.Name -> int */
      inlinedProcLblMap;

    protected int inlineDepth;

    protected List<Variable>
      newLocalVars;

    protected string prefix;

    private InlineCallback inlineCallback;

    private CodeCopier codeCopier;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(program != null);
      Contract.Invariant(newLocalVars != null);
      Contract.Invariant(codeCopier != null);
      Contract.Invariant(depthTracker != null);
      Contract.Invariant(inlinedProcLblMap != null);
    }

    public override Expr VisitCodeExpr(CodeExpr node)
    {
      Inliner codeExprInliner = new Inliner(program, inlineCallback, options.InlineDepth, options);
      codeExprInliner.newLocalVars.AddRange(node.LocVars);
      codeExprInliner.inlinedProcLblMap = this.inlinedProcLblMap;
      List<Block> newCodeExprBlocks = codeExprInliner.DoInlineBlocks(node.Blocks, ref inlinedSomething);
      return new CodeExpr(codeExprInliner.newLocalVars, newCodeExprBlocks);
    }

    protected void NextInlinedProcLabel(string procName)
    {
      Contract.Requires(procName != null);
      if (inlinedProcLblMap.TryGetValue(procName, out var currentId))
      {
        inlinedProcLblMap[procName] = currentId + 1;
      }
      else
      {
        inlinedProcLblMap.Add(procName, 0);
      }
    }

    protected string GetInlinedProcLabel(string procName)
    {
      Contract.Requires(procName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return prefix + procName + "$" + inlinedProcLblMap[procName];
    }

    protected string GetProcVarName(string procName, string formalName)
    {
      Contract.Requires(formalName != null);
      Contract.Requires(procName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return GetInlinedProcLabel(procName) + "$" + formalName;
    }

    public Inliner(Program program, InlineCallback cb, int inlineDepth, CoreOptions options)
    {
      this.program = program;
      this.inlinedProcLblMap = new Dictionary<string, int>();
      this.depthTracker = new UnrollDepthTracker();
      this.inlineDepth = inlineDepth;
      this.options = options;
      this.codeCopier = new CodeCopier();
      this.inlineCallback = cb;
      this.newLocalVars = new List<Variable>();
      this.prefix = null;
    }

    // This method calculates a prefix (storing it in the prefix field) so that prepending it to any string
    // is guaranteed not to create a conflict with the names of variables and blocks in scope inside impl.
    protected void ComputePrefix(Program program, Implementation impl)
    {
      this.prefix = "inline$";
      foreach (var v in impl.InParams)
      {
        DistinguishPrefix(v.Name);
      }

      foreach (var v in impl.OutParams)
      {
        DistinguishPrefix(v.Name);
      }

      foreach (var v in impl.LocVars)
      {
        DistinguishPrefix(v.Name);
      }

      foreach (var v in program.GlobalVariables)
      {
        DistinguishPrefix(v.Name);
      }

      foreach (Block b in impl.Blocks)
      {
        DistinguishPrefix(b.Label);
      }
    }

    private void DistinguishPrefix(string s)
    {
      if (!s.StartsWith(prefix))
      {
        return;
      }

      for (int i = prefix.Length; i < s.Length; i++)
      {
        prefix = prefix + "$";
        if (s[i] != '$')
        {
          break;
        }
      }

      if (prefix == s)
      {
        prefix = prefix + "$";
      }
    }

    protected void ProcessImplementation(Program program, Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);

      ComputePrefix(program, impl);

      newLocalVars.AddRange(impl.LocVars);

      bool inlined = false;
      List<Block> newBlocks = DoInlineBlocks(impl.Blocks, ref inlined);
      Contract.Assert(Cce.NonNullElements(newBlocks));

      if (!inlined)
      {
        return;
      }

      impl.InParams = new List<Variable>(impl.InParams);
      impl.OutParams = new List<Variable>(impl.OutParams);
      impl.LocVars = newLocalVars;
      impl.Blocks = newBlocks;

      impl.ResetImplFormalMap();

      // we need to resolve the new code
      ResolveImpl(impl);
      if (options.PrintInlined)
      {
        EmitImpl(impl);
      }
    }

    public static void ProcessImplementationForHoudini(CoreOptions options, Program program, Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Requires(impl.Proc != null);
      var inliner = new Inliner(program, null, options.InlineDepth, options);
      inliner.ProcessImplementation(program, impl);
    }

    public static void ProcessImplementation(CoreOptions options, Program program, Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Requires(impl.Proc != null);
      var inliner = new Inliner(program, null, -1, options);
      inliner.ProcessImplementation(program, impl);
    }

    protected void EmitImpl(Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      options.OutputWriter.WriteLine("after inlining procedure calls");
      impl.Proc.Emit(new TokenTextWriter("<console>", options.OutputWriter, /*pretty=*/ false, options), 0);
      impl.Emit(new TokenTextWriter("<console>", options.OutputWriter, /*pretty=*/ false, options), 0);
    }

    private sealed class DummyErrorSink : IErrorSink
    {
      public void Error(IToken tok, string msg)
      {
        // FIXME
        // noop.
        // This is required because during the resolution, some resolution errors happen
        // (such as the ones caused addion of loop invariants J_(block.Label) by the AI package
      }
    }

    protected void ResolveImpl(Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Ensures(impl.Proc != null);
      ResolutionContext rc = new ResolutionContext(new DummyErrorSink(), options);
      foreach (var decl in program.TopLevelDeclarations)
      {
        decl.Register(rc);
      }
      impl.Proc = null; // to force Resolve() redo the operation
      impl.Resolve(rc);
      Debug.Assert(rc.ErrorCount == 0);

      TypecheckingContext tc = new TypecheckingContext(new DummyErrorSink(), options);
      impl.Typecheck(tc);
      Debug.Assert(tc.ErrorCount == 0);
    }

    // Redundant for this class; but gives a chance for other classes to
    // override this and implement their own inlining policy
    protected virtual int GetInlineCount(CallCmd callCmd, Implementation impl)
    {
      return TryDefineCount(callCmd, impl);
    }

    protected int TryDefineCount(CallCmd callCmd, Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);

      // getDepth returns -1 when depth for this impl is not defined
      var depth = depthTracker.GetDepth(impl);
      if (depth >= 0)
      {
        return depth;
      }

      int callInlineDepth (CallCmd cmd) {
        return QKeyValue.FindIntAttribute(cmd.Attributes, "inline", -1);
      }

      // first check the inline depth on the call command.
      depth = callInlineDepth(callCmd);
      if (depth < 0) {
        // if call cmd doesn't define the depth, then check the procedure.
        impl.CheckIntAttribute("inline", ref depth);
        impl.Proc.CheckIntAttribute("inline", ref depth);
      }
      if (depth >= 0) {
        depthTracker.SetDepth (callCmd, impl, depth);
      }
      return depth;
    }

    void CheckRecursion(Implementation impl, Stack<Procedure> callStack)
    {
      Contract.Requires(impl != null);
      Contract.Requires(Cce.NonNullElements(callStack));
      foreach (Procedure p in callStack)
      {
        Contract.Assert(p != null);
        if (p == impl.Proc)
        {
          string msg = "";
          foreach (Procedure q in callStack)
          {
            Contract.Assert(q != null);
            msg = q.Name + " -> " + msg;
          }

          msg += p.Name;
          //checkingCtx.Error(impl, "inlined procedure is recursive, call stack: {0}", msg);
        }
      }
    }

    private int InlineCallCmd(Block block, CallCmd callCmd, Implementation impl, List<Cmd> newCmds,
      List<Block> newBlocks, int lblCount)
    {
      Contract.Assume(impl != null);
      Contract.Assert(Cce.NonNull(impl.OriginalBlocks).Count > 0);

      // do inline now
      int nextlblCount = lblCount + 1;
      string nextBlockLabel = block.Label + "$" + nextlblCount;

      // run the callback before each inline
      if (inlineCallback != null)
      {
        inlineCallback(impl);
      }

      // increment the counter for the procedure to be used in constructing the locals and formals
      NextInlinedProcLabel(impl.Proc.Name);

      BeginInline(impl);

      List<Block>
        inlinedBlocks = CreateInlinedBlocks(callCmd, impl, nextBlockLabel);
      Contract.Assert(Cce.NonNullElements(inlinedBlocks));

      EndInline();

      if (inlineDepth >= 0)
      {
        Debug.Assert(inlineDepth > 0);
        inlineDepth = inlineDepth - 1;
      }
      else
      {
        depthTracker.Decrement(impl);
      }

      bool inlinedSomething = true;
      inlinedBlocks = DoInlineBlocks(inlinedBlocks, ref inlinedSomething);

      if (inlineDepth >= 0)
      {
        inlineDepth = inlineDepth + 1;
      }
      else
      {
        depthTracker.Increment(impl);
      }

      Block
        startBlock = inlinedBlocks[0];
      Contract.Assert(startBlock != null);

      GotoCmd gotoCmd = new GotoCmd(Token.NoToken, new List<String> {startBlock.Label});
      Block newBlock = new Block(block.tok, ((lblCount == 0) ? (block.Label) : (block.Label + "$" + lblCount)), newCmds,
        gotoCmd);

      newBlocks.Add(newBlock);
      newBlocks.AddRange(inlinedBlocks);

      return nextlblCount;
    }

    public  virtual List<Block> DoInlineBlocks(IList<Block> blocks, ref bool inlinedSomething)
    {
      Contract.Requires(Cce.NonNullElements(blocks));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Block>>()));
      List<Block>
        newBlocks = new List<Block>();

      foreach (Block block in blocks)
      {
        TransferCmd
          transferCmd = Cce.NonNull(block.TransferCmd);
        List<Cmd> cmds = block.Cmds;
        List<Cmd> newCmds = new List<Cmd>();
        int lblCount = 0;

        for (int i = 0; i < cmds.Count; ++i)
        {
          Cmd cmd = cmds[i];

          if (cmd is CallCmd callCmd && !callCmd.IsAsync)
          {
            Implementation impl = FindProcImpl(program, callCmd.Proc);
            if (impl == null)
            {
              newCmds.Add(codeCopier.CopyCmd(callCmd));
              continue;
            }

            int inline = inlineDepth >= 0 ? inlineDepth : GetInlineCount(callCmd, impl);
            if (inline > 0)
            {
              inlinedSomething = true;
              lblCount = InlineCallCmd(block, callCmd, impl, newCmds, newBlocks, lblCount);
              newCmds = new List<Cmd>();
            }
            else if (inline == 0)
            {
              inlinedSomething = true;
              if (options.ProcedureInlining == CoreOptions.Inlining.Assert)
              {
                // add assert
                newCmds.Add(new AssertCmd(callCmd.tok, Expr.False));
              }
              else if (options.ProcedureInlining == CoreOptions.Inlining.Assume)
              {
                // add assume
                newCmds.Add(new AssumeCmd(callCmd.tok, Expr.False));
              }
              else
              {
                // add call
                newCmds.Add(codeCopier.CopyCmd(callCmd));
              }
            }
            else
            {
              newCmds.Add(codeCopier.CopyCmd(callCmd));
            }
            depthTracker.PopCmd(callCmd, impl);
          }
          else if (cmd is PredicateCmd)
          {
            PredicateCmd predCmd = (PredicateCmd) cmd;
            this.inlinedSomething = false;
            Expr newExpr = this.VisitExpr(predCmd.Expr);
            if (this.inlinedSomething)
            {
              inlinedSomething = true;
              PredicateCmd newPredCmd = (PredicateCmd) codeCopier.CopyCmd(predCmd);
              newPredCmd.Expr = newExpr;
              newCmds.Add(newPredCmd);
            }
            else
            {
              newCmds.Add(codeCopier.CopyCmd(predCmd));
            }
          }
          else if (cmd is AssignCmd)
          {
            AssignCmd assignCmd = (AssignCmd) cmd;
            this.inlinedSomething = false;
            List<Expr> newRhss = new List<Expr>();
            foreach (Expr rhsExpr in assignCmd.Rhss)
            {
              newRhss.Add(this.VisitExpr(rhsExpr));
            }

            if (this.inlinedSomething)
            {
              inlinedSomething = true;
              AssignCmd newAssignCmd = (AssignCmd) codeCopier.CopyCmd(assignCmd);
              newAssignCmd.Rhss = newRhss;
              newCmds.Add(newAssignCmd);
            }
            else
            {
              newCmds.Add(codeCopier.CopyCmd(assignCmd));
            }
          }
          else
          {
            newCmds.Add(codeCopier.CopyCmd(cmd));
          }


        }

        Block newBlock = new Block(block.tok, lblCount == 0 ? block.Label : block.Label + "$" + lblCount,
          newCmds, codeCopier.CopyTransferCmd(transferCmd));
        newBlocks.Add(newBlock);
      }

      return newBlocks;
    }

    protected void BeginInline(Implementation impl)
    {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Requires(newLocalVars != null);

      Dictionary<Variable, Expr> substMap = new Dictionary<Variable, Expr>();
      Procedure proc = impl.Proc;

      foreach (Variable locVar in Cce.NonNull(impl.OriginalLocVars))
      {
        Contract.Assert(locVar != null);
        LocalVariable localVar = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, locVar.Name), locVar.TypedIdent.Type,
            locVar.TypedIdent.WhereExpr));
        localVar.Attributes = locVar.Attributes; // copy attributes
        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMap.Add(locVar, ie);
      }

      for (int i = 0; i < impl.InParams.Count; i++)
      {
        Variable inVar = Cce.NonNull(impl.InParams[i]);
        LocalVariable localVar = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, inVar.Name), inVar.TypedIdent.Type,
            inVar.TypedIdent.WhereExpr));
        newLocalVars.Add(localVar);
        if (impl.Proc != null)
        {
          localVar.Attributes = impl.Proc.InParams[i].Attributes; // copy attributes
        }

        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMap.Add(inVar, ie);
        // also add a substitution from the corresponding formal occurring in the PROCEDURE declaration
        Variable procInVar = Cce.NonNull(proc.InParams[i]);
        if (procInVar != inVar)
        {
          substMap.Add(procInVar, ie);
        }
      }

      for (int i = 0; i < impl.OutParams.Count; i++)
      {
        Variable outVar = Cce.NonNull(impl.OutParams[i]);
        LocalVariable localVar = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, outVar.Name), outVar.TypedIdent.Type,
            outVar.TypedIdent.WhereExpr));
        if (impl.Proc != null)
        {
          localVar.Attributes = impl.Proc.OutParams[i].Attributes; // copy attributes
        }

        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMap.Add(outVar, ie);
        // also add a substitution from the corresponding formal occurring in the PROCEDURE declaration
        Variable procOutVar = Cce.NonNull(proc.OutParams[i]);
        if (procOutVar != outVar)
        {
          substMap.Add(procOutVar, ie);
        }
      }

      Dictionary<Variable, Expr> substMapOld = new Dictionary<Variable, Expr>();

      foreach (var mVar in proc.Modifies.Select(ie => ie.Decl).Distinct())
      {
        LocalVariable localVar = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, mVar.Name), mVar.TypedIdent.Type));
        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        if (!substMapOld.ContainsKey(mVar))
        {
          substMapOld.Add(mVar, ie);
        }
      }

      codeCopier.BeginInline(substMap, substMapOld, GetInlinedProcLabel(proc.Name) + "$");

      foreach (var variable in newLocalVars) {
        if (variable.TypedIdent.WhereExpr != null) {
          variable.TypedIdent.WhereExpr = codeCopier.CopyExpr(variable.TypedIdent.WhereExpr);
        }
      }
    }

    protected void EndInline()
    {
      codeCopier.EndInline();
    }

    private Cmd InlinedRequires(CallCmd callCmd, Requires req)
    {
      Requires
        reqCopy = (Requires) Cce.NonNull(req.Clone());
      if (req.Free)
      {
        reqCopy.Condition = Expr.True;
      }
      else
      {
        reqCopy.Condition = codeCopier.CopyExpr(req.Condition);
      }

      AssertCmd
        a = new AssertRequiresCmd(callCmd, reqCopy);
      a.ErrorDataEnhanced = reqCopy.ErrorDataEnhanced;
      return a;
    }

    private Cmd InlinedEnsures(CallCmd callCmd, Ensures ens)
    {
      if (ens.Attributes.FindBoolAttribute("InlineAssume"))
      {
        return new AssumeCmd(ens.tok, codeCopier.CopyExpr(ens.Condition));
      }
      else if (ens.Free)
      {
        return new AssumeCmd(ens.tok, Expr.True);
      }
      else
      {
        Ensures
          ensCopy = (Ensures) Cce.NonNull(ens.Clone());
        ensCopy.Condition = codeCopier.CopyExpr(ens.Condition);
        return new AssertEnsuresCmd(ensCopy);
      }
    }

    private List<Cmd> RemoveAsserts(List<Cmd> cmds)
    {
      List<Cmd> newCmdSeq = new List<Cmd>();
      for (int i = 0; i < cmds.Count; i++)
      {
        Cmd cmd = cmds[i];
        if (cmd is AssertCmd)
        {
          continue;
        }

        newCmdSeq.Add(cmd);
      }

      return newCmdSeq;
    }

    // result[0] is the entry block
    protected List<Block> CreateInlinedBlocks(CallCmd callCmd, Implementation impl, string nextBlockLabel)
    {
      Contract.Requires(nextBlockLabel != null);
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Requires(callCmd != null);
      Contract.Requires(codeCopier.substMap != null);
      Contract.Requires(codeCopier.oldSubstMap != null);

      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Block>>()));
      var implBlocks = Cce.NonNull(impl.OriginalBlocks);
      Contract.Assert(implBlocks.Count > 0);

      Procedure proc = impl.Proc;
      string startLabel = implBlocks[0].Label;

      List<Block>
        inlinedBlocks = new List<Block>();

      // create in block
      List<Cmd> inCmds = new List<Cmd>();

      // assign in parameters
      for (int i = 0; i < impl.InParams.Count; ++i)
      {
        Cmd cmd = Cmd.SimpleAssign(impl.tok,
          (IdentifierExpr) codeCopier.Subst(Cce.NonNull(impl.InParams[i])),
          Cce.NonNull(callCmd.Ins[i]));
        inCmds.Add(cmd);
      }

      // inject requires
      for (int i = 0; i < proc.Requires.Count; i++)
      {
        Requires
          req = Cce.NonNull(proc.Requires[i]);
        inCmds.Add(InlinedRequires(callCmd, req));
      }

      List<Variable> locVars = Cce.NonNull(impl.OriginalLocVars);

      // havoc locals and out parameters in case procedure is invoked in a loop
      List<IdentifierExpr> havocVars = new List<IdentifierExpr>();
      foreach (Variable v in locVars)
      {
        havocVars.Add((IdentifierExpr) codeCopier.Subst(v));
      }

      foreach (Variable v in impl.OutParams)
      {
        havocVars.Add((IdentifierExpr) codeCopier.Subst(v));
      }

      if (havocVars.Count > 0)
      {
        inCmds.Add(new HavocCmd(Token.NoToken, havocVars));
      }

      // assign modifies old values
      foreach (IdentifierExpr mie in proc.Modifies)
      {
        Contract.Assert(mie != null);
        Variable
          mvar = Cce.NonNull(mie.Decl);
        AssignCmd assign = Cmd.SimpleAssign(impl.tok, (IdentifierExpr) Cce.NonNull(codeCopier.OldSubst(mvar)), mie);
        inCmds.Add(assign);
      }

      GotoCmd inGotoCmd =
        new GotoCmd(callCmd.tok, new List<String> {GetInlinedProcLabel(proc.Name) + "$" + startLabel});
      Block inBlock = new Block(impl.tok, GetInlinedProcLabel(proc.Name) + "$Entry", inCmds, inGotoCmd);
      inlinedBlocks.Add(inBlock);

      // inject the blocks of the implementation
      Block intBlock;
      foreach (Block block in implBlocks)
      {
        List<Cmd> copyCmds = codeCopier.CopyCmdSeq(block.Cmds);
        if (0 <= inlineDepth)
        {
          copyCmds = RemoveAsserts(copyCmds);
        }

        TransferCmd transferCmd =
          CreateInlinedTransferCmd(Cce.NonNull(block.TransferCmd), GetInlinedProcLabel(proc.Name));
        intBlock = new Block(block.tok, GetInlinedProcLabel(proc.Name) + "$" + block.Label, copyCmds, transferCmd);
        inlinedBlocks.Add(intBlock);
      }

      // create out block
      List<Cmd> outCmds = new List<Cmd>();

      // inject ensures
      for (int i = 0; i < proc.Ensures.Count; i++)
      {
        Ensures
          ens = Cce.NonNull(proc.Ensures[i]);
        outCmds.Add(InlinedEnsures(callCmd, ens));
      }

      // assign out params
      for (int i = 0; i < impl.OutParams.Count; ++i)
      {
        Expr
          cout_exp = (IdentifierExpr) Cce.NonNull(codeCopier.Subst(Cce.NonNull(impl.OutParams[i])));
        Cmd cmd = Cmd.SimpleAssign(impl.tok, Cce.NonNull(callCmd.Outs[i]), cout_exp);
        outCmds.Add(cmd);
      }

      // create out block
      GotoCmd outGotoCmd = new GotoCmd(Token.NoToken, new List<String> {nextBlockLabel});
      Block outBlock = new Block(impl.tok, GetInlinedProcLabel(proc.Name) + "$Return", outCmds, outGotoCmd);
      inlinedBlocks.Add(outBlock);

      return inlinedBlocks;
    }

    protected TransferCmd CreateInlinedTransferCmd(TransferCmd transferCmd, string procLabel)
    {
      Contract.Requires(procLabel != null);
      Contract.Requires(transferCmd != null);
      TransferCmd newTransferCmd;

      GotoCmd gotoCmd = transferCmd as GotoCmd;
      if (gotoCmd != null)
      {
        List<String> gotoSeq = gotoCmd.LabelNames;
        List<String> newGotoSeq = new List<String>();
        foreach (string blockLabel in Cce.NonNull(gotoSeq))
        {
          Contract.Assert(blockLabel != null);
          newGotoSeq.Add(procLabel + "$" + blockLabel);
        }

        newTransferCmd = new GotoCmd(transferCmd.tok, newGotoSeq);
      }
      else
      {
        newTransferCmd = new GotoCmd(transferCmd.tok, new List<String> {procLabel + "$Return"});
      }

      return newTransferCmd;
    }

    protected static Implementation FindProcImpl(Program program, Procedure proc)
    {
      Contract.Requires(program != null);
      foreach (var impl in program.Implementations)
      {
        if (impl.Proc == proc)
        {
          return impl;
        }
      }

      return null;
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////

    class CodeCopier
    {
      public Dictionary<Variable, Expr> substMap;
      public Dictionary<Variable, Expr> oldSubstMap;
      public string prefix;

      public void BeginInline(Dictionary<Variable, Expr> substMap, Dictionary<Variable, Expr> oldSubstMap, string prefix)
      {
        Contract.Requires(oldSubstMap != null);
        Contract.Requires(substMap != null);
        this.substMap = substMap;
        this.oldSubstMap = oldSubstMap;
        this.prefix = prefix;
      }

      public void EndInline()
      {
        this.substMap = null;
        this.oldSubstMap = null;
        this.prefix = null;
      }

      public Expr Subst(Variable v)
      {
        return substMap[v];
      }

      public Expr OldSubst(Variable v)
      {
        return oldSubstMap[v];
      }

      public Expr PartialSubst(Variable v)
      {
        return substMap.ContainsKey(v) ? substMap[v] : null;
      }

      public Expr PartialOldSubst(Variable v)
      {
        return oldSubstMap.ContainsKey(v) ? oldSubstMap[v] : null;
      }

      public List<Cmd> CopyCmdSeq(List<Cmd> cmds)
      {
        Contract.Requires(cmds != null);
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);
        List<Cmd> newCmds = new List<Cmd>();
        foreach (Cmd cmd in cmds)
        {
          Contract.Assert(cmd != null);
          newCmds.Add(CopyCmd(cmd));
        }

        return newCmds;
      }

      public TransferCmd CopyTransferCmd(TransferCmd cmd)
      {
        Contract.Requires(cmd != null);
        Contract.Ensures(Contract.Result<TransferCmd>() != null);
        if (cmd is GotoCmd gotoCmd)
        {
          Contract.Assert(gotoCmd.LabelNames != null);
          List<String> labels = new List<String>();
          labels.AddRange(gotoCmd.LabelNames);
          return new GotoCmd(cmd.tok, labels);
        }
        else if (cmd is ReturnExprCmd returnExprCmd)
        {
          return new ReturnExprCmd(cmd.tok, CopyExpr(returnExprCmd.Expr));
        }
        else
        {
          return new ReturnCmd(cmd.tok);
        }
      }

      public Cmd CopyCmd(Cmd cmd)
      {
        if (substMap == null)
        {
          return cmd;
        }
        var copyCmd = BoundVarAndReplacingOldSubstituter.Apply(substMap, oldSubstMap, prefix, cmd);
        if (copyCmd is SugaredCmd sugaredCmd)
        {
          sugaredCmd.ResetDesugaring();
        }
        return copyCmd;
      }

      public Expr CopyExpr(Expr expr)
      {
        if (substMap == null)
        {
          return expr;
        }
        return BoundVarAndReplacingOldSubstituter.Apply(substMap, oldSubstMap, prefix, expr);
      }
    } // end class CodeCopier
  } // end class Inliner
} // end namespace
