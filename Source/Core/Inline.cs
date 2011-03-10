//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie {

  using System;
  using System.IO;
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics.Contracts;
  using BoogiePL=Microsoft.Boogie;
  using System.Diagnostics;
  using System.Text.RegularExpressions; // for procedure inlining

  // this callback is called before inlining a procedure
  public delegate void InlineCallback(Implementation/*!*/ impl);

  public class Inliner {
    private InlineCallback inlineCallback;

    protected CodeCopier/*!*/ codeCopier;

    protected Dictionary<string/*!*/, int>/*!*/ /* Procedure.Name -> int */ recursiveProcUnrollMap;

    protected Dictionary<string/*!*/, int>/*!*/ /* Procedure.Name -> int */ inlinedProcLblMap;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(codeCopier != null);
      Contract.Invariant(recursiveProcUnrollMap != null);
      Contract.Invariant(inlinedProcLblMap != null);
    }


    protected void NextInlinedProcLabel(string procName) {
      Contract.Requires(procName != null);
      int currentId;
      if (inlinedProcLblMap.TryGetValue(procName, out currentId)) {
        inlinedProcLblMap[procName] = currentId + 1;
      } else {
        inlinedProcLblMap.Add(procName, 0);
      }
    }

    protected string GetInlinedProcLabel(string procName) {
      Contract.Requires(procName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      int currentId;
      if (!inlinedProcLblMap.TryGetValue(procName, out currentId)) {
        currentId = 0;
        inlinedProcLblMap.Add(procName, currentId);
      }
      return "inline$" + procName + "$" + currentId;
    }

    protected string GetProcVarName(string procName, string formalName) {
      Contract.Requires(formalName != null);
      Contract.Requires(procName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string/*!*/ prefix = GetInlinedProcLabel(procName);
      Contract.Assert(prefix != null);
      return prefix + "$" + formalName;
    }

    protected Inliner(InlineCallback cb) {
      inlinedProcLblMap = new Dictionary<string/*!*/, int>();
      recursiveProcUnrollMap = new Dictionary<string/*!*/, int>();
      codeCopier = new CodeCopier();
      inlineCallback = cb;
    }

    public static void ProcessImplementation(Program program, Implementation impl, InlineCallback cb) {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Requires(impl.Proc != null);
      Inliner inliner = new Inliner(cb);

      VariableSeq/*!*/ newInParams = new VariableSeq(impl.InParams);
      Contract.Assert(newInParams != null);
      VariableSeq/*!*/ newOutParams = new VariableSeq(impl.OutParams);
      Contract.Assert(newOutParams != null);
      VariableSeq/*!*/ newLocalVars = new VariableSeq(impl.LocVars);
      Contract.Assert(newLocalVars != null);
      IdentifierExprSeq/*!*/ newModifies = new IdentifierExprSeq(impl.Proc.Modifies);
      Contract.Assert(newModifies != null);

      bool inlined = false;
      List<Block/*!*/>/*!*/ newBlocks = inliner.DoInline(impl.Blocks, program, newLocalVars, newModifies, out inlined);
      Contract.Assert(cce.NonNullElements(newBlocks));

      if (!inlined)
        return;

      impl.InParams = newInParams;
      impl.OutParams = newOutParams;
      impl.LocVars = newLocalVars;
      impl.Blocks = newBlocks;
      impl.Proc.Modifies = newModifies;

      impl.ResetImplFormalMap();

      // we need to resolve the new code
      inliner.ResolveImpl(program, impl);

      if (CommandLineOptions.Clo.PrintInlined) {
        inliner.EmitImpl(impl);
      }
    }


    public static void ProcessImplementation(Program program, Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Requires(impl.Proc != null);
      ProcessImplementation(program, impl, null);
    }

    protected void EmitImpl(Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Console.WriteLine("after inlining procedure calls");
      impl.Proc.Emit(new TokenTextWriter("<console>", Console.Out), 0);
      impl.Emit(new TokenTextWriter("<console>", Console.Out), 0);
    }

    private sealed class DummyErrorSink : IErrorSink {
      public void Error(IToken tok, string msg) {
        //Contract.Requires(msg != null);
        //Contract.Requires(tok != null);
        // FIXME 
        // noop.
        // This is required because during the resolution, some resolution errors happen
        // (such as the ones caused addion of loop invariants J_(block.Label) by the AI package
      }
    }

    protected void ResolveImpl(Program program, Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Ensures(impl.Proc != null);
      ResolutionContext rc = new ResolutionContext(new DummyErrorSink());

      foreach (Declaration decl in program.TopLevelDeclarations) {
        decl.Register(rc);
      }

      impl.Proc = null; // to force Resolve() redo the operation
      impl.Resolve(rc);

      TypecheckingContext tc = new TypecheckingContext(new DummyErrorSink());

      impl.Typecheck(tc);
    }


    // returns true if it is ok to further unroll the procedure
    // otherwise, the procedure is not inlined at the call site
    protected int GetInlineCount(Implementation impl) {
      Contract.Requires(impl != null);
      string/*!*/ procName = impl.Name;
      Contract.Assert(procName != null);
      int c;
      if (recursiveProcUnrollMap.TryGetValue(procName, out c)) {
        return c;
      }

      c = -1; // TryGetValue above always overwrites c
      impl.CheckIntAttribute("inline", ref c);
      // procedure attribute overrides implementation
      if (impl.Proc != null) {
        impl.Proc.CheckIntAttribute("inline", ref c);
      }

      recursiveProcUnrollMap[procName] = c;
      return c;
    }

    void CheckRecursion(Implementation impl, Stack<Procedure/*!*/>/*!*/ callStack) {
      Contract.Requires(impl != null);
      Contract.Requires(cce.NonNullElements(callStack));
      foreach (Procedure/*!*/ p in callStack) {
        Contract.Assert(p != null);
        if (p == impl.Proc) {
          string msg = "";
          foreach (Procedure/*!*/ q in callStack) {
            Contract.Assert(q != null);
            msg = q.Name + " -> " + msg;
          }
          msg += p.Name;
          //checkingCtx.Error(impl, "inlined procedure is recursive, call stack: {0}", msg);
        }
      }
    }

    private List<Block/*!*/>/*!*/ DoInlineBlocks(Stack<Procedure/*!*/>/*!*/ callStack, List<Block/*!*/>/*!*/ blocks, Program/*!*/ program,
                                         VariableSeq/*!*/ newLocalVars, IdentifierExprSeq/*!*/ newModifies, ref bool inlinedSomething) {
      Contract.Requires(cce.NonNullElements(callStack));
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Requires(program != null);
      Contract.Requires(newLocalVars != null);
      Contract.Requires(newModifies != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      List<Block/*!*/>/*!*/ newBlocks = new List<Block/*!*/>();
      

      foreach (Block block in blocks) {
        TransferCmd/*!*/ transferCmd = cce.NonNull(block.TransferCmd);
        CmdSeq cmds = block.Cmds;
        CmdSeq newCmds = new CmdSeq();
        Block newBlock;
        string label = block.Label;
        int lblCount = 0;

        for (int i = 0; i < cmds.Length; ++i) {
          Cmd cmd = cmds[i];
          CallCmd callCmd = cmd as CallCmd;

          if (callCmd == null) {
            // if not call command, leave it as is
            newCmds.Add(codeCopier.CopyCmd(cmd));
          } else {
            Contract.Assert(callCmd.Proc != null);
            Procedure proc = callCmd.Proc;
            int inline = -1;

            Implementation impl = FindProcImpl(program, proc);
            if (impl != null) {
              inline = GetInlineCount(impl);
            }

            if (inline > 0) { // at least one block should exist
              Contract.Assume(impl != null);
              Contract.Assert(cce.NonNull(impl.OriginalBlocks).Count > 0);
              inlinedSomething = true;

              // do inline now
              int nextlblCount = lblCount + 1;
              string nextBlockLabel = label + "$" + nextlblCount;

              // run the callback before each inline
              if (inlineCallback != null) {
                inlineCallback(impl);
              }

              // increment the counter for the procedure to be used in constructing the locals and formals
              NextInlinedProcLabel(proc.Name);

              BeginInline(newLocalVars, newModifies, proc, impl);

              List<Block/*!*/>/*!*/ inlinedBlocks = CreateInlinedBlocks(callCmd, proc, impl, nextBlockLabel);
              Contract.Assert(cce.NonNullElements(inlinedBlocks));

              EndInline();

              recursiveProcUnrollMap[impl.Name] = recursiveProcUnrollMap[impl.Name] - 1;
              callStack.Push(cce.NonNull(impl.Proc));
              inlinedBlocks = DoInlineBlocks(callStack, inlinedBlocks, program, newLocalVars, newModifies, ref inlinedSomething);
              callStack.Pop();
              recursiveProcUnrollMap[impl.Name] = recursiveProcUnrollMap[impl.Name] + 1;

              Block/*!*/ startBlock = inlinedBlocks[0];
              Contract.Assert(startBlock != null);

              GotoCmd gotoCmd = new GotoCmd(Token.NoToken, new StringSeq(startBlock.Label));
              newBlock = new Block(block.tok, ((lblCount == 0) ? (label) : (label + "$" + lblCount)), newCmds, gotoCmd);

              newBlocks.Add(newBlock);
              newBlocks.AddRange(inlinedBlocks);

              lblCount = nextlblCount;
              newCmds = new CmdSeq();
            } else if (inline == 0) {
              inlinedSomething = true;
              if (CommandLineOptions.Clo.ProcedureInlining == CommandLineOptions.Inlining.Assert) {
                // add assert
                newCmds.Add(new AssertCmd(callCmd.tok, Expr.False));
              } else if (CommandLineOptions.Clo.ProcedureInlining == CommandLineOptions.Inlining.Assume) {
                // add assume
                newCmds.Add(new AssumeCmd(callCmd.tok, Expr.False));
              } else {
                // add call
                newCmds.Add(codeCopier.CopyCmd(callCmd));
              }
            } else {
              newCmds.Add(codeCopier.CopyCmd(callCmd));
            }
          }
        }

        newBlock = new Block(block.tok, ((lblCount == 0) ? (label) : (label + "$" + lblCount)), newCmds, codeCopier.CopyTransferCmd(transferCmd));
        newBlocks.Add(newBlock);
      }

      return newBlocks;
    }

    protected List<Block/*!*/>/*!*/ DoInline(List<Block/*!*/>/*!*/ blocks, Program program, VariableSeq newLocalVars, IdentifierExprSeq newModifies, out bool inlined) {
      Contract.Requires(newModifies != null);
      Contract.Requires(newLocalVars != null);
      Contract.Requires(program != null);
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      inlinedProcLblMap.Clear();
      recursiveProcUnrollMap.Clear();

      inlined = false;
      return DoInlineBlocks(new Stack<Procedure/*!*/>(), blocks, program, newLocalVars, newModifies, ref inlined);
    }

    protected void BeginInline(VariableSeq newLocalVars, IdentifierExprSeq newModifies, Procedure proc, Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Requires(proc != null);
      Contract.Requires(newModifies != null);
      Contract.Requires(newLocalVars != null);
      Hashtable substMap = new Hashtable();

      foreach (Variable/*!*/ locVar in cce.NonNull(impl.OriginalLocVars)) {
        Contract.Assert(locVar != null);
        LocalVariable localVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, locVar.Name), locVar.TypedIdent.Type, locVar.TypedIdent.WhereExpr));
        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMap.Add(locVar, ie);
      }

      for (int i = 0; i < impl.InParams.Length; i++) {
        Variable inVar = cce.NonNull(impl.InParams[i]);
        LocalVariable localVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, inVar.Name), inVar.TypedIdent.Type, inVar.TypedIdent.WhereExpr));
        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMap.Add(inVar, ie);
        // also add a substitution from the corresponding formal occurring in the PROCEDURE declaration
        Variable procInVar = cce.NonNull(proc.InParams[i]);
        if (procInVar != inVar) {
          substMap.Add(procInVar, ie);
        }
      }

      for (int i = 0; i < impl.OutParams.Length; i++) {
        Variable outVar = cce.NonNull(impl.OutParams[i]);
        LocalVariable localVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, outVar.Name), outVar.TypedIdent.Type, outVar.TypedIdent.WhereExpr));
        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMap.Add(outVar, ie);
        // also add a substitution from the corresponding formal occurring in the PROCEDURE declaration
        Variable procOutVar = cce.NonNull(proc.OutParams[i]);
        if (procOutVar != outVar) {
          substMap.Add(procOutVar, ie);
        }
      }

      Hashtable /*Variable -> Expr*/ substMapOld = new Hashtable/*Variable -> Expr*/();

      foreach (IdentifierExpr/*!*/ mie in proc.Modifies) {
        Contract.Assert(mie != null);
        Variable/*!*/ mVar = cce.NonNull(mie.Decl);
        LocalVariable localVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, GetProcVarName(proc.Name, mVar.Name), mVar.TypedIdent.Type));
        newLocalVars.Add(localVar);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, localVar);
        substMapOld.Add(mVar, ie);
        // FIXME why are we doing this? the modifies list should already include them.
        // add the modified variable to the modifies list of the procedure
        if (!newModifies.Has(mie)) {
          newModifies.Add(mie);
        }
      }

      codeCopier.Subst = Substituter.SubstitutionFromHashtable(substMap);
      codeCopier.OldSubst = Substituter.SubstitutionFromHashtable(substMapOld);
    }

    protected void EndInline() {
      codeCopier.Subst = null;
      codeCopier.OldSubst = null;
    }


    // result[0] is the entry block
    protected List<Block/*!*/>/*!*/ CreateInlinedBlocks(CallCmd callCmd, Procedure proc, Implementation impl, string nextBlockLabel) {
      Contract.Requires(nextBlockLabel != null);
      Contract.Requires(impl != null);
      Contract.Requires(proc != null);
      Contract.Requires(callCmd != null);
      Contract.Requires(((codeCopier.Subst != null)));

      Contract.Requires((codeCopier.OldSubst != null));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      List<Block/*!*/>/*!*/ implBlocks = cce.NonNull(impl.OriginalBlocks);
      Contract.Assert(implBlocks.Count > 0);

      string startLabel = implBlocks[0].Label;

      List<Block/*!*/>/*!*/ inlinedBlocks = new List<Block/*!*/>();

      // create in block
      CmdSeq inCmds = new CmdSeq();

      // assign in parameters
      for (int i = 0; i < impl.InParams.Length; ++i) {
        Cmd cmd = Cmd.SimpleAssign(impl.tok,
                                   (IdentifierExpr)cce.NonNull(codeCopier.Subst)(cce.NonNull(impl.InParams[i])),
                                   cce.NonNull(callCmd.Ins[i]));
        inCmds.Add(cmd);
      }

      // inject non-free requires
      for (int i = 0; i < proc.Requires.Length; i++) {
        Requires/*!*/ req = cce.NonNull(proc.Requires[i]);
        if (!req.Free) {
          Requires/*!*/ reqCopy = (Requires/*!*/)cce.NonNull(req.Clone());
          reqCopy.Condition = codeCopier.CopyExpr(req.Condition);
          AssertCmd/*!*/ a = new AssertRequiresCmd(callCmd, reqCopy);
          Contract.Assert(a != null);
          a.ErrorDataEnhanced = reqCopy.ErrorDataEnhanced;
          inCmds.Add(a);
        }
      }

      VariableSeq locVars = cce.NonNull(impl.OriginalLocVars);

      // add where clauses of local vars as assume
      for (int i = 0; i < locVars.Length; ++i) {
        Expr whereExpr = (cce.NonNull(locVars[i])).TypedIdent.WhereExpr;
        if (whereExpr != null) {
          whereExpr = Substituter.Apply(codeCopier.Subst, whereExpr);
          // FIXME we cannot overwrite it, can we?!
          (cce.NonNull(locVars[i])).TypedIdent.WhereExpr = whereExpr;
          AssumeCmd/*!*/ a = new AssumeCmd(Token.NoToken, whereExpr);
          Contract.Assert(a != null);
          inCmds.Add(a);
        }
      }

      // add where clauses of output params as assume
      for (int i = 0; i < impl.OutParams.Length; ++i) {
        Expr whereExpr = (cce.NonNull(impl.OutParams[i])).TypedIdent.WhereExpr;
        if (whereExpr != null) {
          whereExpr = Substituter.Apply(codeCopier.Subst, whereExpr);
          // FIXME likewise
          (cce.NonNull(impl.OutParams[i])).TypedIdent.WhereExpr = whereExpr;
          AssumeCmd/*!*/ a = new AssumeCmd(Token.NoToken, whereExpr);
          Contract.Assert(a != null);
          inCmds.Add(a);
        }
      }

      // assign modifies old values
      foreach (IdentifierExpr/*!*/ mie in proc.Modifies) {
        Contract.Assert(mie != null);
        Variable/*!*/ mvar = cce.NonNull(mie.Decl);
        AssignCmd assign = Cmd.SimpleAssign(impl.tok, (IdentifierExpr)cce.NonNull(codeCopier.OldSubst(mvar)), mie);
        inCmds.Add(assign);
      }

      GotoCmd inGotoCmd = new GotoCmd(callCmd.tok, new StringSeq(GetInlinedProcLabel(proc.Name) + "$" + startLabel));
      Block inBlock = new Block(impl.tok, GetInlinedProcLabel(proc.Name) + "$Entry", inCmds, inGotoCmd);
      inlinedBlocks.Add(inBlock);

      // inject the blocks of the implementation
      Block intBlock;
      foreach (Block block in implBlocks) {
        CmdSeq copyCmds = codeCopier.CopyCmdSeq(block.Cmds);
        TransferCmd transferCmd = CreateInlinedTransferCmd(cce.NonNull(block.TransferCmd), GetInlinedProcLabel(proc.Name));
        intBlock = new Block(block.tok, GetInlinedProcLabel(proc.Name) + "$" + block.Label, copyCmds, transferCmd);
        inlinedBlocks.Add(intBlock);
      }

      // create out block
      CmdSeq outCmds = new CmdSeq();

      // inject non-free ensures
      for (int i = 0; i < proc.Ensures.Length; i++) {
        Ensures/*!*/ ens = cce.NonNull(proc.Ensures[i]);
        if (!ens.Free) {
          Ensures/*!*/ ensCopy = (Ensures/*!*/)cce.NonNull(ens.Clone());
          ensCopy.Condition = codeCopier.CopyExpr(ens.Condition);
          AssertCmd/*!*/ a = new AssertEnsuresCmd(ensCopy);
          Contract.Assert(a != null);
          outCmds.Add(a);
        }
      }

      // assign out params
      for (int i = 0; i < impl.OutParams.Length; ++i) {
        Expr/*!*/ cout_exp = (IdentifierExpr)cce.NonNull(codeCopier.Subst(cce.NonNull(impl.OutParams[i])));
        Cmd cmd = Cmd.SimpleAssign(impl.tok, cce.NonNull(callCmd.Outs[i]), cout_exp);
        outCmds.Add(cmd);
      }

      // create out block
      GotoCmd outGotoCmd = new GotoCmd(Token.NoToken, new StringSeq(nextBlockLabel));
      Block outBlock = new Block(impl.tok, GetInlinedProcLabel(proc.Name) + "$Return", outCmds, outGotoCmd);
      inlinedBlocks.Add(outBlock);

      return inlinedBlocks;
    }

    protected TransferCmd CreateInlinedTransferCmd(TransferCmd transferCmd, string procLabel) {
      Contract.Requires(procLabel != null);
      Contract.Requires(transferCmd != null);
      TransferCmd newTransferCmd;

      GotoCmd gotoCmd = transferCmd as GotoCmd;
      if (gotoCmd != null) {
        StringSeq gotoSeq = gotoCmd.labelNames;
        StringSeq newGotoSeq = new StringSeq();
        foreach (string/*!*/ blockLabel in cce.NonNull(gotoSeq)) {
          Contract.Assert(blockLabel != null);
          newGotoSeq.Add(procLabel + "$" + blockLabel);
        }
        newTransferCmd = new GotoCmd(transferCmd.tok, newGotoSeq);
      } else {
        newTransferCmd = new GotoCmd(transferCmd.tok, new StringSeq(procLabel + "$Return"));
      }

      return newTransferCmd;
    }

    protected static Implementation FindProcImpl(Program program, Procedure proc) {
      Contract.Requires(program != null);
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Implementation impl = decl as Implementation;
        if (impl != null && impl.Proc == proc) {
          return impl;
        }
      }
      return null;
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////

  public class CodeCopier {
    public Substitution Subst;
    public Substitution OldSubst;

    public CodeCopier(Hashtable substMap) {
      Contract.Requires(substMap != null);
      Subst = Substituter.SubstitutionFromHashtable(substMap);
    }

    public CodeCopier(Hashtable substMap, Hashtable oldSubstMap) {
      Contract.Requires(oldSubstMap != null);
      Contract.Requires(substMap != null);
      Subst = Substituter.SubstitutionFromHashtable(substMap);
      OldSubst = Substituter.SubstitutionFromHashtable(oldSubstMap);
    }

    public CodeCopier() {
    }

    public CmdSeq CopyCmdSeq(CmdSeq cmds) {
      Contract.Requires(cmds != null);
      Contract.Ensures(Contract.Result<CmdSeq>() != null);
      CmdSeq newCmds = new CmdSeq();
      foreach (Cmd/*!*/ cmd in cmds) {
        Contract.Assert(cmd != null);
        newCmds.Add(CopyCmd(cmd));
      }
      return newCmds;
    }

    public TransferCmd CopyTransferCmd(TransferCmd cmd) {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      TransferCmd transferCmd;
      GotoCmd gotocmd = cmd as GotoCmd;
      if (gotocmd != null) {
        Contract.Assert(gotocmd.labelNames != null);
        StringSeq labels = new StringSeq();
        labels.AddRange(gotocmd.labelNames);
        transferCmd = new GotoCmd(cmd.tok, labels);
      } else {
        transferCmd = new ReturnCmd(cmd.tok);
      }
      return transferCmd;
    }

    public Cmd CopyCmd(Cmd cmd) {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      if (Subst == null) {
        return cmd;
      } else if (OldSubst == null) {
        return Substituter.Apply(Subst, cmd);
      } else {
        return Substituter.ApplyReplacingOldExprs(Subst, OldSubst, cmd);
      }
    }

    public Expr CopyExpr(Expr expr) {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (Subst == null) {
        return expr;
      } else if (OldSubst == null) {
        return Substituter.Apply(Subst, expr);
      } else {
        return Substituter.ApplyReplacingOldExprs(Subst, OldSubst, expr);
      }
    }
  } // end class CodeCopier


  public class AxiomExpander : Duplicator {
    readonly Program/*!*/ program;
    readonly TypecheckingContext/*!*/ tc;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(program != null);
      Contract.Invariant(tc != null);
    }


    public AxiomExpander(Program prog, TypecheckingContext t) {
      Contract.Requires(t != null);
      Contract.Requires(prog != null);
      program = prog;
      tc = t;
    }

    public void CollectExpansions() {
      foreach (Declaration/*!*/ decl in program.TopLevelDeclarations) {
        Contract.Assert(decl != null);
        Axiom ax = decl as Axiom;
        if (ax != null) {
          bool expand = false;
          if (!ax.CheckBooleanAttribute("inline", ref expand)) {
            Error(decl.tok, "{:inline ...} expects either true or false as the argument");
          }
          if (expand) {
            AddExpansion(ax.Expr, ax.FindStringAttribute("ignore"));
          }
        }
        Function f = decl as Function;
        if (f != null && f.Body != null) {
          Variable[]/*!*/ formals = new Variable[f.InParams.Length];
          Contract.Assert(formals != null);
          for (int i = 0; i < formals.Length; ++i)
            formals[i] = f.InParams[i];
          AddExpansion(f, new Expansion(null, f.Body,
                                        new TypeVariableSeq(f.TypeParameters),
                                        formals));
        }
      }
    }

    void Error(IToken tok, string msg) {
      Contract.Requires(tok != null);
      tc.Error(tok, "expansion: " + msg);
    }

    void AddExpansion(Expr axiomBody, string ignore) {
      Contract.Requires(axiomBody != null);
      // it would be sooooooooo much easier with pattern matching
      ForallExpr all = axiomBody as ForallExpr;
      if (all != null) {
        NAryExpr nary = all.Body as NAryExpr;
        BinaryOperator bin = nary == null ? null : nary.Fun as BinaryOperator;
        //System.Console.WriteLine("{0} {1} {2}", nary==null, bin==null, bin==null?0 : bin.Op);
        if (nary != null && bin != null && (bin.Op == BinaryOperator.Opcode.Eq || bin.Op == BinaryOperator.Opcode.Iff)) {

          NAryExpr func = nary.Args[0] as NAryExpr;
          //System.Console.WriteLine("{0} {1}", func == null, func == null ? null : func.Fun.GetType());
          while (func != null && func.Fun is TypeCoercion)
            func = func.Args[0] as NAryExpr;
          if (func != null && func.Fun is FunctionCall) {
            Function fn = cce.NonNull((FunctionCall)func.Fun).Func;
            Expansion exp = new Expansion(ignore, cce.NonNull(nary.Args[1]),
                                          new TypeVariableSeq(),
                                          new Variable[func.Args.Length]);
            int pos = 0;
            HashSet<Declaration> parms = new HashSet<Declaration>();
            foreach (Expr/*!*/ e in func.Args) {
              Contract.Assert(e != null);
              IdentifierExpr id = e as IdentifierExpr;
              if (id == null) {
                Error(e.tok, "only identifiers supported as function arguments");
                return;
              }
              exp.formals[pos++] = id.Decl;
              if (parms.Contains(id.Decl)) {
                Error(all.tok, "an identifier was used more than once");
                return;
              }
              parms.Add(id.Decl);
              if (!all.Dummies.Has(id.Decl)) {
                Error(all.tok, "identifier was not quantified over");
                return;
              }
            }
            if (func.Args.Length != all.Dummies.Length) {
              Error(all.tok, "more variables quantified over, than used in function");
              return;
            }

            HashSet<TypeVariable/*!*/> typeVars = new HashSet<TypeVariable/*!*/>();
            foreach (TypeVariable/*!*/ v in cce.NonNull(func.TypeParameters).FormalTypeParams) {
              Contract.Assert(v != null);
              if (!func.TypeParameters[v].IsVariable) {
                Error(all.tok, "only identifiers supported as type parameters");
                return;
              }
              TypeVariable/*!*/ formal = func.TypeParameters[v].AsVariable;
              Contract.Assert(formal != null);
              exp.TypeParameters.Add(formal);
              if (typeVars.Contains(formal)) {
                Error(all.tok, "an identifier was used more than once");
                return;
              }
              typeVars.Add(formal);
              if (!all.TypeParameters.Has(formal)) {
                Error(all.tok, "identifier was not quantified over");
                return;
              }
            }
            if (((FunctionCall)func.Fun).Func.TypeParameters.Length != all.TypeParameters.Length) {
              Error(all.tok, "more variables quantified over, than used in function");
              return;
            }
            AddExpansion(fn, exp);
            return;
          }
        }
      }

      Error(axiomBody.tok, "axiom to be expanded must have form (forall VARS :: f(VARS) == expr(VARS))");
    }

    void AddExpansion(Function fn, Expansion x) {
      Contract.Requires(x != null);
      Contract.Requires(fn != null);
      if (fn.expansions == null) {
        fn.expansions = new List<Expansion/*!*/>();
      }
      fn.expansions.Add(x);
    }
  }
} // end namespace