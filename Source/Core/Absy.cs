//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// BoogiePL - Absy.cs
//---------------------------------------------------------------------------------------------
namespace Microsoft.Boogie.AbstractInterpretation {
  using System.Diagnostics;
  using System.Diagnostics.Contracts;
  using System.Collections;
  using System.Collections.Generic;
  using AI = Microsoft.AbstractInterpretationFramework;

  public class CallSite {
    public readonly Implementation/*!*/ Impl;
    public readonly Block/*!*/ Block;
    public readonly int Statement; // invariant: Block[Statement] is CallCmd
    public readonly AI.Lattice.Element/*!*/ KnownBeforeCall;
    public readonly ProcedureSummaryEntry/*!*/ SummaryEntry;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Impl != null);
      Contract.Invariant(Block != null);
      Contract.Invariant(KnownBeforeCall != null);
      Contract.Invariant(SummaryEntry != null);
    }


    public CallSite(Implementation impl, Block b, int stmt, AI.Lattice.Element e, ProcedureSummaryEntry summaryEntry) {
      Contract.Requires(summaryEntry != null);
      Contract.Requires(e != null);
      Contract.Requires(b != null);
      Contract.Requires(impl != null);
      this.Impl = impl;
      this.Block = b;
      this.Statement = stmt;
      this.KnownBeforeCall = e;
      this.SummaryEntry = summaryEntry;
    }
  }

  public class ProcedureSummaryEntry {
    public AI.Lattice/*!*/ Lattice;
    public AI.Lattice.Element/*!*/ OnEntry;
    public AI.Lattice.Element/*!*/ OnExit;
    public HashSet<CallSite>/*!*/ ReturnPoints; // whenever OnExit changes, we start analysis again at all the ReturnPoints
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Lattice != null);
      Contract.Invariant(OnEntry != null);
      Contract.Invariant(OnExit != null);
      Contract.Invariant(ReturnPoints != null);
    }


    public ProcedureSummaryEntry(AI.Lattice lattice, AI.Lattice.Element onEntry) {
      Contract.Requires(onEntry != null);
      Contract.Requires(lattice != null);
      this.Lattice = lattice;
      this.OnEntry = onEntry;
      this.OnExit = lattice.Bottom;
      this.ReturnPoints = new HashSet<CallSite>();
      // base();
    }

  } // class

  public class ProcedureSummary : ArrayList/*<ProcedureSummaryEntry>*/
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(
        !IsReadOnly && !IsFixedSize);
    }

    public new ProcedureSummaryEntry/*!*/ this[int i] {
      get {
        Contract.Requires(0 <= i && i < Count);
        Contract.Ensures(Contract.Result<ProcedureSummaryEntry>() != null);
        return cce.NonNull((ProcedureSummaryEntry/*!*/)base[i]);
      }
    }

  } // class
} // namespace

namespace Microsoft.Boogie {
  using System;
  using System.Collections;
  using System.Diagnostics;
  using System.Collections.Generic;
  using System.Diagnostics.Contracts;
  using Microsoft.Boogie.AbstractInterpretation;
  using AI = Microsoft.AbstractInterpretationFramework;
  using Graphing;
  using Set = GSet<object>;

  [ContractClass(typeof(AbsyContracts))]
  public abstract class Absy {
    public IToken/*!*/ tok;
    private int uniqueId;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }


    public int Line {
      get {
        return tok != null ? tok.line : -1;
      }
    }
    public int Col {
      get {
        return tok != null ? tok.col : -1;
      }
    }

    public Absy(IToken tok) {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.uniqueId = AbsyNodeCount++;
      // base();
    }

    private static int AbsyNodeCount = 0;

    // We uniquely number every AST node to make them
    // suitable for our implementation of functional maps.
    //
    public int UniqueId {
      get {
        return this.uniqueId;
      }
    }

    private const int indent_size = 2;
    protected static string Indent(int level) {
      return new string(' ', (indent_size * level));
    }
    [NeedsContracts]
    public abstract void Resolve(ResolutionContext/*!*/ rc);

    /// <summary>
    /// Requires the object to have been successfully resolved.
    /// </summary>
    /// <param name="tc"></param>
    [NeedsContracts]
    public abstract void Typecheck(TypecheckingContext/*!*/ tc);
    /// <summary>
    /// Intorduced this so the uniqueId is not the same on a cloned object.
    /// </summary>
    /// <param name="tc"></param>
    public virtual Absy Clone() {
      Contract.Ensures(Contract.Result<Absy>() != null);
      Absy/*!*/ result = cce.NonNull((Absy/*!*/)this.MemberwiseClone());
      result.uniqueId = AbsyNodeCount++; // BUGBUG??
      return result;
    }

    public virtual Absy StdDispatch(StandardVisitor visitor) {
      Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      System.Diagnostics.Debug.Fail("Unknown Absy node type: " + this.GetType());
      throw new System.NotImplementedException();
    }
  }

  [ContractClassFor(typeof(Absy))]
  public abstract class AbsyContracts : Absy {
    public override void Resolve(ResolutionContext rc) {
      Contract.Requires(rc != null);
      throw new NotImplementedException();
    }
    public AbsyContracts() :base(null){

    }
    public override void Typecheck(TypecheckingContext tc) {
      Contract.Requires(tc != null);
      throw new NotImplementedException();
    }
  }

  // TODO: Ideally, this would use generics.
  public interface IPotentialErrorNode {
    object ErrorData {
      get;
      set;
    }
  }

  public class Program : Absy {
    [Rep]
    public List<Declaration/*!*/>/*!*/ TopLevelDeclarations;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TopLevelDeclarations));
      Contract.Invariant(globals == null || cce.NonNullElements(globals));
    }


    public Program()
      : base(Token.NoToken) {
      this.TopLevelDeclarations = new List<Declaration>();
      // base(Token.NoToken);
    }

    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      stream.SetToken(this);
      Emitter.Declarations(this.TopLevelDeclarations, stream);
    }

    public void ProcessDatatypeConstructors() {
      Dictionary<string, DatatypeConstructor> constructors = new Dictionary<string, DatatypeConstructor>();
      List<Declaration> prunedTopLevelDeclarations = new List<Declaration>();
      foreach (Declaration decl in TopLevelDeclarations) {
        Function func = decl as Function;
        if (func == null || !QKeyValue.FindBoolAttribute(decl.Attributes, "constructor")) {
          prunedTopLevelDeclarations.Add(decl);
          continue;
        }
        if (constructors.ContainsKey(func.Name)) continue;
        DatatypeConstructor constructor = new DatatypeConstructor(func);
        constructors.Add(func.Name, constructor);
        prunedTopLevelDeclarations.Add(constructor);
      }
      TopLevelDeclarations = prunedTopLevelDeclarations;
    
      foreach (DatatypeConstructor f in constructors.Values) {
        for (int i = 0; i < f.InParams.Length; i++) {
          DatatypeSelector selector = new DatatypeSelector(f, i);
          f.selectors.Add(selector);
          TopLevelDeclarations.Add(selector);
        }
        DatatypeMembership membership = new DatatypeMembership(f);
        f.membership = membership;
        TopLevelDeclarations.Add(membership);
      }
    }

    /// <summary>
    /// Returns the number of name resolution errors.
    /// </summary>
    /// <returns></returns>
    public int Resolve() {
      return Resolve((IErrorSink)null);
    }

    public int Resolve(IErrorSink errorSink) {
      ResolutionContext rc = new ResolutionContext(errorSink);
      Resolve(rc);
      return rc.ErrorCount;
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      Helpers.ExtraTraceInformation("Starting resolution");

      foreach (Declaration d in TopLevelDeclarations) {
        d.Register(rc);
      }

      ResolveTypes(rc);

      var prunedTopLevelDecls = new List<Declaration/*!*/>();
      foreach (Declaration d in TopLevelDeclarations) {
        if (QKeyValue.FindBoolAttribute(d.Attributes, "ignore")) {
          continue;
        }
        // resolve all the non-type-declarations
        if (d is TypeCtorDecl || d is TypeSynonymDecl) {
        } else {
          int e = rc.ErrorCount;
          d.Resolve(rc);
          if (CommandLineOptions.Clo.OverlookBoogieTypeErrors && rc.ErrorCount != e && d is Implementation) {
            // ignore this implementation
            System.Console.WriteLine("Warning: Ignoring implementation {0} because of translation resolution errors", ((Implementation)d).Name);
            rc.ErrorCount = e;
            continue;
          }
        }
        prunedTopLevelDecls.Add(d);
      }
      TopLevelDeclarations = prunedTopLevelDecls;

      foreach (Declaration d in TopLevelDeclarations) {
        Variable v = d as Variable;
        if (v != null) {
          v.ResolveWhere(rc);
        }
      }
    }

    private void ResolveTypes(ResolutionContext rc) {
      Contract.Requires(rc != null);
      // first resolve type constructors
      foreach (Declaration d in TopLevelDeclarations) {
        if (d is TypeCtorDecl && !QKeyValue.FindBoolAttribute(d.Attributes, "ignore"))
          d.Resolve(rc);
      }

      // collect type synonym declarations
      List<TypeSynonymDecl/*!*/>/*!*/ synonymDecls = new List<TypeSynonymDecl/*!*/>();
      foreach (Declaration d in TopLevelDeclarations) {
        Contract.Assert(d != null);
        if (d is TypeSynonymDecl && !QKeyValue.FindBoolAttribute(d.Attributes, "ignore"))
          synonymDecls.Add((TypeSynonymDecl)d);
      }

      // then resolve the type synonyms by a simple
      // fixed-point iteration
      TypeSynonymDecl.ResolveTypeSynonyms(synonymDecls, rc);
    }

    public int Typecheck() {
      return this.Typecheck((IErrorSink)null);
    }

    public int Typecheck(IErrorSink errorSink) {
      TypecheckingContext tc = new TypecheckingContext(errorSink);
      Typecheck(tc);
      return tc.ErrorCount;
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Helpers.ExtraTraceInformation("Starting typechecking");

      int oldErrorCount = tc.ErrorCount;
      foreach (Declaration d in TopLevelDeclarations) {
        d.Typecheck(tc);
      }

      if (oldErrorCount == tc.ErrorCount) {
        // check whether any type proxies have remained uninstantiated
        TypeAmbiguitySeeker/*!*/ seeker = new TypeAmbiguitySeeker(tc);
        foreach (Declaration d in TopLevelDeclarations) {
          seeker.Visit(d);
        }
      }
    }

    public void ComputeStronglyConnectedComponents() {
      foreach (Declaration d in this.TopLevelDeclarations) {
        d.ComputeStronglyConnectedComponents();
      }
    }

    public void InstrumentWithInvariants() {
      foreach (Declaration d in this.TopLevelDeclarations) {
        d.InstrumentWithInvariants();
      }
    }

    /// <summary>
    /// Reset the abstract stated computed before
    /// </summary>
    public void ResetAbstractInterpretationState() {
      foreach (Declaration d in this.TopLevelDeclarations) {
        d.ResetAbstractInterpretationState();
      }
    }

    public void UnrollLoops(int n) {
      Contract.Requires(0 <= n);
      foreach (Declaration d in this.TopLevelDeclarations) {
        Implementation impl = d as Implementation;
        if (impl != null && impl.Blocks != null && impl.Blocks.Count > 0) {
          cce.BeginExpose(impl);
          {
            Block start = impl.Blocks[0];
            Contract.Assume(start != null);
            Contract.Assume(cce.IsConsistent(start));
            impl.Blocks = LoopUnroll.UnrollLoops(start, n);
          }
          cce.EndExpose();
        }
      }
    }

    void CreateProceduresForLoops(Implementation impl, Graph<Block/*!*/>/*!*/ g,
                                  List<Implementation/*!*/>/*!*/ loopImpls,
                                  Dictionary<string, Dictionary<string, Block>> fullMap) {
      Contract.Requires(impl != null);
      Contract.Requires(cce.NonNullElements(loopImpls));
      // Enumerate the headers
      // for each header h:
      //   create implementation p_h with
      //     inputs = inputs, outputs, and locals of impl
      //     outputs = outputs and locals of impl
      //     locals = empty set
      //   add call o := p_h(i) at the beginning of the header block
      //   break the back edges whose target is h
      // Enumerate the headers again to create the bodies of p_h
      // for each header h:
      //   compute the loop corresponding to h
      //   make copies of all blocks in the loop for h
      //   delete all target edges that do not go to a block in the loop
      //   create a new entry block and a new return block
      //   add edges from entry block to the loop header and the return block
      //   add calls o := p_h(i) at the end of the blocks that are sources of back edges
      foreach (Block block in impl.Blocks)
      {
          AddToFullMap(fullMap, impl.Name, block.Label, block);
      }

      bool detLoopExtract = CommandLineOptions.Clo.DeterministicExtractLoops;

      Dictionary<Block/*!*/, VariableSeq/*!*/>/*!*/ loopHeaderToInputs = new Dictionary<Block/*!*/, VariableSeq/*!*/>();
      Dictionary<Block/*!*/, VariableSeq/*!*/>/*!*/ loopHeaderToOutputs = new Dictionary<Block/*!*/, VariableSeq/*!*/>();
      Dictionary<Block/*!*/, Hashtable/*!*/>/*!*/ loopHeaderToSubstMap = new Dictionary<Block/*!*/, Hashtable/*!*/>();
      Dictionary<Block/*!*/, LoopProcedure/*!*/>/*!*/ loopHeaderToLoopProc = new Dictionary<Block/*!*/, LoopProcedure/*!*/>();
      Dictionary<Block/*!*/, CallCmd/*!*/>/*!*/ loopHeaderToCallCmd1 = new Dictionary<Block/*!*/, CallCmd/*!*/>();
      Dictionary<Block, CallCmd> loopHeaderToCallCmd2 = new Dictionary<Block, CallCmd>();
      Dictionary<Block, AssignCmd> loopHeaderToAssignCmd = new Dictionary<Block, AssignCmd>();

      foreach (Block/*!*/ header in g.Headers) {
        Contract.Assert(header != null);
        Contract.Assert(header != null);
        VariableSeq inputs = new VariableSeq();
        VariableSeq outputs = new VariableSeq();
        ExprSeq callInputs1 = new ExprSeq();
        IdentifierExprSeq callOutputs1 = new IdentifierExprSeq();
        ExprSeq callInputs2 = new ExprSeq();
        IdentifierExprSeq callOutputs2 = new IdentifierExprSeq();
        List<AssignLhs> lhss = new List<AssignLhs>();
        List<Expr> rhss = new List<Expr>();
        Hashtable substMap = new Hashtable(); // Variable -> IdentifierExpr

        VariableSeq/*!*/ targets = new VariableSeq();
        HashSet<Variable> footprint = new HashSet<Variable>();

        foreach (Block/*!*/ b in g.BackEdgeNodes(header))
        {
            Contract.Assert(b != null);
            foreach (Block/*!*/ block in g.NaturalLoops(header, b))
            {
                Contract.Assert(block != null);
                foreach (Cmd/*!*/ cmd in block.Cmds)
                {
                    Contract.Assert(cmd != null);
                    cmd.AddAssignedVariables(targets);

                    VariableCollector c = new VariableCollector();
                    c.Visit(cmd);
                    footprint.UnionWith(c.usedVars);
                }
            }
        }

        IdentifierExprSeq/*!*/ globalMods = new IdentifierExprSeq();
        Set targetSet = new Set();
        foreach (Variable/*!*/ v in targets)
        {
            Contract.Assert(v != null);
            if (targetSet.Contains(v))
                continue;
            targetSet.Add(v);
            if (v is GlobalVariable)
                globalMods.Add(new IdentifierExpr(Token.NoToken, v));
        }

        foreach (Variable v in impl.InParams) {
          Contract.Assert(v != null);
          if (!footprint.Contains(v)) continue;
          callInputs1.Add(new IdentifierExpr(Token.NoToken, v));
          Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in_" + v.Name, v.TypedIdent.Type), true);
          inputs.Add(f);
          callInputs2.Add(new IdentifierExpr(Token.NoToken, f));
          substMap[v] = new IdentifierExpr(Token.NoToken, f);
        }
        foreach (Variable v in impl.OutParams) {
          Contract.Assert(v != null);
          if (!footprint.Contains(v)) continue;
          callInputs1.Add(new IdentifierExpr(Token.NoToken, v));
          Formal f1 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in_" + v.Name, v.TypedIdent.Type), true);
          inputs.Add(f1);
          if (targetSet.Contains(v))
          {
              callOutputs1.Add(new IdentifierExpr(Token.NoToken, v));
              Formal f2 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out_" + v.Name, v.TypedIdent.Type), false);
              outputs.Add(f2);
              callInputs2.Add(new IdentifierExpr(Token.NoToken, f2));
              callOutputs2.Add(new IdentifierExpr(Token.NoToken, f2));
              lhss.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, f2)));
              rhss.Add(new IdentifierExpr(Token.NoToken, f1));
              substMap[v] = new IdentifierExpr(Token.NoToken, f2);
          }
          else
          {
              callInputs2.Add(new IdentifierExpr(Token.NoToken, f1));
              substMap[v] = new IdentifierExpr(Token.NoToken, f1);
          }
        }
        foreach (Variable v in impl.LocVars) {
          Contract.Assert(v != null);
          if (!footprint.Contains(v)) continue;
          callInputs1.Add(new IdentifierExpr(Token.NoToken, v));
          Formal f1 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in_" + v.Name, v.TypedIdent.Type), true);
          inputs.Add(f1);
          if (targetSet.Contains(v))
          {
              callOutputs1.Add(new IdentifierExpr(Token.NoToken, v));
              Formal f2 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out_" + v.Name, v.TypedIdent.Type), false);
              outputs.Add(f2);
              callInputs2.Add(new IdentifierExpr(Token.NoToken, f2));
              callOutputs2.Add(new IdentifierExpr(Token.NoToken, f2));
              lhss.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, f2)));
              rhss.Add(new IdentifierExpr(Token.NoToken, f1));
              substMap[v] = new IdentifierExpr(Token.NoToken, f2);
          }
          else
          {
              callInputs2.Add(new IdentifierExpr(Token.NoToken, f1));
              substMap[v] = new IdentifierExpr(Token.NoToken, f1);
          }
        }

        loopHeaderToInputs[header] = inputs;
        loopHeaderToOutputs[header] = outputs;
        loopHeaderToSubstMap[header] = substMap;
        LoopProcedure loopProc = new LoopProcedure(impl, header, inputs, outputs, globalMods);
        loopHeaderToLoopProc[header] = loopProc;

        CallCmd callCmd1 = new CallCmd(Token.NoToken, loopProc.Name, callInputs1, callOutputs1);
        callCmd1.Proc = loopProc;
        loopHeaderToCallCmd1[header] = callCmd1;

        CallCmd callCmd2 = new CallCmd(Token.NoToken, loopProc.Name, callInputs2, callOutputs2);
        callCmd2.Proc = loopProc;
        loopHeaderToCallCmd2[header] = callCmd2;

        Debug.Assert(lhss.Count == rhss.Count);
        if (lhss.Count > 0)
        {
            AssignCmd assignCmd = new AssignCmd(Token.NoToken, lhss, rhss);
            loopHeaderToAssignCmd[header] = assignCmd;
        }
      }

      // Keep track of the new blocks created: maps a header node to the
      // header_last block that was created because of splitting header.
      Dictionary<Block, Block> newBlocksCreated = new Dictionary<Block, Block>();

      bool headRecursion = false; // testing an option to put recursive call before loop body 

      IEnumerable<Block> sortedHeaders = g.SortHeadersByDominance();
      foreach (Block/*!*/ header in sortedHeaders)
      {
        Contract.Assert(header != null);
        LoopProcedure loopProc = loopHeaderToLoopProc[header];
        Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
        HashSet<string> dummyBlocks = new HashSet<string>();

        CodeCopier codeCopier = new CodeCopier(loopHeaderToSubstMap[header]);  // fix me
        VariableSeq inputs = loopHeaderToInputs[header];
        VariableSeq outputs = loopHeaderToOutputs[header];
        int si_unique_loc = 1; // Added by AL: to distinguish the back edges
        foreach (Block/*!*/ source in g.BackEdgeNodes(header)) {
          Contract.Assert(source != null);
          foreach (Block/*!*/ block in g.NaturalLoops(header, source)) {
            Contract.Assert(block != null);
            if (blockMap.ContainsKey(block))
              continue;
            Block newBlock = new Block();
            newBlock.Label = block.Label;
            if (headRecursion && block == header)
            {
                CallCmd callCmd = (CallCmd)(loopHeaderToCallCmd2[header]).Clone();
                addUniqueCallAttr(si_unique_loc, callCmd);
                si_unique_loc++;
                newBlock.Cmds.Add(callCmd);  // add the recursive call at head of loop
                var rest = codeCopier.CopyCmdSeq(block.Cmds);
                newBlock.Cmds.AddRange(rest);
            }
            else
              newBlock.Cmds = codeCopier.CopyCmdSeq(block.Cmds);
            blockMap[block] = newBlock;
            if (newBlocksCreated.ContainsKey(block))
            {
                Block newBlock2 = new Block();
                newBlock2.Label = newBlocksCreated[block].Label;
                newBlock2.Cmds = codeCopier.CopyCmdSeq(newBlocksCreated[block].Cmds);
                blockMap[newBlocksCreated[block]] = newBlock2;
            }
            //for detLoopExtract, need the immediate successors even outside the loop
            if (detLoopExtract) {
                GotoCmd auxGotoCmd = block.TransferCmd as GotoCmd;
                Contract.Assert(auxGotoCmd != null && auxGotoCmd.labelNames != null && 
                    auxGotoCmd.labelTargets != null && auxGotoCmd.labelTargets.Length >= 1);
                foreach(var bl in auxGotoCmd.labelTargets) {
                    bool found = false;
                    foreach(var n in g.NaturalLoops(header, source)) { //very expensive, can we do a contains?
                        if (bl == n) { //clarify: is this the right comparison?
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        Block auxNewBlock = new Block();
                        auxNewBlock.Label = ((Block)bl).Label;
                        auxNewBlock.Cmds = codeCopier.CopyCmdSeq(((Block)bl).Cmds);
                        //add restoration code for such blocks
                        if (loopHeaderToAssignCmd.ContainsKey(header))
                        {
                            AssignCmd assignCmd = loopHeaderToAssignCmd[header];
                            auxNewBlock.Cmds.Add(assignCmd);
                        }
                        List<AssignLhs> lhsg = new List<AssignLhs>();
                        IdentifierExprSeq/*!*/ globalsMods = loopHeaderToLoopProc[header].Modifies;
                        foreach (IdentifierExpr gl in globalsMods)
                            lhsg.Add(new SimpleAssignLhs(Token.NoToken, gl));
                        List<Expr> rhsg = new List<Expr>();
                        foreach (IdentifierExpr gl in globalsMods)
                            rhsg.Add(new OldExpr(Token.NoToken, gl));
                        if (lhsg.Count != 0)
                        {
                            AssignCmd globalAssignCmd = new AssignCmd(Token.NoToken, lhsg, rhsg);
                            auxNewBlock.Cmds.Add(globalAssignCmd);
                        }
                        blockMap[(Block)bl] = auxNewBlock;
                    }
                }

            }
          }

          CmdSeq cmdSeq;
          if (headRecursion)
              cmdSeq = new CmdSeq();
          else
          {
              CallCmd callCmd = (CallCmd)(loopHeaderToCallCmd2[header]).Clone();
              addUniqueCallAttr(si_unique_loc, callCmd);
              si_unique_loc++;
              cmdSeq = new CmdSeq(callCmd);
          }

          Block/*!*/ block1 = new Block(Token.NoToken, source.Label + "_dummy",
                              new CmdSeq(new AssumeCmd(Token.NoToken, Expr.False)), new ReturnCmd(Token.NoToken));
          Block/*!*/ block2 = new Block(Token.NoToken, block1.Label,
                              cmdSeq, new ReturnCmd(Token.NoToken));
          impl.Blocks.Add(block1);
          dummyBlocks.Add(block1.Label);

          GotoCmd gotoCmd = source.TransferCmd as GotoCmd;
          Contract.Assert(gotoCmd != null && gotoCmd.labelNames != null && gotoCmd.labelTargets != null && gotoCmd.labelTargets.Length >= 1);
          StringSeq/*!*/ newLabels = new StringSeq();
          BlockSeq/*!*/ newTargets = new BlockSeq();
          for (int i = 0; i < gotoCmd.labelTargets.Length; i++) {
            if (gotoCmd.labelTargets[i] == header)
              continue;
            newTargets.Add(gotoCmd.labelTargets[i]);
            newLabels.Add(gotoCmd.labelNames[i]);
          }
          newTargets.Add(block1);
          newLabels.Add(block1.Label);
          gotoCmd.labelNames = newLabels;
          gotoCmd.labelTargets = newTargets;
          blockMap[block1] = block2;
        }
        List<Block/*!*/>/*!*/ blocks = new List<Block/*!*/>();
        Block exit = new Block(Token.NoToken, "exit", new CmdSeq(), new ReturnCmd(Token.NoToken));
        GotoCmd cmd = new GotoCmd(Token.NoToken,
                                    new StringSeq(cce.NonNull(blockMap[header]).Label, exit.Label),
                                    new BlockSeq(blockMap[header], exit));

        if (detLoopExtract) //cutting the non-determinism
            cmd = new GotoCmd(Token.NoToken,
                                    new StringSeq(cce.NonNull(blockMap[header]).Label),
                                    new BlockSeq(blockMap[header]));

        Block entry;
        CmdSeq initCmds = new CmdSeq();
        if (loopHeaderToAssignCmd.ContainsKey(header)) {
            AssignCmd assignCmd = loopHeaderToAssignCmd[header];
            initCmds.Add(assignCmd);
        }

        entry = new Block(Token.NoToken, "entry", initCmds, cmd);
        blocks.Add(entry);

        foreach (Block/*!*/ block in blockMap.Keys) {
          Contract.Assert(block != null);
          Block/*!*/ newBlock = cce.NonNull(blockMap[block]);
          GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
          if (gotoCmd == null) {
            newBlock.TransferCmd = new ReturnCmd(Token.NoToken);
          } else {
            Contract.Assume(gotoCmd.labelNames != null && gotoCmd.labelTargets != null);
            StringSeq newLabels = new StringSeq();
            BlockSeq newTargets = new BlockSeq();
            for (int i = 0; i < gotoCmd.labelTargets.Length; i++) {
              Block target = gotoCmd.labelTargets[i];
              if (blockMap.ContainsKey(target)) {
                newLabels.Add(gotoCmd.labelNames[i]);
                newTargets.Add(blockMap[target]);
              }  
            }
            if (newTargets.Length == 0) {
                if (!detLoopExtract)
                    newBlock.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                newBlock.TransferCmd = new ReturnCmd(Token.NoToken);
            } else {
              newBlock.TransferCmd = new GotoCmd(Token.NoToken, newLabels, newTargets);
            }
          }
          blocks.Add(newBlock);
        }
        blocks.Add(exit);
        Implementation loopImpl =
            new Implementation(Token.NoToken, loopProc.Name,
                                new TypeVariableSeq(), inputs, outputs, new VariableSeq(), blocks);
        loopImpl.Proc = loopProc;
        loopImpls.Add(loopImpl);

        // Make a (shallow) copy of the header before splitting it
        Block origHeader = new Block(header.tok, header.Label, header.Cmds, header.TransferCmd);

        // Finally, add call to the loop in the containing procedure
        string lastIterBlockName = header.Label + "_last";
        Block lastIterBlock = new Block(Token.NoToken, lastIterBlockName, header.Cmds, header.TransferCmd);
        newBlocksCreated[header] = lastIterBlock;
        header.Cmds = new CmdSeq(loopHeaderToCallCmd1[header]);
        header.TransferCmd = new GotoCmd(Token.NoToken, new StringSeq(lastIterBlockName), new BlockSeq(lastIterBlock));
        impl.Blocks.Add(lastIterBlock);
        blockMap[origHeader] = blockMap[header];
        blockMap.Remove(header);

        Contract.Assert(fullMap[impl.Name][header.Label] == header);
        fullMap[impl.Name][header.Label] = origHeader;

        foreach (Block block in blockMap.Keys)
        {
            // Don't add dummy blocks to the map
            if (dummyBlocks.Contains(blockMap[block].Label)) continue;

            // Following two statements are for nested loops: compose map
            if (!fullMap[impl.Name].ContainsKey(block.Label)) continue;
            var target = fullMap[impl.Name][block.Label];

            AddToFullMap(fullMap, loopProc.Name, blockMap[block].Label, target);
        }

        fullMap[impl.Name].Remove(header.Label);
        fullMap[impl.Name][lastIterBlockName] = origHeader;
      }
    }

    private void addUniqueCallAttr(int val, CallCmd cmd)
    {
        var a = new List<object>();
        a.Add(new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(val)));

        cmd.Attributes = new QKeyValue(Token.NoToken, "si_unique_call", a, cmd.Attributes);
    }

    private void AddToFullMap(Dictionary<string, Dictionary<string, Block>> fullMap, string procName, string blockName, Block block)
    {
        if (!fullMap.ContainsKey(procName))
            fullMap[procName] = new Dictionary<string, Block>();
        fullMap[procName][blockName] = block;
    }

    public static Graph<Block/*!*/>/*!*/ GraphFromImpl(Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<Graph<Block>>().TopologicalSort()));
      Contract.Ensures(Contract.Result<Graph<Block>>() != null);

      Graph<Block/*!*/> g = new Graph<Block/*!*/>();
      g.AddSource(impl.Blocks[0]); // there is always at least one node in the graph

      foreach (Block b in impl.Blocks) {
        Contract.Assert(b != null);
        GotoCmd gtc = b.TransferCmd as GotoCmd;
        if (gtc != null) {
          foreach (Block/*!*/ dest in cce.NonNull(gtc.labelTargets)) {
            Contract.Assert(dest != null);
            g.AddEdge(b, dest);
          }
        }
      }
      return g;
    }

    public class IrreducibleLoopException : Exception {}

    public Graph<Block> ProcessLoops(Implementation impl) {
      while (true) {
        impl.PruneUnreachableBlocks();
        impl.ComputePredecessorsForBlocks();
        Graph<Block/*!*/>/*!*/ g = GraphFromImpl(impl);
        g.ComputeLoops();
        if (g.Reducible) {
          return g;
        }
        throw new IrreducibleLoopException();
#if USED_CODE
        System.Diagnostics.Debug.Assert(g.SplitCandidates.Count > 0);
        Block splitCandidate = null;
        foreach (Block b in g.SplitCandidates) {
          if (b.Predecessors.Length > 1) {
            splitCandidate = b;
            break;
          }
        }
        System.Diagnostics.Debug.Assert(splitCandidate != null);
        int count = 0;
        foreach (Block b in splitCandidate.Predecessors) {
          GotoCmd gotoCmd = (GotoCmd)b.TransferCmd;
          gotoCmd.labelNames.Remove(splitCandidate.Label);
          gotoCmd.labelTargets.Remove(splitCandidate);

          CodeCopier codeCopier = new CodeCopier(new Hashtable(), new Hashtable());
          CmdSeq newCmdSeq = codeCopier.CopyCmdSeq(splitCandidate.Cmds);
          TransferCmd newTransferCmd;
          GotoCmd splitGotoCmd = splitCandidate.TransferCmd as GotoCmd;
          if (splitGotoCmd == null) {
            newTransferCmd = new ReturnCmd(splitCandidate.tok);
          }
          else {
            StringSeq newLabelNames = new StringSeq();
            newLabelNames.AddRange(splitGotoCmd.labelNames);
            BlockSeq newLabelTargets = new BlockSeq();
            newLabelTargets.AddRange(splitGotoCmd.labelTargets);
            newTransferCmd = new GotoCmd(splitCandidate.tok, newLabelNames, newLabelTargets);
          }
          Block copy = new Block(splitCandidate.tok, splitCandidate.Label + count++, newCmdSeq, newTransferCmd);

          impl.Blocks.Add(copy);
          gotoCmd.AddTarget(copy);
        }
#endif
      }
    }

    public Dictionary<string, Dictionary<string, Block>> ExtractLoops()
    {
        List<Implementation/*!*/>/*!*/ loopImpls = new List<Implementation/*!*/>();
        Dictionary<string, Dictionary<string, Block>> fullMap = new Dictionary<string, Dictionary<string, Block>>();
        foreach (Declaration d in this.TopLevelDeclarations)
        {
            Implementation impl = d as Implementation;
            if (impl != null && impl.Blocks != null && impl.Blocks.Count > 0)
            {
                try
                {
                    Graph<Block> g = ProcessLoops(impl);
                    CreateProceduresForLoops(impl, g, loopImpls, fullMap);
                }
                catch (IrreducibleLoopException)
                {
                    System.Diagnostics.Debug.Assert(!fullMap.ContainsKey(impl.Name));
                    fullMap[impl.Name] = null;

                    // statically unroll loops in this procedure

                    // First, build a map of the current blocks
                    var origBlocks = new Dictionary<string, Block>();
                    foreach (var blk in impl.Blocks) origBlocks.Add(blk.Label, blk);

                    // unroll
                    Block start = impl.Blocks[0];
                    impl.Blocks = LoopUnroll.UnrollLoops(start, CommandLineOptions.Clo.RecursionBound);

                    // Now construct the "map back" information
                    // Resulting block label -> original block
                    var blockMap = new Dictionary<string, Block>();
                    foreach (var blk in impl.Blocks)
                    {
                        var sl = LoopUnroll.sanitizeLabel(blk.Label);
                        if (sl == blk.Label) blockMap.Add(blk.Label, blk);
                        else
                        {
                            Contract.Assert(origBlocks.ContainsKey(sl));
                            blockMap.Add(blk.Label, origBlocks[sl]);
                        }
                    }
                    fullMap[impl.Name] = blockMap;
                }
            }
        }
        foreach (Implementation/*!*/ loopImpl in loopImpls)
        {
            Contract.Assert(loopImpl != null);
            TopLevelDeclarations.Add(loopImpl);
            TopLevelDeclarations.Add(loopImpl.Proc);
        }
        return fullMap;
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitProgram(this);
    }

    private List<GlobalVariable/*!*/> globals = null;
    public List<GlobalVariable/*!*/>/*!*/ GlobalVariables() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<GlobalVariable>>()));
      if (globals != null)
        return globals;
      globals = new List<GlobalVariable/*!*/>();
      foreach (Declaration d in TopLevelDeclarations) {
        GlobalVariable gvar = d as GlobalVariable;
        if (gvar != null)
          globals.Add(gvar);
      }
      return globals;
    }

    private int invariantGenerationCounter = 0;

    public Constant MakeExistentialBoolean() {
      Constant ExistentialBooleanConstant = new Constant(Token.NoToken, new TypedIdent(tok, "_b" + invariantGenerationCounter, Microsoft.Boogie.Type.Bool), false);
      invariantGenerationCounter++;
      ExistentialBooleanConstant.AddAttribute("existential", new object[] { Expr.True });
      TopLevelDeclarations.Add(ExistentialBooleanConstant);
      return ExistentialBooleanConstant;
    }

    public PredicateCmd CreateCandidateInvariant(Expr e, string tag = null) {
      Constant ExistentialBooleanConstant = MakeExistentialBoolean();
      IdentifierExpr ExistentialBoolean = new IdentifierExpr(Token.NoToken, ExistentialBooleanConstant);
      PredicateCmd invariant = new AssertCmd(Token.NoToken, Expr.Imp(ExistentialBoolean, e));
      if (tag != null)
        invariant.Attributes = new QKeyValue(Token.NoToken, "tag", new List<object>(new object[] { tag }), null);
      return invariant;
    }
  }

  //---------------------------------------------------------------------
  // Declarations

  [ContractClass(typeof(DeclarationContracts))]
  public abstract class Declaration : Absy {
    public QKeyValue Attributes;

    public Declaration(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }

    protected void EmitAttributes(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        kv.Emit(stream);
        stream.Write(" ");
      }
    }

    protected void ResolveAttributes(ResolutionContext rc) {
      Contract.Requires(rc != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        kv.Resolve(rc);
      }
    }

    protected void TypecheckAttributes(TypecheckingContext rc) {
      Contract.Requires(rc != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        kv.Typecheck(rc);
      }
    }

    // Look for {:name true} or {:name false} in list of attributes. Return result in 'result'
    // (which is not touched if there is no attribute specified).
    //
    // Returns false is there was an error processing the flag, true otherwise.
    public bool CheckBooleanAttribute(string name, ref bool result) {
      Contract.Requires(name != null);
      Expr expr = FindExprAttribute(name);
      if (expr != null) {
        if (expr is LiteralExpr && ((LiteralExpr)expr).isBool) {
          result = ((LiteralExpr)expr).asBool;
        } else {
          return false;
        }
      }
      return true;
    }

    // Look for {:name expr} in list of attributes.
    public Expr FindExprAttribute(string name) {
      Contract.Requires(name != null);
      Expr res = null;
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next) {
        if (kv.Key == name) {
          if (kv.Params.Count == 1 && kv.Params[0] is Expr) {
            res = (Expr)kv.Params[0];
          }
        }
      }
      return res;
    }

    // Look for {:name string} in list of attributes.
    public string FindStringAttribute(string name) {
      Contract.Requires(name != null);
      return QKeyValue.FindStringAttribute(this.Attributes, name);
    }

    // Look for {:name N} or {:name N} in list of attributes. Return result in 'result'
    // (which is not touched if there is no attribute specified).
    //
    // Returns false is there was an error processing the flag, true otherwise.
    public bool CheckIntAttribute(string name, ref int result) {
      Contract.Requires(name != null);
      Expr expr = FindExprAttribute(name);
      if (expr != null) {
        if (expr is LiteralExpr && ((LiteralExpr)expr).isBigNum) {
          result = ((LiteralExpr)expr).asBigNum.ToInt;
        } else {
          return false;
        }
      }
      return true;
    }

    public void AddAttribute(string name, params object[] vals) {
      Contract.Requires(name != null);
      QKeyValue kv;
      for (kv = this.Attributes; kv != null; kv = kv.Next) {
        if (kv.Key == name) {
          kv.Params.AddRange(vals);
          break;
        }
      }
      if (kv == null) {
        Attributes = new QKeyValue(tok, name, new List<object/*!*/>(vals), Attributes);
      }
    }

    public abstract void Emit(TokenTextWriter/*!*/ stream, int level);
    public abstract void Register(ResolutionContext/*!*/ rc);

    /// <summary>
    /// Compute the strongly connected components of the declaration.
    /// By default, it does nothing
    /// </summary>
    public virtual void ComputeStronglyConnectedComponents() { /* Does nothing */
    }

    /// <summary>
    /// This method inserts the abstract-interpretation-inferred invariants
    /// as assume (or possibly assert) statements in the statement sequences of
    /// each block.
    /// </summary>
    public virtual void InstrumentWithInvariants() {
    }

    /// <summary>
    /// Reset the abstract stated computed before
    /// </summary>
    public virtual void ResetAbstractInterpretationState() { /* does nothing */
    }
  }
  [ContractClassFor(typeof(Declaration))]
  public abstract class DeclarationContracts : Declaration {
    public DeclarationContracts() :base(null){
    }
    public override void Register(ResolutionContext rc) {
      Contract.Requires(rc != null);
      throw new NotImplementedException();
    }
    public override void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }
  }

  public class Axiom : Declaration {
    public Expr/*!*/ Expr;
    [ContractInvariantMethod]
    void ExprInvariant() {
      Contract.Invariant(Expr != null);
    }

    public string Comment;

    public Axiom(IToken tok, Expr expr)
      : this(tok, expr, null) {
      Contract.Requires(expr != null);
      Contract.Requires(tok != null);
      //:this(tok, expr, null);//BASEMOVEA
    }

    public Axiom(IToken/*!*/ tok, Expr/*!*/ expr, string comment)
      : base(tok) {//BASEMOVE DANGER
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
      Comment = comment;
      // :base(tok);
    }

    public Axiom(IToken tok, Expr expr, string comment, QKeyValue kv)
      : this(tok, expr, comment) {//BASEMOVEA
      Contract.Requires(expr != null);
      Contract.Requires(tok != null);
      //:this(tok, expr, comment);
      this.Attributes = kv;
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      if (Comment != null) {
        stream.WriteLine(this, level, "// " + Comment);
      }
      stream.Write(this, level, "axiom ");
      EmitAttributes(stream);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddAxiom(this);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      ResolveAttributes(rc);
      rc.StateMode = ResolutionContext.State.StateLess;
      Expr.Resolve(rc);
      rc.StateMode = ResolutionContext.State.Single;
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(tc);
      Expr.Typecheck(tc);
      Contract.Assert(Expr.Type != null);  // follows from postcondition of Expr.Typecheck
      if (!Expr.Type.Unify(Type.Bool)) {
        tc.Error(this, "axioms must be of type bool");
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAxiom(this);
    }
  }

  public abstract class NamedDeclaration : Declaration {
    private string/*!*/ name;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
    }

    public string/*!*/ Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);

        return this.name;
      }
      set {
        Contract.Requires(value != null);
        this.name = value;
      }
    }


    public NamedDeclaration(IToken/*!*/ tok, string/*!*/ name)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      this.name = name;
      // base(tok);
    }
    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return cce.NonNull(Name);
    }
  }

  public class TypeCtorDecl : NamedDeclaration {
    public readonly int Arity;

    public TypeCtorDecl(IToken/*!*/ tok, string/*!*/ name, int Arity)
      : base(tok, name) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      this.Arity = Arity;
    }
    public TypeCtorDecl(IToken/*!*/ tok, string/*!*/ name, int Arity, QKeyValue kv)
      : base(tok, name) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      this.Arity = Arity;
      this.Attributes = kv;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "type ");
      EmitAttributes(stream);
      stream.Write("{0}", TokenTextWriter.SanitizeIdentifier(Name));
      for (int i = 0; i < Arity; ++i)
        stream.Write(" _");
      stream.WriteLine(";");
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddType(this);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      ResolveAttributes(rc);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(tc);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTypeCtorDecl(this);
    }
  }

  public class TypeSynonymDecl : NamedDeclaration {
    public TypeVariableSeq/*!*/ TypeParameters;
    public Type/*!*/ Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TypeParameters != null);
      Contract.Invariant(Body != null);
    }


    public TypeSynonymDecl(IToken/*!*/ tok, string/*!*/ name,
                           TypeVariableSeq/*!*/ typeParams, Type/*!*/ body)
      : base(tok, name) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(body != null);
      this.TypeParameters = typeParams;
      this.Body = body;
    }
    public TypeSynonymDecl(IToken/*!*/ tok, string/*!*/ name,
                           TypeVariableSeq/*!*/ typeParams, Type/*!*/ body, QKeyValue kv)
      : base(tok, name) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(body != null);
      this.TypeParameters = typeParams;
      this.Body = body;
      this.Attributes = kv;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "type ");
      EmitAttributes(stream);
      stream.Write("{0}", TokenTextWriter.SanitizeIdentifier(Name));
      if (TypeParameters.Length > 0)
        stream.Write(" ");
      TypeParameters.Emit(stream, " ");
      stream.Write(" = ");
      Body.Emit(stream);
      stream.WriteLine(";");
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddType(this);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      ResolveAttributes(rc);

      int previousState = rc.TypeBinderState;
      try {
        foreach (TypeVariable/*!*/ v in TypeParameters) {
          Contract.Assert(v != null);
          rc.AddTypeBinder(v);
        }
        Body = Body.ResolveType(rc);
      } finally {
        rc.TypeBinderState = previousState;
      }
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(tc);
    }

    public static void ResolveTypeSynonyms(List<TypeSynonymDecl/*!*/>/*!*/ synonymDecls, ResolutionContext/*!*/ rc) {
      Contract.Requires(cce.NonNullElements(synonymDecls));
      Contract.Requires(rc != null);
      // then discover all dependencies between type synonyms
      IDictionary<TypeSynonymDecl/*!*/, List<TypeSynonymDecl/*!*/>/*!*/>/*!*/ deps =
        new Dictionary<TypeSynonymDecl/*!*/, List<TypeSynonymDecl/*!*/>/*!*/>();
      foreach (TypeSynonymDecl/*!*/ decl in synonymDecls) {
        Contract.Assert(decl != null);
        List<TypeSynonymDecl/*!*/>/*!*/ declDeps = new List<TypeSynonymDecl/*!*/>();
        FindDependencies(decl.Body, declDeps, rc);
        deps.Add(decl, declDeps);
      }

      List<TypeSynonymDecl/*!*/>/*!*/ resolved = new List<TypeSynonymDecl/*!*/>();

      int unresolved = synonymDecls.Count - resolved.Count;
      while (unresolved > 0) {
        foreach (TypeSynonymDecl/*!*/ decl in synonymDecls) {
          Contract.Assert(decl != null);
          if (!resolved.Contains(decl) &&
              Contract.ForAll(deps[decl], d => resolved.Contains(d))) {
            decl.Resolve(rc);
            resolved.Add(decl);
          }
        }

        int newUnresolved = synonymDecls.Count - resolved.Count;
        if (newUnresolved < unresolved) {
          // we are making progress
          unresolved = newUnresolved;
        } else {
          // there have to be cycles in the definitions
          foreach (TypeSynonymDecl/*!*/ decl in synonymDecls) {
            Contract.Assert(decl != null);
            if (!resolved.Contains(decl)) {
              rc.Error(decl,
                         "type synonym could not be resolved because of cycles: {0}" +
                         " (replacing body with \"bool\" to continue resolving)",
                         decl.Name);

              // we simply replace the bodies of all remaining type
              // synonyms with "bool" so that resolution can continue
              decl.Body = Type.Bool;
              decl.Resolve(rc);
            }
          }

          unresolved = 0;
        }
      }
    }

    // determine a list of all type synonyms that occur in "type"
    private static void FindDependencies(Type/*!*/ type, List<TypeSynonymDecl/*!*/>/*!*/ deps, ResolutionContext/*!*/ rc) {
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullElements(deps));
      Contract.Requires(rc != null);
      if (type.IsVariable || type.IsBasic) {
        // nothing
      } else if (type.IsUnresolved) {
        UnresolvedTypeIdentifier/*!*/ unresType = type.AsUnresolved;
        Contract.Assert(unresType != null);
        TypeSynonymDecl dep = rc.LookUpTypeSynonym(unresType.Name);
        if (dep != null)
          deps.Add(dep);
        foreach (Type/*!*/ subtype in unresType.Arguments) {
          Contract.Assert(subtype != null);
          FindDependencies(subtype, deps, rc);
        }
      } else if (type.IsMap) {
        MapType/*!*/ mapType = type.AsMap;
        Contract.Assert(mapType != null);
        foreach (Type/*!*/ subtype in mapType.Arguments) {
          Contract.Assert(subtype != null);
          FindDependencies(subtype, deps, rc);
        }
        FindDependencies(mapType.Result, deps, rc);
      } else if (type.IsCtor) {
        // this can happen because we allow types to be resolved multiple times
        CtorType/*!*/ ctorType = type.AsCtor;
        Contract.Assert(ctorType != null);
        foreach (Type/*!*/ subtype in ctorType.Arguments) {
          Contract.Assert(subtype != null);
          FindDependencies(subtype, deps, rc);
        }
      } else {
        System.Diagnostics.Debug.Fail("Did not expect this type during resolution: "
                                      + type);
      }
    }


    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTypeSynonymDecl(this);
    }
  }

  public abstract class Variable : NamedDeclaration, AI.IVariable {
    public TypedIdent/*!*/ TypedIdent;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TypedIdent != null);
    }

    public Variable(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent)
      : base(tok, typedIdent.Name) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
      this.TypedIdent = typedIdent;
      // base(tok, typedIdent.Name);
    }

    public Variable(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent, QKeyValue kv)
      : base(tok, typedIdent.Name) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
      this.TypedIdent = typedIdent;
      // base(tok, typedIdent.Name);
      this.Attributes = kv;
    }

    public abstract bool IsMutable {
      get;
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "var ");
      EmitAttributes(stream);
      EmitVitals(stream, level);
      stream.WriteLine(";");
    }
    public void EmitVitals(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds && this.TypedIdent.HasName) {
        stream.Write("h{0}^^", this.GetHashCode());  // the idea is that this will prepend the name printed by TypedIdent.Emit
      }
      this.TypedIdent.Emit(stream);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      this.TypedIdent.Resolve(rc);
    }
    public void ResolveWhere(ResolutionContext rc) {
      Contract.Requires(rc != null);
      if (this.TypedIdent.WhereExpr != null) {
        this.TypedIdent.WhereExpr.Resolve(rc);
      }
      ResolveAttributes(rc);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(tc);
      this.TypedIdent.Typecheck(tc);
    }
    [Pure]
    public object DoVisit(AI.ExprVisitor visitor) {
      //Contract.Requires(visitor != null);
      return visitor.VisitVariable(this);
    }
  }

  public class VariableComparer : IComparer {
    public int Compare(object a, object b) {
      Variable A = a as Variable;
      Variable B = b as Variable;
      if (A == null || B == null) {
        throw new ArgumentException("VariableComparer works only on objects of type Variable");
      }
      return cce.NonNull(A.Name).CompareTo(B.Name);
    }
  }

  // class to specify the <:-parents of the values of constants
  public class ConstantParent {
    public readonly IdentifierExpr/*!*/ Parent;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Parent != null);
    }

    // if true, the sub-dag underneath this constant-parent edge is
    // disjoint from all other unique sub-dags
    public readonly bool Unique;

    public ConstantParent(IdentifierExpr parent, bool unique) {
      Contract.Requires(parent != null);
      Parent = parent;
      Unique = unique;
    }
  }

  public class Constant : Variable {
    // when true, the value of this constant is meant to be distinct
    // from all other constants.
    public readonly bool Unique;

    // the <:-parents of the value of this constant. If the field is
    // null, no information about the parents is provided, which means
    // that the parental situation is unconstrained.
    public readonly List<ConstantParent/*!*/> Parents;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Parents, true));
    }


    // if true, it is assumed that the immediate <:-children of the
    // value of this constant are completely specified
    public readonly bool ChildrenComplete;

    public Constant(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent)
      : base(tok, typedIdent) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
      Contract.Requires(typedIdent.Name != null && (!typedIdent.HasName || typedIdent.Name.Length > 0));
      Contract.Requires(typedIdent.WhereExpr == null);
      // base(tok, typedIdent);
      this.Unique = true;
      this.Parents = null;
      this.ChildrenComplete = false;
    }
    public Constant(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent, bool unique)
      : base(tok, typedIdent) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
      Contract.Requires(typedIdent.Name != null && typedIdent.Name.Length > 0);
      Contract.Requires(typedIdent.WhereExpr == null);
      // base(tok, typedIdent);
      this.Unique = unique;
      this.Parents = null;
      this.ChildrenComplete = false;
    }
    public Constant(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent,
                    bool unique,
                    List<ConstantParent/*!*/> parents, bool childrenComplete,
                    QKeyValue kv)
      : base(tok, typedIdent, kv) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
      Contract.Requires(parents == null || cce.NonNullElements(parents));
      Contract.Requires(typedIdent.Name != null && typedIdent.Name.Length > 0);
      Contract.Requires(typedIdent.WhereExpr == null);
      // base(tok, typedIdent);
      this.Unique = unique;
      this.Parents = parents;
      this.ChildrenComplete = childrenComplete;
    }
    public override bool IsMutable {
      get {
        return false;
      }
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "const ");
      EmitAttributes(stream);
      if (this.Unique) {
        stream.Write(this, level, "unique ");
      }
      EmitVitals(stream, level);

      if (Parents != null || ChildrenComplete) {
        stream.Write(this, level, " extends");
        string/*!*/ sep = " ";
        foreach (ConstantParent/*!*/ p in cce.NonNull(Parents)) {
          Contract.Assert(p != null);
          stream.Write(this, level, sep);
          sep = ", ";
          if (p.Unique)
            stream.Write(this, level, "unique ");
          p.Parent.Emit(stream);
        }
        if (ChildrenComplete)
          stream.Write(this, level, " complete");
      }

      stream.WriteLine(";");
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddVariable(this, true);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      base.Resolve(rc);
      if (Parents != null) {
        foreach (ConstantParent/*!*/ p in Parents) {
          Contract.Assert(p != null);
          p.Parent.Resolve(rc);
          if (p.Parent.Decl != null && !(p.Parent.Decl is Constant))
            rc.Error(p.Parent, "the parent of a constant has to be a constant");
          if (this.Equals(p.Parent.Decl))
            rc.Error(p.Parent, "constant cannot be its own parent");
        }
      }

      // check that no parent occurs twice
      // (could be optimised)
      if (Parents != null) {
        for (int i = 0; i < Parents.Count; ++i) {
          if (Parents[i].Parent.Decl != null) {
            for (int j = i + 1; j < Parents.Count; ++j) {
              if (Parents[j].Parent.Decl != null &&
                  cce.NonNull(Parents[i].Parent.Decl).Equals(Parents[j].Parent.Decl))
                rc.Error(Parents[j].Parent,
                         "{0} occurs more than once as parent",
                         Parents[j].Parent.Decl);
            }
          }
        }
      }
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      base.Typecheck(tc);

      if (Parents != null) {
        foreach (ConstantParent/*!*/ p in Parents) {
          Contract.Assert(p != null);
          p.Parent.Typecheck(tc);
          if (!cce.NonNull(p.Parent.Decl).TypedIdent.Type.Unify(this.TypedIdent.Type))
            tc.Error(p.Parent,
                     "parent of constant has incompatible type ({0} instead of {1})",
                     p.Parent.Decl.TypedIdent.Type, this.TypedIdent.Type);
        }
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitConstant(this);
    }
  }
  public class GlobalVariable : Variable {
    public GlobalVariable(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent)
      : base(tok, typedIdent) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
    }
    public GlobalVariable(IToken/*!*/ tok, TypedIdent/*!*/ typedIdent, QKeyValue kv)
      : base(tok, typedIdent, kv) {
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent != null);
    }
    public override bool IsMutable {
      get {
        return true;
      }
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddVariable(this, true);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitGlobalVariable(this);
    }
  }
  public class Formal : Variable {
    public bool InComing;
    public Formal(IToken tok, TypedIdent typedIdent, bool incoming)
      : base(tok, typedIdent) {
      Contract.Requires(typedIdent != null);
      Contract.Requires(tok != null);
      InComing = incoming;
    }
    public override bool IsMutable {
      get {
        return !InComing;
      }
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddVariable(this, false);
    }

    /// <summary>
    /// Given a sequence of Formal declarations, returns sequence of Formals like the given one but without where clauses.
    /// The Type of each Formal is cloned.
    /// </summary>
    public static VariableSeq StripWhereClauses(VariableSeq w) {
      Contract.Requires(w != null);
      Contract.Ensures(Contract.Result<VariableSeq>() != null);
      VariableSeq s = new VariableSeq();
      foreach (Variable/*!*/ v in w) {
        Contract.Assert(v != null);
        Formal f = (Formal)v;
        TypedIdent ti = f.TypedIdent;
        s.Add(new Formal(f.tok, new TypedIdent(ti.tok, ti.Name, ti.Type.CloneUnresolved()), f.InComing));
      }
      return s;
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitFormal(this);
    }
  }
  public class LocalVariable : Variable {
    public LocalVariable(IToken tok, TypedIdent typedIdent, QKeyValue kv)
      : base(tok, typedIdent, kv) {//BASEMOVEA
      Contract.Requires(typedIdent != null);
      Contract.Requires(tok != null);
      //:base(tok, typedIdent, kv);
    }
    public LocalVariable(IToken tok, TypedIdent typedIdent)
      : base(tok, typedIdent, null) {//BASEMOVEA
      Contract.Requires(typedIdent != null);
      Contract.Requires(tok != null);
      //:base(tok, typedIdent, null);
    }
    public override bool IsMutable {
      get {
        return true;
      }
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddVariable(this, false);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitLocalVariable(this);
    }
  }
  public class Incarnation : LocalVariable {
    public int incarnationNumber;
    public Incarnation(Variable/*!*/ var, int i) :
      base(
      var.tok,
      new TypedIdent(var.TypedIdent.tok, var.TypedIdent.Name + "@" + i, var.TypedIdent.Type)
      ) {
      Contract.Requires(var != null);
      incarnationNumber = i;
    }

  }
  public class BoundVariable : Variable {
    public BoundVariable(IToken tok, TypedIdent typedIdent)
      : base(tok, typedIdent) {//BASEMOVEA
      Contract.Requires(typedIdent != null);
      Contract.Requires(tok != null);
      Contract.Requires(typedIdent.WhereExpr == null);
      //:base(tok, typedIdent);  // here for aesthetic reasons
    }
    public override bool IsMutable {
      get {
        return false;
      }
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddVariable(this, false);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBoundVariable(this);
    }
  }

  public abstract class DeclWithFormals : NamedDeclaration {
    public TypeVariableSeq/*!*/ TypeParameters;
    public /*readonly--except in StandardVisitor*/ VariableSeq/*!*/ InParams, OutParams;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TypeParameters != null);
      Contract.Invariant(InParams != null);
      Contract.Invariant(OutParams != null);
    }

    public DeclWithFormals(IToken tok, string name, TypeVariableSeq typeParams,
                            VariableSeq inParams, VariableSeq outParams)
      : base(tok, name) {
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      this.TypeParameters = typeParams;
      this.InParams = inParams;
      this.OutParams = outParams;
      // base(tok, name);
    }

    protected DeclWithFormals(DeclWithFormals that)
      : base(that.tok, cce.NonNull(that.Name)) {
      Contract.Requires(that != null);
      this.TypeParameters = that.TypeParameters;
      this.InParams = that.InParams;
      this.OutParams = that.OutParams;
      // base(that.tok, (!) that.Name);
    }

    protected void EmitSignature(TokenTextWriter stream, bool shortRet) {
      Contract.Requires(stream != null);
      Type.EmitOptionalTypeParams(stream, TypeParameters);
      stream.Write("(");
      InParams.Emit(stream);
      stream.Write(")");

      if (shortRet) {
        Contract.Assert(OutParams.Length == 1);
        stream.Write(" : ");
        cce.NonNull(OutParams[0]).TypedIdent.Type.Emit(stream);
      } else if (OutParams.Length > 0) {
        stream.Write(" returns (");
        OutParams.Emit(stream);
        stream.Write(")");
      }
    }

    // Register all type parameters at the resolution context
    protected void RegisterTypeParameters(ResolutionContext rc) {
      Contract.Requires(rc != null);
      foreach (TypeVariable/*!*/ v in TypeParameters) {
        Contract.Assert(v != null);
        rc.AddTypeBinder(v);
      }
    }

    protected void SortTypeParams() {
      TypeSeq/*!*/ allTypes = InParams.ToTypeSeq;
      Contract.Assert(allTypes != null);
      allTypes.AddRange(OutParams.ToTypeSeq);
      TypeParameters = Type.SortTypeParams(TypeParameters, allTypes, null);
    }

    /// <summary>
    /// Adds the given formals to the current variable context, and then resolves
    /// the types of those formals.  Does NOT resolve the where clauses of the
    /// formals.
    /// Relies on the caller to first create, and later tear down, that variable
    /// context.
    /// </summary>
    /// <param name="rc"></param>
    protected void RegisterFormals(VariableSeq formals, ResolutionContext rc) {
      Contract.Requires(rc != null);
      Contract.Requires(formals != null);
      foreach (Formal/*!*/ f in formals) {
        Contract.Assert(f != null);
        if (f.Name != TypedIdent.NoName) {
          rc.AddVariable(f, false);
        }
        f.Resolve(rc);
      }
    }

    /// <summary>
    /// Resolves the where clauses (and attributes) of the formals.
    /// </summary>
    /// <param name="rc"></param>
    protected void ResolveFormals(VariableSeq formals, ResolutionContext rc) {
      Contract.Requires(rc != null);
      Contract.Requires(formals != null);
      foreach (Formal/*!*/ f in formals) {
        Contract.Assert(f != null);
        f.ResolveWhere(rc);
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(tc);
      foreach (Formal/*!*/ p in InParams) {
        Contract.Assert(p != null);
        p.Typecheck(tc);
      }
      foreach (Formal/*!*/ p in OutParams) {
        Contract.Assert(p != null);
        p.Typecheck(tc);
      }
    }
  }

  public class DatatypeConstructor : Function {
    public List<DatatypeSelector> selectors;
    public DatatypeMembership membership;

    public DatatypeConstructor(Function func) 
    : base(func.tok, func.Name, func.TypeParameters, func.InParams, func.OutParams[0], func.Comment, func.Attributes)
    {
      selectors = new List<DatatypeSelector>();
    }

    public override void Resolve(ResolutionContext rc) {
      HashSet<string> selectorNames = new HashSet<string>();
      foreach (DatatypeSelector selector in selectors) {
        if (selector.Name.StartsWith("#")) {
          rc.Error(selector.tok, "The selector must be a non-empty string");
        }
        else {
          if (selectorNames.Contains(selector.Name))
            rc.Error(this.tok, "The selectors for a constructor must be distinct strings");
          else
            selectorNames.Add(selector.Name);
        }
      }
      base.Resolve(rc);
    }
    
    public override void Typecheck(TypecheckingContext tc) {
      CtorType outputType = this.OutParams[0].TypedIdent.Type as CtorType;
      if (outputType == null || !outputType.IsDatatype()) {
        tc.Error(tok, "The output type of a constructor must be a datatype");
      }
      base.Typecheck(tc);
    }
  }

  public class DatatypeSelector : Function {
    public Function constructor;
    public int index;
    public DatatypeSelector(Function constructor, int index)
      : base(constructor.InParams[index].tok, 
             constructor.InParams[index].Name + "#" + constructor.Name,
             new VariableSeq(new Formal(constructor.tok, new TypedIdent(constructor.tok, "", constructor.OutParams[0].TypedIdent.Type), true)),
             new Formal(constructor.tok, new TypedIdent(constructor.tok, "", constructor.InParams[index].TypedIdent.Type), false)) 
    {
      this.constructor = constructor;
      this.index = index;
    }

    public override void Emit(TokenTextWriter stream, int level) { }
  }

  public class DatatypeMembership : Function {
    public Function constructor;
    public DatatypeMembership(Function constructor)
      : base(constructor.tok, 
             "is#" + constructor.Name,
             new VariableSeq(new Formal(constructor.tok, new TypedIdent(constructor.tok, "", constructor.OutParams[0].TypedIdent.Type), true)),
             new Formal(constructor.tok, new TypedIdent(constructor.tok, "", Type.Bool), false)) 
    {
      this.constructor = constructor;
    }

    public override void Emit(TokenTextWriter stream, int level) { }
  }

  public class Function : DeclWithFormals {
    public string Comment;

    // the body is only set if the function is declared with {:inline}
    public Expr Body;
    public bool doingExpansion;

    private bool neverTrigger;
    private bool neverTriggerComputed;

    public Function(IToken tok, string name, VariableSeq args, Variable result)
      : this(tok, name, new TypeVariableSeq(), args, result, null) {
      Contract.Requires(result != null);
      Contract.Requires(args != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, new TypeVariableSeq(), args, result, null);
    }
    public Function(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq args, Variable result)
      : this(tok, name, typeParams, args, result, null) {
      Contract.Requires(result != null);
      Contract.Requires(args != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, typeParams, args, result, null);
    }
    public Function(IToken tok, string name, VariableSeq args, Variable result, string comment)
      : this(tok, name, new TypeVariableSeq(), args, result, comment) {
      Contract.Requires(result != null);
      Contract.Requires(args != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, new TypeVariableSeq(), args, result, comment);
    }
    public Function(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq args, Variable/*!*/ result, string comment)
      : base(tok, name, typeParams, args, new VariableSeq(result)) {
      Contract.Requires(result != null);
      Contract.Requires(args != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      Comment = comment;
      // base(tok, name, args, new VariableSeq(result));
    }
    public Function(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq args, Variable result,
                    string comment, QKeyValue kv)
      : this(tok, name, typeParams, args, result, comment) {
      Contract.Requires(args != null);
      Contract.Requires(result != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, typeParams, args, result, comment);
      this.Attributes = kv;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      if (Comment != null) {
        stream.WriteLine(this, level, "// " + Comment);
      }
      stream.Write(this, level, "function ");
      EmitAttributes(stream);
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        stream.Write("h{0}^^{1}", this.GetHashCode(), TokenTextWriter.SanitizeIdentifier(this.Name));
      } else {
        stream.Write("{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
      }
      EmitSignature(stream, true);
      if (Body != null) {
        stream.WriteLine();
        stream.WriteLine("{");
        stream.Write(level + 1, "");
        Body.Emit(stream);
        stream.WriteLine();
        stream.WriteLine("}");
      } else {
        stream.WriteLine(";");
      }
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddProcedure(this);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      int previousTypeBinderState = rc.TypeBinderState;
      try {
        RegisterTypeParameters(rc);
        rc.PushVarContext();
        RegisterFormals(InParams, rc);
        RegisterFormals(OutParams, rc);
        ResolveAttributes(rc);
        if (Body != null)
          Body.Resolve(rc);
        rc.PopVarContext();
        Type.CheckBoundVariableOccurrences(TypeParameters,
                                           InParams.ToTypeSeq, OutParams.ToTypeSeq,
                                           this.tok, "function arguments",
                                           rc);
      } finally {
        rc.TypeBinderState = previousTypeBinderState;
      }
      SortTypeParams();
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      // PR: why was the base call left out previously?
      base.Typecheck(tc);
      // TypecheckAttributes(tc);
      if (Body != null) {
        Body.Typecheck(tc);
        if (!cce.NonNull(Body.Type).Unify(cce.NonNull(OutParams[0]).TypedIdent.Type))
          tc.Error(Body,
                   "function body with invalid type: {0} (expected: {1})",
                   Body.Type, cce.NonNull(OutParams[0]).TypedIdent.Type);
      }
    }

    public bool NeverTrigger {
      get {
        if (!neverTriggerComputed) {
          this.CheckBooleanAttribute("never_pattern", ref neverTrigger);
          neverTriggerComputed = true;
        }
        return neverTrigger;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitFunction(this);
    }
  }

  public class Macro : Function {
    public Macro(IToken tok, string name, VariableSeq args, Variable result)
      : base(tok, name, args, result) { }
  }

  public class Requires : Absy, IPotentialErrorNode {
    public readonly bool Free;
    public Expr/*!*/ Condition;
    public string Comment;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Condition != null);
      Contract.Invariant(errorData == null || errorData is string);
    }


    // TODO: convert to use generics
    private object errorData;
    public object ErrorData {
      get {
        return errorData;
      }
      set {
        errorData = value;
      }
    }


    private MiningStrategy errorDataEnhanced;
    public MiningStrategy ErrorDataEnhanced {
      get {
        return errorDataEnhanced;
      }
      set {
        errorDataEnhanced = value;
      }
    }

    public QKeyValue Attributes;

    public String ErrorMessage {
      get {
        return QKeyValue.FindStringAttribute(Attributes, "msg");
      }
    }

    public Requires(IToken token, bool free, Expr condition, string comment, QKeyValue kv)
      : base(token) {
      Contract.Requires(condition != null);
      Contract.Requires(token != null);
      this.Free = free;
      this.Condition = condition;
      this.Comment = comment;
      this.Attributes = kv;
      // base(token);
    }

    public Requires(IToken token, bool free, Expr condition, string comment)
      : this(token, free, condition, comment, null) {
      Contract.Requires(condition != null);
      Contract.Requires(token != null);
      //:this(token, free, condition, comment, null);
    }

    public Requires(bool free, Expr condition)
      : this(Token.NoToken, free, condition, null) {
      Contract.Requires(condition != null);
      //:this(Token.NoToken, free, condition, null);
    }

    public Requires(bool free, Expr condition, string comment)
      : this(Token.NoToken, free, condition, comment) {
      Contract.Requires(condition != null);
      //:this(Token.NoToken, free, condition, comment);
    }

    public void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      if (Comment != null) {
        stream.WriteLine(this, level, "// " + Comment);
      }
      stream.Write(this, level, "{0}requires ", Free ? "free " : "");
      Cmd.EmitAttributes(stream, Attributes);
      this.Condition.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      this.Condition.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      this.Condition.Typecheck(tc);
      Contract.Assert(this.Condition.Type != null);  // follows from postcondition of Expr.Typecheck
      if (!this.Condition.Type.Unify(Type.Bool)) {
        tc.Error(this, "preconditions must be of type bool");
      }
    }
  }

  public class Ensures : Absy, IPotentialErrorNode {
    public readonly bool Free;
    public Expr/*!*/ Condition;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Condition != null);
      Contract.Invariant(errorData == null || errorData is string);
    }

    public string Comment;

    // TODO: convert to use generics
    private object errorData;
    public object ErrorData {
      get {
        return errorData;
      }
      set {
        errorData = value;
      }
    }

    private MiningStrategy errorDataEnhanced;
    public MiningStrategy ErrorDataEnhanced {
      get {
        return errorDataEnhanced;
      }
      set {
        errorDataEnhanced = value;
      }
    }

    public String ErrorMessage {
      get {
        return QKeyValue.FindStringAttribute(Attributes, "msg");
      }
    }

    public QKeyValue Attributes;

    public Ensures(IToken token, bool free, Expr/*!*/ condition, string comment, QKeyValue kv)
      : base(token) {
      Contract.Requires(condition != null);
      Contract.Requires(token != null);
      this.Free = free;
      this.Condition = condition;
      this.Comment = comment;
      this.Attributes = kv;
      // base(token);
    }

    public Ensures(IToken token, bool free, Expr condition, string comment)
      : this(token, free, condition, comment, null) {
      Contract.Requires(condition != null);
      Contract.Requires(token != null);
      //:this(token, free, condition, comment, null);
    }

    public Ensures(bool free, Expr condition)
      : this(Token.NoToken, free, condition, null) {
      Contract.Requires(condition != null);
      //:this(Token.NoToken, free, condition, null);
    }

    public Ensures(bool free, Expr condition, string comment)
      : this(Token.NoToken, free, condition, comment) {
      Contract.Requires(condition != null);
      //:this(Token.NoToken, free, condition, comment);
    }

    public void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      if (Comment != null) {
        stream.WriteLine(this, level, "// " + Comment);
      }
      stream.Write(this, level, "{0}ensures ", Free ? "free " : "");
      Cmd.EmitAttributes(stream, Attributes);
      this.Condition.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      this.Condition.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      this.Condition.Typecheck(tc);
      Contract.Assert(this.Condition.Type != null);  // follows from postcondition of Expr.Typecheck
      if (!this.Condition.Type.Unify(Type.Bool)) {
        tc.Error(this, "postconditions must be of type bool");
      }
    }
  }

  public class Procedure : DeclWithFormals {
    public RequiresSeq/*!*/ Requires;
    public IdentifierExprSeq/*!*/ Modifies;
    public EnsuresSeq/*!*/ Ensures;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Requires != null);
      Contract.Invariant(Modifies != null);
      Contract.Invariant(Ensures != null);
      Contract.Invariant(Summary != null);
    }


    // Abstract interpretation:  Procedure-specific invariants...
    [Rep]
    public readonly ProcedureSummary/*!*/ Summary;

    public Procedure(IToken/*!*/ tok, string/*!*/ name, TypeVariableSeq/*!*/ typeParams, VariableSeq/*!*/ inParams, VariableSeq/*!*/ outParams,
      RequiresSeq/*!*/ requires, IdentifierExprSeq/*!*/ modifies, EnsuresSeq/*!*/ ensures)
      : this(tok, name, typeParams, inParams, outParams, requires, modifies, ensures, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(requires != null);
      Contract.Requires(modifies != null);
      Contract.Requires(ensures != null);
      //:this(tok, name, typeParams, inParams, outParams, requires, modifies, ensures, null);
    }

    public Procedure(IToken/*!*/ tok, string/*!*/ name, TypeVariableSeq/*!*/ typeParams, VariableSeq/*!*/ inParams, VariableSeq/*!*/ outParams,
      RequiresSeq/*!*/ @requires, IdentifierExprSeq/*!*/ @modifies, EnsuresSeq/*!*/ @ensures, QKeyValue kv
      )
      : base(tok, name, typeParams, inParams, outParams) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(@requires != null);
      Contract.Requires(@modifies != null);
      Contract.Requires(@ensures != null);
      this.Requires = @requires;
      this.Modifies = @modifies;
      this.Ensures = @ensures;
      this.Summary = new ProcedureSummary();
      this.Attributes = kv;
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "procedure ");
      EmitAttributes(stream);
      stream.Write(this, level, "{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
      EmitSignature(stream, false);
      stream.WriteLine(";");

      level++;

      foreach (Requires/*!*/ e in this.Requires) {
        Contract.Assert(e != null);
        e.Emit(stream, level);
      }

      if (this.Modifies.Length > 0) {
        stream.Write(level, "modifies ");
        this.Modifies.Emit(stream, false);
        stream.WriteLine(";");
      }

      foreach (Ensures/*!*/ e in this.Ensures) {
        Contract.Assert(e != null);
        e.Emit(stream, level);
      }

      if (!CommandLineOptions.Clo.IntraproceduralInfer) {
        for (int s = 0; s < this.Summary.Count; s++) {
          ProcedureSummaryEntry/*!*/ entry = cce.NonNull(this.Summary[s]);
          stream.Write(level + 1, "// ");
          Expr e;
          e = (Expr)entry.Lattice.ToPredicate(entry.OnEntry);
          e.Emit(stream);
          stream.Write("   ==>   ");
          e = (Expr)entry.Lattice.ToPredicate(entry.OnExit);
          e.Emit(stream);
          stream.WriteLine();
        }
      }

      stream.WriteLine();
      stream.WriteLine();
    }

    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.AddProcedure(this);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.PushVarContext();

      foreach (IdentifierExpr/*!*/ ide in Modifies) {
        Contract.Assert(ide != null);
        ide.Resolve(rc);
      }

      int previousTypeBinderState = rc.TypeBinderState;
      try {
        RegisterTypeParameters(rc);

        RegisterFormals(InParams, rc);
        ResolveFormals(InParams, rc);  // "where" clauses of in-parameters are resolved without the out-parameters in scope
        foreach (Requires/*!*/ e in Requires) {
          Contract.Assert(e != null);
          e.Resolve(rc);
        }
        RegisterFormals(OutParams, rc);
        ResolveFormals(OutParams, rc);  // "where" clauses of out-parameters are resolved with both in- and out-parametes in scope

        rc.StateMode = ResolutionContext.State.Two;
        foreach (Ensures/*!*/ e in Ensures) {
          Contract.Assert(e != null);
          e.Resolve(rc);
        }
        rc.StateMode = ResolutionContext.State.Single;
        ResolveAttributes(rc);

        Type.CheckBoundVariableOccurrences(TypeParameters,
                                           InParams.ToTypeSeq, OutParams.ToTypeSeq,
                                           this.tok, "procedure arguments",
                                           rc);

      } finally {
        rc.TypeBinderState = previousTypeBinderState;
      }

      rc.PopVarContext();

      SortTypeParams();
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      base.Typecheck(tc);
      foreach (IdentifierExpr/*!*/ ide in Modifies) {
        Contract.Assert(ide != null);
        Contract.Assume(ide.Decl != null);
        if (!ide.Decl.IsMutable) {
          tc.Error(this, "modifies list contains constant: {0}", ide.Name);
        }
        ide.Typecheck(tc);
      }
      foreach (Requires/*!*/ e in Requires) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }
      foreach (Ensures/*!*/ e in Ensures) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitProcedure(this);
    }
  }

  public class LoopProcedure : Procedure
  {
      public Implementation enclosingImpl;
      private Dictionary<Block, Block> blockMap;
      private Dictionary<string, Block> blockLabelMap;

      public LoopProcedure(Implementation impl, Block header,
                           VariableSeq inputs, VariableSeq outputs, IdentifierExprSeq globalMods)
          : base(Token.NoToken, impl.Name + "_loop_" + header.ToString(),
               new TypeVariableSeq(), inputs, outputs,
               new RequiresSeq(), globalMods, new EnsuresSeq())
      {
          enclosingImpl = impl;
      }

      public void setBlockMap(Dictionary<Block, Block> bm)
      {
          blockMap = bm;
          blockLabelMap = new Dictionary<string, Block>();
          foreach (var kvp in bm)
          {
              blockLabelMap.Add(kvp.Key.Label, kvp.Value);
          }
      }

      public Block getBlock(string label)
      {
          if (blockLabelMap.ContainsKey(label)) return blockLabelMap[label];
          return null;
      }
  }

  public class Implementation : DeclWithFormals {
    public VariableSeq/*!*/ LocVars;
    [Rep]
    public StmtList StructuredStmts;
    [Rep]
    public List<Block/*!*/>/*!*/ Blocks;
    public Procedure Proc;

    // Blocks before applying passification etc.
    // Both are used only when /inline is set.
    public List<Block/*!*/> OriginalBlocks;
    public VariableSeq OriginalLocVars;

    // Strongly connected components
    private StronglyConnectedComponents<Block/*!*/> scc;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(LocVars != null);
      Contract.Invariant(cce.NonNullElements(Blocks));
      Contract.Invariant(cce.NonNullElements(OriginalBlocks, true));
      Contract.Invariant(cce.NonNullElements(scc, true));

    }
    private bool BlockPredecessorsComputed;
    public bool StronglyConnectedComponentsComputed {
      get {
        return this.scc != null;
      }
    }

    public bool SkipVerification {
      get {
        bool verify = true;
        cce.NonNull(this.Proc).CheckBooleanAttribute("verify", ref verify);
        this.CheckBooleanAttribute("verify", ref verify);
        if (!verify) {
          return true;
        }

        if (CommandLineOptions.Clo.ProcedureInlining == CommandLineOptions.Inlining.Assert ||
            CommandLineOptions.Clo.ProcedureInlining == CommandLineOptions.Inlining.Assume) {
          Expr inl = this.FindExprAttribute("inline");
          if (inl == null)
            inl = this.Proc.FindExprAttribute("inline");
          if (inl != null && inl is LiteralExpr && ((LiteralExpr)inl).isBigNum && ((LiteralExpr)inl).asBigNum.Signum > 0) {
            return true;
          }
        }

        if (CommandLineOptions.Clo.StratifiedInlining > 0) {
          return !QKeyValue.FindBoolAttribute(Attributes, "entrypoint");
        }

        return false;
      }
    }

    public Implementation(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq inParams, VariableSeq outParams, VariableSeq localVariables, [Captured] StmtList structuredStmts, QKeyValue kv)
      : this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, kv, new Errors()) {
      Contract.Requires(structuredStmts != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(outParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, new Errors());
    }

    public Implementation(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq inParams, VariableSeq outParams, VariableSeq localVariables, [Captured] StmtList structuredStmts)
      : this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, new Errors()) {
      Contract.Requires(structuredStmts != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(outParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, new Errors());
    }

    public Implementation(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq inParams, VariableSeq outParams, VariableSeq localVariables, [Captured] StmtList structuredStmts, Errors errorHandler)
      : this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, errorHandler) {
      Contract.Requires(errorHandler != null);
      Contract.Requires(structuredStmts != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(outParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, errorHandler);
    }

    public Implementation(IToken/*!*/ tok,
      string/*!*/ name,
      TypeVariableSeq/*!*/ typeParams,
      VariableSeq/*!*/ inParams,
      VariableSeq/*!*/ outParams,
      VariableSeq/*!*/ localVariables,
      [Captured] StmtList/*!*/ structuredStmts,
      QKeyValue kv,
      Errors/*!*/ errorHandler)
      : base(tok, name, typeParams, inParams, outParams) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(structuredStmts != null);
      Contract.Requires(errorHandler != null);
      LocVars = localVariables;
      StructuredStmts = structuredStmts;
      BigBlocksResolutionContext ctx = new BigBlocksResolutionContext(structuredStmts, errorHandler);
      Blocks = ctx.Blocks;
      BlockPredecessorsComputed = false;
      scc = null;
      Attributes = kv;

      // base(tok, name, inParams, outParams);
    }

    public Implementation(IToken tok, string name, TypeVariableSeq typeParams, VariableSeq inParams, VariableSeq outParams, VariableSeq localVariables, [Captured] List<Block/*!*/> block)
      : this(tok, name, typeParams, inParams, outParams, localVariables, block, null) {
      Contract.Requires(cce.NonNullElements(block));
      Contract.Requires(localVariables != null);
      Contract.Requires(outParams != null);
      Contract.Requires(inParams != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(name != null);
      Contract.Requires(tok != null);
      //:this(tok, name, typeParams, inParams, outParams, localVariables, block, null);
    }

    public Implementation(IToken/*!*/ tok,
      string/*!*/ name,
      TypeVariableSeq/*!*/ typeParams,
      VariableSeq/*!*/ inParams,
      VariableSeq/*!*/ outParams,
      VariableSeq/*!*/ localVariables,
      [Captured] List<Block/*!*/>/*!*/ blocks,
      QKeyValue kv)
      : base(tok, name, typeParams, inParams, outParams) {
      Contract.Requires(name != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(cce.NonNullElements(blocks));
      LocVars = localVariables;
      Blocks = blocks;
      BlockPredecessorsComputed = false;
      scc = null;
      Attributes = kv;

      //base(tok, name, inParams, outParams);
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "implementation ");
      EmitAttributes(stream);
      stream.Write(this, level, "{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
      EmitSignature(stream, false);
      stream.WriteLine();

      stream.WriteLine(level, "{0}", '{');

      foreach (Variable/*!*/ v in this.LocVars) {
        Contract.Assert(v != null);
        v.Emit(stream, level + 1);
      }

      if (this.StructuredStmts != null && !CommandLineOptions.Clo.PrintInstrumented && !CommandLineOptions.Clo.PrintInlined) {
        if (this.LocVars.Length > 0) {
          stream.WriteLine();
        }
        if (CommandLineOptions.Clo.PrintUnstructured < 2) {
          if (CommandLineOptions.Clo.PrintUnstructured == 1) {
            stream.WriteLine(this, level + 1, "/*** structured program:");
          }
          this.StructuredStmts.Emit(stream, level + 1);
          if (CommandLineOptions.Clo.PrintUnstructured == 1) {
            stream.WriteLine(level + 1, "**** end structured program */");
          }
        }
      }

      if (this.StructuredStmts == null || 1 <= CommandLineOptions.Clo.PrintUnstructured ||
          CommandLineOptions.Clo.PrintInstrumented || CommandLineOptions.Clo.PrintInlined) {
        foreach (Block b in this.Blocks) {
          b.Emit(stream, level + 1);
        }
      }

      stream.WriteLine(level, "{0}", '}');

      stream.WriteLine();
      stream.WriteLine();
    }
    public override void Register(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      // nothing to register
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      if (Proc != null) {
        // already resolved
        return;
      }
      DeclWithFormals dwf = rc.LookUpProcedure(cce.NonNull(this.Name));
      Proc = dwf as Procedure;
      if (dwf == null) {
        rc.Error(this, "implementation given for undeclared procedure: {0}", this.Name);
      } else if (Proc == null) {
        rc.Error(this, "implementations given for function, not procedure: {0}", this.Name);
      }

      int previousTypeBinderState = rc.TypeBinderState;
      try {
        RegisterTypeParameters(rc);

        rc.PushVarContext();
        RegisterFormals(InParams, rc);
        RegisterFormals(OutParams, rc);

        foreach (Variable/*!*/ v in LocVars) {
          Contract.Assert(v != null);
          v.Register(rc);
          v.Resolve(rc);
        }
        foreach (Variable/*!*/ v in LocVars) {
          Contract.Assert(v != null);
          v.ResolveWhere(rc);
        }

        rc.PushProcedureContext();
        foreach (Block b in Blocks) {
          b.Register(rc);
        }

        ResolveAttributes(rc);

        rc.StateMode = ResolutionContext.State.Two;
        foreach (Block b in Blocks) {
          b.Resolve(rc);
        }
        rc.StateMode = ResolutionContext.State.Single;

        rc.PopProcedureContext();
        rc.PopVarContext();

        Type.CheckBoundVariableOccurrences(TypeParameters,
                                           InParams.ToTypeSeq, OutParams.ToTypeSeq,
                                           this.tok, "implementation arguments",
                                           rc);
      } finally {
        rc.TypeBinderState = previousTypeBinderState;
      }
      SortTypeParams();
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      base.Typecheck(tc);

      Contract.Assume(this.Proc != null);

      if (this.TypeParameters.Length != Proc.TypeParameters.Length) {
        tc.Error(this, "mismatched number of type parameters in procedure implementation: {0}",
                 this.Name);
      } else {
        // if the numbers of type parameters are different, it is
        // difficult to compare the argument types
        MatchFormals(this.InParams, Proc.InParams, "in", tc);
        MatchFormals(this.OutParams, Proc.OutParams, "out", tc);
      }

      foreach (Variable/*!*/ v in LocVars) {
        Contract.Assert(v != null);
        v.Typecheck(tc);
      }
      IdentifierExprSeq oldFrame = tc.Frame;
      tc.Frame = Proc.Modifies;
      foreach (Block b in Blocks) {
        b.Typecheck(tc);
      }
      Contract.Assert(tc.Frame == Proc.Modifies);
      tc.Frame = oldFrame;
    }
    void MatchFormals(VariableSeq/*!*/ implFormals, VariableSeq/*!*/ procFormals, string/*!*/ inout, TypecheckingContext/*!*/ tc) {
      Contract.Requires(implFormals != null);
      Contract.Requires(procFormals != null);
      Contract.Requires(inout != null);
      Contract.Requires(tc != null);
      if (implFormals.Length != procFormals.Length) {
        tc.Error(this, "mismatched number of {0}-parameters in procedure implementation: {1}",
                 inout, this.Name);
      } else {
        // unify the type parameters so that types can be compared
        Contract.Assert(Proc != null);
        Contract.Assert(this.TypeParameters.Length == Proc.TypeParameters.Length);

        IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ subst1 =
          new Dictionary<TypeVariable/*!*/, Type/*!*/>();
        IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ subst2 =
          new Dictionary<TypeVariable/*!*/, Type/*!*/>();

        for (int i = 0; i < this.TypeParameters.Length; ++i) {
          TypeVariable/*!*/ newVar =
            new TypeVariable(Token.NoToken, Proc.TypeParameters[i].Name);
          Contract.Assert(newVar != null);
          subst1.Add(Proc.TypeParameters[i], newVar);
          subst2.Add(this.TypeParameters[i], newVar);
        }

        for (int i = 0; i < implFormals.Length; i++) {
          // the names of the formals are allowed to change from the proc to the impl

          // but types must be identical
          Type t = cce.NonNull((Variable)implFormals[i]).TypedIdent.Type.Substitute(subst2);
          Type u = cce.NonNull((Variable)procFormals[i]).TypedIdent.Type.Substitute(subst1);
          if (!t.Equals(u)) {
            string/*!*/ a = cce.NonNull((Variable)implFormals[i]).Name;
            Contract.Assert(a != null);
            string/*!*/ b = cce.NonNull((Variable)procFormals[i]).Name;
            Contract.Assert(b != null);
            string/*!*/ c;
            if (a == b) {
              c = a;
            } else {
              c = String.Format("{0} (named {1} in implementation)", b, a);
            }
            tc.Error(this, "mismatched type of {0}-parameter in implementation {1}: {2}", inout, this.Name, c);
          }
        }
      }
    }

    private Hashtable/*Variable->Expr*//*?*/ formalMap = null;
    public void ResetImplFormalMap() {
      this.formalMap = null;
    }
    public Hashtable /*Variable->Expr*//*!*/ GetImplFormalMap() {
      Contract.Ensures(Contract.Result<Hashtable>() != null);

      if (this.formalMap != null)
        return this.formalMap;
      else {
        Hashtable /*Variable->Expr*//*!*/ map = new Hashtable /*Variable->Expr*/ (InParams.Length + OutParams.Length);

        Contract.Assume(this.Proc != null);
        Contract.Assume(InParams.Length == Proc.InParams.Length);
        for (int i = 0; i < InParams.Length; i++) {
          Variable/*!*/ v = InParams[i];
          Contract.Assert(v != null);
          IdentifierExpr ie = new IdentifierExpr(v.tok, v);
          Variable/*!*/ pv = Proc.InParams[i];
          Contract.Assert(pv != null);
          map.Add(pv, ie);
        }
        System.Diagnostics.Debug.Assert(OutParams.Length == Proc.OutParams.Length);
        for (int i = 0; i < OutParams.Length; i++) {
          Variable/*!*/ v = cce.NonNull(OutParams[i]);
          IdentifierExpr ie = new IdentifierExpr(v.tok, v);
          Variable pv = cce.NonNull(Proc.OutParams[i]);
          map.Add(pv, ie);
        }
        this.formalMap = map;

        if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
          Console.WriteLine("Implementation.GetImplFormalMap on {0}:", this.Name);
          using (TokenTextWriter stream = new TokenTextWriter("<console>", Console.Out, false)) {
            foreach (DictionaryEntry e in map) {
              Console.Write("  ");
              cce.NonNull((Variable/*!*/)e.Key).Emit(stream, 0);
              Console.Write("  --> ");
              cce.NonNull((Expr)e.Value).Emit(stream);
              Console.WriteLine();
            }
          }
        }

        return map;
      }
    }

    /// <summary>
    /// Instrument the blocks with the inferred invariants
    /// </summary>
    public override void InstrumentWithInvariants() {
      foreach (Block b in this.Blocks) {
        if (b.Lattice != null) {
          Contract.Assert(b.PreInvariant != null);      /* If the pre-abstract state is null, then something is wrong */
          Contract.Assert(b.PostInvariant != null);      /* If the post-state is null, then something is wrong */

          bool instrumentEntry;
          bool instrumentExit;
          switch (CommandLineOptions.Clo.InstrumentInfer) {
            case CommandLineOptions.InstrumentationPlaces.Everywhere:
              instrumentEntry = true;
              instrumentExit = true;
              break;
            case CommandLineOptions.InstrumentationPlaces.LoopHeaders:
              instrumentEntry = b.widenBlock;
              instrumentExit = false;
              break;
            default: {
                Contract.Assert(false);
                throw new cce.UnreachableException();
              } // unexpected InstrumentationPlaces value
          }

          if (instrumentEntry || instrumentExit) {
            CmdSeq newCommands = new CmdSeq();
            if (instrumentEntry) {
              Expr inv = (Expr)b.Lattice.ToPredicate(b.PreInvariant); /*b.PreInvariantBuckets.GetDisjunction(b.Lattice);*/
              var kv = new QKeyValue(Token.NoToken, "inferred", new List<object>(), null);
              PredicateCmd cmd = CommandLineOptions.Clo.InstrumentWithAsserts ? (PredicateCmd)new AssertCmd(Token.NoToken, inv, kv) : (PredicateCmd)new AssumeCmd(Token.NoToken, inv, kv);
              newCommands.Add(cmd);
            }
            newCommands.AddRange(b.Cmds);
            if (instrumentExit) {
              Expr inv = (Expr)b.Lattice.ToPredicate(b.PostInvariant);
              var kv = new QKeyValue(Token.NoToken, "inferred", new List<object>(), null);
              PredicateCmd cmd = CommandLineOptions.Clo.InstrumentWithAsserts ? (PredicateCmd)new AssertCmd(Token.NoToken, inv, kv) : (PredicateCmd)new AssumeCmd(Token.NoToken, inv, kv);
              newCommands.Add(cmd);
            }
            b.Cmds = newCommands;
          }
        }
      }
    }

    /// <summary>
    /// Return a collection of blocks that are reachable from the block passed as a parameter.
    /// The block must be defined in the current implementation
    /// </summary>
    public ICollection<Block/*!*/> GetConnectedComponents(Block startingBlock) {
      Contract.Requires(startingBlock != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<Block>>(), true));
      Contract.Assert(this.Blocks.Contains(startingBlock));

      if (!this.BlockPredecessorsComputed)
        ComputeStronglyConnectedComponents();

#if  DEBUG_PRINT
      System.Console.WriteLine("* Strongly connected components * \n{0} \n ** ", scc);
#endif

      foreach (ICollection<Block/*!*/> component in cce.NonNull(this.scc)) {
        foreach (Block/*!*/ b in component) {
          Contract.Assert(b != null);
          if (b == startingBlock)          // We found the compontent that owns the startingblock
          {
            return component;
          }
        }
      }

      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }  // if we are here, it means that the block is not in one of the components. This is an error.
    }

    /// <summary>
    /// Compute the strongly connected compontents of the blocks in the implementation.
    /// As a side effect, it also computes the "predecessor" relation for the block in the implementation
    /// </summary>
    override public void ComputeStronglyConnectedComponents() {
      if (!this.BlockPredecessorsComputed)
        ComputePredecessorsForBlocks();

      Adjacency<Block/*!*/> next = new Adjacency<Block/*!*/>(Successors);
      Adjacency<Block/*!*/> prev = new Adjacency<Block/*!*/>(Predecessors);

      this.scc = new StronglyConnectedComponents<Block/*!*/>(this.Blocks, next, prev);
      scc.Compute();

      foreach (Block/*!*/ block in this.Blocks) {
        Contract.Assert(block != null);
        block.Predecessors = new BlockSeq();
      }

    }

    /// <summary>
    /// Reset the abstract stated computed before
    /// </summary>
    override public void ResetAbstractInterpretationState() {
      foreach (Block/*!*/ b in this.Blocks) {
        Contract.Assert(b != null);
        b.ResetAbstractInterpretationState();
      }
    }

    /// <summary>
    /// A private method used as delegate for the strongly connected components.
    /// It return, given a node, the set of its successors
    /// </summary>
    private IEnumerable/*<Block!>*//*!*/ Successors(Block node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<IEnumerable>() != null);

      GotoCmd gotoCmd = node.TransferCmd as GotoCmd;

      if (gotoCmd != null) { // If it is a gotoCmd
        Contract.Assert(gotoCmd.labelTargets != null);

        return gotoCmd.labelTargets;
      } else { // otherwise must be a ReturnCmd
        Contract.Assert(node.TransferCmd is ReturnCmd);

        return new List<Block/*!*/>();
      }
    }

    /// <summary>
    /// A private method used as delegate for the strongly connected components.
    /// It return, given a node, the set of its predecessors
    /// </summary>
    private IEnumerable/*<Block!>*//*!*/ Predecessors(Block node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<IEnumerable>() != null);

      Contract.Assert(this.BlockPredecessorsComputed);

      return node.Predecessors;
    }

    /// <summary>
    /// Compute the predecessor informations for the blocks
    /// </summary>
    public void ComputePredecessorsForBlocks() {
      foreach (Block b in this.Blocks) {
        b.Predecessors = new BlockSeq();
      }
      foreach (Block b in this.Blocks) {
        GotoCmd gtc = b.TransferCmd as GotoCmd;
        if (gtc != null) {
          Contract.Assert(gtc.labelTargets != null);
          foreach (Block/*!*/ dest in gtc.labelTargets) {
            Contract.Assert(dest != null);
            dest.Predecessors.Add(b);
          }
        }
      }
      this.BlockPredecessorsComputed = true;
    }

    public void PruneUnreachableBlocks() {
      ArrayList /*Block!*/ visitNext = new ArrayList /*Block!*/ ();
      List<Block/*!*/> reachableBlocks = new List<Block/*!*/>();
      HashSet<Block> reachable = new HashSet<Block>();  // the set of elements in "reachableBlocks"

      visitNext.Add(this.Blocks[0]);
      while (visitNext.Count != 0) {
        Block b = cce.NonNull((Block)visitNext[visitNext.Count - 1]);
        visitNext.RemoveAt(visitNext.Count - 1);
        if (!reachable.Contains(b)) {
          reachableBlocks.Add(b);
          reachable.Add(b);
          if (b.TransferCmd is GotoCmd) {
            foreach (Cmd/*!*/ s in b.Cmds) {
              Contract.Assert(s != null);
              if (s is PredicateCmd) {
                LiteralExpr e = ((PredicateCmd)s).Expr as LiteralExpr;
                if (e != null && e.IsFalse) {
                  // This statement sequence will never reach the end, because of this "assume false" or "assert false".
                  // Hence, it does not reach its successors.
                  b.TransferCmd = new ReturnCmd(b.TransferCmd.tok);
                  goto NEXT_BLOCK;
                }
              }
            }
            // it seems that the goto statement at the end may be reached
            foreach (Block succ in cce.NonNull((GotoCmd)b.TransferCmd).labelTargets) {
              Contract.Assume(succ != null);
              visitNext.Add(succ);
            }
          }
        }
      NEXT_BLOCK: {
        }
      }

      this.Blocks = reachableBlocks;
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitImplementation(this);
    }
  }


  public class TypedIdent : Absy {
    public const string NoName = "";
    public string/*!*/ Name;
    public Type/*!*/ Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(Type != null);
    }

    public Expr WhereExpr;
    // [NotDelayed]
    public TypedIdent(IToken/*!*/ tok, string/*!*/ name, Type/*!*/ type)
      : this(tok, name, type, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Ensures(this.WhereExpr == null);  //PM: needed to verify BoogiePropFactory.FreshBoundVariable
      //:this(tok, name, type, null); // here for aesthetic reasons
    }
    // [NotDelayed]
    public TypedIdent(IToken/*!*/ tok, string/*!*/ name, Type/*!*/ type, Expr whereExpr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Ensures(this.WhereExpr == whereExpr);
      this.Name = name;
      this.Type = type;
      this.WhereExpr = whereExpr;
      // base(tok);
    }
    public bool HasName {
      get {
        return this.Name != NoName;
      }
    }
    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      stream.SetToken(this);
      if (this.Name != NoName) {
        stream.Write("{0}: ", TokenTextWriter.SanitizeIdentifier(this.Name));
      }
      this.Type.Emit(stream);
      if (this.WhereExpr != null) {
        stream.Write(" where ");
        this.WhereExpr.Emit(stream);
      }
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      // NOTE: WhereExpr needs to be resolved by the caller, because the caller must provide a modified ResolutionContext
      this.Type = this.Type.ResolveType(rc);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      //   type variables can occur when working with polymorphic functions/procedures
      //      if (!this.Type.IsClosed)
      //        tc.Error(this, "free variables in type of an identifier: {0}",
      //                 this.Type.FreeVariables);
      if (this.WhereExpr != null) {
        this.WhereExpr.Typecheck(tc);
        Contract.Assert(this.WhereExpr.Type != null);  // follows from postcondition of Expr.Typecheck
        if (!this.WhereExpr.Type.Unify(Type.Bool)) {
          tc.Error(this, "where clauses must be of type bool");
        }
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTypedIdent(this);
    }
  }

  /// <summary>
  /// Conceptually, a LatticeElementList is a infinite array indexed from 0,
  /// where some finite number of elements have a non-null value.  All elements
  /// have type Lattice.Element.
  ///
  /// The Count property returns the first index above all non-null values.
  ///
  /// The [i] getter returns the element at position i, which may be null.  The
  /// index i is not allowed to be negative.
  /// The [i] setter sets the element at position i.  As a side effect, this
  /// operation may increase Count.  The index i is not allowed to be negative.
  /// The right-hand value of the setter is not allowed to be null; that is,
  /// null can occur in the list only as an "unused" element.
  /// </summary>
  public class LatticeElementList : ArrayList {
    public new /*Maybe null*/ AI.Lattice.Element this[int i] {
      get {
        if (i < Count) {
          return (AI.Lattice.Element)base[i];
        } else {
          return null;
        }
      }
      set {
        System.Diagnostics.Debug.Assert(value != null);
        while (Count <= i) {
          Add(null);
        }
        base[i] = value;
      }
    }
    /// <summary>
    /// Returns the disjunction of (the expression formed from) the
    /// non-null lattice elements in the list.  The expressions are
    /// formed according to the given "lattice", which is assumed to
    /// be the lattice of the lattice elements stored in the list.
    /// </summary>
    /// <param name="lattice"></param>
    /// <returns></returns>
    public Expr GetDisjunction(AI.Lattice lattice) {
      Contract.Requires(lattice != null);
      Expr disjunction = null;
      foreach (AI.Lattice.Element el in this) {
        if (el != null) {
          Expr e = (Expr)lattice.ToPredicate(el);
          if (disjunction == null) {
            disjunction = e;
          } else {
            disjunction = Expr.Or(disjunction, e);
          }
        }
      }
      if (disjunction == null) {
        return Expr.False;
      } else {
        return disjunction;
      }
    }
  }

  public abstract class BoogieFactory {
    public static Expr IExpr2Expr(AI.IExpr e) {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Variable v = e as Variable;
      if (v != null) {
        return new IdentifierExpr(Token.NoToken, v);
      } else if (e is AI.IVariable) { // but not a Variable
        return new AIVariableExpr(Token.NoToken, (AI.IVariable)e);
      } else if (e is IdentifierExpr.ConstantFunApp) {
        return ((IdentifierExpr.ConstantFunApp)e).IdentifierExpr;
      } else if (e is QuantifierExpr.AIQuantifier) {
        return ((QuantifierExpr.AIQuantifier)e).arg.RealQuantifier;
      } else {
        return (Expr)e;
      }
    }
    public static ExprSeq IExprArray2ExprSeq(IList/*<AI.IExpr!>*/ a) {
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExprSeq>() != null);
      Expr[] e = new Expr[a.Count];
      int i = 0;
      foreach (AI.IExpr/*!*/ aei in a) {
        Contract.Assert(aei != null);
        e[i] = IExpr2Expr(aei);
        i++;
      }
      return new ExprSeq(e);
    }

    // Convert a Boogie type into an AIType if possible.  This should be
    // extended when AIFramework gets more types.
    public static AI.AIType Type2AIType(Type t) {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<AI.AIType>() != null);
      //      if (t.IsRef)
      //        return AI.Ref.Type;
      //      else
      if (t.IsInt)
        return AI.Int.Type;
      //      else if (t.IsName)               PR: how to handle this case?
      //        return AI.FieldName.Type;
      else
        return AI.Value.Type;
    }
  }

  #region Generic Sequences
  //---------------------------------------------------------------------
  // Generic Sequences
  //---------------------------------------------------------------------

  public sealed class TypedIdentSeq : PureCollections.Sequence {
    public TypedIdentSeq(params Type[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public new TypedIdent this[int index] {
      get {
        return (TypedIdent)base[index];
      }
      set {
        base[index] = value;
      }
    }
  }

  public sealed class RequiresSeq : PureCollections.Sequence {
    public RequiresSeq(params Requires[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public new Requires/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<Requires>() != null);

        return cce.NonNull((Requires/*!*/)base[index]);
      }
      set {
        base[index] = value;
      }
    }
  }

  public sealed class EnsuresSeq : PureCollections.Sequence {
    public EnsuresSeq(params Ensures[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public new Ensures/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<Ensures>() != null);
        return cce.NonNull((Ensures/*!*/)base[index]);
      }
      set {
        base[index] = value;
      }
    }
  }

  public sealed class VariableSeq : PureCollections.Sequence {
    public VariableSeq(params Variable[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public VariableSeq(VariableSeq/*!*/ varSeq)
      : base(varSeq) {
      Contract.Requires(varSeq != null);
    }
    public new Variable this[int index] {
      get {
        return (Variable)base[index];
      }
      set {
        base[index] = value;
      }
    }
    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      string sep = "";
      foreach (Variable/*!*/ v in this) {
        Contract.Assert(v != null);
        stream.Write(sep);
        sep = ", ";
        v.EmitVitals(stream, 0);
      }
    }
    public TypeSeq/*!*/ ToTypeSeq {
      get {
        Contract.Ensures(Contract.Result<TypeSeq>() != null);

        TypeSeq/*!*/ res = new TypeSeq();
        foreach (Variable/*!*/ v in this) {
          Contract.Assert(v != null);
          res.Add(v.TypedIdent.Type);
        }
        return res;
      }
    }
  }

  public sealed class TypeSeq : PureCollections.Sequence {
    public TypeSeq(params Type[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public TypeSeq(TypeSeq/*!*/ varSeq)
      : base(varSeq) {
      Contract.Requires(varSeq != null);
    }
    public new Type/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return cce.NonNull((Type/*!*/)base[index]);
      }
      set {
        base[index] = value;
      }
    }
    public List<Type/*!*/>/*!*/ ToList() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Type>>()));
      List<Type/*!*/>/*!*/ res = new List<Type/*!*/>(Length);
      foreach (Type/*!*/ t in this) {
        Contract.Assert(t != null);
        res.Add(t);
      }
      return res;
    }
    public void Emit(TokenTextWriter stream, string separator) {
      Contract.Requires(separator != null);
      Contract.Requires(stream != null);
      string sep = "";
      foreach (Type/*!*/ v in this) {
        Contract.Assert(v != null);
        stream.Write(sep);
        sep = separator;
        v.Emit(stream);
      }
    }
  }

  public sealed class TypeVariableSeq : PureCollections.Sequence {
    public TypeVariableSeq(params TypeVariable[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public TypeVariableSeq(TypeVariableSeq/*!*/ varSeq)
      : base(varSeq) {
      Contract.Requires(varSeq != null);
    }
    /*  PR: the following two constructors cause Spec# crashes
        public TypeVariableSeq(TypeVariable! var)
          : base(new TypeVariable! [] { var })
        {
        }
        public TypeVariableSeq()
          : base(new TypeVariable![0])
        {
        } */
    public new TypeVariable/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<TypeVariable>() != null);

        return cce.NonNull((TypeVariable)base[index]);
      }
      set {
        base[index] = value;
      }
    }
    public void AppendWithoutDups(TypeVariableSeq s1) {
      Contract.Requires(s1 != null);
      for (int i = 0; i < s1.card; i++) {
        TypeVariable/*!*/ next = s1[i];
        Contract.Assert(next != null);
        if (!this.Has(next))
          this.Add(next);
      }
    }
    public void Emit(TokenTextWriter stream, string separator) {
      Contract.Requires(separator != null);
      Contract.Requires(stream != null);
      string sep = "";
      foreach (TypeVariable/*!*/ v in this) {
        Contract.Assert(v != null);
        stream.Write(sep);
        sep = separator;
        v.Emit(stream);
      }
    }
    public new TypeVariable[] ToArray() {
      Contract.Ensures(Contract.Result<TypeVariable[]>() != null);
      TypeVariable[]/*!*/ n = new TypeVariable[Length];
      int ct = 0;
      foreach (TypeVariable/*!*/ var in this) {
        Contract.Assert(var != null);
        n[ct++] = var;
      }
      return n;
    }
    public List<TypeVariable/*!*/>/*!*/ ToList() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<TypeVariable>>()));
      List<TypeVariable/*!*/>/*!*/ res = new List<TypeVariable/*!*/>(Length);
      foreach (TypeVariable/*!*/ var in this) {
        Contract.Assert(var != null);
        res.Add(var);
      }
      return res;
    }
  }

  public sealed class IdentifierExprSeq : PureCollections.Sequence {
    public IdentifierExprSeq(params IdentifierExpr[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public IdentifierExprSeq(IdentifierExprSeq/*!*/ ideSeq)
      : base(ideSeq) {
      Contract.Requires(ideSeq != null);
    }
    public new IdentifierExpr/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);

        return cce.NonNull((IdentifierExpr)base[index]);
      }
      set {
        base[index] = value;
      }
    }

    public void Emit(TokenTextWriter stream, bool printWhereComments) {
      Contract.Requires(stream != null);
      string sep = "";
      foreach (IdentifierExpr/*!*/ e in this) {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);

        if (printWhereComments && e.Decl != null && e.Decl.TypedIdent.WhereExpr != null) {
          stream.Write(" /* where ");
          e.Decl.TypedIdent.WhereExpr.Emit(stream);
          stream.Write(" */");
        }
      }
    }
  }


  public sealed class CmdSeq : PureCollections.Sequence {
    public CmdSeq(params Cmd[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public CmdSeq(CmdSeq/*!*/ cmdSeq)
      : base(cmdSeq) {
      Contract.Requires(cmdSeq != null);
    }
    public new Cmd/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<Cmd>() != null);

        return cce.NonNull((Cmd)base[index]);
      }
      set {
        base[index] = value;
      }
    }
  }

  public sealed class ExprSeq : PureCollections.Sequence {
    public ExprSeq(params Expr[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public ExprSeq(ExprSeq/*!*/ exprSeq)
      : base(exprSeq) {
      Contract.Requires(exprSeq != null);
    }
    public new Expr this[int index] {
      get {
        return (Expr)base[index];
      }
      set {
        base[index] = value;
      }
    }

    public new Expr Last() {
      return (Expr)base.Last();
    }

    public static ExprSeq operator +(ExprSeq a, ExprSeq b) {
      if (a == null)
        throw new ArgumentNullException("a");
      if (b == null)
        throw new ArgumentNullException("b");
      return Append(a, b);
    }

    public static ExprSeq Append(ExprSeq s, ExprSeq t) {
      Contract.Requires(t != null);
      Contract.Requires(s != null);
      Expr[] n = new Expr[s.card + t.card];
      for (int i = 0; i < s.card; i++)
        n[i] = s[i];
      for (int i = 0; i < t.card; i++)
        n[s.card + i] = t[i];
      return new ExprSeq(n);
    }
    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      string sep = "";
      foreach (Expr/*!*/ e in this) {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }
    }
    public TypeSeq/*!*/ ToTypeSeq {
      get {
        Contract.Ensures(Contract.Result<TypeSeq>() != null);

        TypeSeq res = new TypeSeq();
        foreach (Expr e in this)
          res.Add(cce.NonNull(e).Type);
        return res;
      }
    }
  }

  public sealed class TokenSeq : PureCollections.Sequence {
    public TokenSeq(params Token[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public new Token this[int index] {
      get {
        return (Token)base[index];
      }
      set {
        base[index] = value;
      }
    }
  }

  public sealed class StringSeq : PureCollections.Sequence {
    public StringSeq(params string[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public new String this[int index] {
      get {
        return (String)base[index];
      }
      set {
        base[index] = value;
      }
    }
    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      string sep = "";
      foreach (string/*!*/ s in this) {
        Contract.Assert(s != null);
        stream.Write(sep);
        sep = ", ";
        stream.Write(s);
      }
    }
  }

  public sealed class BlockSeq : PureCollections.Sequence {
    public BlockSeq(params Block[]/*!*/ args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public BlockSeq(BlockSeq blockSeq)
      : base(blockSeq) {
      Contract.Requires(blockSeq != null);
    }

    public new Block this[int index] {
      get {
        return (Block)base[index];
      }
      set {
        base[index] = value;
      }
    }
  }

  public static class Emitter {
    public static void Declarations(List<Declaration/*!*/>/*!*/ decls, TokenTextWriter stream) {
      Contract.Requires(stream != null);
      Contract.Requires(cce.NonNullElements(decls));
      bool first = true;
      foreach (Declaration d in decls) {
        if (d == null)
          continue;
        if (first) {
          first = false;
        } else {
          stream.WriteLine();
        }
        d.Emit(stream, 0);
      }
    }
  }
  public sealed class DeclarationSeq : PureCollections.Sequence {
    public DeclarationSeq(params string[] args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public new Declaration this[int index] {
      get {
        return (Declaration)base[index];
      }
      set {
        base[index] = value;
      }
    }
    public void Emit(TokenTextWriter stream) {
      Contract.Requires(stream != null);
      bool first = true;
      foreach (Declaration d in this) {
        if (d == null)
          continue;
        if (first) {
          first = false;
        } else {
          stream.WriteLine();
        }
        d.Emit(stream, 0);
      }
    }
  }
  #endregion


  #region Regular Expressions
  // a data structure to recover the "program structure" from the flow graph
  public sealed class RESeq : PureCollections.Sequence {
    public RESeq(params RE[] args)
      : base(args) {
      Contract.Requires(args != null);
    }
    public RESeq(RESeq reSeq)
      : base(reSeq) {
      Contract.Requires(reSeq != null);
    }
    public new RE this[int index] {
      get {
        return (RE)base[index];
      }
      set {
        base[index] = value;
      }
    }
    //        public void Emit(TokenTextWriter stream)
    //        {
    //            string sep = "";
    //            foreach (RE e in this)
    //            {
    //                stream.Write(sep);
    //                sep = ", ";
    //                e.Emit(stream);
    //            }
    //        }
  }
  public abstract class RE : Cmd {
    public RE()
      : base(Token.NoToken) {
    }
    public override void AddAssignedVariables(VariableSeq vars) {
      //Contract.Requires(vars != null);
      throw new NotImplementedException();
    }
  }
  public class AtomicRE : RE {
    public Block/*!*/ b;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(b != null);
    }

    public AtomicRE(Block block) {
      Contract.Requires(block != null);
      b = block;
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      b.Resolve(rc);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      b.Typecheck(tc);
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      b.Emit(stream, level);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAtomicRE(this);
    }
  }
  public abstract class CompoundRE : RE {
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      return;
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      return;
    }
  }
  public class Sequential : CompoundRE {
    public RE/*!*/ first;
    public RE/*!*/ second;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(first != null);
      Contract.Invariant(second != null);
    }

    public Sequential(RE a, RE b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      first = a;
      second = b;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.WriteLine();
      stream.WriteLine("{0};", Indent(level));
      first.Emit(stream, level + 1);
      second.Emit(stream, level + 1);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitSequential(this);
    }
  }
  public class Choice : CompoundRE {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(rs != null);
    }

    public RESeq/*!*/ rs;
    public Choice(RESeq operands) {
      Contract.Requires(operands != null);
      rs = operands;
      // base();
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.WriteLine();
      stream.WriteLine("{0}[]", Indent(level));
      foreach (RE/*!*/ r in rs) {
        Contract.Assert(r != null);
        r.Emit(stream, level + 1);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitChoice(this);
    }
  }
  public class DAG2RE {
    public static RE Transform(Block b) {
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<RE>() != null);
      TransferCmd tc = b.TransferCmd;
      if (tc is ReturnCmd) {
        return new AtomicRE(b);
      } else if (tc is GotoCmd) {
        GotoCmd/*!*/ g = (GotoCmd)tc;
        Contract.Assert(g != null);
        Contract.Assume(g.labelTargets != null);
        if (g.labelTargets.Length == 1) {
          return new Sequential(new AtomicRE(b), Transform(cce.NonNull(g.labelTargets[0])));
        } else {
          RESeq rs = new RESeq();
          foreach (Block/*!*/ target in g.labelTargets) {
            Contract.Assert(target != null);
            RE r = Transform(target);
            rs.Add(r);
          }
          RE second = new Choice(rs);
          return new Sequential(new AtomicRE(b), second);
        }
      } else {
        Contract.Assume(false);
        throw new cce.UnreachableException();
      }
    }
  }

  #endregion

  // NOTE: This class is here for convenience, since this file's
  // classes are used pretty much everywhere.

  public class BoogieDebug {
    public static bool DoPrinting = false;

    public static void Write(string format, params object[] args) {
      Contract.Requires(args != null);
      Contract.Requires(format != null);
      if (DoPrinting) {
        Console.Error.Write(format, args);
      }
    }

    public static void WriteLine(string format, params object[] args) {
      Contract.Requires(args != null);
      Contract.Requires(format != null);
      if (DoPrinting) {
        Console.Error.WriteLine(format, args);
      }
    }

    public static void WriteLine() {
      if (DoPrinting) {
        Console.Error.WriteLine();
      }
    }
  }
}
