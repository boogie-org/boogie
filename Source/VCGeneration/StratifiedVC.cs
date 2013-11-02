using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC {
  using Bpl = Microsoft.Boogie;
  
  public class StratifiedVC {
    public StratifiedInliningInfo info;
    public int id;
    public List<VCExprVar> interfaceExprVars;
    public Dictionary<Block, List<StratifiedCallSite>> callSites;
    public Dictionary<Block, List<StratifiedCallSite>> recordProcCallSites;
    public VCExpr vcexpr;

    // the following three fields are not being used at the moment
    public VCExprVar entryExprVar;
    public Dictionary<Block, Macro> reachMacros;
    public Dictionary<Block, VCExpr> reachMacroDefinitions;

    public StratifiedVC(StratifiedInliningInfo siInfo) {
      info = siInfo;
      info.GenerateVC();
      var vcgen = info.vcgen;
      var prover = vcgen.prover;
      VCExpressionGenerator gen = prover.VCExprGen;
      var bet = prover.Context.BoogieExprTranslator; 
      
      vcexpr = info.vcexpr;
      id = vcgen.CreateNewId();
      interfaceExprVars = new List<VCExprVar>();
      Dictionary<VCExprVar, VCExpr> substDict = new Dictionary<VCExprVar, VCExpr>();
      foreach (VCExprVar v in info.interfaceExprVars) {
        VCExprVar newVar = vcgen.CreateNewVar(v.Type);
        interfaceExprVars.Add(newVar);
        substDict.Add(v, newVar);
      }
      foreach (VCExprVar v in info.privateExprVars) {
        substDict.Add(v, vcgen.CreateNewVar(v.Type));
      }
      substDict.Add(bet.LookupVariable(info.controlFlowVariable), gen.Integer(BigNum.FromInt(id)));
      VCExprSubstitution subst = new VCExprSubstitution(substDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
      SubstitutingVCExprVisitor substVisitor = new SubstitutingVCExprVisitor(prover.VCExprGen);
      vcexpr = substVisitor.Mutate(vcexpr, subst);

      var impl = info.impl;
      reachMacros = new Dictionary<Block, Macro>();
      reachMacroDefinitions = new Dictionary<Block, VCExpr>();
      foreach (Block b in impl.Blocks) {
        reachMacros[b] = vcgen.CreateNewMacro();
        reachMacroDefinitions[b] = VCExpressionGenerator.False;
      }
      entryExprVar = vcgen.CreateNewVar(Microsoft.Boogie.Type.Bool);
      reachMacroDefinitions[impl.Blocks[0]] = entryExprVar;
      foreach (Block currBlock in impl.Blocks) {
        GotoCmd gotoCmd = currBlock.TransferCmd as GotoCmd;
        if (gotoCmd == null) continue;
        foreach (Block successorBlock in gotoCmd.labelTargets) {
          VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(gen.Integer(BigNum.FromInt(id)), gen.Integer(BigNum.FromInt(currBlock.UniqueId)));
          VCExpr controlTransferExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(successorBlock.UniqueId)));
          reachMacroDefinitions[successorBlock] = gen.Or(reachMacroDefinitions[successorBlock], gen.And(gen.Function(reachMacros[currBlock]), controlTransferExpr));
        }
      }

      callSites = new Dictionary<Block, List<StratifiedCallSite>>();
      foreach (Block b in info.callSites.Keys) {
        callSites[b] = new List<StratifiedCallSite>();
        foreach (CallSite cs in info.callSites[b]) {
          callSites[b].Add(new StratifiedCallSite(cs, substVisitor, subst));
        }
      }

      recordProcCallSites = new Dictionary<Block, List<StratifiedCallSite>>();
      foreach (Block b in info.recordProcCallSites.Keys) {
        recordProcCallSites[b] = new List<StratifiedCallSite>();
        foreach (CallSite cs in info.recordProcCallSites[b]) {
          recordProcCallSites[b].Add(new StratifiedCallSite(cs, substVisitor, subst));
        }
      }
    }

    public List<StratifiedCallSite> CallSites {
      get {
        var ret = new List<StratifiedCallSite>();
        foreach (var b in callSites.Keys) {
          foreach (var cs in callSites[b]) {
            ret.Add(cs);
          }
        }
        return ret;
      }
    }

    public List<StratifiedCallSite> RecordProcCallSites {
      get {
        var ret = new List<StratifiedCallSite>();
        foreach (var b in recordProcCallSites.Keys) {
          foreach (var cs in recordProcCallSites[b]) {
            ret.Add(cs);
          }
        }
        return ret;
      }
    }
  }

  public class CallSite {
    public string calleeName;
    public List<VCExpr> interfaceExprs;
    public Block block;
    public int numInstr;  // for TraceLocation
    public VCExprVar callSiteVar;
    public CallSite(string callee, List<VCExpr> interfaceExprs, VCExprVar callSiteVar, Block block, int numInstr) {
      this.calleeName = callee;
      this.interfaceExprs = interfaceExprs;
      this.callSiteVar = callSiteVar;
      this.block = block;
      this.numInstr = numInstr;
    }
  }

  public class StratifiedCallSite {
    public CallSite callSite;
    public List<VCExpr> interfaceExprs;
    public VCExpr callSiteExpr;

    public StratifiedCallSite(CallSite cs, SubstitutingVCExprVisitor substVisitor, VCExprSubstitution subst) {
      callSite = cs;
      interfaceExprs = new List<VCExpr>();
      foreach (VCExpr v in cs.interfaceExprs) {
        interfaceExprs.Add(substVisitor.Mutate(v, subst));
      }
      if (callSite.callSiteVar != null)
        callSiteExpr = substVisitor.Mutate(callSite.callSiteVar, subst);
    }

    public VCExpr Attach(StratifiedVC svc) {
      Contract.Assert(interfaceExprs.Count == svc.interfaceExprVars.Count);
      StratifiedInliningInfo info = svc.info;
      ProverInterface prover = info.vcgen.prover;
      VCExpressionGenerator gen = prover.VCExprGen;
      
      Dictionary<VCExprVar, VCExpr> substDict = new Dictionary<VCExprVar, VCExpr>();
      for (int i = 0; i < svc.interfaceExprVars.Count; i++) {
        VCExprVar v = svc.interfaceExprVars[i];
        substDict.Add(v, interfaceExprs[i]);
      }
      VCExprSubstitution subst = new VCExprSubstitution(substDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
      SubstitutingVCExprVisitor substVisitor = new SubstitutingVCExprVisitor(prover.VCExprGen);
      svc.vcexpr = substVisitor.Mutate(svc.vcexpr, subst);
      foreach (StratifiedCallSite scs in svc.CallSites) {
        List<VCExpr> newInterfaceExprs = new List<VCExpr>();
        foreach (VCExpr expr in scs.interfaceExprs) {
          newInterfaceExprs.Add(substVisitor.Mutate(expr, subst));
        }
        scs.interfaceExprs = newInterfaceExprs;
      }
      foreach (StratifiedCallSite scs in svc.RecordProcCallSites) {
        List<VCExpr> newInterfaceExprs = new List<VCExpr>();
        foreach (VCExpr expr in scs.interfaceExprs) {
          newInterfaceExprs.Add(substVisitor.Mutate(expr, subst));
        }
        scs.interfaceExprs = newInterfaceExprs;
      }
      return gen.Implies(callSiteExpr, svc.vcexpr);
    }
  }

  public class StratifiedInliningInfo {
    public StratifiedVCGenBase vcgen;
    public Implementation impl;
    public Function function;
    public Variable controlFlowVariable;
    public AssertCmd exitAssertCmd;
    public VCExpr vcexpr;
    public List<VCExprVar> interfaceExprVars;
    public List<VCExprVar> privateExprVars;
    public Dictionary<int, Absy> label2absy;
    public ModelViewInfo mvInfo;
    public Dictionary<Block, List<CallSite>> callSites;
    public Dictionary<Block, List<CallSite>> recordProcCallSites;
    public bool initialized { get; private set; }

    public StratifiedInliningInfo(Implementation implementation, StratifiedVCGenBase stratifiedVcGen) {
      vcgen = stratifiedVcGen;
      impl = implementation;

      List<Variable> functionInterfaceVars = new List<Variable>();
      foreach (Variable v in vcgen.program.GlobalVariables()) {
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type), true));
      }
      foreach (Variable v in impl.InParams) {
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type), true));
      }
      foreach (Variable v in impl.OutParams) {
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type), true));
      }
      foreach (IdentifierExpr e in impl.Proc.Modifies) {
        if (e.Decl == null) continue;
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", e.Decl.TypedIdent.Type), true));
      }
      Formal returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false);
      function = new Function(Token.NoToken, impl.Name, functionInterfaceVars, returnVar);
      vcgen.prover.Context.DeclareFunction(function, "");

      List<Expr> exprs = new List<Expr>();
      foreach (Variable v in vcgen.program.GlobalVariables()) {
        Contract.Assert(v != null);
        exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
      }
      foreach (Variable v in impl.Proc.InParams) {
        Contract.Assert(v != null);
        exprs.Add(new IdentifierExpr(Token.NoToken, v));
      }
      foreach (Variable v in impl.Proc.OutParams) {
        Contract.Assert(v != null);
        exprs.Add(new IdentifierExpr(Token.NoToken, v));
      }
      foreach (IdentifierExpr ie in impl.Proc.Modifies) {
        Contract.Assert(ie != null);
        if (ie.Decl == null)
          continue;
        exprs.Add(ie);
      }
      Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(function), exprs);
      impl.Proc.Ensures.Add(new Ensures(Token.NoToken, true, freePostExpr, "", new QKeyValue(Token.NoToken, "si_fcall", new List<object>(), null)));

      initialized = false;
    }

    public void GenerateVC() {
      if (initialized) return;
      List<Variable> outputVariables = new List<Variable>();
      Expr assertExpr = new LiteralExpr(Token.NoToken, true);
      foreach (Variable v in impl.OutParams) {
        Constant c = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
        outputVariables.Add(c);
        Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
        assertExpr = Expr.And(assertExpr, eqExpr);
      }
      foreach (IdentifierExpr e in impl.Proc.Modifies) {
        if (e.Decl == null) continue;
        Variable v = e.Decl;
        Constant c = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
        outputVariables.Add(c);
        Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
        assertExpr = Expr.And(assertExpr, eqExpr);
      }
      exitAssertCmd = new AssertCmd(Token.NoToken, Expr.Not(assertExpr));

      Program program = vcgen.program;
      ProverInterface proverInterface = vcgen.prover;
      vcgen.ConvertCFG2DAG(impl);
      vcgen.PassifyImpl(impl, out mvInfo);

      VCExpressionGenerator gen = proverInterface.VCExprGen;
      var exprGen = proverInterface.Context.ExprGen;
      var translator = proverInterface.Context.BoogieExprTranslator;
      
      VCExpr controlFlowVariableExpr = null;
      if (!CommandLineOptions.Clo.UseLabels) {
        controlFlowVariable = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "@cfc", Microsoft.Boogie.Type.Int));
        controlFlowVariableExpr = translator.LookupVariable(controlFlowVariable);
        vcgen.InstrumentCallSites(impl);
      }
      
      label2absy = new Dictionary<int, Absy>();
      VCGen.CodeExprConversionClosure cc = new VCGen.CodeExprConversionClosure(label2absy, proverInterface.Context);
      translator.SetCodeExprConverter(cc.CodeExprToVerificationCondition); 
      vcexpr = gen.Not(vcgen.GenerateVCAux(impl, controlFlowVariableExpr, label2absy, proverInterface.Context));
      
      if (controlFlowVariableExpr != null) {
        VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(controlFlowVariableExpr, exprGen.Integer(BigNum.ZERO));
        VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
        vcexpr = exprGen.And(eqExpr, vcexpr);
        callSites = vcgen.CollectCallSites(impl);
        recordProcCallSites = vcgen.CollectRecordProcedureCallSites(impl);
      }

      privateExprVars = new List<VCExprVar>();
      foreach (Variable v in impl.LocVars) {
        privateExprVars.Add(translator.LookupVariable(v));
      }
      foreach (Variable v in impl.OutParams) {
        privateExprVars.Add(translator.LookupVariable(v));
      }

      interfaceExprVars = new List<VCExprVar>();
      foreach (Variable v in program.GlobalVariables()) {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }
      foreach (Variable v in impl.InParams) {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }
      foreach (Variable v in outputVariables) {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }

      initialized = true;
    }
  }

  public abstract class StratifiedVCGenBase : VCGen {
    public readonly static string recordProcName = "boogie_si_record";
    public Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo;
    public ProverInterface prover;

    public StratifiedVCGenBase(Program program, string/*?*/ logFilePath, bool appendLogFile, List<Checker> checkers)
      : base(program, logFilePath, appendLogFile, checkers) {
      implName2StratifiedInliningInfo = new Dictionary<string, StratifiedInliningInfo>();
      prover = ProverInterface.CreateProver(program, logFilePath, appendLogFile, CommandLineOptions.Clo.ProverKillTime);
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Implementation impl = decl as Implementation;
        if (impl == null) continue;
        implName2StratifiedInliningInfo[impl.Name] = new StratifiedInliningInfo(impl, this);
      }
      GenerateRecordFunctions();
    }

    private void GenerateRecordFunctions() {
      foreach (var decl in program.TopLevelDeclarations) {
        var proc = decl as Procedure;
        if (proc == null) continue;
        if (!proc.Name.StartsWith(recordProcName)) continue;
        Contract.Assert(proc.InParams.Count == 1);

        // Make a new function
        TypedIdent ti = new TypedIdent(Token.NoToken, "", Bpl.Type.Bool);
        Contract.Assert(ti != null);
        Formal returnVar = new Formal(Token.NoToken, ti, false);
        Contract.Assert(returnVar != null);

        // Get record type
        var argtype = proc.InParams[0].TypedIdent.Type;

        var ins = new List<Variable>();
        ins.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "x", argtype), true));

        var recordFunc = new Function(Token.NoToken, proc.Name, ins, returnVar);
        prover.Context.DeclareFunction(recordFunc, "");

        var exprs = new List<Expr>();
        exprs.Add(new IdentifierExpr(Token.NoToken, proc.InParams[0]));

        Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(recordFunc), exprs);
        proc.Ensures.Add(new Ensures(true, freePostExpr));
      }
    }

    public override void Close() {
      prover.Close();
      base.Close();
    }

    public void InstrumentCallSites(Implementation implementation) {
      var callSiteId = 0;
      foreach (Block block in implementation.Blocks) {
        List<Cmd> newCmds = new List<Cmd>();
        for (int i = 0; i < block.Cmds.Count; i++) {
          Cmd cmd = block.Cmds[i];
          newCmds.Add(cmd);
          AssumeCmd assumeCmd = cmd as AssumeCmd;
          if (assumeCmd == null) continue;
          NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
          if (naryExpr == null) continue;
          if (!implName2StratifiedInliningInfo.ContainsKey(naryExpr.Fun.FunctionName)) continue;
          Variable callSiteVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "StratifiedInliningCallSite" + callSiteId, Microsoft.Boogie.Type.Bool));
          implementation.LocVars.Add(callSiteVar);
          newCmds.Add(new AssumeCmd(Token.NoToken, new IdentifierExpr(Token.NoToken, callSiteVar)));
          callSiteId++;
        }
        block.Cmds = newCmds;
      }
    }

    public Dictionary<Block, List<CallSite>> CollectCallSites(Implementation implementation) {
      var callSites = new Dictionary<Block, List<CallSite>>();
      foreach (Block block in implementation.Blocks) {
        for (int i = 0; i < block.Cmds.Count; i++) {
          Cmd cmd = block.Cmds[i];
          AssumeCmd assumeCmd = cmd as AssumeCmd;
          if (assumeCmd == null) continue;
          NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
          if (naryExpr == null) continue;
          if (!implName2StratifiedInliningInfo.ContainsKey(naryExpr.Fun.FunctionName)) continue;
          List<VCExpr> interfaceExprs = new List<VCExpr>();
          foreach (Expr e in naryExpr.Args) {
            interfaceExprs.Add(prover.Context.BoogieExprTranslator.Translate(e));
          }
          int instr = i;
          i++;
          AssumeCmd callSiteAssumeCmd = (AssumeCmd)block.Cmds[i];
          IdentifierExpr iexpr = (IdentifierExpr) callSiteAssumeCmd.Expr;
          CallSite cs = new CallSite(naryExpr.Fun.FunctionName, interfaceExprs, prover.Context.BoogieExprTranslator.LookupVariable(iexpr.Decl), block, instr);
          if (!callSites.ContainsKey(block))
            callSites[block] = new List<CallSite>();
          callSites[block].Add(cs);
        }
      }
      return callSites;
    }

    public Dictionary<Block, List<CallSite>> CollectRecordProcedureCallSites(Implementation implementation) {
      var callSites = new Dictionary<Block, List<CallSite>>();
      foreach (Block block in implementation.Blocks) {
        for (int i = 0; i < block.Cmds.Count; i++) {
          AssumeCmd assumeCmd = block.Cmds[i] as AssumeCmd;
          if (assumeCmd == null) continue;
          NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
          if (naryExpr == null) continue;
          if (!naryExpr.Fun.FunctionName.StartsWith(recordProcName)) continue;
          List<VCExpr> interfaceExprs = new List<VCExpr>();
          foreach (Expr e in naryExpr.Args) {
            interfaceExprs.Add(prover.Context.BoogieExprTranslator.Translate(e));
          }
          CallSite cs = new CallSite(naryExpr.Fun.FunctionName, interfaceExprs, null, block, i);
          if (!callSites.ContainsKey(block))
            callSites[block] = new List<CallSite>();
          callSites[block].Add(cs);
        }
      }
      return callSites;
    }

    private int macroCountForStratifiedInlining = 0;
    public Macro CreateNewMacro() {
      string newName = "StratifiedInliningMacro@" + macroCountForStratifiedInlining.ToString();
      macroCountForStratifiedInlining++;
      return new Macro(Token.NoToken, newName, new List<Variable>(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool), false));
    }
    private int varCountForStratifiedInlining = 0;
    public VCExprVar CreateNewVar(Microsoft.Boogie.Type type) {
      string newName = "StratifiedInliningVar@" + varCountForStratifiedInlining.ToString();
      varCountForStratifiedInlining++;
      Constant newVar = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, type));
      prover.Context.DeclareConstant(newVar, false, null);
      return prover.VCExprGen.Variable(newVar.Name, type);
    }
    private int idCountForStratifiedInlining = 0;
    public int CreateNewId() {
      return idCountForStratifiedInlining++;
    }

    // Used inside PassifyImpl
    protected override void addExitAssert(string implName, Block exitBlock) {
      if (implName2StratifiedInliningInfo != null && implName2StratifiedInliningInfo.ContainsKey(implName)) {
        AssertCmd exitAssertCmd = implName2StratifiedInliningInfo[implName].exitAssertCmd;
        Contract.Assert(exitAssertCmd != null);
        exitBlock.Cmds.Add(exitAssertCmd);
      }
    }

    public override Counterexample extractLoopTrace(Counterexample cex, string mainProcName, Program program, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo) {
      // Construct the set of inlined procs in the original program
      var inlinedProcs = new HashSet<string>();
      foreach (var decl in program.TopLevelDeclarations) {
        // Implementations
        if (decl is Implementation) {
          var impl = decl as Implementation;
          if (!(impl.Proc is LoopProcedure)) {
            inlinedProcs.Add(impl.Name);
          }
        }

        // And recording procedures
        if (decl is Procedure) {
          var proc = decl as Procedure;
          if (proc.Name.StartsWith(recordProcName)) {
            Debug.Assert(!(decl is LoopProcedure));
            inlinedProcs.Add(proc.Name);
          }
        }
      }

      return extractLoopTraceRec(
          new CalleeCounterexampleInfo(cex, new List<object>()),
          mainProcName, inlinedProcs, extractLoopMappingInfo).counterexample;
    }

    protected override bool elIsLoop(string procname) {
      StratifiedInliningInfo info = null;
      if (implName2StratifiedInliningInfo.ContainsKey(procname)) {
        info = implName2StratifiedInliningInfo[procname];
      }

      if (info == null) return false;

      var lp = info.impl.Proc as LoopProcedure;

      if (lp == null) return false;
      return true;
    }

    public abstract Outcome FindLeastToVerify(Implementation impl, ref HashSet<string> allBoolVars);
  }

  public class StratifiedVCGen : StratifiedVCGenBase {
    public bool PersistCallTree;
    public static Dictionary<string, int> callTree = null;
    public int numInlined = 0;
    private bool useSummary;
    private SummaryComputation summaryComputation;
    private HashSet<string> procsThatReachedRecBound;
    public HashSet<string> procsToSkip;
    public Dictionary<string, int> extraRecBound;

    public StratifiedVCGen(bool usePrevCallTree, Dictionary<string, int> prevCallTree, 
                           HashSet<string> procsToSkip, Dictionary<string, int> extraRecBound,
                           Program program, string/*?*/ logFilePath, bool appendLogFile, List<Checker> checkers) 
    : this(program, logFilePath, appendLogFile, checkers)
    {
      this.procsToSkip = new HashSet<string>(procsToSkip);
      this.extraRecBound = new Dictionary<string, int>(extraRecBound);

      if (usePrevCallTree) {
        callTree = prevCallTree;
        PersistCallTree = true;
      }
      else {
        PersistCallTree = false;
      }
    }

    public StratifiedVCGen(Program program, string/*?*/ logFilePath, bool appendLogFile, List<Checker> checkers)
      : base(program, logFilePath, appendLogFile, checkers) {
      PersistCallTree = false;
      useSummary = false;
      procsThatReachedRecBound = new HashSet<string>();
      procsToSkip = new HashSet<string>();
      extraRecBound = new Dictionary<string, int>();
    }

    // Is this procedure to be "skipped" 
    // Currently this is experimental
    public bool isSkipped(string procName) {
      return procsToSkip.Contains(procName);
    }
    public bool isSkipped(int candidate, FCallHandler calls) {
      return isSkipped(calls.getProc(candidate));
    }
    // Extra rec bound for procedures
    public int GetExtraRecBound(string procName) {
      if (!extraRecBound.ContainsKey(procName))
        return 0;
      else return extraRecBound[procName];
    }

    public class SummaryComputation {
      // The verification state
      VerificationState vState;
      // The call tree
      FCallHandler calls;
      // Fully-inlined guys we have already queried
      HashSet<string> fullyInlinedCache;

      // The summary: boolean guards that are true
      HashSet<VCExprVar> trueSummaryConst;
      HashSet<VCExprVar> trueSummaryConstUndeBound;

      // Compute summaries under recursion bound or not?
      bool ComputeUnderBound;

      public SummaryComputation(VerificationState vState, bool ComputeUnderBound) {
        this.vState = vState;
        this.calls = vState.calls;
        this.fullyInlinedCache = new HashSet<string>();
        this.trueSummaryConst = new HashSet<VCExprVar>();
        this.trueSummaryConstUndeBound = new HashSet<VCExprVar>();
        this.ComputeUnderBound = false;
      }

      public void boundChanged() {
        if (ComputeUnderBound) {
          var s = "";
          trueSummaryConstUndeBound.Iter(v => s = s + v.ToString() + ",");
          Console.WriteLine("Clearing summaries: {0}", s);

          // start from scratch
          trueSummaryConst.ExceptWith(trueSummaryConstUndeBound);
          trueSummaryConstUndeBound = new HashSet<VCExprVar>();
        }
      }

      public void compute(HashSet<int> goodCandidates, int bound) {
        var start = DateTime.UtcNow;
        goodCandidates = calls.currCandidates;

        var found = 0;

        // Find all nodes that have children only in goodCandidates
        var overApproxNodes = FindNodes(calls.candidateParent, calls.currCandidates, goodCandidates);
        overApproxNodes.IntersectWith(calls.summaryCandidates.Keys);

        var roots = FindTopMostAncestors(calls.candidateParent, overApproxNodes);
        var prover2 = vState.checker2.prover;
        var reporter2 = vState.checker2.reporter;

        prover2.Push();

        // candidates to block
        var block = new HashSet<int>();
        var usesBound = new HashSet<int>();
        if (ComputeUnderBound) {
          calls.currCandidates.Iter(id => { if (calls.getRecursionBound(id) > bound) block.Add(id); });
          foreach (var id in block) {
            prover2.Assert(calls.getFalseExpr(id), true);
            var curr = id;
            usesBound.Add(id);
            while (curr != 0) {
              curr = calls.candidateParent[curr];
              usesBound.Add(curr);
            }
          }

        }

        // Iterate over the roots
        foreach (var id in roots) {
          // inline procedures in post order
          var post = getPostOrder(calls.candidateParent, id);

          vState.checker.prover.Push();
          foreach (var cid in post) {
            if (goodCandidates.Contains(cid)) continue;

            prover2.Assert(calls.id2VC[cid], true);
            if (!overApproxNodes.Contains(cid)) continue;
            prover2.Assert(calls.id2ControlVar[cid], true);

            foreach (var tup in calls.summaryCandidates[cid]) {
              if (trueSummaryConst.Contains(tup.Item1)) continue;

              //Console.WriteLine("Going to try ({0} ==> {1}) on {2}", tup.Item1, tup.Item2, id);
              //Console.WriteLine("Call expr: {0}", calls.id2Candidate[id]);

              // It is OK to assume the summary while trying to prove it
              var summary = getSummary(tup.Item1);

              prover2.Push();
              prover2.Assert(summary, true);
              prover2.Assert(prover2.VCExprGen.Not(tup.Item2), true);
              prover2.Check();
              var outcome = ConditionGeneration.ProverInterfaceOutcomeToConditionGenerationOutcome(prover2.CheckOutcomeCore(reporter2));

              prover2.Pop();
              if (outcome == Outcome.Correct) {
                //Console.WriteLine("Found summary: {0}", tup.Item1);
                found++;
                trueSummaryConst.Add(tup.Item1);
                if (usesBound.Contains(cid)) trueSummaryConstUndeBound.Add(tup.Item1);
              }
            }
          }
          prover2.Pop();
        }
        prover2.Pop();

        var end = DateTime.UtcNow;
        if (CommandLineOptions.Clo.StratifiedInliningVerbose > 0) {
          Console.WriteLine(">> Summary computation took {0} sec and inferred {1} of {2} contracts",
              (end - start).TotalSeconds, found, calls.allSummaryConst.Count);
        }

      }


      public VCExpr getSummary() {
        return getSummary(new HashSet<VCExprVar>());
      }

      public VCExpr getSummary(params VCExprVar[] p) {
        var s = new HashSet<VCExprVar>();
        p.Iter(v => s.Add(v));
        return getSummary(s);
      }

      public VCExpr getSummary(HashSet<VCExprVar> extraToSet) {
        if (calls.allSummaryConst.Count == 0) return null;
        // TODO: does it matter which checker we use here?
        var Gen = vState.checker.prover.VCExprGen;

        var ret = VCExpressionGenerator.True;
        foreach (var c in calls.allSummaryConst) {
          if (trueSummaryConst.Contains(c) || extraToSet.Contains(c)) {
            ret = Gen.And(ret, c);
          }
          else {
            ret = Gen.And(ret, Gen.Not(c));
          }
        }
        return ret;
      }

      // Return a subset of nodes such that all other nodes are their decendent
      private HashSet<int> FindTopMostAncestors(Dictionary<int, int> parents, HashSet<int> nodes) {
        var ret = new HashSet<int>();
        //var ancestorFound = new HashSet<int>();
        foreach (var n in nodes) {
          var ancestor = n;
          var curr = n;
          while (curr != 0) {
            curr = parents[curr];
            if (nodes.Contains(curr)) ancestor = curr;
          }
          ret.Add(ancestor);
        }
        return ret;
      }

      // Returns the set of candidates whose child leaves are all "good". Remove fully inlined ones.
      HashSet<int> FindNodes(Dictionary<int, int> parents, HashSet<int> allLeaves,
          HashSet<int> goodLeaves) {
        var ret = new HashSet<int>();
        var leaves = new Dictionary<int, HashSet<int>>();
        leaves.Add(0, new HashSet<int>());
        parents.Keys.Iter(n => leaves.Add(n, new HashSet<int>()));
        allLeaves.Iter(l => leaves[l].Add(l));

        foreach (var l in allLeaves) {
          var curr = l;
          leaves[curr].Add(l);
          while (parents.ContainsKey(curr)) {
            curr = parents[curr];
            leaves[curr].Add(l);
          }
        }

        foreach (var kvp in leaves) {
          if (kvp.Value.Count == 0) {
            var proc = calls.getProc(kvp.Key);
            if (fullyInlinedCache.Contains(proc)) continue;
            else {
              ret.Add(kvp.Key);
              fullyInlinedCache.Add(proc);
            }
          }

          if (kvp.Value.IsSubsetOf(goodLeaves)) {
            ret.Add(kvp.Key);
          }
        }

        return ret;
      }


      // returns children of root in post order
      static List<int> getPostOrder(Dictionary<int, int> parents, int root) {
        var children = new Dictionary<int, HashSet<int>>();
        foreach (var id in parents.Keys) children.Add(id, new HashSet<int>());
        children.Add(0, new HashSet<int>());
        foreach (var kvp in parents) children[kvp.Value].Add(kvp.Key);
        return getPostOrder(children, root);
      }
      static List<int> getPostOrder(Dictionary<int, HashSet<int>> children, int root) {
        var ret = new List<int>();
        foreach (var ch in children[root]) ret.AddRange(getPostOrder(children, ch));
        ret.Add(root);
        return ret;
      }
    }

    public class ApiChecker {
      public ProverInterface prover;
      public ProverInterface.ErrorHandler reporter;

      public ApiChecker(ProverInterface prover, ProverInterface.ErrorHandler reporter) {
        this.reporter = reporter;
        this.prover = prover;
      }

      private Outcome CheckVC() {
        prover.Check();
        ProverInterface.Outcome outcome = prover.CheckOutcomeCore(reporter);

        return ConditionGeneration.ProverInterfaceOutcomeToConditionGenerationOutcome(outcome);
      }

      public Outcome CheckAssumptions(List<VCExpr> assumptions) {
        if (assumptions.Count == 0) {
          return CheckVC();
        }

        prover.Push();
        foreach (var a in assumptions) {
          prover.Assert(a, true);
        }
        Outcome ret = CheckVC();
        prover.Pop();
        return ret;
      }

      public Outcome CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions) {
        List<int> unsatisfiedSoftAssumptions;
        ProverInterface.Outcome outcome = prover.CheckAssumptions(hardAssumptions, softAssumptions, out unsatisfiedSoftAssumptions, reporter);
        return ConditionGeneration.ProverInterfaceOutcomeToConditionGenerationOutcome(outcome);
      }

      public Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore) {
        ProverInterface.Outcome outcome = prover.CheckAssumptions(assumptions, out unsatCore, reporter);
        return ConditionGeneration.ProverInterfaceOutcomeToConditionGenerationOutcome(outcome);
      }
    }

    // Store important information related to a single VerifyImplementation query
    public class VerificationState {
      // The call tree
      public FCallHandler calls;
      public ApiChecker checker;
      // For statistics
      public int vcSize;
      public int expansionCount;

      // For making summary queries on the side
      public ApiChecker checker2;

      public VerificationState(VCExpr vcMain, FCallHandler calls, ProverInterface prover, ProverInterface.ErrorHandler reporter) {
        prover.Assert(vcMain, true);
        this.calls = calls;
        this.checker = new ApiChecker(prover, reporter);
        vcSize = 0;
        expansionCount = 0;
      }
      public VerificationState(VCExpr vcMain, FCallHandler calls, ProverInterface prover, ProverInterface.ErrorHandler reporter,
                               ProverInterface prover2, ProverInterface.ErrorHandler reporter2)
        : this(vcMain, calls, prover, reporter) {
        this.checker2 = new ApiChecker(prover2, reporter2);
      }
    }

    public override Outcome FindLeastToVerify(Implementation impl, ref HashSet<string> allBoolVars) {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      // Record current time
      var startTime = DateTime.UtcNow;

      // No Max: avoids theorem prover restarts
      CommandLineOptions.Clo.MaxProverMemory = 0;

      // Initialize cache
      satQueryCache = new Dictionary<int, List<HashSet<string>>>();
      unsatQueryCache = new Dictionary<int, List<HashSet<string>>>();

      Contract.Assert(implName2StratifiedInliningInfo != null);

      // Build VCs for all procedures
      implName2StratifiedInliningInfo.Values
          .Iter(info => info.GenerateVC());

      // Get the VC of the current procedure
      VCExpr vcMain = implName2StratifiedInliningInfo[impl.Name].vcexpr;
      Dictionary<int, Absy> mainLabel2absy = implName2StratifiedInliningInfo[impl.Name].label2absy;

      // Find all procedure calls in vc and put labels on them      
      FCallHandler calls = new FCallHandler(prover.VCExprGen, implName2StratifiedInliningInfo, impl.Name, mainLabel2absy);
      calls.setCurrProcAsMain();
      vcMain = calls.Mutate(vcMain, true);

      // Put all of the necessary state into one object
      var vState = new VerificationState(vcMain, calls, prover, new EmptyErrorHandler());

      // We'll restore the original state of the theorem prover at the end
      // of this procedure
      vState.checker.prover.Push();

      // Do eager inlining
      while (calls.currCandidates.Count > 0) {
        List<int> toExpand = new List<int>();

        foreach (int id in calls.currCandidates) {
          Debug.Assert(calls.getRecursionBound(id) <= 1, "Recursion not supported");
          toExpand.Add(id);
        }
        DoExpansion(toExpand, vState);
      }

      // Find all the boolean constants
      var allConsts = new HashSet<VCExprVar>();
      foreach (var decl in program.TopLevelDeclarations) {
        var constant = decl as Constant;
        if (constant == null) continue;
        if (!allBoolVars.Contains(constant.Name)) continue;
        var v = prover.Context.BoogieExprTranslator.LookupVariable(constant);
        allConsts.Add(v);
      }

      // Now, lets start the algo
      var min = refinementLoop(vState.checker, new HashSet<VCExprVar>(), allConsts, allConsts);

      var ret = new HashSet<string>();
      foreach (var v in min) {
        //Console.WriteLine(v.Name);
        ret.Add(v.Name);
      }
      allBoolVars = ret;

      vState.checker.prover.Pop();

      return Outcome.Correct;
    }

    private HashSet<VCExprVar> refinementLoop(ApiChecker apiChecker, HashSet<VCExprVar> trackedVars, HashSet<VCExprVar> trackedVarsUpperBound, HashSet<VCExprVar> allVars) {
      Debug.Assert(trackedVars.IsSubsetOf(trackedVarsUpperBound));

      // If we already know the fate of all vars, then we're done.
      if (trackedVars.Count == trackedVarsUpperBound.Count)
        return new HashSet<VCExprVar>(trackedVars);

      // See if we already have enough variables tracked
      var success = refinementLoopCheckPath(apiChecker, trackedVars, allVars);
      if (success) {
        // We have enough
        return new HashSet<VCExprVar>(trackedVars);
      }

      // If all that remains is 1 variable, then we know that we must track it
      if (trackedVars.Count + 1 == trackedVarsUpperBound.Count)
        return new HashSet<VCExprVar>(trackedVarsUpperBound);

      // Partition the remaining set of variables
      HashSet<VCExprVar> part1, part2;
      var temp = new HashSet<VCExprVar>(trackedVarsUpperBound);
      temp.ExceptWith(trackedVars);
      Partition<VCExprVar>(temp, out part1, out part2);

      // First half
      var fh = new HashSet<VCExprVar>(trackedVars); fh.UnionWith(part2);
      var s1 = refinementLoop(apiChecker, fh, trackedVarsUpperBound, allVars);

      var a = new HashSet<VCExprVar>(part1); a.IntersectWith(s1);
      var b = new HashSet<VCExprVar>(part1); b.ExceptWith(s1);
      var c = new HashSet<VCExprVar>(trackedVarsUpperBound); c.ExceptWith(b);
      a.UnionWith(trackedVars);

      // Second half
      return refinementLoop(apiChecker, a, c, allVars);
    }

    Dictionary<int, List<HashSet<string>>> satQueryCache;
    Dictionary<int, List<HashSet<string>>> unsatQueryCache;

    private bool refinementLoopCheckPath(ApiChecker apiChecker, HashSet<VCExprVar> varsToSet, HashSet<VCExprVar> allVars) {
      var assumptions = new List<VCExpr>();
      var prover = apiChecker.prover;
      var query = new HashSet<string>();
      varsToSet.Iter(v => query.Add(v.Name));

      if (checkCache(query, unsatQueryCache)) {
        prover.LogComment("FindLeast: Query Cache Hit");
        return true;
      }
      if (checkCache(query, satQueryCache)) {
        prover.LogComment("FindLeast: Query Cache Hit");
        return false;
      }

      prover.LogComment("FindLeast: Query Begin");

      foreach (var c in allVars) {
        if (varsToSet.Contains(c)) {
          assumptions.Add(c);
        }
        else {
          assumptions.Add(prover.VCExprGen.Not(c));
        }
      }

      var o = apiChecker.CheckAssumptions(assumptions);
      Debug.Assert(o == Outcome.Correct || o == Outcome.Errors);
      //Console.WriteLine("Result = " + o.ToString());
      prover.LogComment("FindLeast: Query End");

      if (o == Outcome.Correct) {
        insertCache(query, unsatQueryCache);
        return true;
      }

      insertCache(query, satQueryCache);
      return false;
    }

    private bool checkCache(HashSet<string> q, Dictionary<int, List<HashSet<string>>> cache) {
      if (!cache.ContainsKey(q.Count)) return false;
      foreach (var s in cache[q.Count]) {
        if (q.SetEquals(s)) return true;
      }
      return false;
    }

    private void insertCache(HashSet<string> q, Dictionary<int, List<HashSet<string>>> cache) {
      if (!cache.ContainsKey(q.Count)) {
        cache.Add(q.Count, new List<HashSet<string>>());
      }
      cache[q.Count].Add(q);
    }

    public static void Partition<T>(HashSet<T> values, out HashSet<T> part1, out HashSet<T> part2) {
      part1 = new HashSet<T>();
      part2 = new HashSet<T>();
      var size = values.Count;
      var crossed = false;
      var curr = 0;
      foreach (var s in values) {
        if (crossed) part2.Add(s);
        else part1.Add(s);
        curr++;
        if (!crossed && curr >= size / 2) crossed = true;
      }
    }

    public override Outcome VerifyImplementation(Implementation/*!*/ impl, VerifierCallback/*!*/ callback) {
      Debug.Assert(QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint"));
      Debug.Assert(this.program == program);

      var computeUnderBound = true;

      #region stratified inlining options
      switch (CommandLineOptions.Clo.StratifiedInliningOption) {
        case 1:
          useSummary = true;
          break;
        case 2:
          useSummary = true;
          computeUnderBound = false;
          break;
      }
      #endregion

      ProverInterface prover2 = null;
      if (useSummary) {
        prover2 = ProverInterface.CreateProver(program, "prover2.txt", true, CommandLineOptions.Clo.ProverKillTime);
      }

      // Record current time
      var startTime = DateTime.UtcNow;

      // Flush any axioms that came with the program before we start SI on this implementation
      prover.AssertAxioms();

      // Run live variable analysis
      if (CommandLineOptions.Clo.LiveVariableAnalysis == 2) {
        Microsoft.Boogie.InterProcGenKill.ComputeLiveVars(impl, program);
      }

      // Get the VC of the current procedure
      StratifiedInliningInfo info = implName2StratifiedInliningInfo[impl.Name];
      info.GenerateVC();
      VCExpr vc = info.vcexpr;
      Dictionary<int, Absy> mainLabel2absy = info.label2absy;
      var reporter = new StratifiedInliningErrorReporter(implName2StratifiedInliningInfo, prover, callback, info);

      // Find all procedure calls in vc and put labels on them      
      FCallHandler calls = new FCallHandler(prover.VCExprGen, implName2StratifiedInliningInfo, impl.Name, mainLabel2absy);
      calls.setCurrProcAsMain();
      vc = calls.Mutate(vc, true);
      reporter.SetCandidateHandler(calls);
      calls.id2VC.Add(0, vc);
      calls.extraRecursion = extraRecBound;

      // Identify summary candidates: Match ensure clauses with the appropriate call site
      if (useSummary) calls.matchSummaries();

      // We'll restore the original state of the theorem prover at the end
      // of this procedure
      prover.Push();

      // Put all of the necessary state into one object
      var vState = new VerificationState(vc, calls, prover, reporter, prover2, new EmptyErrorHandler());
      vState.vcSize += SizeComputingVisitor.ComputeSize(vc);

      if (useSummary) summaryComputation = new SummaryComputation(vState, computeUnderBound);


      Outcome ret = Outcome.ReachedBound;

      #region eager inlining
      for (int i = 1; i < CommandLineOptions.Clo.StratifiedInlining && calls.currCandidates.Count > 0; i++) {
        List<int> toExpand = new List<int>();

        foreach (int id in calls.currCandidates) {
          if (calls.getRecursionBound(id) <= CommandLineOptions.Clo.RecursionBound) {
            toExpand.Add(id);
          }
        }
        DoExpansion(toExpand, vState);
      }
      #endregion

      #region Repopulate call tree, if there is one
      if (PersistCallTree && callTree != null) {
        bool expand = true;
        while (expand) {
          List<int> toExpand = new List<int>();
          foreach (int id in calls.currCandidates) {
            if (callTree.ContainsKey(calls.getPersistentId(id))) {
              toExpand.Add(id);
            }
          }
          if (toExpand.Count == 0) expand = false;
          else {
            DoExpansion(toExpand, vState);
          }
        }
      }
      #endregion

      if (CommandLineOptions.Clo.StratifiedInliningVerbose > 0) {
        Console.WriteLine(">> SI: Size of VC after eager inlining: {0}", vState.vcSize);
      }

      // Under-approx query is only needed if something was inlined since
      // the last time an under-approx query was made
      // TODO: introduce this
      // bool underApproxNeeded = true;

      // The recursion bound for stratified search
      int bound = CommandLineOptions.Clo.NonUniformUnfolding ? CommandLineOptions.Clo.RecursionBound : 1;

      int done = 0;

      int iters = 0;

      // for blocking candidates (and focusing on a counterexample)
      var block = new HashSet<int>();

      // Process tasks while not done. We're done when:
      //   case 1: (correct) We didn't find a bug (either an over-approx query was valid
      //                     or we reached the recursion bound) and the task is "step"
      //   case 2: (bug)     We find a bug
      //   case 3: (internal error)   The theorem prover TimesOut of runs OutOfMemory
      while (true)
      {
          // Check timeout
          if (CommandLineOptions.Clo.ProverKillTime != -1)
          {
              if ((DateTime.UtcNow - startTime).TotalSeconds > CommandLineOptions.Clo.ProverKillTime)
              {
                  ret = Outcome.TimedOut;
                  break;
              }
          }

          if (done > 0)
          {
              break;
          }

          VCExpr summary = null;
          if (useSummary) summary = summaryComputation.getSummary();

          if (useSummary && summary != null)
          {
              vState.checker.prover.Push();
              vState.checker.prover.Assert(summary, true);
          }

          // Stratified Step
          ret = stratifiedStep(bound, vState, block);
          iters++;

          if (useSummary && summary != null)
          {
              vState.checker.prover.Pop();
          }

          // Sorry, out of luck (time/memory)
          if (ret == Outcome.Inconclusive || ret == Outcome.OutOfMemory || ret == Outcome.TimedOut)
          {
              done = 3;
              continue;
          }

          if (ret == Outcome.Errors && reporter.underapproximationMode)
          {
              // Found a bug
              done = 2;
          }
          else if (ret == Outcome.Correct)
          {
              if (block.Count == 0)
              {
                  // Correct
                  done = 1;
              }
              else
              {
                  Contract.Assert(useSummary);
                  // reset blocked and continue loop
                  block.Clear();
              }
          }
          else if (ret == Outcome.ReachedBound)
          {
              if (block.Count == 0)
              {
                  // Increment bound
                  bound++;
                  if (useSummary) summaryComputation.boundChanged();

                  if (bound > CommandLineOptions.Clo.RecursionBound)
                  {
                      // Correct under bound
                      done = 1;
                  }
              }
              else
              {
                  Contract.Assert(useSummary);
                  // reset blocked and continue loop
                  block.Clear();
              }
          }
          else
          {
              // Do inlining
              Debug.Assert(ret == Outcome.Errors && !reporter.underapproximationMode);
              Contract.Assert(reporter.candidatesToExpand.Count != 0);
              if (useSummary)
              {
                  // compute candidates to block  
                  block = new HashSet<int>(calls.currCandidates);
                  block.ExceptWith(reporter.candidatesToExpand);
              }

              #region expand call tree
              if (CommandLineOptions.Clo.StratifiedInliningVerbose > 0)
              {
                  Console.Write(">> SI Inlining: ");
                  reporter.candidatesToExpand
                      .Select(c => calls.getProc(c))
                      .Iter(c => { if (!isSkipped(c)) Console.Write("{0} ", c); });

                  Console.WriteLine();
                  Console.Write(">> SI Skipping: ");
                  reporter.candidatesToExpand
                      .Select(c => calls.getProc(c))
                      .Iter(c => { if (isSkipped(c)) Console.Write("{0} ", c); });

                  Console.WriteLine();

              }

              // Expand and try again
              vState.checker.prover.LogComment(";;;;;;;;;;;; Expansion begin ;;;;;;;;;;");
              DoExpansion(reporter.candidatesToExpand, vState);
              vState.checker.prover.LogComment(";;;;;;;;;;;; Expansion end ;;;;;;;;;;");

              #endregion
          }
      }

      // Pop off everything that we pushed so that there are no side effects from
      // this call to VerifyImplementation
      vState.checker.prover.Pop();

      if (CommandLineOptions.Clo.StratifiedInliningVerbose > 0) {
        Console.WriteLine(">> SI: Expansions performed: {0}", vState.expansionCount);
        Console.WriteLine(">> SI: Candidates left: {0}", calls.currCandidates.Count);
        Console.WriteLine(">> SI: Candidates skipped: {0}", calls.currCandidates.Where(i => isSkipped(i, calls)).Count());
        Console.WriteLine(">> SI: VC Size: {0}", vState.vcSize);
      }

      numInlined = (calls.candidateParent.Keys.Count + 1) - (calls.currCandidates.Count);

      var rbound = "Procs that reached bound: ";
      foreach (var s in procsThatReachedRecBound) rbound += "  " + s;
      if (ret == Outcome.ReachedBound) Helpers.ExtraTraceInformation(rbound);

      // Store current call tree
      if (PersistCallTree && (ret == Outcome.Correct || ret == Outcome.Errors || ret == Outcome.ReachedBound)) {
        callTree = new Dictionary<string, int>();
        //var persistentNodes = new HashSet<int>(calls.candidateParent.Values);
        var persistentNodes = new HashSet<int>(calls.candidateParent.Keys);
        persistentNodes.Add(0);
        persistentNodes.ExceptWith(calls.currCandidates);

        foreach (var id in persistentNodes) {
          callTree.Add(calls.getPersistentId(id), 0);
        }
      }
      if (prover2 != null) prover2.Close();
      return ret;
    }

    // A step of the stratified inlining algorithm: both under-approx and over-approx queries
    private Outcome stratifiedStep(int bound, VerificationState vState, HashSet<int> block) {
      var calls = vState.calls;
      var checker = vState.checker;
      var prover = checker.prover;
      var reporter = checker.reporter as StratifiedInliningErrorReporter;

      reporter.underapproximationMode = true;
      prover.LogComment(";;;;;;;;;;;; Underapprox mode begin ;;;;;;;;;;");
      List<VCExpr> assumptions = new List<VCExpr>();

      foreach (int id in calls.currCandidates) {
        if (!isSkipped(id, calls))
          assumptions.Add(calls.getFalseExpr(id));
      }
      Outcome ret = checker.CheckAssumptions(assumptions);
      prover.LogComment(";;;;;;;;;;;; Underapprox mode end ;;;;;;;;;;");

      if (ret != Outcome.Correct) {
        // Either the query returned an error or it ran out of memory or time.
        // In all cases, we are done.
        return ret;
      }

      if (calls.currCandidates.Count == 0) {
        // If we didn't underapproximate, then we're done
        return ret;
      }

      prover.LogComment(";;;;;;;;;;;; Overapprox mode begin ;;;;;;;;;;");

      // Over-approx query
      reporter.underapproximationMode = false;

      // Push "true" for all, except:
      // push "false" for all candidates that have reached
      // the recursion bounds

      bool allTrue = true;
      bool allFalse = true;
      List<VCExpr> softAssumptions = new List<VCExpr>();

      assumptions = new List<VCExpr>();
      procsThatReachedRecBound.Clear();

      foreach (int id in calls.currCandidates) {
        if (isSkipped(id, calls)) continue;

        int idBound = calls.getRecursionBound(id);
        if (idBound <= bound) {
          if (idBound > 1)
            softAssumptions.Add(calls.getFalseExpr(id));

          if (block.Contains(id)) {
            Contract.Assert(useSummary);
            assumptions.Add(calls.getFalseExpr(id));
            allTrue = false;
          }
          else {
            allFalse = false;
          }
        }
        else {
          procsThatReachedRecBound.Add(calls.getProc(id));
          assumptions.Add(calls.getFalseExpr(id));
          allTrue = false;
        }
      }

      if (allFalse) {
        // If we made all candidates false, then this is the same
        // as the underapprox query. We already know the answer.
        ret = Outcome.Correct;
      }
      else {
        ret = CommandLineOptions.Clo.NonUniformUnfolding
              ? checker.CheckAssumptions(assumptions, softAssumptions)
              : checker.CheckAssumptions(assumptions);
      }

      if (ret != Outcome.Correct && ret != Outcome.Errors) {
        // The query ran out of memory or time, that's it,
        // we cannot do better. Give up!
        return ret;
      }

      if (ret == Outcome.Correct) {
        // If nothing was made false, then the program is correct
        if (allTrue) {
          return ret;
        }

        if (useSummary) {
          // Find the set of candidates with valid over-approximations
          var assumeTrueCandidates = new HashSet<int>(vState.calls.currCandidates);
          assumeTrueCandidates.ExceptWith(block);
          summaryComputation.compute(assumeTrueCandidates, bound);
        }

        // Nothing more can be done with current recursion bound. 
        return Outcome.ReachedBound;
      }

      Contract.Assert(ret == Outcome.Errors);

      prover.LogComment(";;;;;;;;;;;; Overapprox mode end ;;;;;;;;;;");

      return ret;
    }

    // A counter for adding new variables
    static int newVarCnt = 0;

    // Does on-demand inlining -- pushes procedure bodies on the theorem prover stack.
    private void DoExpansion(List<int>/*!*/ candidates, VerificationState vState) {
      Contract.Requires(candidates != null);
      Contract.Requires(vState.calls != null);
      Contract.Requires(vState.checker.prover != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      // Skipped calls don't get inlined
      candidates = candidates.FindAll(id => !isSkipped(id, vState.calls));

      vState.expansionCount += candidates.Count;

      var prover = vState.checker.prover;
      var calls = vState.calls;

      VCExpr exprToPush = VCExpressionGenerator.True;
      Contract.Assert(exprToPush != null);
      foreach (int id in candidates) {
        VCExprNAry expr = calls.id2Candidate[id];
        Contract.Assert(expr != null);
        string procName = cce.NonNull(expr.Op as VCExprBoogieFunctionOp).Func.Name;
        if (!implName2StratifiedInliningInfo.ContainsKey(procName)) continue;

        StratifiedInliningInfo info = implName2StratifiedInliningInfo[procName];
        info.GenerateVC();
        //Console.WriteLine("Inlining {0}", procName);
        VCExpr expansion = cce.NonNull(info.vcexpr);

        // Instantiate the "forall" variables
        Dictionary<VCExprVar, VCExpr> substForallDict = new Dictionary<VCExprVar, VCExpr>();
        Contract.Assert(info.interfaceExprVars.Count == expr.Length);
        for (int i = 0; i < info.interfaceExprVars.Count; i++) {
          substForallDict.Add(info.interfaceExprVars[i], expr[i]);
        }
        VCExprSubstitution substForall = new VCExprSubstitution(substForallDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());

        SubstitutingVCExprVisitor subst = new SubstitutingVCExprVisitor(prover.VCExprGen);
        Contract.Assert(subst != null);
        expansion = subst.Mutate(expansion, substForall);

        // Instantiate and declare the "exists" variables
        Dictionary<VCExprVar, VCExpr> substExistsDict = new Dictionary<VCExprVar, VCExpr>();
        foreach (VCExprVar v in info.privateExprVars) {
          Contract.Assert(v != null);
          string newName = v.Name + "_si_" + newVarCnt.ToString();
          newVarCnt++;
          prover.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, v.Type)), false, null);
          substExistsDict.Add(v, prover.VCExprGen.Variable(newName, v.Type));
        }
        if (CommandLineOptions.Clo.ModelViewFile != null) {
          SaveSubstitution(vState, id, substForallDict, substExistsDict);
        }
        VCExprSubstitution substExists = new VCExprSubstitution(substExistsDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());

        subst = new SubstitutingVCExprVisitor(prover.VCExprGen);
        expansion = subst.Mutate(expansion, substExists);

        if (!calls.currCandidates.Contains(id)) {
          Console.WriteLine("Don't know what we just expanded");
        }

        calls.currCandidates.Remove(id);

        // Record the new set of candidates and rename absy labels
        calls.currInlineCount = id;
        calls.setCurrProc(procName);
        expansion = calls.Mutate(expansion, true);
        if (useSummary) calls.matchSummaries();

        //expansion = checker.VCExprGen.Eq(calls.id2ControlVar[id], expansion);
        expansion = prover.VCExprGen.Implies(calls.id2ControlVar[id], expansion);
        calls.id2VC.Add(id, expansion);

        exprToPush = prover.VCExprGen.And(exprToPush, expansion);
      }
      vState.checker.prover.Assert(exprToPush, true);
      vState.vcSize += SizeComputingVisitor.ComputeSize(exprToPush);
    }

    private void SaveSubstitution(VerificationState vState, int id,
      Dictionary<VCExprVar, VCExpr> substForallDict, Dictionary<VCExprVar, VCExpr> substExistsDict) {
      var prover = vState.checker.prover;
      var calls = vState.calls;
      Boogie2VCExprTranslator translator = prover.Context.BoogieExprTranslator;
      VCExprVar mvStateConstant = translator.LookupVariable(ModelViewInfo.MVState_ConstantDef);
      substExistsDict.Add(mvStateConstant, prover.VCExprGen.Integer(BigNum.FromInt(id)));
      Dictionary<VCExprVar, VCExpr> mapping = new Dictionary<VCExprVar, VCExpr>();
      foreach (var key in substForallDict.Keys)
        mapping[key] = substForallDict[key];
      foreach (var key in substExistsDict.Keys)
        mapping[key] = substExistsDict[key];
      calls.id2Vars[id] = mapping;
    }

    // Uniquely identifies a procedure call (the call expr, instance)
    public class BoogieCallExpr : IEquatable<BoogieCallExpr> {
      public NAryExpr expr;
      public int inlineCnt;

      public BoogieCallExpr(NAryExpr expr, int inlineCnt) {
        this.expr = expr;
        this.inlineCnt = inlineCnt;
      }

      public override int GetHashCode() {
        return expr.GetHashCode() + 131 * inlineCnt.GetHashCode();
      }

      public override bool Equals(object obj) {
        BoogieCallExpr that = obj as BoogieCallExpr;
        return (expr == that.expr && inlineCnt == that.inlineCnt);
      }

      public bool Equals(BoogieCallExpr that) {
        return (expr == that.expr && inlineCnt == that.inlineCnt);
      }
    }

    // This class is used to traverse VCs and do the following:
    // -- collect the set of FunctionCall nodes and label them with a unique string
    // -- Rename all other labels (so that calling this on the same VC results in 
    //    VCs with different labels each time)
    public class FCallHandler : MutatingVCExprVisitor<bool> {
      Dictionary<string/*!*/, StratifiedInliningInfo/*!*/>/*!*/ implName2StratifiedInliningInfo;
      public readonly Dictionary<int, Absy>/*!*/ mainLabel2absy;
      public Dictionary<BoogieCallExpr/*!*/, int>/*!*/ boogieExpr2Id;
      public Dictionary<BoogieCallExpr/*!*/, VCExpr>/*!*/ recordExpr2Var;
      public Dictionary<int, VCExprNAry/*!*/>/*!*/ id2Candidate;
      public Dictionary<int, VCExprVar/*!*/>/*!*/ id2ControlVar;
      public Dictionary<int, VCExpr> id2VC;
      public Dictionary<string/*!*/, int>/*!*/ label2Id;
      // Stores the candidate from which this one originated
      public Dictionary<int, int> candidateParent;
      // Mapping from candidate Id to the "si_unique_call" id that led to 
      // this candidate. This is useful for getting persistent names for
      // candidates
      public Dictionary<int, int> candidate2callId;
      // A cache for candidate id to its persistent name
      public Dictionary<int, string> persistentNameCache;
      // Inverse of the above map
      public Dictionary<string, int> persistentNameInv;
      // Used to record candidates recently added
      public HashSet<int> recentlyAddedCandidates;
      // Name of main procedure
      private string mainProcName;
      // A map from candidate id to the VCExpr that represents its
      // first argument (used for obtaining concrete values in error trace)
      public Dictionary<int, VCExpr> argExprMap;

      // map from candidate to summary candidates
      public Dictionary<int, List<Tuple<VCExprVar, VCExpr>>> summaryCandidates;
      private Dictionary<string, List<Tuple<VCExprVar, VCExpr>>> summaryTemp;
      // set of all boolean guards of summaries
      public HashSet<VCExprVar> allSummaryConst;

      public HashSet<int> forcedCandidates;

      // User info -- to decrease/increase calculation of recursion bound
      public Dictionary<int, int> recursionIncrement;
      public Dictionary<string, int> extraRecursion;

      public HashSet<int> currCandidates;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
        Contract.Invariant(mainLabel2absy != null);
        Contract.Invariant(boogieExpr2Id != null);
        Contract.Invariant(cce.NonNullDictionaryAndValues(id2Candidate));
        Contract.Invariant(cce.NonNullDictionaryAndValues(id2ControlVar));
        Contract.Invariant(label2Id != null);
      }

      // Name of the procedure whose VC we're mutating
      string currProc;

      // The 0^th candidate is main
      static int candidateCount = 1;
      public int currInlineCount;

      public Dictionary<int, Dictionary<VCExprVar, VCExpr>> id2Vars;

      public FCallHandler(VCExpressionGenerator/*!*/ gen,
                            Dictionary<string/*!*/, StratifiedInliningInfo/*!*/>/*!*/ implName2StratifiedInliningInfo,
                            string mainProcName, Dictionary<int, Absy>/*!*/ mainLabel2absy)
        : base(gen) {
        Contract.Requires(gen != null);
        Contract.Requires(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
        Contract.Requires(mainLabel2absy != null);
        this.implName2StratifiedInliningInfo = implName2StratifiedInliningInfo;
        this.mainProcName = mainProcName;
        this.mainLabel2absy = mainLabel2absy;
        id2Candidate = new Dictionary<int, VCExprNAry>();
        id2ControlVar = new Dictionary<int, VCExprVar>();
        boogieExpr2Id = new Dictionary<BoogieCallExpr, int>();
        label2Id = new Dictionary<string, int>();
        currCandidates = new HashSet<int>();
        currInlineCount = 0;
        currProc = null;
        labelRenamer = new Dictionary<string, int>();
        labelRenamerInv = new Dictionary<string, string>();
        candidateParent = new Dictionary<int, int>();
        //callGraphMapping = new Dictionary<int, int>();
        recursionIncrement = new Dictionary<int, int>();
        candidate2callId = new Dictionary<int, int>();
        persistentNameCache = new Dictionary<int, string>();
        persistentNameInv = new Dictionary<string, int>();
        persistentNameCache[0] = "0";
        persistentNameInv["0"] = 0;
        recentlyAddedCandidates = new HashSet<int>();
        argExprMap = new Dictionary<int, VCExpr>();
        recordExpr2Var = new Dictionary<BoogieCallExpr, VCExpr>();

        forcedCandidates = new HashSet<int>();
        extraRecursion = new Dictionary<string, int>();

        id2Vars = new Dictionary<int, Dictionary<VCExprVar, VCExpr>>();
        summaryCandidates = new Dictionary<int, List<Tuple<VCExprVar, VCExpr>>>();
        summaryTemp = new Dictionary<string, List<Tuple<VCExprVar, VCExpr>>>();
        allSummaryConst = new HashSet<VCExprVar>();
        id2VC = new Dictionary<int, VCExpr>();
      }

      public void Clear() {
        currCandidates = new HashSet<int>();
      }

      // Return the set of all candidates
      public HashSet<int> getAllCandidates() {
        var ret = new HashSet<int>(candidateParent.Keys);
        ret.Add(0);
        return ret;
      }

      // Given a candidate "id", let proc(id) be the
      // procedure corresponding to id. This procedure returns
      // the number of times proc(id) appears as an ancestor
      // of id. This is the same as the number of times we've
      // recursed on proc(id)
      public int getRecursionBound(int id) {
        int ret = 1;
        var str = getProc(id);

        while (candidateParent.ContainsKey(id)) {
          if (recursionIncrement.ContainsKey(id)) ret += recursionIncrement[id];
          id = candidateParent[id];
          if (getProc(id) == str && !forcedCandidates.Contains(id)) ret++;
        }

        // Usual
        if (!extraRecursion.ContainsKey(str))
            return ret;

        // Usual
        if (ret <= CommandLineOptions.Clo.RecursionBound - 1)
            return ret;

        // Special
        if (ret >= CommandLineOptions.Clo.RecursionBound &&
            ret <= CommandLineOptions.Clo.RecursionBound + extraRecursion[str] - 1)
            return CommandLineOptions.Clo.RecursionBound - 1;

        // Special
        return ret - extraRecursion[str];
      }

      // Set user-define increment/decrement to recursionBound
      public void setRecursionIncrement(int id, int incr) {
        if (recursionIncrement.ContainsKey(id))
          recursionIncrement[id] = incr;
        else
          recursionIncrement.Add(id, incr);
      }

      // Returns the name of the procedure corresponding to candidate id
      public string getProc(int id) {
        if (id == 0) return mainProcName;

        return (id2Candidate[id].Op as VCExprBoogieFunctionOp).Func.Name;
      }

      // Get a unique id for this candidate (dependent only on the Call
      // graph of the program). The persistent id is:
      // 0: for main
      // a_b_c: where a is the persistent id of parent, and b is the procedure name
      //        and c is the unique call id (if any)
      public string getPersistentId(int top_id) {
        if (top_id == 0) return "0";
        Debug.Assert(candidateParent.ContainsKey(top_id));
        if (persistentNameCache.ContainsKey(top_id))
          return persistentNameCache[top_id];

        var parent_id = getPersistentId(candidateParent[top_id]);
        var call_id = candidate2callId.ContainsKey(top_id) ? candidate2callId[top_id] : -1;
        var ret = string.Format("{0}_131_{1}_131_{2}", parent_id, getProc(top_id), call_id);
        persistentNameCache[top_id] = ret;
        persistentNameInv[ret] = top_id;
        return ret;
      }

      public int getCandidateFromGraphNode(string n) {
        if (!persistentNameInv.ContainsKey(n)) {
          return -1;
        }
        return persistentNameInv[n];
      }

      private int GetNewId(VCExprNAry vc) {
        Contract.Requires(vc != null);
        int id = candidateCount;

        id2Candidate[id] = vc;
        id2ControlVar[id] = Gen.Variable("si_control_var_bool_" + id.ToString(), Microsoft.Boogie.Type.Bool);

        candidateCount++;
        currCandidates.Add(id);
        recentlyAddedCandidates.Add(id);

        return id;
      }

      private string GetLabel(int id) {
        Contract.Ensures(Contract.Result<string>() != null);

        string ret = "si_fcall_" + id.ToString();
        if (!label2Id.ContainsKey(ret))
          label2Id[ret] = id;

        return ret;
      }

      public int GetId(string label) {
        Contract.Requires(label != null);
        if (!label2Id.ContainsKey(label))
          return -1;
        return label2Id[label];
      }

      Dictionary<string, int> labelRenamer;
      Dictionary<string, string> labelRenamerInv;

      public string RenameAbsyLabel(string label) {
        Contract.Requires(label != null);
        Contract.Requires(label.Length >= 1);
        Contract.Ensures(Contract.Result<string>() != null);

        // Remove the sign from the label
        string nosign = label.Substring(1);
        var ret = "si_inline_" + currInlineCount.ToString() + "_" + nosign;

        if (!labelRenamer.ContainsKey(ret)) {
          var c = labelRenamer.Count + 11; // two digit labels only
          labelRenamer.Add(ret, c);
          labelRenamerInv.Add(c.ToString(), ret);
        }
        return labelRenamer[ret].ToString();
      }

      public string ParseRenamedAbsyLabel(string label, int cnt) {
        Contract.Requires(label != null);
        if (!labelRenamerInv.ContainsKey(label)) {
          return null;
        }
        var str = labelRenamerInv[label];
        var prefix = "si_inline_" + cnt.ToString() + "_";
        if (!str.StartsWith(prefix)) return null;
        return str.Substring(prefix.Length);
      }

      public void setCurrProc(string name) {
        Contract.Requires(name != null);
        currProc = name;
        Contract.Assert(implName2StratifiedInliningInfo.ContainsKey(name));
      }

      public void setCurrProcAsMain() {
        currProc = "";
      }

      // Return the formula (candidate IFF false)
      public VCExpr getFalseExpr(int candidateId) {
        //return Gen.Eq(VCExpressionGenerator.False, id2ControlVar[candidateId]);
        return Gen.Not(id2ControlVar[candidateId]);
      }

      // Return the formula (candidate IFF true)
      public VCExpr getTrueExpr(int candidateId) {
        return Gen.Eq(VCExpressionGenerator.True, id2ControlVar[candidateId]);
      }

      public Dictionary<int, Absy> getLabel2absy() {
        Contract.Ensures(Contract.Result<Dictionary<int, Absy>>() != null);

        Contract.Assert(currProc != null);
        if (currProc == "") {
          return mainLabel2absy;
        }
        return cce.NonNull(implName2StratifiedInliningInfo[currProc].label2absy);
      }

      // Finds labels and changes them:
      //   si_fcall_id:  if "id" corresponds to a tracked procedure call, then
      //                 si_control_var_candidateId
      //   si_fcall_id:  if "id" does not corresponds to a tracked procedure call, then
      //                 delete
      //   num:          si_inline_num
      //  
      protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                                    List<VCExpr/*!*/>/*!*/ newSubExprs,
        // has any of the subexpressions changed?
                                                    bool changed,
                                                    bool arg) {
        //Contract.Requires(originalNode != null);
        //Contract.Requires(cce.NonNullElements(newSubExprs));
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        VCExpr ret;
        if (changed)
          ret = Gen.Function(originalNode.Op,
                             newSubExprs, originalNode.TypeArguments);
        else
          ret = originalNode;

        VCExprLabelOp lop = originalNode.Op as VCExprLabelOp;
        if (lop == null) return ret;
        if (!(ret is VCExprNAry)) return ret;

        VCExprNAry retnary = (VCExprNAry)ret;
        Contract.Assert(retnary != null);
        string prefix = "si_fcall_"; // from Wlp.ssc::Cmd(...)
        if (lop.label.Substring(1).StartsWith(prefix)) {
          int id = Int32.Parse(lop.label.Substring(prefix.Length + 1));
          Dictionary<int, Absy> label2absy = getLabel2absy();
          Absy cmd = label2absy[id] as Absy;
          //label2absy.Remove(id);

          Contract.Assert(cmd != null);
          AssumeCmd acmd = cmd as AssumeCmd;
          Contract.Assert(acmd != null);
          NAryExpr naryExpr = acmd.Expr as NAryExpr;
          Contract.Assert(naryExpr != null);

          string calleeName = naryExpr.Fun.FunctionName;

          VCExprNAry callExpr = retnary[0] as VCExprNAry;

          if (implName2StratifiedInliningInfo.ContainsKey(calleeName)) {
            Contract.Assert(callExpr != null);
            int candidateId = GetNewId(callExpr);
            boogieExpr2Id[new BoogieCallExpr(naryExpr, currInlineCount)] = candidateId;
            candidateParent[candidateId] = currInlineCount;
            string label = GetLabel(candidateId);
            var unique_call_id = QKeyValue.FindIntAttribute(acmd.Attributes, "si_unique_call", -1);
            if (unique_call_id != -1)
              candidate2callId[candidateId] = unique_call_id;

            //return Gen.LabelPos(label, callExpr);
            return Gen.LabelPos(label, id2ControlVar[candidateId]);
          }
          else if (calleeName.StartsWith(recordProcName)) {
            Contract.Assert(callExpr != null);
            Debug.Assert(callExpr.Length == 1);
            Debug.Assert(callExpr[0] != null);
            recordExpr2Var[new BoogieCallExpr(naryExpr, currInlineCount)] = callExpr[0];
            return callExpr;
          }
          else {
              // callExpr can be null; this happens when the FunctionCall was on a
              // pure function (not procedure) and the function got inlined
              return retnary[0];
          }
        }

        // summary candidate
        if (lop.label.Substring(1).StartsWith("candidate_")) {
          var pname = lop.label.Substring("candidate_".Length + 1);

          if (!summaryTemp.ContainsKey(pname))
            summaryTemp.Add(pname, new List<Tuple<VCExprVar, VCExpr>>());

          var expr = retnary[0] as VCExprNAry;
          if (expr == null) return retnary[0];
          if (expr.Op != VCExpressionGenerator.ImpliesOp) return retnary[0];
          var tup = Tuple.Create(expr[0] as VCExprVar, expr[1]);
          summaryTemp[pname].Add(tup);

          return retnary[0];
        }

        // Else, rename label
        string newLabel = RenameAbsyLabel(lop.label);
        if (lop.pos) {
          return Gen.LabelPos(newLabel, retnary[0]);
        }
        else {
          return Gen.LabelNeg(newLabel, retnary[0]);
        }

      }

      // Upgrades summaryTemp to summaryCandidates by matching ensure clauses with
      // the appropriate candidate they came from
      public void matchSummaries() {
        var id2Set = new Dictionary<string, List<Tuple<int, HashSet<VCExprVar>>>>();
        foreach (var id in recentlyAddedCandidates) {
          var collect = new CollectVCVars();
          var proc = getProc(id);
          if (!id2Set.ContainsKey(proc)) id2Set.Add(proc, new List<Tuple<int, HashSet<VCExprVar>>>());
          id2Set[proc].Add(Tuple.Create(id, collect.Collect(id2Candidate[id], true)));
        }

        foreach (var kvp in summaryTemp) {
          Contract.Assert(id2Set.ContainsKey(kvp.Key));
          var ls = id2Set[kvp.Key];
          foreach (var tup in kvp.Value) {
            var collect = new CollectVCVars();
            var s1 = collect.Collect(tup.Item2, true);
            var found = false;
            foreach (var t in ls) {
              var s2 = t.Item2;
              if (s1.IsSubsetOf(s2)) {
                if (!summaryCandidates.ContainsKey(t.Item1))
                  summaryCandidates.Add(t.Item1, new List<Tuple<VCExprVar, VCExpr>>());
                summaryCandidates[t.Item1].Add(tup);
                allSummaryConst.Add(tup.Item1);
                found = true;
                break;
              }
            }
            Contract.Assert(found);
          }
        }
        summaryTemp.Clear();
      }

      public IEnumerable<int> getInlinedCandidates() {
        return candidateParent.Keys.Except(currCandidates).Union(new int[] { 0 });
      }

    } // end FCallHandler

    // Collects the set of all VCExprVar in a given VCExpr
    class CollectVCVars : CollectingVCExprVisitor<HashSet<VCExprVar>, bool> {
      public override HashSet<VCExprVar> Visit(VCExprVar node, bool arg) {
        var ret = new HashSet<VCExprVar>();
        ret.Add(node);
        return ret;
      }

      protected override HashSet<VCExprVar> CombineResults(List<HashSet<VCExprVar>> results, bool arg) {
        var ret = new HashSet<VCExprVar>();
        results.ForEach(s => ret.UnionWith(s));
        return ret;
      }
    }

    public class FCallInliner : MutatingVCExprVisitor<bool> {
      public Dictionary<int, VCExpr/*!*/>/*!*/ subst;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullDictionaryAndValues(subst));
      }


      public FCallInliner(VCExpressionGenerator gen)
        : base(gen) {
        Contract.Requires(gen != null);
        subst = new Dictionary<int, VCExpr>();
      }

      public void Clear() {
        subst = new Dictionary<int, VCExpr>();
      }

      protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                                    List<VCExpr/*!*/>/*!*/ newSubExprs,
        // has any of the subexpressions changed?
                                                    bool changed,
                                                    bool arg) {
        //Contract.Requires(originalNode != null);Contract.Requires(newSubExprs != null);
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        VCExpr ret;
        if (changed)
          ret = Gen.Function(originalNode.Op, newSubExprs, originalNode.TypeArguments);
        else
          ret = originalNode;

        VCExprLabelOp lop = originalNode.Op as VCExprLabelOp;
        if (lop == null) return ret;
        if (!(ret is VCExprNAry)) return ret;

        string prefix = "si_fcall_"; // from FCallHandler::GetLabel
        if (lop.label.Substring(1).StartsWith(prefix)) {
          int id = Int32.Parse(lop.label.Substring(prefix.Length + 1));
          if (subst.ContainsKey(id)) {
            return subst[id];
          }
        }
        return ret;
      }

    } // end FCallInliner

    public class EmptyErrorHandler : ProverInterface.ErrorHandler {
      public override void OnModel(IList<string> labels, Model model) {

      }
    }

    public class StratifiedInliningErrorReporter : ProverInterface.ErrorHandler {
      Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo;
      ProverInterface theoremProver;
      VerifierCallback callback;
      FCallHandler calls;
      StratifiedInliningInfo mainInfo;
      StratifiedVC mainVC;

      public bool underapproximationMode;
      public List<int> candidatesToExpand;
      public List<StratifiedCallSite> callSitesToExpand;

      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(candidatesToExpand != null);
        Contract.Invariant(mainInfo != null);
        Contract.Invariant(callback != null);
        Contract.Invariant(theoremProver != null);
        Contract.Invariant(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
      }


      public StratifiedInliningErrorReporter(Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo,
                                             ProverInterface theoremProver, VerifierCallback callback,
                                             StratifiedInliningInfo mainInfo) {
        Contract.Requires(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
        Contract.Requires(theoremProver != null);
        Contract.Requires(callback != null);
        Contract.Requires(mainInfo != null);
        this.implName2StratifiedInliningInfo = implName2StratifiedInliningInfo;
        this.theoremProver = theoremProver;
        this.callback = callback;
        this.mainInfo = mainInfo;
        this.underapproximationMode = false;
        this.calls = null;
        this.candidatesToExpand = new List<int>();
      }

      public StratifiedInliningErrorReporter(Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo,
                                             ProverInterface theoremProver, VerifierCallback callback,
                                             StratifiedVC mainVC) {
        Contract.Requires(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
        Contract.Requires(theoremProver != null);
        Contract.Requires(callback != null);
        Contract.Requires(mainVC != null);
        this.implName2StratifiedInliningInfo = implName2StratifiedInliningInfo;
        this.theoremProver = theoremProver;
        this.callback = callback;
        this.mainVC = mainVC;
        this.underapproximationMode = false;
        this.candidatesToExpand = new List<int>();
      }

      public void SetCandidateHandler(FCallHandler calls) {
        Contract.Requires(calls != null);
        this.calls = calls;
      }

      List<Tuple<int, int>> orderedStateIds;

      private Model.Element GetModelValue(Model m, Variable v, int candidateId) {
        // first, get the unique name
        string uniqueName;

        VCExprVar vvar = theoremProver.Context.BoogieExprTranslator.TryLookupVariable(v);
        if (vvar == null) {
          uniqueName = v.Name;
        }
        else {
          if (candidateId != 0) {
            Dictionary<VCExprVar, VCExpr> mapping = calls.id2Vars[candidateId];
            if (mapping.ContainsKey(vvar)) {
              VCExpr e = mapping[vvar];
              if (e is VCExprLiteral) {
                VCExprLiteral lit = (VCExprLiteral)e;
                return m.MkElement(lit.ToString());
              }
              vvar = (VCExprVar)mapping[vvar];
            }
          }
          uniqueName = theoremProver.Context.Lookup(vvar);
        }

        var f = m.TryGetFunc(uniqueName);
        if (f == null)
          return m.MkFunc("@undefined", 0).GetConstant();
        return f.GetConstant();
      }

      public readonly static int CALL = -1;
      public readonly static int RETURN = -2;

      public void PrintModel(Model model) {
        var filename = CommandLineOptions.Clo.ModelViewFile;
        if (model == null || filename == null) return;

        if (filename == "-") {
          model.Write(Console.Out);
          Console.Out.Flush();
        }
        else {
          using (var wr = new StreamWriter(filename, !Counterexample.firstModelFile)) {
            Counterexample.firstModelFile = false;
            model.Write(wr);
          }
        }
      }

      private void GetModelWithStates(Model m) {
        if (m == null) return;
        var mvInfo = mainInfo.mvInfo;
        var mvstates = m.TryGetFunc("$mv_state");
        if (mvstates == null)
          return;

        Contract.Assert(mvstates.Arity == 2);

        foreach (Variable v in mvInfo.AllVariables) {
          m.InitialState.AddBinding(v.Name, GetModelValue(m, v, 0));
        }

        int lastCandidate = 0;
        int lastCapturePoint = CALL;
        for (int i = 0; i < this.orderedStateIds.Count; ++i) {
          var s = orderedStateIds[i];
          int candidate = s.Item1;
          int capturePoint = s.Item2;
          string implName = calls.getProc(candidate);
          ModelViewInfo info = candidate == 0 ? mvInfo : implName2StratifiedInliningInfo[implName].mvInfo;

          if (capturePoint == CALL || capturePoint == RETURN) {
            lastCandidate = candidate;
            lastCapturePoint = capturePoint;
            continue;
          }

          Contract.Assume(0 <= capturePoint && capturePoint < info.CapturePoints.Count);
          VC.ModelViewInfo.Mapping map = info.CapturePoints[capturePoint];
          var prevInc = (lastCapturePoint != CALL && lastCapturePoint != RETURN && candidate == lastCandidate)
            ? info.CapturePoints[lastCapturePoint].IncarnationMap : new Dictionary<Variable, Expr>();
          var cs = m.MkState(map.Description);

          foreach (Variable v in info.AllVariables) {
            var e = (Expr)map.IncarnationMap[v];

            if (e == null) {
              if (lastCapturePoint == CALL || lastCapturePoint == RETURN) {
                cs.AddBinding(v.Name, GetModelValue(m, v, candidate));
              }
              continue;
            }

            if (lastCapturePoint != CALL && lastCapturePoint != RETURN && prevInc[v] == e) continue; // skip unchanged variables

            Model.Element elt;
            if (e is IdentifierExpr) {
              IdentifierExpr ide = (IdentifierExpr)e;
              elt = GetModelValue(m, ide.Decl, candidate);
            }
            else if (e is LiteralExpr) {
              LiteralExpr lit = (LiteralExpr)e;
              elt = m.MkElement(lit.Val.ToString());
            }
            else {
              Contract.Assume(false);
              elt = m.MkFunc(e.ToString(), 0).GetConstant();
            }
            cs.AddBinding(v.Name, elt);
          }

          lastCandidate = candidate;
          lastCapturePoint = capturePoint;
        }

        return;
      }

      public override void OnModel(IList<string/*!*/>/*!*/ labels, Model model) {
        Contract.Assert(CommandLineOptions.Clo.StratifiedInliningWithoutModels || model != null);

        if (CommandLineOptions.Clo.PrintErrorModel >= 1 && model != null) {
          model.Write(ErrorReporter.ModelWriter);
          ErrorReporter.ModelWriter.Flush();
        }

        candidatesToExpand = new List<int>();
        orderedStateIds = new List<Tuple<int, int>>();
        var cex = GenerateTrace(labels, model, 0, mainInfo.impl, mainInfo.mvInfo);

        if (underapproximationMode && cex != null) {
          //Debug.Assert(candidatesToExpand.All(calls.isSkipped));
          GetModelWithStates(model);
          callback.OnCounterexample(cex, null);
          this.PrintModel(model);
        }
      }

      private Counterexample GenerateTrace(IList<string/*!*/>/*!*/ labels, Model/*!*/ errModel,
                                           int candidateId, Implementation procImpl, ModelViewInfo mvInfo) {
        Contract.Requires(cce.NonNullElements(labels));
        Contract.Requires(procImpl != null);

        Hashtable traceNodes = new Hashtable();

        foreach (string s in labels) {
          Contract.Assert(s != null);
          var absylabel = calls.ParseRenamedAbsyLabel(s, candidateId);

          if (absylabel == null) continue;

          Absy absy;

          if (candidateId == 0) {
            absy = Label2Absy(absylabel);
          }
          else {
            absy = Label2Absy(procImpl.Name, absylabel);
          }

          if (traceNodes.ContainsKey(absy))
            System.Console.WriteLine("Warning: duplicate label: " + s + " read while tracing nodes");
          else
            traceNodes.Add(absy, null);
        }

        List<Block> trace = new List<Block>();
        Block entryBlock = cce.NonNull(procImpl.Blocks[0]);
        Contract.Assert(entryBlock != null);
        Contract.Assert(traceNodes.Contains(entryBlock));
        trace.Add(entryBlock);

        var calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
        Counterexample newCounterexample = GenerateTraceRec(labels, errModel, mvInfo, candidateId, entryBlock, traceNodes, trace, calleeCounterexamples);

        return newCounterexample;
      }

      private Counterexample GenerateTraceRec(
                            IList<string/*!*/>/*!*/ labels, Model/*!*/ errModel, ModelViewInfo mvInfo,
                            int candidateId,
                            Block/*!*/ b, Hashtable/*!*/ traceNodes, List<Block>/*!*/ trace,
                            Dictionary<TraceLocation/*!*/, CalleeCounterexampleInfo/*!*/>/*!*/ calleeCounterexamples) {
        Contract.Requires(cce.NonNullElements(labels));
        Contract.Requires(b != null);
        Contract.Requires(traceNodes != null);
        Contract.Requires(trace != null);
        Contract.Requires(cce.NonNullDictionaryAndValues(calleeCounterexamples));
        // After translation, all potential errors come from asserts.
        while (true) {
          List<Cmd> cmds = b.Cmds;
          TransferCmd transferCmd = cce.NonNull(b.TransferCmd);
          for (int i = 0; i < cmds.Count; i++) {
            Cmd cmd = cce.NonNull(cmds[i]);

            // Skip if 'cmd' not contained in the trace or not an assert
            if (cmd is AssertCmd && traceNodes.Contains(cmd)) {
              Counterexample newCounterexample = AssertCmdToCounterexample((AssertCmd)cmd, transferCmd, trace, errModel, mvInfo, theoremProver.Context);
              newCounterexample.AddCalleeCounterexample(calleeCounterexamples);
              return newCounterexample;
            }

            // Counterexample generation for inlined procedures
            AssumeCmd assumeCmd = cmd as AssumeCmd;
            if (assumeCmd == null)
              continue;
            NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
            if (naryExpr == null)
              continue;
            string calleeName = naryExpr.Fun.FunctionName;
            Contract.Assert(calleeName != null);

            BinaryOperator binOp = naryExpr.Fun as BinaryOperator;
            if (binOp != null && binOp.Op == BinaryOperator.Opcode.And) {
              Expr expr = naryExpr.Args[0];
              NAryExpr mvStateExpr = expr as NAryExpr;
              if (mvStateExpr != null && mvStateExpr.Fun.FunctionName == ModelViewInfo.MVState_FunctionDef.Name) {
                LiteralExpr x = mvStateExpr.Args[1] as LiteralExpr;
                orderedStateIds.Add(new Tuple<int, int>(candidateId, x.asBigNum.ToInt));
              }
            }

            if (calleeName.StartsWith(recordProcName) && (errModel != null || CommandLineOptions.Clo.UseProverEvaluate)) {
              var expr = calls.recordExpr2Var[new BoogieCallExpr(naryExpr, candidateId)];

              // Record concrete value of the argument to this procedure
              var args = new List<object>();
              if (errModel == null && CommandLineOptions.Clo.UseProverEvaluate)
              {
                  object exprv;
                  try
                  {
                      exprv = theoremProver.Evaluate(expr);
                  }
                  catch (Exception)
                  {
                      exprv = null;
                  }
                  args.Add(exprv);
              }
              else
              {
                  if (expr is VCExprIntLit)
                  {
                      args.Add(errModel.MkElement((expr as VCExprIntLit).Val.ToString()));
                  }
                  else if (expr == VCExpressionGenerator.True)
                  {
                      args.Add(errModel.MkElement("true"));
                  }
                  else if (expr == VCExpressionGenerator.False)
                  {
                      args.Add(errModel.MkElement("false"));
                  }
                  else if (expr is VCExprVar)
                  {
                      var idExpr = expr as VCExprVar;
                      string name = theoremProver.Context.Lookup(idExpr);
                      Contract.Assert(name != null);
                      Model.Func f = errModel.TryGetFunc(name);
                      if (f != null)
                      {
                          args.Add(f.GetConstant());
                      }
                  }
                  else
                  {
                      Contract.Assert(false);
                  }
              }
              calleeCounterexamples[new TraceLocation(trace.Count - 1, i)] =
                   new CalleeCounterexampleInfo(null, args);
              continue;
            }

            if (!implName2StratifiedInliningInfo.ContainsKey(calleeName))
              continue;

            Contract.Assert(calls != null);

            int calleeId = calls.boogieExpr2Id[new BoogieCallExpr(naryExpr, candidateId)];

            if (calls.currCandidates.Contains(calleeId)) {
              candidatesToExpand.Add(calleeId);
            }
            else {
              orderedStateIds.Add(new Tuple<int, int>(calleeId, StratifiedInliningErrorReporter.CALL));
              var calleeInfo = implName2StratifiedInliningInfo[calleeName];
              calleeCounterexamples[new TraceLocation(trace.Count - 1, i)] =
                  new CalleeCounterexampleInfo(GenerateTrace(labels, errModel, calleeId, calleeInfo.impl, calleeInfo.mvInfo), new List<object>());
              orderedStateIds.Add(new Tuple<int, int>(candidateId, StratifiedInliningErrorReporter.RETURN));
            }
          }

          GotoCmd gotoCmd = transferCmd as GotoCmd;
          if (gotoCmd != null) {
            b = null;
            foreach (Block bb in cce.NonNull(gotoCmd.labelTargets)) {
              Contract.Assert(bb != null);
              if (traceNodes.Contains(bb)) {
                trace.Add(bb);
                b = bb;
                break;
              }
            }
            if (b != null) continue;
          }
          return null;
        }
      }

      public override Absy Label2Absy(string label) {
        //Contract.Requires(label != null);
        Contract.Ensures(Contract.Result<Absy>() != null);

        int id = int.Parse(label);
        Contract.Assert(calls != null);
        return cce.NonNull((Absy)calls.mainLabel2absy[id]);
      }

      public Absy Label2Absy(string procName, string label) {
        Contract.Requires(label != null);
        Contract.Requires(procName != null);
        Contract.Ensures(Contract.Result<Absy>() != null);

        int id = int.Parse(label);
        Dictionary<int, Absy> l2a = cce.NonNull(implName2StratifiedInliningInfo[procName]).label2absy;
        return cce.NonNull((Absy)l2a[id]);
      }

      public override void OnResourceExceeded(string msg) {
        //Contract.Requires(msg != null);
        //resourceExceededMessage = msg;
      }

      public override void OnProverWarning(string msg) {
        //Contract.Requires(msg != null);
        callback.OnWarning(msg);
      }
    }

  } // class StratifiedVCGen

} // namespace VC
