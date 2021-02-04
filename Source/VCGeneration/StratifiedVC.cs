using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
  using Bpl = Microsoft.Boogie;

  public class StratifiedVC
  {
    public StratifiedInliningInfo info;
    public int id;
    public List<VCExprVar> interfaceExprVars;

    // boolControlVC (block -> its bool variable)
    public Dictionary<Block, VCExpr> blockToControlVar;

    public Dictionary<Block, List<StratifiedCallSite>> callSites;
    public Dictionary<Block, List<StratifiedCallSite>> recordProcCallSites;
    public VCExpr vcexpr;

    // Must-Reach Information
    Dictionary<Block, VCExprVar> mustReachVar;
    List<VCExprLetBinding> mustReachBindings;

    public StratifiedVC(StratifiedInliningInfo siInfo, HashSet<string> procCalls)
    {
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
      foreach (VCExprVar v in info.interfaceExprVars)
      {
        VCExprVar newVar = vcgen.CreateNewVar(v.Type);
        interfaceExprVars.Add(newVar);
        substDict.Add(v, newVar);
      }

      foreach (VCExprVar v in info.privateExprVars)
      {
        substDict.Add(v, vcgen.CreateNewVar(v.Type));
      }

      if (info.controlFlowVariable != null)
        substDict.Add(bet.LookupVariable(info.controlFlowVariable), gen.Integer(BigNum.FromInt(id)));
      VCExprSubstitution subst =
        new VCExprSubstitution(substDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
      SubstitutingVCExprVisitor substVisitor = new SubstitutingVCExprVisitor(prover.VCExprGen);
      vcexpr = substVisitor.Mutate(vcexpr, subst);

      // For BoolControlVC generation
      if (info.blockToControlVar != null)
      {
        blockToControlVar = new Dictionary<Block, VCExpr>();
        foreach (var tup in info.blockToControlVar)
          blockToControlVar.Add(tup.Key, substDict[tup.Value]);
      }

      if (procCalls != null)
        vcexpr = RemoveProcedureCalls.Apply(vcexpr, info.vcgen.prover.VCExprGen, procCalls);

      callSites = new Dictionary<Block, List<StratifiedCallSite>>();
      foreach (Block b in info.callSites.Keys)
      {
        callSites[b] = new List<StratifiedCallSite>();
        foreach (CallSite cs in info.callSites[b])
        {
          callSites[b].Add(new StratifiedCallSite(cs, substVisitor, subst));
        }
      }

      recordProcCallSites = new Dictionary<Block, List<StratifiedCallSite>>();
      foreach (Block b in info.recordProcCallSites.Keys)
      {
        recordProcCallSites[b] = new List<StratifiedCallSite>();
        foreach (CallSite cs in info.recordProcCallSites[b])
        {
          recordProcCallSites[b].Add(new StratifiedCallSite(cs, substVisitor, subst));
        }
      }
    }

    public VCExpr MustReach(Block block)
    {
      // This information is computed lazily
      if (mustReachBindings == null)
      {
        var vcgen = info.vcgen;
        var gen = vcgen.prover.VCExprGen;
        var impl = info.impl;
        mustReachVar = new Dictionary<Block, VCExprVar>();
        mustReachBindings = new List<VCExprLetBinding>();
        foreach (Block b in impl.Blocks)
          mustReachVar[b] = vcgen.CreateNewVar(Bpl.Type.Bool);

        var dag = new Graph<Block>();
        dag.AddSource(impl.Blocks[0]);
        foreach (Block b in impl.Blocks)
        {
          var gtc = b.TransferCmd as GotoCmd;
          if (gtc != null)
            foreach (Block dest in gtc.labelTargets)
              dag.AddEdge(dest, b);
        }

        IEnumerable sortedNodes = dag.TopologicalSort();

        foreach (Block currBlock in dag.TopologicalSort())
        {
          if (currBlock == impl.Blocks[0])
          {
            mustReachBindings.Add(gen.LetBinding(mustReachVar[currBlock], VCExpressionGenerator.True));
            continue;
          }

          VCExpr expr = VCExpressionGenerator.False;
          foreach (var pred in dag.Successors(currBlock))
          {
            VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(gen.Integer(BigNum.FromInt(id)),
              gen.Integer(BigNum.FromInt(pred.UniqueId)));
            VCExpr controlTransferExpr =
              gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(currBlock.UniqueId)));
            expr = gen.Or(expr, gen.And(mustReachVar[pred], controlTransferExpr));
          }

          mustReachBindings.Add(gen.LetBinding(mustReachVar[currBlock], expr));
        }
      }

      Contract.Assert(mustReachVar.ContainsKey(block));
      return info.vcgen.prover.VCExprGen.Let(mustReachBindings, mustReachVar[block]);
    }

    public List<StratifiedCallSite> CallSites
    {
      get
      {
        var ret = new List<StratifiedCallSite>();
        foreach (var b in callSites.Keys)
        {
          foreach (var cs in callSites[b])
          {
            ret.Add(cs);
          }
        }

        return ret;
      }
    }

    public List<StratifiedCallSite> RecordProcCallSites
    {
      get
      {
        var ret = new List<StratifiedCallSite>();
        foreach (var b in recordProcCallSites.Keys)
        {
          foreach (var cs in recordProcCallSites[b])
          {
            ret.Add(cs);
          }
        }

        return ret;
      }
    }

    public override string ToString()
    {
      return info.impl.Name;
    }
  }

  // Remove the uninterpreted function calls that substitute procedure calls
  class RemoveProcedureCalls : MutatingVCExprVisitor<bool>
  {
    HashSet<string> procNames;

    RemoveProcedureCalls(VCExpressionGenerator gen, HashSet<string> procNames)
      : base(gen)
    {
      this.procNames = procNames;
    }

    public static VCExpr Apply(VCExpr expr, VCExpressionGenerator gen, HashSet<string> procNames)
    {
      return (new RemoveProcedureCalls(gen, procNames)).Mutate(expr, true);
    }

    // Finds labels and changes them to a globally unique label:
    protected override VCExpr /*!*/ UpdateModifiedNode(VCExprNAry /*!*/ originalNode,
      List<VCExpr /*!*/> /*!*/ newSubExprs,
      bool changed,
      bool arg)
    {
      //Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExpr ret;
      if (changed)
        ret = Gen.Function(originalNode.Op,
          newSubExprs, originalNode.TypeArguments);
      else
        ret = originalNode;

      if (!(ret is VCExprNAry)) return ret;
      VCExprNAry retnary = (VCExprNAry) ret;
      if (!(retnary.Op is VCExprBoogieFunctionOp))
        return ret;

      var fcall = (retnary.Op as VCExprBoogieFunctionOp).Func.Name;
      if (procNames.Contains(fcall))
        return VCExpressionGenerator.True;
      return ret;
    }
  }


  public class CallSite
  {
    public string calleeName;
    public List<VCExpr> interfaceExprs;
    public Block block;
    public int numInstr; // for TraceLocation
    public VCExprVar callSiteVar;
    public QKeyValue Attributes; // attributes on the call cmd

    public CallSite(string callee, List<VCExpr> interfaceExprs, VCExprVar callSiteVar, Block block, int numInstr,
      QKeyValue Attributes)
    {
      this.calleeName = callee;
      this.interfaceExprs = interfaceExprs;
      this.callSiteVar = callSiteVar;
      this.block = block;
      this.numInstr = numInstr;
      this.Attributes = Attributes;
    }
  }

  public class StratifiedCallSite
  {
    public CallSite callSite;
    public List<VCExpr> interfaceExprs;
    public VCExpr callSiteExpr;

    public StratifiedCallSite(CallSite cs, SubstitutingVCExprVisitor substVisitor, VCExprSubstitution subst)
    {
      callSite = cs;
      interfaceExprs = new List<VCExpr>();
      foreach (VCExpr v in cs.interfaceExprs)
      {
        interfaceExprs.Add(substVisitor.Mutate(v, subst));
      }

      if (callSite.callSiteVar != null)
        callSiteExpr = substVisitor.Mutate(callSite.callSiteVar, subst);
    }

    public VCExpr Attach(StratifiedVC svc)
    {
      Contract.Assert(interfaceExprs.Count == svc.interfaceExprVars.Count);
      StratifiedInliningInfo info = svc.info;
      ProverInterface prover = info.vcgen.prover;
      VCExpressionGenerator gen = prover.VCExprGen;

      Dictionary<VCExprVar, VCExpr> substDict = new Dictionary<VCExprVar, VCExpr>();
      for (int i = 0; i < svc.interfaceExprVars.Count; i++)
      {
        VCExprVar v = svc.interfaceExprVars[i];
        substDict.Add(v, interfaceExprs[i]);
      }

      VCExprSubstitution subst =
        new VCExprSubstitution(substDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
      SubstitutingVCExprVisitor substVisitor = new SubstitutingVCExprVisitor(prover.VCExprGen);
      svc.vcexpr = substVisitor.Mutate(svc.vcexpr, subst);
      foreach (StratifiedCallSite scs in svc.CallSites)
      {
        List<VCExpr> newInterfaceExprs = new List<VCExpr>();
        foreach (VCExpr expr in scs.interfaceExprs)
        {
          newInterfaceExprs.Add(substVisitor.Mutate(expr, subst));
        }

        scs.interfaceExprs = newInterfaceExprs;
      }

      foreach (StratifiedCallSite scs in svc.RecordProcCallSites)
      {
        List<VCExpr> newInterfaceExprs = new List<VCExpr>();
        foreach (VCExpr expr in scs.interfaceExprs)
        {
          newInterfaceExprs.Add(substVisitor.Mutate(expr, subst));
        }

        scs.interfaceExprs = newInterfaceExprs;
      }

      //return gen.Implies(callSiteExpr, svc.vcexpr);
      return svc.vcexpr;
    }

    public override string ToString()
    {
      return callSite.calleeName;
    }
  }

  public class StratifiedInliningInfo
  {
    public StratifiedVCGenBase vcgen;
    public Implementation impl;
    public Function function;
    public Variable controlFlowVariable;
    public Cmd exitAssertCmd;
    public VCExpr vcexpr;
    public List<VCExprVar> interfaceExprVars;
    public List<VCExprVar> privateExprVars;
    public Dictionary<int, Absy> label2absy;
    public ModelViewInfo mvInfo;
    public Dictionary<Block, List<CallSite>> callSites;
    public Dictionary<Block, List<CallSite>> recordProcCallSites;

    public bool initialized { get; private set; }

    // Instrumentation to apply after PassiveImpl, but before VCGen
    Action<Implementation> PassiveImplInstrumentation;

    // boolControlVC (block -> its Bool variable)
    public Dictionary<Block, VCExprVar> blockToControlVar;

    public StratifiedInliningInfo(Implementation implementation, StratifiedVCGenBase stratifiedVcGen,
      Action<Implementation> PassiveImplInstrumentation)
    {
      vcgen = stratifiedVcGen;
      impl = implementation;
      this.PassiveImplInstrumentation = PassiveImplInstrumentation;

      List<Variable> functionInterfaceVars = new List<Variable>();
      foreach (Variable v in vcgen.program.GlobalVariables)
      {
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type),
          true));
      }

      foreach (Variable v in impl.InParams)
      {
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type),
          true));
      }

      foreach (Variable v in impl.OutParams)
      {
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type),
          true));
      }

      foreach (IdentifierExpr e in impl.Proc.Modifies)
      {
        if (e.Decl == null) continue;
        functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", e.Decl.TypedIdent.Type),
          true));
      }

      Formal returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false);
      function = new Function(Token.NoToken, impl.Name, functionInterfaceVars, returnVar);
      vcgen.prover.Context.DeclareFunction(function, "");

      List<Expr> exprs = new List<Expr>();
      foreach (Variable v in vcgen.program.GlobalVariables)
      {
        Contract.Assert(v != null);
        exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
      }

      foreach (Variable v in impl.Proc.InParams)
      {
        Contract.Assert(v != null);
        exprs.Add(new IdentifierExpr(Token.NoToken, v));
      }

      foreach (Variable v in impl.Proc.OutParams)
      {
        Contract.Assert(v != null);
        exprs.Add(new IdentifierExpr(Token.NoToken, v));
      }

      foreach (IdentifierExpr ie in impl.Proc.Modifies)
      {
        Contract.Assert(ie != null);
        if (ie.Decl == null)
          continue;
        exprs.Add(ie);
      }

      Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(function), exprs);
      impl.Proc.Ensures.Add(new Ensures(Token.NoToken, true, freePostExpr, "",
        new QKeyValue(Token.NoToken, "si_fcall", new List<object>(), null)));

      initialized = false;
    }

    public void GenerateVCBoolControl()
    {
      Debug.Assert(!initialized);
      Debug.Assert(CommandLineOptions.Clo.SIBoolControlVC);

      // fix names for exit variables
      var outputVariables = new List<Variable>();
      var assertConjuncts = new List<Expr>();
      foreach (Variable v in impl.OutParams)
      {
        Constant c = new Constant(Token.NoToken,
          new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
        outputVariables.Add(c);
        Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
        assertConjuncts.Add(eqExpr);
      }

      foreach (IdentifierExpr e in impl.Proc.Modifies)
      {
        if (e.Decl == null) continue;
        Variable v = e.Decl;
        Constant c = new Constant(Token.NoToken,
          new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
        outputVariables.Add(c);
        Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
        assertConjuncts.Add(eqExpr);
      }

      exitAssertCmd = new AssumeCmd(Token.NoToken, Expr.BinaryTreeAnd(assertConjuncts));
      (exitAssertCmd as AssumeCmd).Attributes = new QKeyValue(Token.NoToken, "exitAssert", new List<object>(), null);

      // no need for label2absy
      label2absy = new Dictionary<int, Absy>();

      // Passify
      Program program = vcgen.program;
      ProverInterface proverInterface = vcgen.prover;
      vcgen.ConvertCFG2DAG(impl);
      vcgen.PassifyImpl(impl, out mvInfo);

      VCExpressionGenerator gen = proverInterface.VCExprGen;
      var exprGen = proverInterface.Context.ExprGen;
      var translator = proverInterface.Context.BoogieExprTranslator;

      // add a boolean variable at each call site
      vcgen.InstrumentCallSites(impl);

      // typecheck
      var tc = new TypecheckingContext(null);
      impl.Typecheck(tc);

      ///////////////////
      // Generate the VC
      ///////////////////

      // block -> bool variable
      blockToControlVar = new Dictionary<Block, VCExprVar>();
      foreach (var b in impl.Blocks)
        blockToControlVar.Add(b, gen.Variable(b.Label + "_holds", Bpl.Type.Bool));

      vcexpr = VCExpressionGenerator.True;
      foreach (var b in impl.Blocks)
      {
        // conjoin all assume cmds
        VCExpr c = VCExpressionGenerator.True;
        foreach (var cmd in b.Cmds)
        {
          var acmd = cmd as AssumeCmd;
          if (acmd == null)
          {
            Debug.Assert(cmd is AssertCmd && (cmd as AssertCmd).Expr is LiteralExpr &&
                         ((cmd as AssertCmd).Expr as LiteralExpr).IsTrue);
            continue;
          }

          var expr = translator.Translate(acmd.Expr);
          c = gen.AndSimp(c, expr);
        }

        // block implies a disjunction of successors
        Debug.Assert(!(b.TransferCmd is ReturnExprCmd), "Not supported");
        var gc = b.TransferCmd as GotoCmd;
        if (gc != null)
        {
          VCExpr succ = VCExpressionGenerator.False;
          foreach (var sb in gc.labelTargets)
            succ = gen.OrSimp(succ, blockToControlVar[sb]);
          c = gen.AndSimp(c, succ);
        }
        else
        {
          // nothing to do
        }

        vcexpr = gen.AndSimp(vcexpr, gen.Eq(blockToControlVar[b], c));
      }

      // assert start block
      vcexpr = gen.AndSimp(vcexpr, blockToControlVar[impl.Blocks[0]]);

      //Console.WriteLine("VC of {0}: {1}", impl.Name, vcexpr);
      // Collect other information
      callSites = vcgen.CollectCallSites(impl);
      recordProcCallSites = vcgen.CollectRecordProcedureCallSites(impl);

      // record interface variables
      privateExprVars = new List<VCExprVar>();
      foreach (Variable v in impl.LocVars)
      {
        privateExprVars.Add(translator.LookupVariable(v));
      }

      foreach (Variable v in impl.OutParams)
      {
        privateExprVars.Add(translator.LookupVariable(v));
      }

      privateExprVars.AddRange(blockToControlVar.Values);

      interfaceExprVars = new List<VCExprVar>();
      foreach (Variable v in program.GlobalVariables)
      {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }

      foreach (Variable v in impl.InParams)
      {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }

      foreach (Variable v in outputVariables)
      {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }
    }

    public void GenerateVC()
    {
      if (initialized) return;
      if (CommandLineOptions.Clo.SIBoolControlVC)
      {
        GenerateVCBoolControl();
        initialized = true;
        return;
      }

      List<Variable> outputVariables = new List<Variable>();
      List<Expr> assertConjuncts = new List<Expr>();
      foreach (Variable v in impl.OutParams)
      {
        Constant c = new Constant(Token.NoToken,
          new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
        outputVariables.Add(c);
        Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
        assertConjuncts.Add(eqExpr);
      }

      foreach (IdentifierExpr e in impl.Proc.Modifies)
      {
        if (e.Decl == null) continue;
        Variable v = e.Decl;
        Constant c = new Constant(Token.NoToken,
          new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
        outputVariables.Add(c);
        Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
        assertConjuncts.Add(eqExpr);
      }

      exitAssertCmd = new AssertCmd(Token.NoToken, Expr.Not(Expr.BinaryTreeAnd(assertConjuncts)));

      Program program = vcgen.program;
      ProverInterface proverInterface = vcgen.prover;
      vcgen.ConvertCFG2DAG(impl);
      vcgen.PassifyImpl(impl, out mvInfo);

      VCExpressionGenerator gen = proverInterface.VCExprGen;
      var exprGen = proverInterface.Context.ExprGen;
      var translator = proverInterface.Context.BoogieExprTranslator;

      controlFlowVariable =
        new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "@cfc", Microsoft.Boogie.Type.Int));
      VCExpr controlFlowVariableExpr = translator.LookupVariable(controlFlowVariable);

      vcgen.InstrumentCallSites(impl);

      if (PassiveImplInstrumentation != null)
        PassiveImplInstrumentation(impl);

      label2absy = new Dictionary<int, Absy>();
      VCGen.CodeExprConversionClosure cc = new VCGen.CodeExprConversionClosure(label2absy, proverInterface.Context);
      translator.SetCodeExprConverter(cc.CodeExprToVerificationCondition);
      vcexpr = gen.Not(vcgen.GenerateVCAux(impl, controlFlowVariableExpr, label2absy, proverInterface.Context));

      if (controlFlowVariableExpr != null)
      {
        VCExpr controlFlowFunctionAppl =
          exprGen.ControlFlowFunctionApplication(controlFlowVariableExpr, exprGen.Integer(BigNum.ZERO));
        VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
        vcexpr = exprGen.And(eqExpr, vcexpr);
      }

      callSites = vcgen.CollectCallSites(impl);
      recordProcCallSites = vcgen.CollectRecordProcedureCallSites(impl);

      privateExprVars = new List<VCExprVar>();
      foreach (Variable v in impl.LocVars)
      {
        privateExprVars.Add(translator.LookupVariable(v));
      }

      foreach (Variable v in impl.OutParams)
      {
        privateExprVars.Add(translator.LookupVariable(v));
      }

      interfaceExprVars = new List<VCExprVar>();
      foreach (Variable v in program.GlobalVariables)
      {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }

      foreach (Variable v in impl.InParams)
      {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }

      foreach (Variable v in outputVariables)
      {
        interfaceExprVars.Add(translator.LookupVariable(v));
      }

      initialized = true;
    }
  }

  // This class is derived and used by Corral to create VCs for Stratified Inlining.
  public abstract class StratifiedVCGenBase : VCGen
  {
    public readonly static string recordProcName = "boogie_si_record";
    public readonly static string callSiteVarAttr = "callSiteVar";
    public Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo;
    public ProverInterface prover;

    public StratifiedVCGenBase(Program program, string /*?*/ logFilePath, bool appendLogFile, List<Checker> checkers,
      Action<Implementation> PassiveImplInstrumentation)
      : base(program, logFilePath, appendLogFile, checkers)
    {
      implName2StratifiedInliningInfo = new Dictionary<string, StratifiedInliningInfo>();
      prover = ProverInterface.CreateProver(program, logFilePath, appendLogFile, CommandLineOptions.Clo.TimeLimit);
      foreach (var impl in program.Implementations)
      {
        implName2StratifiedInliningInfo[impl.Name] = new StratifiedInliningInfo(impl, this, PassiveImplInstrumentation);
      }

      GenerateRecordFunctions();
    }

    private void GenerateRecordFunctions()
    {
      foreach (var proc in program.Procedures)
      {
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

    public override void Close()
    {
      prover.Close();
      base.Close();
    }

    public void InstrumentCallSites(Implementation implementation)
    {
      var callSiteId = 0;
      foreach (Block block in implementation.Blocks)
      {
        List<Cmd> newCmds = new List<Cmd>();
        for (int i = 0; i < block.Cmds.Count; i++)
        {
          Cmd cmd = block.Cmds[i];
          newCmds.Add(cmd);
          AssumeCmd assumeCmd = cmd as AssumeCmd;
          if (assumeCmd == null) continue;
          NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
          if (naryExpr == null) continue;
          if (!implName2StratifiedInliningInfo.ContainsKey(naryExpr.Fun.FunctionName)) continue;
          Variable callSiteVar = new LocalVariable(Token.NoToken,
            new TypedIdent(Token.NoToken, "SICS" + callSiteId, Microsoft.Boogie.Type.Bool));
          implementation.LocVars.Add(callSiteVar);
          var toInsert = new AssumeCmd(Token.NoToken, new IdentifierExpr(Token.NoToken, callSiteVar),
            new QKeyValue(Token.NoToken, callSiteVarAttr, new List<object>(), null));
          newCmds.Add(toInsert);
          callSiteId++;
        }

        block.Cmds = newCmds;
      }
    }

    public Dictionary<Block, List<CallSite>> CollectCallSites(Implementation implementation)
    {
      var callSites = new Dictionary<Block, List<CallSite>>();
      foreach (Block block in implementation.Blocks)
      {
        for (int i = 0; i < block.Cmds.Count; i++)
        {
          Cmd cmd = block.Cmds[i];
          AssumeCmd assumeCmd = cmd as AssumeCmd;
          if (assumeCmd == null) continue;
          NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
          if (naryExpr == null) continue;
          if (!implName2StratifiedInliningInfo.ContainsKey(naryExpr.Fun.FunctionName)) continue;
          List<VCExpr> interfaceExprs = new List<VCExpr>();
          foreach (Expr e in naryExpr.Args)
          {
            interfaceExprs.Add(prover.Context.BoogieExprTranslator.Translate(e));
          }

          int instr = i;
          i++;
          AssumeCmd callSiteAssumeCmd = (AssumeCmd) block.Cmds[i];
          IdentifierExpr iexpr = (IdentifierExpr) callSiteAssumeCmd.Expr;
          CallSite cs = new CallSite(naryExpr.Fun.FunctionName, interfaceExprs,
            prover.Context.BoogieExprTranslator.LookupVariable(iexpr.Decl), block, instr, assumeCmd.Attributes);
          if (!callSites.ContainsKey(block))
            callSites[block] = new List<CallSite>();
          callSites[block].Add(cs);
        }
      }

      return callSites;
    }

    public Dictionary<Block, List<CallSite>> CollectRecordProcedureCallSites(Implementation implementation)
    {
      var callSites = new Dictionary<Block, List<CallSite>>();
      foreach (Block block in implementation.Blocks)
      {
        for (int i = 0; i < block.Cmds.Count; i++)
        {
          AssumeCmd assumeCmd = block.Cmds[i] as AssumeCmd;
          if (assumeCmd == null) continue;
          NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
          if (naryExpr == null) continue;
          if (!naryExpr.Fun.FunctionName.StartsWith(recordProcName)) continue;
          List<VCExpr> interfaceExprs = new List<VCExpr>();
          foreach (Expr e in naryExpr.Args)
          {
            interfaceExprs.Add(prover.Context.BoogieExprTranslator.Translate(e));
          }

          CallSite cs = new CallSite(naryExpr.Fun.FunctionName, interfaceExprs, null, block, i, assumeCmd.Attributes);
          if (!callSites.ContainsKey(block))
            callSites[block] = new List<CallSite>();
          callSites[block].Add(cs);
        }
      }

      return callSites;
    }

    private int macroCountForStratifiedInlining = 0;

    public Macro CreateNewMacro()
    {
      string newName = "SIMacro@" + macroCountForStratifiedInlining.ToString();
      macroCountForStratifiedInlining++;
      return new Macro(Token.NoToken, newName, new List<Variable>(),
        new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool), false));
    }

    private int varCountForStratifiedInlining = 0;

    public VCExprVar CreateNewVar(Microsoft.Boogie.Type type)
    {
      string newName = "SIV@" + varCountForStratifiedInlining.ToString();
      varCountForStratifiedInlining++;
      Constant newVar = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, type));
      prover.Context.DeclareConstant(newVar, false, null);
      return prover.VCExprGen.Variable(newVar.Name, type);
    }

    private int idCountForStratifiedInlining = 0;

    public int CreateNewId()
    {
      return idCountForStratifiedInlining++;
    }

    // Used inside PassifyImpl
    protected override void addExitAssert(string implName, Block exitBlock)
    {
      if (implName2StratifiedInliningInfo != null && implName2StratifiedInliningInfo.ContainsKey(implName))
      {
        var exitAssertCmd = implName2StratifiedInliningInfo[implName].exitAssertCmd;
        if (exitAssertCmd != null) exitBlock.Cmds.Add(exitAssertCmd);
      }
    }

    public override Counterexample extractLoopTrace(Counterexample cex, string mainProcName, Program program,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
      // Construct the set of inlined procs in the original program
      var inlinedProcs = new HashSet<string>();
      foreach (var decl in program.TopLevelDeclarations)
      {
        // Implementations
        if (decl is Implementation)
        {
          var impl = decl as Implementation;
          if (!(impl.Proc is LoopProcedure))
          {
            inlinedProcs.Add(impl.Name);
          }
        }

        // And recording procedures
        if (decl is Procedure)
        {
          var proc = decl as Procedure;
          if (proc.Name.StartsWith(recordProcName))
          {
            Debug.Assert(!(decl is LoopProcedure));
            inlinedProcs.Add(proc.Name);
          }
        }
      }

      return extractLoopTraceRec(
        new CalleeCounterexampleInfo(cex, new List<object>()),
        mainProcName, inlinedProcs, extractLoopMappingInfo).counterexample;
    }

    protected override bool elIsLoop(string procname)
    {
      StratifiedInliningInfo info = null;
      if (implName2StratifiedInliningInfo.ContainsKey(procname))
      {
        info = implName2StratifiedInliningInfo[procname];
      }

      if (info == null) return false;

      var lp = info.impl.Proc as LoopProcedure;

      if (lp == null) return false;
      return true;
    }

    public abstract Outcome FindLeastToVerify(Implementation impl, ref HashSet<string> allBoolVars);
  }

  public class InvalidProgramForSecureVc : Exception
  {
    public InvalidProgramForSecureVc(string msg) :
      base(msg)
    {
    }
  }

  public class SecureVCGen : VCGen
  {
    // Z3
    ProverInterface prover;

    // Handler
    ErrorReporter handler;

    // dump file
    public static TokenTextWriter outfile = null;


    public SecureVCGen(Program program, string /*?*/ logFilePath, bool appendLogFile, List<Checker> checkers)
      : base(program, logFilePath, appendLogFile, checkers)
    {
      prover = null;
      handler = null;
      if (CommandLineOptions.Clo.SecureVcGen != "" && outfile == null)
      {
        outfile = new TokenTextWriter(new StreamWriter(CommandLineOptions.Clo.SecureVcGen));
        CommandLineOptions.Clo.PrintInstrumented = true;
        var implsToVerify = new HashSet<string>(
          program.TopLevelDeclarations.OfType<Implementation>()
            .Where(impl => !impl.SkipVerification)
            .Select(impl => impl.Name));

        foreach (var decl in program.TopLevelDeclarations)
        {
          if (decl is NamedDeclaration && implsToVerify.Contains((decl as NamedDeclaration).Name))
            continue;
          decl.Emit(outfile, 0);
        }
      }
    }

    private Block GetExitBlock(Implementation impl)
    {
      var exitblocks = impl.Blocks.Where(blk => blk.TransferCmd is ReturnCmd);
      if (exitblocks.Count() == 1)
        return exitblocks.First();
      // create a new exit block
      var eb = new Block(Token.NoToken, "SVCeb", new List<Cmd>(), new ReturnCmd(Token.NoToken));
      foreach (var b in exitblocks)
      {
        b.TransferCmd = new GotoCmd(Token.NoToken, new List<Block> {eb});
      }

      impl.Blocks.Add(eb);
      return eb;
    }

    //static int LocalVarCounter = 0;
    private LocalVariable GetNewLocal(Variable v, string suffix)
    {
      return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken,
        string.Format("svc_{0}_{1}", v.Name, suffix), v.TypedIdent.Type));
    }

    private void GenVc(Implementation impl, VerifierCallback collector)
    {
      if (impl.Proc.Requires.Any())
        throw new InvalidProgramForSecureVc("SecureVc: Requires not supported");
      if (impl.LocVars.Any(v => isVisible(v)))
        throw new InvalidProgramForSecureVc("SecureVc: Visible Local variables not allowed");

      // Desugar procedure calls
      DesugarCalls(impl);

      // Gather spec, remove existing ensures
      var secureAsserts = new List<AssertCmd>();
      var logicalAsserts = new List<AssertCmd>();

      foreach (var ens in impl.Proc.Ensures)
      {
        if (ens.Free)
          throw new InvalidProgramForSecureVc("SecureVc: Free Ensures not supported");
        var dd = new Duplicator();
        secureAsserts.Add(new AssertCmd(ens.tok, Expr.Not(ens.Condition)));
        logicalAsserts.Add(dd.VisitAssertCmd(new AssertCmd(ens.tok, ens.Condition)) as AssertCmd);
      }

      impl.Proc.Ensures.Clear();

      // Make a copy of the impl
      var dup = new Duplicator();
      var implDup = dup.VisitImplementation(impl);

      // Get exit block
      var eb = GetExitBlock(impl);

      // Create two blocks: one for secureAsserts, one for logical asserts
      var ebSecure = new Block(Token.NoToken, "svc_secure_asserts", new List<Cmd>(), new ReturnCmd(Token.NoToken));
      var ebLogical = new Block(Token.NoToken, "svc_logical_asserts", new List<Cmd>(), new ReturnCmd(Token.NoToken));

      eb.TransferCmd = new GotoCmd(eb.TransferCmd.tok, new List<Block> {ebSecure, ebLogical});
      impl.Blocks.Add(ebSecure);
      impl.Blocks.Add(ebLogical);

      // Rename spec, while create copies of the hidden variables
      var substOld = new Dictionary<Variable, Expr>();
      var substVarSpec = new Dictionary<Variable, Expr>();
      var substVarPath = new Dictionary<Variable, Expr>();
      foreach (var g in program.GlobalVariables)
      {
        if (!isHidden(g)) continue;
        var lv = GetNewLocal(g, "In");
        impl.LocVars.Add(lv);
        substOld.Add(g, Expr.Ident(lv));
      }

      for (int i = 0; i < impl.InParams.Count; i++)
      {
        var v = impl.Proc.InParams[i];
        if (!isHidden(v))
        {
          substVarSpec.Add(impl.Proc.InParams[i], Expr.Ident(impl.InParams[i]));
          continue;
        }

        var lv = GetNewLocal(v, "In");
        impl.LocVars.Add(lv);
        substVarSpec.Add(v, Expr.Ident(lv));
        substVarPath.Add(impl.InParams[i], Expr.Ident(lv));
      }

      for (int i = 0; i < impl.OutParams.Count; i++)
      {
        var v = impl.Proc.OutParams[i];
        if (!isHidden(v))
        {
          substVarSpec.Add(impl.Proc.OutParams[i], Expr.Ident(impl.OutParams[i]));
          continue;
        }

        var lv = GetNewLocal(v, "Out");
        impl.LocVars.Add(lv);
        substVarSpec.Add(v, Expr.Ident(lv));
        substVarPath.Add(impl.OutParams[i], Expr.Ident(lv));
      }

      foreach (var g in program.GlobalVariables)
      {
        if (!isHidden(g)) continue;
        if (!impl.Proc.Modifies.Any(ie => ie.Name == g.Name)) continue;

        var lv = GetNewLocal(g, "Out");
        impl.LocVars.Add(lv);
        substVarSpec.Add(g, Expr.Ident(lv));
        substVarPath.Add(g, Expr.Ident(lv));
      }

      secureAsserts = secureAsserts.ConvertAll(ac =>
        Substituter.ApplyReplacingOldExprs(
          Substituter.SubstitutionFromHashtable(substVarSpec),
          Substituter.SubstitutionFromHashtable(substOld),
          ac) as AssertCmd);

      var substVarProcToImpl = new Dictionary<Variable, Expr>();
      for (int i = 0; i < impl.InParams.Count; i++)
        substVarProcToImpl.Add(impl.Proc.InParams[i], Expr.Ident(impl.InParams[i]));

      for (int i = 0; i < impl.OutParams.Count; i++)
        substVarProcToImpl.Add(impl.Proc.OutParams[i], Expr.Ident(impl.OutParams[i]));

      logicalAsserts = logicalAsserts.ConvertAll(ac =>
        Substituter.Apply(Substituter.SubstitutionFromHashtable(substVarProcToImpl), ac)
          as AssertCmd);

      // Paths
      foreach (var path in GetAllPaths(implDup))
      {
        var wp = ComputeWP(implDup, path);

        // replace hidden variables to match those used in the spec
        wp = Substituter.ApplyReplacingOldExprs(
          Substituter.SubstitutionFromHashtable(substVarPath),
          Substituter.SubstitutionFromHashtable(substOld),
          wp);

        ebSecure.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(wp)));
      }

      ebSecure.Cmds.AddRange(secureAsserts);
      ebLogical.Cmds.AddRange(logicalAsserts);

      if (outfile != null)
      {
        impl.Proc.Emit(outfile, 0);
        impl.Emit(outfile, 0);
      }

      ModelViewInfo mvInfo;
      ConvertCFG2DAG(impl);
      var gotoCmdOrigins = PassifyImpl(impl, out mvInfo);

      var gen = prover.VCExprGen;
      var exprGen = prover.Context.ExprGen;
      var translator = prover.Context.BoogieExprTranslator;

      var label2absy = new Dictionary<int, Absy>();
      VCGen.CodeExprConversionClosure cc = new VCGen.CodeExprConversionClosure(label2absy, prover.Context);
      translator.SetCodeExprConverter(cc.CodeExprToVerificationCondition);
      var implVc = gen.Not(GenerateVCAux(impl, null, label2absy, prover.Context));

      handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, debugInfos, collector,
        mvInfo, prover.Context, program);

      prover.Assert(implVc, true);
    }

    Expr ComputeWP(Implementation impl, List<Cmd> path)
    {
      Expr expr = Expr.True;

      // create constants for out varibles
      var subst = new Dictionary<Variable, Expr>();
      foreach (var g in impl.Proc.Modifies)
      {
        var c = new Constant(Token.NoToken, new TypedIdent(Token.NoToken,
          "svc_out_const_" + g.Name, g.Decl.TypedIdent.Type));
        subst.Add(c, g);
        expr = Expr.And(expr, Expr.Eq(Expr.Ident(c), g));
      }

      foreach (var v in impl.OutParams)
      {
        var c = new Constant(Token.NoToken, new TypedIdent(Token.NoToken,
          "svc_out_const_" + v.Name, v.TypedIdent.Type));
        subst.Add(c, Expr.Ident(v));
        expr = Expr.And(expr, Expr.Eq(Expr.Ident(c), Expr.Ident(v)));
      }

      // we need this technicality
      var subst1 = new Dictionary<Variable, Expr>();
      foreach (var g in program.GlobalVariables)
      {
        subst1.Add(g, new OldExpr(Token.NoToken, Expr.Ident(g)));
      }

      // Implicitly close with havoc of all the locals and OutParams
      path.Insert(0, new HavocCmd(Token.NoToken, new List<IdentifierExpr>(
        impl.LocVars.Select(v => Expr.Ident(v)).Concat(
          impl.OutParams.Select(v => Expr.Ident(v))))));

      for (int i = path.Count - 1; i >= 0; i--)
      {
        var cmd = path[i];
        if (cmd is AssumeCmd)
        {
          expr = Expr.And(expr, (cmd as AssumeCmd).Expr);
        }
        else if (cmd is AssignCmd)
        {
          var h = new Dictionary<Variable, Expr>();
          var acmd = cmd as AssignCmd;
          for (int j = 0; j < acmd.Lhss.Count; j++)
          {
            h.Add(acmd.Lhss[j].DeepAssignedVariable, acmd.Rhss[j]);
          }

          var s = Substituter.SubstitutionFromHashtable(h);
          expr = Substituter.Apply(s, expr);
        }
        else if (cmd is HavocCmd)
        {
          var h = new Dictionary<Variable, Expr>();
          var formals = new List<Variable>();

          var vc = new VariableCollector();
          vc.VisitExpr(expr);

          foreach (var ie in (cmd as HavocCmd).Vars)
          {
            if (!vc.usedVars.Contains(ie.Decl)) continue;
            var f = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken,
              ie.Decl.Name + "_formal", ie.Decl.TypedIdent.Type));
            h.Add(ie.Decl, Expr.Ident(f));
            formals.Add(f);
          }

          if (!formals.Any())
            continue;
          var s = Substituter.SubstitutionFromHashtable(h);
          expr = Substituter.Apply(s, expr);
          expr = new ExistsExpr(Token.NoToken, formals, expr);
        }
        else
        {
          throw new InvalidProgramForSecureVc(string.Format("Unhandled cmd: {0}", cmd));
        }
      }

      // Implicitly close with havoc of all the locals and OutParams


      expr = Substituter.Apply(Substituter.SubstitutionFromHashtable(subst1), expr);
      expr = Substituter.Apply(Substituter.SubstitutionFromHashtable(subst),
        Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>()), expr);
      expr.Typecheck(new TypecheckingContext(null));
      return expr;
    }

    // Generate all paths in the impl
    IEnumerable<List<Cmd>> GetAllPaths(Implementation impl)
    {
      var stk = new Stack<Tuple<Block, int>>();
      stk.Push(Tuple.Create(impl.Blocks[0], 0));

      while (stk.Any())
      {
        var tup = stk.Peek();
        if (tup.Item1.TransferCmd is ReturnCmd)
        {
          var ret = new List<Cmd>();
          var ls = stk.ToList();
          ls.Iter(t => ret.AddRange(t.Item1.Cmds));
          yield return ret;

          stk.Pop();
          continue;
        }

        stk.Pop();

        var gc = tup.Item1.TransferCmd as GotoCmd;
        if (gc.labelTargets.Count <= tup.Item2)
          continue;

        stk.Push(Tuple.Create(tup.Item1, tup.Item2 + 1));
        stk.Push(Tuple.Create(gc.labelTargets[tup.Item2], 0));
      }

      yield break;
    }

    bool isHidden(Variable v)
    {
      return QKeyValue.FindBoolAttribute(v.Attributes, "hidden");
    }

    bool isVisible(Variable v)
    {
      return !isHidden(v);
    }

    public override Outcome VerifyImplementation(Implementation /*!*/ impl, VerifierCallback /*!*/ callback)
    {
      // Record current time
      var startTime = DateTime.UtcNow;
      
      CommandLineOptions.Clo.ErrorLimit = 1;
      prover = ProverInterface.CreateProver(program, logFilePath, appendLogFile, CommandLineOptions.Clo.TimeLimit);

      // Flush any axioms that came with the program before we start SI on this implementation
      prover.AssertAxioms();

      GenVc(impl, callback);

      prover.Check();
      var outcome = prover.CheckOutcomeCore(handler);
      //var outcome = ProverInterface.Outcome.Valid;

      prover.Close();


      //Console.WriteLine("Answer = {0}", outcome);

      return ProverInterfaceOutcomeToConditionGenerationOutcome(outcome);
    }
  }
} // namespace VC