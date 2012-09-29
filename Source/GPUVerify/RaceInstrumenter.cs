using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify {
  class RaceInstrumenter : IRaceInstrumenter {
    protected GPUVerifier verifier;

    private QKeyValue SourceLocationAttributes = null;

    private int CurrStmtNo = 1;

    private Dictionary<string, List<int>> ReadAccessSourceLocations = new Dictionary<string, List<int>>();

    private Dictionary<string, List<int>> WriteAccessSourceLocations = new Dictionary<string, List<int>>();

    public IKernelArrayInfo NonLocalStateToCheck;

    private Dictionary<string, Procedure> RaceCheckingProcedures = new Dictionary<string, Procedure>();

    public void setVerifier(GPUVerifier verifier) {
      this.verifier = verifier;
      NonLocalStateToCheck = new KernelArrayInfoLists();
      foreach (Variable v in verifier.KernelArrayInfo.getGlobalArrays()) {
        NonLocalStateToCheck.getGlobalArrays().Add(v);
      }
      foreach (Variable v in verifier.KernelArrayInfo.getGroupSharedArrays()) {
        NonLocalStateToCheck.getGroupSharedArrays().Add(v);
      }
    }

    private void AddNoReadOrWriteCandidateInvariants(IRegion region, Variable v) {
      // Reasoning: if READ_HAS_OCCURRED_v is not in the modifies set for the
      // loop then there is no point adding an invariant
      //
      // If READ_HAS_OCCURRED_v is in the modifies set, but the loop does not
      // contain a barrier, then it is almost certain that a read CAN be
      // pending at the loop head, so the invariant will not hold
      //
      // If there is a barrier in the loop body then READ_HAS_OCCURRED_v will
      // be in the modifies set, but there may not be a live read at the loop
      // head, so it is worth adding the loop invariant candidate.
      //
      // The same reasoning applies for WRITE

      if (verifier.ContainsBarrierCall(region)) {
        if (verifier.ContainsNamedVariable(
            LoopInvariantGenerator.GetModifiedVariables(region), GPUVerifier.MakeAccessHasOccurredVariableName(v.Name, "READ"))) {
          AddNoReadOrWriteCandidateInvariant(region, v, "READ");
        }

        if (verifier.ContainsNamedVariable(
            LoopInvariantGenerator.GetModifiedVariables(region), GPUVerifier.MakeAccessHasOccurredVariableName(v.Name, "WRITE"))) {
          AddNoReadOrWriteCandidateInvariant(region, v, "WRITE");
        }
      }
    }

    private void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v) {
      AddNoReadOrWriteCandidateRequires(Proc, v, "READ", "1");
      AddNoReadOrWriteCandidateRequires(Proc, v, "WRITE", "1");
    }

    private void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v) {
      AddNoReadOrWriteCandidateEnsures(Proc, v, "READ", "1");
      AddNoReadOrWriteCandidateEnsures(Proc, v, "WRITE", "1");
    }

    private void AddNoReadOrWriteCandidateInvariant(IRegion region, Variable v, string ReadOrWrite) {
      Expr candidate = NoReadOrWriteExpr(v, ReadOrWrite, "1");
      verifier.AddCandidateInvariant(region, candidate, "no " + ReadOrWrite.ToLower());
    }

    public void AddRaceCheckingCandidateInvariants(Implementation impl, IRegion region) {
      List<Expr> offsetPredicatesRead = new List<Expr>();
      List<Expr> offsetPredicatesWrite = new List<Expr>();
      foreach (Variable v in NonLocalStateToCheck.getAllNonLocalArrays()) {
        AddNoReadOrWriteCandidateInvariants(region, v);
        AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(impl, region, v, "READ");
        AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(impl, region, v, "WRITE");
        offsetPredicatesRead = CollectOffsetPredicates(impl, region, v, "READ");
        offsetPredicatesWrite = CollectOffsetPredicates(impl, region, v, "WRITE");
        AddOffsetsSatisfyPredicatesCandidateInvariant(region, v, "READ", offsetPredicatesRead);
        AddOffsetsSatisfyPredicatesCandidateInvariant(region, v, "WRITE", offsetPredicatesWrite);
        AddOffsetsSatisfyPredicatesCandidateInvariant(region, v, "READ", new List<Expr>(offsetPredicatesRead.Zip(CollectSourceLocPredicates(region, v, "READ"), Expr.And)));
        AddOffsetsSatisfyPredicatesCandidateInvariant(region, v, "WRITE", new List<Expr>(offsetPredicatesWrite.Zip(CollectSourceLocPredicates(region, v, "WRITE"), Expr.And)));
      }
    }

    private void AddAccessRelatedCandidateInvariant(IRegion region, string accessKind, Expr candidateInvariantExpr, string procName, string tag) {
      Expr candidate = new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(candidateInvariantExpr.Clone() as Expr);
      verifier.AddCandidateInvariant(region, candidate, tag);
    }

    private bool DoesNotReferTo(Expr expr, string v) {
      FindReferencesToNamedVariableVisitor visitor = new FindReferencesToNamedVariableVisitor(v);
      visitor.VisitExpr(expr);
      return !visitor.found;
    }

    private List<Expr> CollectSourceLocPredicates(IRegion region, Variable v, string accessType) {
      var sourceVar = verifier.FindOrCreateSourceVariable(v.Name, accessType);
      var sourceExpr = new IdentifierExpr(Token.NoToken, sourceVar);
      var sourcePreds = new List<Expr>();

      foreach (Cmd c in region.Cmds()) {
        if (c is CallCmd) {
          CallCmd call = c as CallCmd;
          if (call.callee == "_LOG_" + accessType + "_" + v.Name) {
            sourcePreds.Add(Expr.Eq(sourceExpr, call.Ins[2]));
          }
        }
      }

      return sourcePreds;
    }
    private List<Expr> CollectOffsetPredicates(Implementation impl, IRegion region, Variable v, string accessType) {
      var offsetVar = new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeOffsetVariable(v.Name, accessType));
      var offsetExpr = new IdentifierExpr(Token.NoToken, offsetVar);
      var offsetPreds = new List<Expr>();

      foreach (var offset in GetOffsetsAccessed(region, v, accessType)) {
        bool isConstant;
        var def = verifier.varDefAnalyses[impl].SubstDefinitions(offset, impl.Name, out isConstant);
        if (def == null)
          continue;

        if (isConstant) {
          offsetPreds.Add(Expr.Eq(offsetExpr, def));
        }
        else {
          var sc = StrideConstraint.FromExpr(verifier, impl, def);
          var pred = sc.MaybeBuildPredicate(verifier, offsetExpr);
          if (pred != null)
            offsetPreds.Add(pred);
        }
      }

      return offsetPreds;
    }

    private void AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(Implementation impl, IRegion region, Variable v, string accessType) {
      KeyValuePair<IdentifierExpr, Expr> iLessThanC = GetILessThanC(region.Guard());
      if (iLessThanC.Key != null) {
        foreach (Expr e in GetOffsetsAccessed(region, v, accessType)) {
          if (HasFormIPlusLocalIdTimesC(e, iLessThanC, impl)) {
            AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(region, v, iLessThanC.Value, accessType);
            break;
          }
        }

        foreach (Expr e in GetOffsetsAccessed(region, v, accessType)) {
          if (HasFormIPlusGlobalIdTimesC(e, iLessThanC, impl)) {
            AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(region, v, iLessThanC.Value, accessType);
            break;
          }
        }

      }


    }

    private bool HasFormIPlusLocalIdTimesC(Expr e, KeyValuePair<IdentifierExpr, Expr> iLessThanC, Implementation impl) {
      if (!(e is NAryExpr)) {
        return false;
      }

      NAryExpr nary = e as NAryExpr;

      if (!nary.Fun.FunctionName.Equals("BV32_ADD")) {
        return false;
      }

      return (SameIdentifierExpression(nary.Args[0], iLessThanC.Key) &&
          IsLocalIdTimesConstant(nary.Args[1], iLessThanC.Value, impl)) ||
          (SameIdentifierExpression(nary.Args[1], iLessThanC.Key) &&
          IsLocalIdTimesConstant(nary.Args[0], iLessThanC.Value, impl));
    }

    private bool IsLocalIdTimesConstant(Expr maybeLocalIdTimesConstant, Expr constant, Implementation impl) {
      if (!(maybeLocalIdTimesConstant is NAryExpr)) {
        return false;
      }
      NAryExpr nary = maybeLocalIdTimesConstant as NAryExpr;
      if (!nary.Fun.FunctionName.Equals("BV32_MUL")) {
        return false;
      }

      return
          (SameConstant(nary.Args[0], constant) && verifier.IsLocalId(nary.Args[1], 0, impl)) ||
          (SameConstant(nary.Args[1], constant) && verifier.IsLocalId(nary.Args[0], 0, impl));
    }


    private bool HasFormIPlusGlobalIdTimesC(Expr e, KeyValuePair<IdentifierExpr, Expr> iLessThanC, Implementation impl) {
      if (!(e is NAryExpr)) {
        return false;
      }

      NAryExpr nary = e as NAryExpr;

      if (!nary.Fun.FunctionName.Equals("BV32_ADD")) {
        return false;
      }

      return (SameIdentifierExpression(nary.Args[0], iLessThanC.Key) &&
          IsGlobalIdTimesConstant(nary.Args[1], iLessThanC.Value, impl)) ||
          (SameIdentifierExpression(nary.Args[1], iLessThanC.Key) &&
          IsGlobalIdTimesConstant(nary.Args[0], iLessThanC.Value, impl));
    }

    private bool IsGlobalIdTimesConstant(Expr maybeGlobalIdTimesConstant, Expr constant, Implementation impl) {
      if (!(maybeGlobalIdTimesConstant is NAryExpr)) {
        return false;
      }
      NAryExpr nary = maybeGlobalIdTimesConstant as NAryExpr;
      if (!nary.Fun.FunctionName.Equals("BV32_MUL")) {
        return false;
      }

      return
          (SameConstant(nary.Args[0], constant) && verifier.IsGlobalId(nary.Args[1], 0, impl)) ||
          (SameConstant(nary.Args[1], constant) && verifier.IsGlobalId(nary.Args[0], 0, impl));
    }


    private bool SameConstant(Expr expr, Expr constant) {
      if (constant is IdentifierExpr) {
        IdentifierExpr identifierExpr = constant as IdentifierExpr;
        Debug.Assert(identifierExpr.Decl is Constant);
        return expr is IdentifierExpr && (expr as IdentifierExpr).Decl is Constant && (expr as IdentifierExpr).Decl.Name.Equals(identifierExpr.Decl.Name);
      }
      else {
        Debug.Assert(constant is LiteralExpr);
        LiteralExpr literalExpr = constant as LiteralExpr;
        if (!(expr is LiteralExpr)) {
          return false;
        }
        if (!(literalExpr.Val is BvConst) || !((expr as LiteralExpr).Val is BvConst)) {
          return false;
        }

        return (literalExpr.Val as BvConst).Value.ToInt == ((expr as LiteralExpr).Val as BvConst).Value.ToInt;
      }
    }

    private bool SameIdentifierExpression(Expr expr, IdentifierExpr identifierExpr) {
      if (!(expr is IdentifierExpr)) {
        return false;
      }
      return (expr as IdentifierExpr).Decl.Name.Equals(identifierExpr.Name);
    }

    private KeyValuePair<IdentifierExpr, Expr> GetILessThanC(Expr expr) {

      if (expr is NAryExpr && (expr as NAryExpr).Fun.FunctionName.Equals("bv32_to_bool")) {
        expr = (expr as NAryExpr).Args[0];
      }

      if (!(expr is NAryExpr)) {
        return new KeyValuePair<IdentifierExpr, Expr>(null, null);
      }

      NAryExpr nary = expr as NAryExpr;

      if (!(nary.Fun.FunctionName.Equals("BV32_C_LT") || nary.Fun.FunctionName.Equals("BV32_LT"))) {
        return new KeyValuePair<IdentifierExpr, Expr>(null, null);
      }

      if (!(nary.Args[0] is IdentifierExpr)) {
        return new KeyValuePair<IdentifierExpr, Expr>(null, null);
      }

      if (!IsConstant(nary.Args[1])) {
        return new KeyValuePair<IdentifierExpr, Expr>(null, null);
      }

      return new KeyValuePair<IdentifierExpr, Expr>(nary.Args[0] as IdentifierExpr, nary.Args[1]);

    }

    private static bool IsConstant(Expr e) {
      return ((e is IdentifierExpr && (e as IdentifierExpr).Decl is Constant) || e is LiteralExpr);
    }

    private void AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Procedure Proc, Variable v) {
      AddAccessedOffsetIsThreadLocalIdCandidateRequires(Proc, v, "WRITE", 1);
      AddAccessedOffsetIsThreadLocalIdCandidateRequires(Proc, v, "READ", 1);
    }

    private void AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Procedure Proc, Variable v) {
      AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Proc, v, "WRITE", 1);
      AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Proc, v, "READ", 1);
    }

    public void AddKernelPrecondition() {
      foreach (Variable v in NonLocalStateToCheck.getAllNonLocalArrays()) {
        AddRequiresNoPendingAccess(v);
        AddRequiresSourceAccessZero(v);
      }
    }

    public void AddRaceCheckingInstrumentation() {

      foreach (Declaration d in verifier.Program.TopLevelDeclarations) {
        if (d is Implementation) {
          AddRaceCheckCalls(d as Implementation);
        }
      }

    }

    private void AddRaceCheckingDecsAndProcsForVar(Variable v) {
      AddLogRaceDeclarations(v, "READ");
      AddLogRaceDeclarations(v, "WRITE");
      AddLogAccessProcedure(v, "READ");
      AddCheckAccessProcedure(v, "READ");
      AddLogAccessProcedure(v, "WRITE");
      AddCheckAccessProcedure(v, "WRITE");
    }

    private StmtList AddRaceCheckCalls(StmtList stmtList) {
      Contract.Requires(stmtList != null);

      StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

      foreach (BigBlock bodyBlock in stmtList.BigBlocks) {
        result.BigBlocks.Add(AddRaceCheckCalls(bodyBlock));
      }
      return result;
    }

    private Block AddRaceCheckCalls(Block b) {
      b.Cmds = AddRaceCheckCalls(b.Cmds);
      return b;
    }

    private void AddRaceCheckCalls(Implementation impl) {
      if (CommandLineOptions.Unstructured)
        impl.Blocks = impl.Blocks.Select(AddRaceCheckCalls).ToList();
      else
        impl.StructuredStmts = AddRaceCheckCalls(impl.StructuredStmts);
    }

    private CmdSeq AddRaceCheckCalls(CmdSeq cs) {
      var result = new CmdSeq();
      foreach (Cmd c in cs) {
        result.Add(c);

        if (c is AssertCmd) {
          AssertCmd assertion = c as AssertCmd;
          if (QKeyValue.FindBoolAttribute(assertion.Attributes, "sourceloc")) {
            SourceLocationAttributes = assertion.Attributes;
          }
        }

        if (c is AssignCmd) {
          AssignCmd assign = c as AssignCmd;

          ReadCollector rc = new ReadCollector(NonLocalStateToCheck);
          foreach (var rhs in assign.Rhss)
            rc.Visit(rhs);
          if (rc.accesses.Count > 0) {
            foreach (AccessRecord ar in rc.accesses) {
              AddLogAndCheckCalls(result, ar, "READ");
            }
          }

          foreach (var lhs in assign.Lhss) {
            WriteCollector wc = new WriteCollector(NonLocalStateToCheck);
            wc.Visit(lhs);
            if (wc.GetAccess() != null) {
              AccessRecord ar = wc.GetAccess();
              AddLogAndCheckCalls(result, ar, "WRITE");
            }
          }
        }
      }
      return result;
    }

    private void AddLogAndCheckCalls(CmdSeq result, AccessRecord ar, string Access) {
      ExprSeq inParamsLog = new ExprSeq();
      ExprSeq inParamsChk = new ExprSeq();
      inParamsChk.Add(ar.Index);
      inParamsLog.Add(ar.Index);
      inParamsLog.Add(new LiteralExpr(Token.NoToken, BigNum.FromInt(CurrStmtNo), 32));

      Procedure logProcedure = GetRaceCheckingProcedure(Token.NoToken, "_LOG_" + Access + "_" + ar.v.Name);
      Procedure checkProcedure = GetRaceCheckingProcedure(Token.NoToken, "_CHECK_" + Access + "_" + ar.v.Name);

      verifier.OnlyThread1.Add(logProcedure.Name);
      verifier.OnlyThread2.Add(checkProcedure.Name);

      CallCmd logAccessCallCmd = new CallCmd(Token.NoToken, logProcedure.Name, inParamsLog, new IdentifierExprSeq());
      logAccessCallCmd.Proc = logProcedure;

      CallCmd checkAccessCallCmd = new CallCmd(Token.NoToken, checkProcedure.Name, inParamsChk, new IdentifierExprSeq());
      checkAccessCallCmd.Proc = checkProcedure;
      checkAccessCallCmd.Attributes = SourceLocationAttributes;

      result.Add(logAccessCallCmd);
      result.Add(checkAccessCallCmd);

      string fname = QKeyValue.FindStringAttribute(SourceLocationAttributes, "fname");

      string Key = ar.v.Name;
      if (Access == "WRITE")
      {
        if (!WriteAccessSourceLocations.ContainsKey(Key))
        {
          WriteAccessSourceLocations.Add(Key, new List<int>());
        }
        WriteAccessSourceLocations[Key].Add(CurrStmtNo);
      }
      else if (Access == "READ")
      {
        if (!ReadAccessSourceLocations.ContainsKey(Key))
        {
          ReadAccessSourceLocations.Add(Key, new List<int>());
        }
        ReadAccessSourceLocations[Key].Add(CurrStmtNo);
      }

      if (fname != null)
      {
        writeSourceLocToFile(SourceLocationAttributes, Path.GetFileNameWithoutExtension(CommandLineOptions.inputFiles[0]) + ".loc");
      }
      else
      {
        Debug.Assert(false, "RaceInstrumenter.AddLogAndCheckCalls: Could not write sourceloc to file as filename could not be found.\n");
      }
      CurrStmtNo++;
    }

    private BigBlock AddRaceCheckCalls(BigBlock bb) {
      BigBlock result = new BigBlock(bb.tok, bb.LabelName, AddRaceCheckCalls(bb.simpleCmds), null, bb.tc);

      if (bb.ec is WhileCmd) {
        WhileCmd WhileCommand = bb.ec as WhileCmd;
        result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard,
                WhileCommand.Invariants, AddRaceCheckCalls(WhileCommand.Body));
      }
      else if (bb.ec is IfCmd) {
        IfCmd IfCommand = bb.ec as IfCmd;
        Debug.Assert(IfCommand.elseIf == null); // We don't handle else if yet
        result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, AddRaceCheckCalls(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? AddRaceCheckCalls(IfCommand.elseBlock) : null);
      }
      else if (bb.ec is BreakCmd) {
        result.ec = bb.ec;
      }
      else {
        Debug.Assert(bb.ec == null);
      }

      return result;
    }

    private Procedure GetRaceCheckingProcedure(IToken tok, string name) {
      if (RaceCheckingProcedures.ContainsKey(name)) {
        return RaceCheckingProcedures[name];
      }
      Procedure newProcedure = new Procedure(tok, name, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
      RaceCheckingProcedures[name] = newProcedure;
      return newProcedure;
    }


    public BigBlock MakeResetReadWriteSetStatements(Variable v, Expr ResetCondition) {
      BigBlock result = new BigBlock(Token.NoToken, null, new CmdSeq(), null, null);

      Expr ResetReadAssumeGuard = Expr.Imp(ResetCondition, 
        Expr.Not(new IdentifierExpr(Token.NoToken,
          new VariableDualiser(1, null, null).VisitVariable(
            GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ")))));
      Expr ResetWriteAssumeGuard = Expr.Imp(ResetCondition,
        Expr.Not(new IdentifierExpr(Token.NoToken,
          new VariableDualiser(1, null, null).VisitVariable(
            GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE")))));

      if (verifier.KernelArrayInfo.getGlobalArrays().Contains(v)) {
        ResetReadAssumeGuard = Expr.Imp(GPUVerifier.ThreadsInSameGroup(), ResetReadAssumeGuard);
        ResetWriteAssumeGuard = Expr.Imp(GPUVerifier.ThreadsInSameGroup(), ResetWriteAssumeGuard);
      }

      result.simpleCmds.Add(new AssumeCmd(Token.NoToken, ResetReadAssumeGuard));
      result.simpleCmds.Add(new AssumeCmd(Token.NoToken, ResetWriteAssumeGuard));
      return result;
    }

    protected Procedure MakeLogAccessProcedureHeader(Variable v, string ReadOrWrite) {
      VariableSeq inParams = new VariableSeq();

      Variable PredicateParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_P", Microsoft.Boogie.Type.Bool));

      Debug.Assert(v.TypedIdent.Type is MapType);
      MapType mt = v.TypedIdent.Type as MapType;
      Debug.Assert(mt.Arguments.Length == 1);
      Variable OffsetParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_offset", mt.Arguments[0]));
      Variable SourceParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_source", mt.Arguments[0]));
      Debug.Assert(!(mt.Result is MapType));

      inParams.Add(new VariableDualiser(1, null, null).VisitVariable(PredicateParameter.Clone() as Variable));
      inParams.Add(new VariableDualiser(1, null, null).VisitVariable(OffsetParameter.Clone() as Variable));
      inParams.Add(new VariableDualiser(1, null, null).VisitVariable(SourceParameter.Clone() as Variable));

      string LogProcedureName = "_LOG_" + ReadOrWrite + "_" + v.Name;

      Procedure result = GetRaceCheckingProcedure(v.tok, LogProcedureName);

      result.InParams = inParams;

      result.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

      return result;
    }

    protected Procedure MakeCheckAccessProcedureHeader(Variable v, string ReadOrWrite) {
      VariableSeq inParams = new VariableSeq();

      Variable PredicateParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_P", Microsoft.Boogie.Type.Bool));

      Debug.Assert(v.TypedIdent.Type is MapType);
      MapType mt = v.TypedIdent.Type as MapType;
      Debug.Assert(mt.Arguments.Length == 1);
      Variable OffsetParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_offset", mt.Arguments[0]));
      Debug.Assert(!(mt.Result is MapType));

      inParams.Add(new VariableDualiser(2, null, null).VisitVariable(PredicateParameter.Clone() as Variable));
      inParams.Add(new VariableDualiser(2, null, null).VisitVariable(OffsetParameter.Clone() as Variable));

      string CheckProcedureName = "_CHECK_" + ReadOrWrite + "_" + v.Name;

      Procedure result = GetRaceCheckingProcedure(v.tok, CheckProcedureName);

      result.InParams = inParams;

      result.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

      return result;
    }

    public void AddRaceCheckingCandidateRequires(Procedure Proc) {
      foreach (Variable v in NonLocalStateToCheck.getAllNonLocalArrays()) {
        AddNoReadOrWriteCandidateRequires(Proc, v);
        AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v);
      }
    }

    public void DoHoudiniPointerAnalysis(Procedure Proc) {
      foreach (Variable v in Proc.InParams) {
        if (v.TypedIdent.Type is CtorType) {
          CtorType ct = v.TypedIdent.Type as CtorType;
          if (ct.Decl.Name.Equals("ptr")) {
            foreach (var arrayCollection in new ICollection<Variable>[] { 
                            verifier.KernelArrayInfo.getGlobalArrays(), verifier.KernelArrayInfo.getGroupSharedArrays(),
                            verifier.KernelArrayInfo.getPrivateArrays() }) {
              if (arrayCollection.Count == 0) {
                continue;
              }

              Expr DisjunctionOverPointerSet = null;
              foreach (var array in arrayCollection) {
                Expr PointerSetDisjunct = Expr.Eq(MakePtrBaseExpr(v), MakeArrayIdExpr(array));
                DisjunctionOverPointerSet = (DisjunctionOverPointerSet == null ? PointerSetDisjunct : Expr.Or(DisjunctionOverPointerSet, PointerSetDisjunct));
                verifier.AddCandidateRequires(Proc,
                        Expr.Neq(MakePtrBaseExpr(v), MakeArrayIdExpr(array)));
              }
              Debug.Assert(DisjunctionOverPointerSet != null);
              verifier.AddCandidateRequires(Proc, DisjunctionOverPointerSet);
              verifier.AddCandidateRequires(Proc, Expr.Eq(MakePtrOffsetExpr(v), GPUVerifier.ZeroBV()));
            }
          }
        }
      }
    }

    private IdentifierExpr MakeArrayIdExpr(Variable array) {
      var arrayId = verifier.ResContext.LookUpVariable("$arrayId" + array.Name);
      return new IdentifierExpr(Token.NoToken, arrayId);
    }

    private NAryExpr MakePtrBaseExpr(Variable v) {
      var baseSel = (Function)verifier.ResContext.LookUpProcedure("base#MKPTR");
      return new NAryExpr(Token.NoToken, new FunctionCall(baseSel),
                          new ExprSeq(new Expr[] { Expr.Ident(v) }));
    }

    private NAryExpr MakePtrOffsetExpr(Variable v) {
      var offsetSel = (Function)verifier.ResContext.LookUpProcedure("offset#MKPTR");
      return new NAryExpr(Token.NoToken, new FunctionCall(offsetSel),
                          new ExprSeq(new Expr[] { Expr.Ident(v) }));
    }

    public void AddRaceCheckingCandidateEnsures(Procedure Proc) {
      foreach (Variable v in NonLocalStateToCheck.getAllNonLocalArrays()) {
        AddNoReadOrWriteCandidateEnsures(Proc, v);
        AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v);
      }
    }

    private void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo) {
      verifier.AddCandidateRequires(Proc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
    }

    private void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo) {
      verifier.AddCandidateEnsures(Proc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
    }

    private HashSet<Expr> GetOffsetsAccessed(IRegion region, Variable v, string AccessType) {
      HashSet<Expr> result = new HashSet<Expr>();

      foreach (Cmd c in region.Cmds()) {
        if (c is CallCmd) {
          CallCmd call = c as CallCmd;

          if (call.callee == "_LOG_" + AccessType + "_" + v.Name) {
            // Ins[0] is thread 1's predicate,
            // Ins[1] is the offset to be read
            // If Ins[1] has the form BV32_ADD(offset#construct...(P), offset),
            // we are looking for the second parameter to this BV32_ADD
            Expr offset = call.Ins[1];
            if (offset is NAryExpr) {
              var nExpr = (NAryExpr)offset;
              if (nExpr.Fun.FunctionName == "BV32_ADD" &&
                  nExpr.Args[0] is NAryExpr) {
                var n0Expr = (NAryExpr)nExpr.Args[0];
                if (n0Expr.Fun.FunctionName.StartsWith("offset#"))
                  offset = nExpr.Args[1];
              }
            }
            result.Add(offset);
          }

        }

      }

      return result;
    }

    public void AddRaceCheckingDeclarations() {
      foreach (Variable v in NonLocalStateToCheck.getAllNonLocalArrays()) {
        AddRaceCheckingDecsAndProcsForVar(v);
      }
    }

    protected void AddLogAccessProcedure(Variable v, string Access) {
      Procedure LogAccessProcedure = MakeLogAccessProcedureHeader(v, Access);

      Variable AccessHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, Access);
      Variable AccessOffsetXVariable = GPUVerifier.MakeOffsetVariable(v.Name, Access);
      Variable AccessSourceVariable = GPUVerifier.MakeSourceVariable(v.Name, Access);

      Variable PredicateParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_P", Microsoft.Boogie.Type.Bool));

      Debug.Assert(v.TypedIdent.Type is MapType);
      MapType mt = v.TypedIdent.Type as MapType;
      Debug.Assert(mt.Arguments.Length == 1);
      Variable OffsetParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_offset", mt.Arguments[0]));
      Variable SourceParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_source", mt.Arguments[0]));
      Debug.Assert(!(mt.Result is MapType));

      VariableSeq locals = new VariableSeq();
      Variable TrackVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "track", Microsoft.Boogie.Type.Bool));
      locals.Add(TrackVariable);

      List<BigBlock> bigblocks = new List<BigBlock>();

      CmdSeq simpleCmds = new CmdSeq();

      simpleCmds.Add(new HavocCmd(v.tok, new IdentifierExprSeq(new IdentifierExpr[] { new IdentifierExpr(v.tok, TrackVariable) })));

      simpleCmds.Add(MakeConditionalAssignment(VariableForThread(1, AccessHasOccurredVariable),
          Expr.And(new IdentifierExpr(v.tok, VariableForThread(1, PredicateParameter)), new IdentifierExpr(v.tok, TrackVariable)), Expr.True));
      simpleCmds.Add(MakeConditionalAssignment(VariableForThread(1, AccessOffsetXVariable),
          Expr.And(new IdentifierExpr(v.tok, VariableForThread(1, PredicateParameter)), new IdentifierExpr(v.tok, TrackVariable)),
          new IdentifierExpr(v.tok, VariableForThread(1, OffsetParameter))));
      simpleCmds.Add(MakeConditionalAssignment(VariableForThread(1, AccessSourceVariable),
          Expr.And(new IdentifierExpr(v.tok, VariableForThread(1, PredicateParameter)), new IdentifierExpr(v.tok, TrackVariable)),
          new IdentifierExpr(v.tok, VariableForThread(1, SourceParameter))));

      bigblocks.Add(new BigBlock(v.tok, "_LOG_" + Access + "", simpleCmds, null, null));

      LogAccessProcedure.Modifies.Add(new IdentifierExpr(Token.NoToken, VariableForThread(1, AccessHasOccurredVariable)));
      LogAccessProcedure.Modifies.Add(new IdentifierExpr(Token.NoToken, VariableForThread(1, AccessOffsetXVariable)));

      Implementation LogAccessImplementation = new Implementation(v.tok, "_LOG_" + Access + "_" + v.Name, new TypeVariableSeq(), LogAccessProcedure.InParams, new VariableSeq(), locals, new StmtList(bigblocks, v.tok));
      LogAccessImplementation.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

      LogAccessImplementation.Proc = LogAccessProcedure;

      verifier.Program.TopLevelDeclarations.Add(LogAccessProcedure);
      verifier.Program.TopLevelDeclarations.Add(LogAccessImplementation);
    }


    protected void AddCheckAccessProcedure(Variable v, string Access) {
      Procedure CheckAccessProcedure = MakeCheckAccessProcedureHeader(v, Access);

      Variable AccessHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, Access);
      Variable AccessOffsetXVariable = GPUVerifier.MakeOffsetVariable(v.Name, Access);

      Variable PredicateParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_P", Microsoft.Boogie.Type.Bool));

      Debug.Assert(v.TypedIdent.Type is MapType);
      MapType mt = v.TypedIdent.Type as MapType;
      Debug.Assert(mt.Arguments.Length == 1);
      Variable OffsetParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_offset", mt.Arguments[0]));
      Debug.Assert(!(mt.Result is MapType));

      if (Access.Equals("READ")) {
        // Check read by thread 2 does not conflict with write by thread 1
        Variable WriteHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE");
        Variable WriteOffsetVariable = GPUVerifier.MakeOffsetVariable(v.Name, "WRITE");
        Expr WriteReadGuard = new IdentifierExpr(Token.NoToken, VariableForThread(2, PredicateParameter));
        WriteReadGuard = Expr.And(WriteReadGuard, new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteHasOccurredVariable)));
        WriteReadGuard = Expr.And(WriteReadGuard, Expr.Eq(new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteOffsetVariable)),
                                        new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter))));

        if (!verifier.ArrayModelledAdversarially(v)) {
          WriteReadGuard = Expr.And(WriteReadGuard, Expr.Neq(
              new VariableDualiser(1, null, null).VisitExpr(
                MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, WriteOffsetVariable), "WRITE")),
              new VariableDualiser(2, null, null).VisitExpr(
                MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, OffsetParameter), "READ"))
              ));
        }

        if (verifier.KernelArrayInfo.getGroupSharedArrays().Contains(v)) {
          WriteReadGuard = Expr.And(WriteReadGuard, GPUVerifier.ThreadsInSameGroup());
        }

        WriteReadGuard = Expr.Not(WriteReadGuard);

        Requires NoWriteReadRaceRequires = new Requires(false, WriteReadGuard);
        QKeyValue kv = new QKeyValue(Token.NoToken, "write_read", new List<object>(), null);
        NoWriteReadRaceRequires.Attributes = new QKeyValue(Token.NoToken, "race", new List<object>(), kv);
        CheckAccessProcedure.Requires.Add(NoWriteReadRaceRequires);
      }
      else {
        Debug.Assert(Access.Equals("WRITE"));

        // Check write by thread 2 does not conflict with write by thread 1
        Variable WriteHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE");
        Variable WriteOffsetVariable = GPUVerifier.MakeOffsetVariable(v.Name, "WRITE");

        Expr WriteWriteGuard = new IdentifierExpr(Token.NoToken, VariableForThread(2, PredicateParameter));
        WriteWriteGuard = Expr.And(WriteWriteGuard, new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteHasOccurredVariable)));
        WriteWriteGuard = Expr.And(WriteWriteGuard, Expr.Eq(new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteOffsetVariable)),
                                        new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter))));
        if (!verifier.ArrayModelledAdversarially(v)) {
          WriteWriteGuard = Expr.And(WriteWriteGuard, Expr.Neq(
              new VariableDualiser(1, null, null).VisitExpr(
                MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, WriteOffsetVariable), "WRITE")),
              new VariableDualiser(2, null, null).VisitExpr(
                MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, OffsetParameter), "WRITE"))
              ));
        }

        if (verifier.KernelArrayInfo.getGroupSharedArrays().Contains(v)) {
          WriteWriteGuard = Expr.And(WriteWriteGuard, GPUVerifier.ThreadsInSameGroup());
        }

        WriteWriteGuard = Expr.Not(WriteWriteGuard);
        Requires NoWriteWriteRaceRequires = new Requires(false, WriteWriteGuard);
        QKeyValue kv = new QKeyValue(Token.NoToken, "write_write", new List<object>(), null);
        NoWriteWriteRaceRequires.Attributes = new QKeyValue(Token.NoToken, "race", new List<object>(), kv);
        CheckAccessProcedure.Requires.Add(NoWriteWriteRaceRequires);

        // Check write by thread 2 does not conflict with read by thread 1
        Variable ReadHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ");
        Variable ReadOffsetVariable = GPUVerifier.MakeOffsetVariable(v.Name, "READ");

        Expr ReadWriteGuard = new IdentifierExpr(Token.NoToken, VariableForThread(2, PredicateParameter));
        ReadWriteGuard = Expr.And(ReadWriteGuard, new IdentifierExpr(Token.NoToken, VariableForThread(1, ReadHasOccurredVariable)));
        ReadWriteGuard = Expr.And(ReadWriteGuard, Expr.Eq(new IdentifierExpr(Token.NoToken, VariableForThread(1, ReadOffsetVariable)),
                                        new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter))));
        if (!verifier.ArrayModelledAdversarially(v)) {
          ReadWriteGuard = Expr.And(ReadWriteGuard, Expr.Neq(
              new VariableDualiser(1, null, null).VisitExpr(
                MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, ReadOffsetVariable), "WRITE")),
              new VariableDualiser(2, null, null).VisitExpr(
                MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, OffsetParameter), "READ"))
              ));
        }

        if (verifier.KernelArrayInfo.getGroupSharedArrays().Contains(v)) {
          ReadWriteGuard = Expr.And(ReadWriteGuard, GPUVerifier.ThreadsInSameGroup());
        }

        ReadWriteGuard = Expr.Not(ReadWriteGuard);
        Requires NoReadWriteRaceRequires = new Requires(false, ReadWriteGuard);
        kv = new QKeyValue(Token.NoToken, "read_write", new List<object>(), null);
        NoReadWriteRaceRequires.Attributes = new QKeyValue(Token.NoToken, "race", new List<object>(), kv);
        CheckAccessProcedure.Requires.Add(NoReadWriteRaceRequires);

      }
      verifier.Program.TopLevelDeclarations.Add(CheckAccessProcedure);
    }



    private Variable VariableForThread(int thread, Variable v) {
      return new VariableDualiser(thread, null, null).VisitVariable(v.Clone() as Variable);
    }

    protected void AddLogRaceDeclarations(Variable v, String ReadOrWrite) {
      verifier.FindOrCreateAccessHasOccurredVariable(v.Name, ReadOrWrite);

      Debug.Assert(v.TypedIdent.Type is MapType);
      MapType mt = v.TypedIdent.Type as MapType;
      Debug.Assert(mt.Arguments.Length == 1);

      verifier.FindOrCreateOffsetVariable(v.Name, ReadOrWrite);
      verifier.FindOrCreateSourceVariable(v.Name, ReadOrWrite);

    }


    private static AssignCmd MakeConditionalAssignment(Variable lhs, Expr condition, Expr rhs) {
      List<AssignLhs> lhss = new List<AssignLhs>();
      List<Expr> rhss = new List<Expr>();
      lhss.Add(new SimpleAssignLhs(lhs.tok, new IdentifierExpr(lhs.tok, lhs)));
      rhss.Add(new NAryExpr(rhs.tok, new IfThenElse(rhs.tok), new ExprSeq(new Expr[] { condition, rhs, new IdentifierExpr(lhs.tok, lhs) })));
      return new AssignCmd(lhs.tok, lhss, rhss);
    }

    private Expr MakeAccessedIndex(Variable v, Expr offsetExpr, string AccessType) {
      Expr result = new IdentifierExpr(v.tok, v.Clone() as Variable);
      Debug.Assert(v.TypedIdent.Type is MapType);
      MapType mt = v.TypedIdent.Type as MapType;
      Debug.Assert(mt.Arguments.Length == 1);

      result = Expr.Select(result,
          new Expr[] { offsetExpr });
      Debug.Assert(!(mt.Result is MapType));
      return result;
    }

    protected void AddRequiresNoPendingAccess(Variable v) {
      IdentifierExpr ReadAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ")));
      IdentifierExpr WriteAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE")));

      verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.Not(WriteAccessOccurred1))));
    }

    private void AddRequiresSourceAccessZero(Variable v)
    {
      verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.Eq(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateSourceVariable(v.Name, "READ")),
                                                                        GPUVerifier.ZeroBV())));
      verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.Eq(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateSourceVariable(v.Name, "WRITE")),
                                                                        GPUVerifier.ZeroBV())));
    }

    public void AddSourceLocationLoopInvariants(Implementation impl, IRegion region)
    {
      foreach (string key in WriteAccessSourceLocations.Keys.Union(ReadAccessSourceLocations.Keys))
      {
        region.AddInvariant(BuildNoAccessInvariant(key, "WRITE"));
        region.AddInvariant(BuildNoAccessInvariant(key, "READ"));

        if (WriteAccessSourceLocations.ContainsKey(key))
        {
          region.AddInvariant(BuildPossibleSourceLocationsInvariant(key, "WRITE"));
        }
        else
        {
          region.AddInvariant(BuildAccessOccurredFalseInvariant(key, "WRITE"));
        }

        if (ReadAccessSourceLocations.ContainsKey(key))
        {
          region.AddInvariant(BuildPossibleSourceLocationsInvariant(key, "READ"));
        }
        else
        {
          region.AddInvariant(BuildAccessOccurredFalseInvariant(key, "READ"));
        }
      }
    }

    public void AddStandardSourceVariablePreconditions()
    {
      foreach (Declaration D in verifier.Program.TopLevelDeclarations.ToList())
      {
        if (!(D is Procedure))
        {
          continue;
        }
        Procedure Proc = D as Procedure;
        foreach (string key in WriteAccessSourceLocations.Keys.Union(ReadAccessSourceLocations.Keys))
        {
          Proc.Requires.Add(new Requires(false, BuildNoAccessExpr(key, "WRITE")));
          Proc.Requires.Add(new Requires(false, BuildNoAccessExpr(key, "READ")));

          if (WriteAccessSourceLocations.ContainsKey(key))
          {
            Proc.Requires.Add(new Requires(false, BuildPossibleSourceLocationsExpr(key, "WRITE")));
          }
          else
          {
            Proc.Requires.Add(new Requires(false, BuildAccessOccurredFalseExpr(key, "WRITE")));
          }

          if (ReadAccessSourceLocations.ContainsKey(key))
          {
            Proc.Requires.Add(new Requires(false, BuildPossibleSourceLocationsExpr(key, "READ")));
          }
          else
          {
            Proc.Requires.Add(new Requires(false, BuildAccessOccurredFalseExpr(key, "READ")));
          }
        }
      }
    }

    public void AddStandardSourceVariablePostconditions()
    {
      foreach (Declaration D in verifier.Program.TopLevelDeclarations.ToList())
      {
        if (!(D is Procedure))
        {
          continue;
        }
        Procedure Proc = D as Procedure;
        foreach (string key in WriteAccessSourceLocations.Keys.Union(ReadAccessSourceLocations.Keys))
        {
          Proc.Ensures.Add(new Ensures(false, BuildNoAccessExpr(key, "WRITE")));
          Proc.Ensures.Add(new Ensures(false, BuildNoAccessExpr(key, "READ")));

          if (WriteAccessSourceLocations.ContainsKey(key))
          {
            Proc.Ensures.Add(new Ensures(false, BuildPossibleSourceLocationsExpr(key, "WRITE")));
          }
          else
          {
            Proc.Ensures.Add(new Ensures(false, BuildAccessOccurredFalseExpr(key, "WRITE")));
          }

          if (ReadAccessSourceLocations.ContainsKey(key))
          {
            Proc.Ensures.Add(new Ensures(false, BuildPossibleSourceLocationsExpr(key, "READ")));
          }
          else
          {
            Proc.Ensures.Add(new Ensures(false, BuildAccessOccurredFalseExpr(key, "READ")));
          }
        }
      }
    }

    private Expr BuildAccessOccurredFalseExpr(string name, string AccessType)
    {
      return Expr.Imp(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateAccessHasOccurredVariable(name, AccessType)),
                                         Expr.False);
    }
    
    private AssertCmd BuildAccessOccurredFalseInvariant(string name, string AccessType)
    {
      return new AssertCmd(Token.NoToken, BuildAccessOccurredFalseExpr(name, AccessType));
    }

    private Expr BuildNoAccessExpr(string name, string AccessType)
    {
      return Expr.Imp(Expr.Not(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateAccessHasOccurredVariable(name, AccessType))),
                                                   Expr.Eq(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateSourceVariable(name, AccessType)),
                                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 32)));
    }

    private AssertCmd BuildNoAccessInvariant(string name, string AccessType)
    {
      return new AssertCmd(Token.NoToken, BuildNoAccessExpr(name, AccessType));
    }

    private Expr BuildPossibleSourceLocationsExpr(string name, string AccessType)
    {
      return Expr.Imp(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateAccessHasOccurredVariable(name, AccessType)),
                                         BuildDisjunctionFromAccessSourceLocations(name, AccessType));
    }

    private AssertCmd BuildPossibleSourceLocationsInvariant(string name, string AccessType)
    {
      return new AssertCmd(Token.NoToken, BuildPossibleSourceLocationsExpr(name, AccessType));
    }

    private Expr BuildDisjunctionFromAccessSourceLocations(string key, string AccessType)
    {
      List<Expr> sourceLocExprs = new List<Expr>();
      Dictionary<string, List<int>> AccessSourceLocations = (AccessType.Equals("WRITE")) ? WriteAccessSourceLocations : ReadAccessSourceLocations;
      foreach (int loc in AccessSourceLocations[key])
      {
        sourceLocExprs.Add(Expr.Eq(new IdentifierExpr(Token.NoToken, verifier.FindOrCreateSourceVariable(key, AccessType)),
                                   new LiteralExpr(Token.NoToken, BigNum.FromInt(loc), 32)));
      }
      return sourceLocExprs.Aggregate(Expr.Or);
    }

    protected Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwo) {
      Variable ReadOrWriteHasOccurred = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);
      ReadOrWriteHasOccurred.Name = ReadOrWriteHasOccurred.Name + "$" + OneOrTwo;
      ReadOrWriteHasOccurred.TypedIdent.Name = ReadOrWriteHasOccurred.TypedIdent.Name + "$" + OneOrTwo;
      Expr expr = Expr.Not(new IdentifierExpr(v.tok, ReadOrWriteHasOccurred));
      return expr;
    }


    protected void AddOffsetsSatisfyPredicatesCandidateInvariant(IRegion region, Variable v, string ReadOrWrite, List<Expr> preds) {
      if (preds.Count != 0) {
        Expr expr = AccessedOffsetsSatisfyPredicatesExpr(v, preds, ReadOrWrite, 1);
        verifier.AddCandidateInvariant(region, expr, "accessed offsets satisfy predicates");
      }
    }

    private Expr AccessedOffsetsSatisfyPredicatesExpr(Variable v, IEnumerable<Expr> offsets, string ReadOrWrite, int Thread) {
      return Expr.Imp(
              new IdentifierExpr(Token.NoToken, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite))),
              offsets.Aggregate(Expr.Or));
    }

    private Expr AccessedOffsetIsThreadLocalIdExpr(Variable v, string ReadOrWrite, int Thread) {
      return Expr.Imp(
                new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite))),
                Expr.Eq(new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetVariable(v.Name, ReadOrWrite))), 
                  new IdentifierExpr(v.tok, GPUVerifier.MakeThreadId("X", Thread))));
    }

    private Expr GlobalIdExpr(string dimension, int Thread) {
      return new VariableDualiser(Thread, null, null).VisitExpr(verifier.GlobalIdExpr(dimension).Clone() as Expr);
    }

    protected void AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(IRegion region, Variable v, Expr constant, string ReadOrWrite) {
      Expr expr = MakeCTimesLocalIdRangeExpression(v, constant, ReadOrWrite, 1);
      verifier.AddCandidateInvariant(region,
          expr, "accessed offset in range [ C*local_id, (C+1)*local_id )");
    }

    private Expr MakeCTimesLocalIdRangeExpression(Variable v, Expr constant, string ReadOrWrite, int Thread) {
      Expr CTimesLocalId = verifier.MakeBVMul(constant.Clone() as Expr,
          new IdentifierExpr(Token.NoToken, GPUVerifier.MakeThreadId("X", Thread)));

      Expr CTimesLocalIdPlusC = verifier.MakeBVAdd(verifier.MakeBVMul(constant.Clone() as Expr,
          new IdentifierExpr(Token.NoToken, GPUVerifier.MakeThreadId("X", Thread))), constant.Clone() as Expr);

      Expr CTimesLocalIdLeqAccessedOffset = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LEQ", CTimesLocalId, OffsetXExpr(v, ReadOrWrite, Thread));

      Expr AccessedOffsetLtCTimesLocalIdPlusC = verifier.MakeBVSlt(OffsetXExpr(v, ReadOrWrite, Thread), CTimesLocalIdPlusC);

      return Expr.Imp(
              AccessHasOccurred(v, ReadOrWrite, Thread),
              Expr.And(CTimesLocalIdLeqAccessedOffset, AccessedOffsetLtCTimesLocalIdPlusC));
    }

    private static IdentifierExpr AccessHasOccurred(Variable v, string ReadOrWrite, int Thread) {
      return new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite)));
    }

    private static IdentifierExpr OffsetXExpr(Variable v, string ReadOrWrite, int Thread) {
      return new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetVariable(v.Name, ReadOrWrite)));
    }

    protected void AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(IRegion region, Variable v, Expr constant, string ReadOrWrite) {
      Expr expr = MakeCTimesGloalIdRangeExpr(v, constant, ReadOrWrite, 1);
      verifier.AddCandidateInvariant(region,
          expr, "accessed offset in range [ C*global_id, (C+1)*global_id )");
    }

    private Expr MakeCTimesGloalIdRangeExpr(Variable v, Expr constant, string ReadOrWrite, int Thread) {
      Expr CTimesGlobalId = verifier.MakeBVMul(constant.Clone() as Expr,
          GlobalIdExpr("X", Thread));

      Expr CTimesGlobalIdPlusC = verifier.MakeBVAdd(verifier.MakeBVMul(constant.Clone() as Expr,
          GlobalIdExpr("X", Thread)), constant.Clone() as Expr);

      Expr CTimesGlobalIdLeqAccessedOffset = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LEQ", CTimesGlobalId, OffsetXExpr(v, ReadOrWrite, Thread));

      Expr AccessedOffsetLtCTimesGlobalIdPlusC = verifier.MakeBVSlt(OffsetXExpr(v, ReadOrWrite, Thread), CTimesGlobalIdPlusC);

      Expr implication = Expr.Imp(
              AccessHasOccurred(v, ReadOrWrite, Thread),
              Expr.And(CTimesGlobalIdLeqAccessedOffset, AccessedOffsetLtCTimesGlobalIdPlusC));
      return implication;
    }

    private void writeSourceLocToFile(QKeyValue kv, string path) {
      TextWriter tw = new StreamWriter(path, true);
      tw.Write("\n" + QKeyValue.FindIntAttribute(SourceLocationAttributes, "line", -1) 
                    + "#" + QKeyValue.FindIntAttribute(SourceLocationAttributes, "col", -1) 
                    + "#" + QKeyValue.FindStringAttribute(SourceLocationAttributes, "fname") 
                    + "#" + QKeyValue.FindStringAttribute(SourceLocationAttributes, "dir"));
      tw.Close();
    }
    
    protected void AddAccessedOffsetIsThreadLocalIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread) {
      verifier.AddCandidateRequires(Proc, AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread));
    }

    protected void AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread) {
      verifier.AddCandidateEnsures(Proc, AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread));
    }



  }



  class FindReferencesToNamedVariableVisitor : StandardVisitor {
    internal bool found = false;
    private string name;

    internal FindReferencesToNamedVariableVisitor(string name) {
      this.name = name;
    }

    public override Variable VisitVariable(Variable node) {
      if (GPUVerifier.StripThreadIdentifier(node.Name).Equals(name)) {
        found = true;
      }
      return base.VisitVariable(node);
    }
  }



}
