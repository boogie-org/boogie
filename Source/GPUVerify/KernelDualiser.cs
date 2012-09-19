using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify {
  class KernelDualiser {
    private GPUVerifier verifier;

    public KernelDualiser(GPUVerifier verifier) {
      this.verifier = verifier;
    }

    private string procName = null;

    internal void DualiseProcedure(Microsoft.Boogie.Procedure proc) {
      procName = proc.Name;

      proc.Requires = DualiseRequires(proc.Requires);
      proc.Ensures = DualiseEnsures(proc.Ensures);

      proc.InParams = DualiseVariableSequence(proc.InParams);
      proc.OutParams = DualiseVariableSequence(proc.OutParams);

      procName = null;
    }

    private RequiresSeq DualiseRequires(RequiresSeq requiresSeq) {
      RequiresSeq newRequires = new RequiresSeq();
      foreach (Requires r in requiresSeq) {
        newRequires.Add(MakeThreadSpecificRequires(r, 1));
        if (!ContainsAsymmetricExpression(r.Condition)
            && !verifier.uniformityAnalyser.IsUniform(procName, r.Condition)) {
          newRequires.Add(MakeThreadSpecificRequires(r, 2));
        }
      }
      return newRequires;
    }

    private EnsuresSeq DualiseEnsures(EnsuresSeq ensuresSeq) {
      EnsuresSeq newEnsures = new EnsuresSeq();
      foreach (Ensures e in ensuresSeq) {
        newEnsures.Add(MakeThreadSpecificEnsures(e, 1));
        if (!ContainsAsymmetricExpression(e.Condition)
            && !verifier.uniformityAnalyser.IsUniform(procName, e.Condition)) {
          newEnsures.Add(MakeThreadSpecificEnsures(e, 2));
        }
      }
      return newEnsures;
    }

    private Requires MakeThreadSpecificRequires(Requires r, int Thread) {
      Requires newR = new Requires(r.Free, new VariableDualiser(Thread, verifier.uniformityAnalyser, procName).
          VisitExpr(r.Condition.Clone() as Expr));
      newR.Attributes = MakeThreadSpecificAttributes(r.Attributes, Thread);
      return newR;
    }

    private Ensures MakeThreadSpecificEnsures(Ensures e, int Thread) {
      Ensures newE = new Ensures(e.Free, new VariableDualiser(Thread, verifier.uniformityAnalyser, procName).
          VisitExpr(e.Condition.Clone() as Expr));
      newE.Attributes = MakeThreadSpecificAttributes(e.Attributes, Thread);
      return newE;
    }

    private AssertCmd MakeThreadSpecificAssert(AssertCmd a, int Thread) {
      AssertCmd result = new AssertCmd(Token.NoToken, new VariableDualiser(Thread, 
        verifier.uniformityAnalyser, procName).VisitExpr(a.Expr.Clone() as Expr),
        MakeThreadSpecificAttributes(a.Attributes, Thread));
      return result;
    }

    private QKeyValue MakeThreadSpecificAttributes(QKeyValue attributes, int Thread) {
      if (attributes == null) {
        return null;
      }
      QKeyValue result = (QKeyValue)attributes.Clone();
      result.AddLast(new QKeyValue(Token.NoToken, "thread",
        new List<object>(new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(Thread)) }), null));
      return result;
    }

    private StmtList MakeDual(StmtList stmtList) {
      Contract.Requires(stmtList != null);

      StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

      foreach (BigBlock bodyBlock in stmtList.BigBlocks) {
        result.BigBlocks.Add(MakeDual(bodyBlock));
      }

      return result;
    }

    private void MakeDual(CmdSeq cs, Cmd c) {
      if (c is CallCmd) {
        CallCmd Call = c as CallCmd;

        List<Expr> uniformNewIns = new List<Expr>();
        List<Expr> nonUniformNewIns = new List<Expr>();
        for (int i = 0; i < Call.Ins.Count; i++) {
          if (verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetInParameter(Call.callee, i))) {
            uniformNewIns.Add(Call.Ins[i]);
          }
          else if(!verifier.OnlyThread2.Contains(Call.callee)) {
            nonUniformNewIns.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(Call.Ins[i]));
          }
        }
        for (int i = 0; i < Call.Ins.Count; i++) {
          if (
            !(verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetInParameter(Call.callee, i)))
            && !verifier.OnlyThread1.Contains(Call.callee)) {
            nonUniformNewIns.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(Call.Ins[i]));
          }
        }

        List<Expr> newIns = uniformNewIns;
        newIns.AddRange(nonUniformNewIns);

        List<IdentifierExpr> uniformNewOuts = new List<IdentifierExpr>();
        List<IdentifierExpr> nonUniformNewOuts = new List<IdentifierExpr>();
        for (int i = 0; i < Call.Outs.Count; i++) {
          if (verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetOutParameter(Call.callee, i))) {
            uniformNewOuts.Add(Call.Outs[i]);
          }
          else {
            nonUniformNewOuts.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(Call.Outs[i].Clone() as IdentifierExpr) as IdentifierExpr);
          }

        }
        for (int i = 0; i < Call.Outs.Count; i++) {
          if (!(verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetOutParameter(Call.callee, i)))) {
            nonUniformNewOuts.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(Call.Outs[i].Clone() as IdentifierExpr) as IdentifierExpr);
          }
        }

        List<IdentifierExpr> newOuts = uniformNewOuts;
        newOuts.AddRange(nonUniformNewOuts);

        CallCmd NewCallCmd = new CallCmd(Call.tok, Call.callee, newIns, newOuts);

        NewCallCmd.Proc = Call.Proc;

        NewCallCmd.Attributes = Call.Attributes;

        cs.Add(NewCallCmd);
      }
      else if (c is AssignCmd) {
        AssignCmd assign = c as AssignCmd;

        var vd1 = new VariableDualiser(1, verifier.uniformityAnalyser, procName);
        var vd2 = new VariableDualiser(2, verifier.uniformityAnalyser, procName);

        List<AssignLhs> lhss1 = new List<AssignLhs>();
        List<AssignLhs> lhss2 = new List<AssignLhs>();

        List<Expr> rhss1 = new List<Expr>();
        List<Expr> rhss2 = new List<Expr>();
 
        foreach(var pair in assign.Lhss.Zip(assign.Rhss)) {
          if(pair.Item1 is SimpleAssignLhs &&
            verifier.uniformityAnalyser.IsUniform(procName, 
            (pair.Item1 as SimpleAssignLhs).AssignedVariable.Name)) {
            lhss1.Add(pair.Item1);
            rhss1.Add(pair.Item2);
          } else {
            lhss1.Add(vd1.Visit(pair.Item1.Clone() as AssignLhs) as AssignLhs);
            lhss2.Add(vd2.Visit(pair.Item1.Clone() as AssignLhs) as AssignLhs);
            rhss1.Add(vd1.VisitExpr(pair.Item2.Clone() as Expr));
            rhss2.Add(vd2.VisitExpr(pair.Item2.Clone() as Expr));
          }
        }

        Debug.Assert(lhss1.Count > 0);
        cs.Add(new AssignCmd(Token.NoToken, lhss1, rhss1));

        if(lhss2.Count > 0) {
          cs.Add(new AssignCmd(Token.NoToken, lhss2, rhss2));
        }

      }
      else if (c is HavocCmd) {
        HavocCmd havoc = c as HavocCmd;
        Debug.Assert(havoc.Vars.Length == 1);

        HavocCmd newHavoc;

        newHavoc = new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                    (IdentifierExpr)(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr)), 
                    (IdentifierExpr)(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr))
                }));

        cs.Add(newHavoc);
      }
      else if (c is AssertCmd) {
        AssertCmd a = c as AssertCmd;

        if (QKeyValue.FindBoolAttribute(a.Attributes, "sourceloc")) {
          // This is just a location marker, so we do not dualise it
          cs.Add(new AssertCmd(Token.NoToken, new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(a.Expr.Clone() as Expr), 
            (QKeyValue)a.Attributes.Clone()));
        }
        else {
          cs.Add(MakeThreadSpecificAssert(a, 1));
          if (!ContainsAsymmetricExpression(a.Expr)) {
            cs.Add(MakeThreadSpecificAssert(a, 2));
          }
        }
      }
      else if (c is AssumeCmd) {
        AssumeCmd ass = c as AssumeCmd;
        if (QKeyValue.FindBoolAttribute(ass.Attributes, "backedge")) {
          cs.Add(new AssumeCmd(c.tok, Expr.Or(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr),
              new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr))));
        }
        else {
          cs.Add(new AssumeCmd(c.tok, new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr)));
          if (!ContainsAsymmetricExpression(ass.Expr)) {
            cs.Add(new AssumeCmd(c.tok, new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr)));
          }
        }
      }
      else {
        Debug.Assert(false);
      }
    }

    private BigBlock MakeDual(BigBlock bb) {
      // Not sure what to do about the transfer command

      BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

      foreach (Cmd c in bb.simpleCmds) {
        MakeDual(result.simpleCmds, c);
      }

      if (bb.ec is WhileCmd) {
        Expr NewGuard;
        if (verifier.uniformityAnalyser.IsUniform(procName, (bb.ec as WhileCmd).Guard)) {
          NewGuard = (bb.ec as WhileCmd).Guard;
        }
        else {
          NewGuard = Expr.Or(Dualise((bb.ec as WhileCmd).Guard, 1),
                  Dualise((bb.ec as WhileCmd).Guard, 2)
          );
        }
        result.ec = new WhileCmd(bb.ec.tok,
            NewGuard,
            MakeDualInvariants((bb.ec as WhileCmd).Invariants), MakeDual((bb.ec as WhileCmd).Body));
      }
      else if (bb.ec is IfCmd) {
        Debug.Assert(verifier.uniformityAnalyser.IsUniform(procName, (bb.ec as IfCmd).Guard));
        result.ec = new IfCmd(bb.ec.tok,
            (bb.ec as IfCmd).Guard,
                     MakeDual((bb.ec as IfCmd).thn),
                     null,
                     (bb.ec as IfCmd).elseBlock == null ? null : MakeDual((bb.ec as IfCmd).elseBlock));

      }
      else if (bb.ec is BreakCmd) {
        result.ec = bb.ec;
      }
      else {
        Debug.Assert(bb.ec == null);
      }

      return result;

    }

    private Block MakeDual(Block b) {
      var newCmds = new CmdSeq();
      foreach (Cmd c in b.Cmds) {
        MakeDual(newCmds, c);
      }
      b.Cmds = newCmds;
      return b;
    }

    private List<PredicateCmd> MakeDualInvariants(List<PredicateCmd> originalInvariants) {
      List<PredicateCmd> result = new List<PredicateCmd>();
      foreach (PredicateCmd p in originalInvariants) {
        {
          PredicateCmd newP = new AssertCmd(p.tok,
              Dualise(p.Expr, 1));
          newP.Attributes = p.Attributes;
          result.Add(newP);
        }
        if (!ContainsAsymmetricExpression(p.Expr)
            && !verifier.uniformityAnalyser.IsUniform(procName, p.Expr)) {
          PredicateCmd newP = new AssertCmd(p.tok, Dualise(p.Expr, 2));
          newP.Attributes = p.Attributes;
          result.Add(newP);
        }
      }

      return result;
    }

    private void MakeDualLocalVariables(Implementation impl) {
      VariableSeq NewLocalVars = new VariableSeq();

      foreach (LocalVariable v in impl.LocVars) {
        if (verifier.uniformityAnalyser.IsUniform(procName, v.Name)) {
          NewLocalVars.Add(v);
        }
        else {
          NewLocalVars.Add(
              new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitVariable(v.Clone() as Variable));
          NewLocalVars.Add(
              new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitVariable(v.Clone() as Variable));
        }
      }

      impl.LocVars = NewLocalVars;
    }

    private bool ContainsAsymmetricExpression(Expr expr) {
      AsymmetricExpressionFinder finder = new AsymmetricExpressionFinder();
      finder.VisitExpr(expr);
      return finder.foundAsymmetricExpr();
    }

    private VariableSeq DualiseVariableSequence(VariableSeq seq) {
      VariableSeq uniform = new VariableSeq();
      VariableSeq nonuniform = new VariableSeq();

      foreach (Variable v in seq) {
        if (verifier.uniformityAnalyser.IsUniform(procName, v.Name)) {
          uniform.Add(v);
        }
        else {
          nonuniform.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitVariable((Variable)v.Clone()));
        }
      }

      foreach (Variable v in seq) {
        if (!verifier.uniformityAnalyser.IsUniform(procName, v.Name)) {
          nonuniform.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitVariable((Variable)v.Clone()));
        }
      }

      VariableSeq result = uniform;
      result.AddRange(nonuniform);
      return result;
    }


    internal void DualiseImplementation(Implementation impl, bool unstructured) {
      procName = impl.Name;

      impl.InParams = DualiseVariableSequence(impl.InParams);
      impl.OutParams = DualiseVariableSequence(impl.OutParams);
      MakeDualLocalVariables(impl);
      if (unstructured)
        impl.Blocks = new List<Block>(impl.Blocks.Select(MakeDual));
      else
        impl.StructuredStmts = MakeDual(impl.StructuredStmts);

      procName = null;
    }

    private Expr Dualise(Expr expr, int thread) {
      return new VariableDualiser(thread, verifier.uniformityAnalyser, procName).VisitExpr(expr.Clone() as Expr);
    }

  }

}
