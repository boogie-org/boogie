using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace GPUVerify
{
    class KernelDualiser
    {
        private GPUVerifier verifier;

        public KernelDualiser(GPUVerifier verifier)
        {
            this.verifier = verifier;
        }

        private string procName = null;

        internal void DualiseProcedure(Microsoft.Boogie.Procedure proc)
        {
            procName = proc.Name;

            bool HalfDualise = verifier.HalfDualisedProcedureNames.Contains(proc.Name);

            proc.Requires = DualiseRequires(proc.Requires);
            proc.Ensures = DualiseEnsures(proc.Ensures);

            proc.InParams = DualiseVariableSequence(proc.InParams, HalfDualise);
            proc.OutParams = DualiseVariableSequence(proc.OutParams, HalfDualise);
            IdentifierExprSeq NewModifies = new IdentifierExprSeq();
            foreach (IdentifierExpr v in proc.Modifies)
            {
                NewModifies.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitIdentifierExpr((IdentifierExpr)v.Clone()));
            }

            if (!HalfDualise)
            {
                foreach (IdentifierExpr v in proc.Modifies)
                {
                    if (!CommandLineOptions.Symmetry || !verifier.HalfDualisedVariableNames.Contains(v.Name))
                    {
                        NewModifies.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitIdentifierExpr((IdentifierExpr)v.Clone()));
                    }
                }
            }
            proc.Modifies = NewModifies;

            procName = null;
        }

        private RequiresSeq DualiseRequires(RequiresSeq requiresSeq)
        {
            RequiresSeq newRequires = new RequiresSeq();
            foreach (Requires r in requiresSeq)
            {
                newRequires.Add(new Requires(r.Free, new VariableDualiser(1, verifier.uniformityAnalyser, procName).
                    VisitExpr(r.Condition.Clone() as Expr)));

                if ((!CommandLineOptions.Symmetry || !ContainsAsymmetricExpression(r.Condition))
                    && !verifier.uniformityAnalyser.IsUniform(procName, r.Condition))
                {
                    newRequires.Add(new Requires(r.Free, new VariableDualiser(2, verifier.uniformityAnalyser, procName).
                        VisitExpr(r.Condition.Clone() as Expr)));
                }
            }
            return newRequires;
        }

        private EnsuresSeq DualiseEnsures(EnsuresSeq ensuresSeq)
        {
            EnsuresSeq newEnsures = new EnsuresSeq();
            foreach (Ensures e in ensuresSeq)
            {
                newEnsures.Add(new Ensures(e.Free, new VariableDualiser(1, verifier.uniformityAnalyser, procName).
                    VisitExpr(e.Condition.Clone() as Expr)));
                if ((!CommandLineOptions.Symmetry || !ContainsAsymmetricExpression(e.Condition))
                    && !verifier.uniformityAnalyser.IsUniform(procName, e.Condition))
                {
                    newEnsures.Add(new Ensures(e.Free, new VariableDualiser(2, verifier.uniformityAnalyser, procName).
                        VisitExpr(e.Condition.Clone() as Expr)));
                }
            }
            return newEnsures;
        }


        private StmtList MakeDual(StmtList stmtList, bool HalfDualise)
        {
            Contract.Requires(stmtList != null);

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(MakeDual(bodyBlock, HalfDualise));
            }

            return result;
        }

        private BigBlock MakeDual(BigBlock bb, bool HalfDualise)
        {
            // Not sure what to do about the transfer command

            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is CallCmd)
                {
                    CallCmd Call = c as CallCmd;

                    List<Expr> uniformNewIns = new List<Expr>();
                    List<Expr> nonUniformNewIns = new List<Expr>();
                    for (int i = 0; i < Call.Ins.Count; i++)
                    {
                        if (verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetInParameter(Call.callee, i)))
                        {
                            uniformNewIns.Add(Call.Ins[i]);
                        }
                        else
                        {
                            nonUniformNewIns.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(Call.Ins[i]));
                        }
                    }
                    if (!HalfDualise && !verifier.HalfDualisedProcedureNames.Contains(Call.callee))
                    {
                        for (int i = 0; i < Call.Ins.Count; i++)
                        {
                            if (!(verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetInParameter(Call.callee, i))))
                            {
                                nonUniformNewIns.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(Call.Ins[i]));
                            }
                        }
                    }

                    List<Expr> newIns = uniformNewIns;
                    newIns.AddRange(nonUniformNewIns);

                    List<IdentifierExpr> uniformNewOuts = new List<IdentifierExpr>();
                    List<IdentifierExpr> nonUniformNewOuts = new List<IdentifierExpr>();
                    for (int i = 0; i < Call.Outs.Count; i++)
                    {
                        if (verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetOutParameter(Call.callee, i)))
                        {
                            uniformNewOuts.Add(Call.Outs[i]);
                        }
                        else
                        {
                            nonUniformNewOuts.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(Call.Outs[i].Clone() as IdentifierExpr) as IdentifierExpr);
                        }

                    }
                    if (!HalfDualise && !verifier.HalfDualisedProcedureNames.Contains(Call.callee))
                    {
                        for (int i = 0; i < Call.Outs.Count; i++)
                        {
                            if (!(verifier.uniformityAnalyser.knowsOf(Call.callee) && verifier.uniformityAnalyser.IsUniform(Call.callee, verifier.uniformityAnalyser.GetOutParameter(Call.callee, i))))
                            {
                                nonUniformNewOuts.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(Call.Outs[i].Clone() as IdentifierExpr) as IdentifierExpr);
                            }
                        }
                    }

                    List<IdentifierExpr> newOuts = uniformNewOuts;
                    newOuts.AddRange(nonUniformNewOuts);

                    CallCmd NewCallCmd = new CallCmd(Call.tok, Call.callee, newIns, newOuts);

                    NewCallCmd.Proc = Call.Proc;

                    result.simpleCmds.Add(NewCallCmd);
                }
                else if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);

                    if (assign.Lhss[0] is SimpleAssignLhs &&
                        verifier.uniformityAnalyser.IsUniform(procName, (assign.Lhss[0] as SimpleAssignLhs).AssignedVariable.Name))
                    {
                        result.simpleCmds.Add(assign);
                    }
                    else
                    {
                        List<AssignLhs> newLhss = new List<AssignLhs>();
                        List<Expr> newRhss = new List<Expr>();

                        newLhss.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).Visit(assign.Lhss.ElementAt(0).Clone() as AssignLhs) as AssignLhs);

                        if (!HalfDualise)
                        {
                            newLhss.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).Visit(assign.Lhss.ElementAt(0).Clone() as AssignLhs) as AssignLhs);
                        }

                        newRhss.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(assign.Rhss.ElementAt(0).Clone() as Expr));

                        if (!HalfDualise)
                        {
                            newRhss.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(assign.Rhss.ElementAt(0).Clone() as Expr));
                        }

                        AssignCmd newAssign = new AssignCmd(assign.tok, newLhss, newRhss);

                        result.simpleCmds.Add(newAssign);
                    }
                }
                else if (c is HavocCmd)
                {
                    HavocCmd havoc = c as HavocCmd;
                    Debug.Assert(havoc.Vars.Length == 1);

                    HavocCmd newHavoc;

                    if (HalfDualise)
                    {
                        newHavoc = new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                            (IdentifierExpr)(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr)) 
                        }));
                    }
                    else
                    {
                        newHavoc = new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                            (IdentifierExpr)(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr)), 
                            (IdentifierExpr)(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr))
                        }));
                    }
                    result.simpleCmds.Add(newHavoc);
                }
                else if (c is AssertCmd)
                {
                    AssertCmd ass = c as AssertCmd;
                    if (HalfDualise || ContainsAsymmetricExpression(ass.Expr))
                    {
                        result.simpleCmds.Add(new AssertCmd(c.tok, new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr)));
                    }
                    else
                    {
                        result.simpleCmds.Add(new AssertCmd(c.tok, Expr.And(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr),
                            new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr))));
                    }
                }
                else if (c is AssumeCmd)
                {
                    AssumeCmd ass = c as AssumeCmd;
                    if (HalfDualise || ContainsAsymmetricExpression(ass.Expr))
                    {
                        result.simpleCmds.Add(new AssumeCmd(c.tok, new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr)));
                    }
                    else
                    {
                        result.simpleCmds.Add(new AssumeCmd(c.tok, Expr.And(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr),
                            new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(ass.Expr.Clone() as Expr))));
                    }
                }
                else
                {
                    Debug.Assert(false);
                }
            }

            if (bb.ec is WhileCmd)
            {
                Expr NewGuard;
                if (verifier.uniformityAnalyser.IsUniform(procName, (bb.ec as WhileCmd).Guard))
                {
                    NewGuard = (bb.ec as WhileCmd).Guard;
                }
                else
                {
                    NewGuard = Expr.Or(Dualise((bb.ec as WhileCmd).Guard, 1),
                            Dualise((bb.ec as WhileCmd).Guard, 2)
                    );
                }
                result.ec = new WhileCmd(bb.ec.tok,
                    NewGuard,
                    MakeDualInvariants((bb.ec as WhileCmd).Invariants), MakeDual((bb.ec as WhileCmd).Body, HalfDualise));
            }
            else if (bb.ec is IfCmd)
            {
                Debug.Assert(verifier.uniformityAnalyser.IsUniform(procName, (bb.ec as IfCmd).Guard));
                result.ec = new IfCmd(bb.ec.tok,
                    (bb.ec as IfCmd).Guard,
                             MakeDual((bb.ec as IfCmd).thn, HalfDualise),
                             null,
                             (bb.ec as IfCmd).elseBlock == null ? null : MakeDual((bb.ec as IfCmd).elseBlock, HalfDualise));

            }
            else if (bb.ec is BreakCmd)
            {
                result.ec = bb.ec;
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }

        private List<PredicateCmd> MakeDualInvariants(List<PredicateCmd> originalInvariants)
        {
            List<PredicateCmd> result = new List<PredicateCmd>();
            foreach (PredicateCmd p in originalInvariants)
            {
                {
                    PredicateCmd newP = new AssertCmd(p.tok,
                        Dualise(p.Expr, 1));
                    newP.Attributes = p.Attributes;
                    result.Add(newP);
                }
                if ((!CommandLineOptions.Symmetry || !ContainsAsymmetricExpression(p.Expr))
                    && !verifier.uniformityAnalyser.IsUniform(procName, p.Expr))
                {
                    PredicateCmd newP = new AssertCmd(p.tok, Dualise(p.Expr, 2));
                    newP.Attributes = p.Attributes;
                    result.Add(newP);
                }
            }

            return result;
        }

        private void MakeDualLocalVariables(Implementation impl, bool HalfDualise)
        {
            VariableSeq NewLocalVars = new VariableSeq();

            foreach (LocalVariable v in impl.LocVars)
            {
                if (verifier.uniformityAnalyser.IsUniform(procName, v.Name))
                {
                    NewLocalVars.Add (v);
                }
                else
                {
                    NewLocalVars.Add(
                        new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitVariable(v.Clone() as Variable));
                    if (!HalfDualise)
                    {
                        NewLocalVars.Add(
                            new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitVariable(v.Clone() as Variable));
                    }
                }
            }

            impl.LocVars = NewLocalVars;
        }

        private bool ContainsAsymmetricExpression(Expr expr)
        {
            AsymmetricExpressionFinder finder = new AsymmetricExpressionFinder();
            finder.VisitExpr(expr);
            return finder.foundAsymmetricExpr();
        }

        private VariableSeq DualiseVariableSequence(VariableSeq seq, bool HalfDualise)
        {
            VariableSeq uniform = new VariableSeq();
            VariableSeq nonuniform = new VariableSeq();

            foreach (Variable v in seq)
            {
                if (verifier.uniformityAnalyser.IsUniform(procName, v.Name))
                {
                    uniform.Add(v);
                }
                else
                {
                    nonuniform.Add(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitVariable((Variable)v.Clone()));
                }
            }

             if (!HalfDualise)
            {
                foreach (Variable v in seq)
                {
                    if (!verifier.uniformityAnalyser.IsUniform(procName, v.Name))
                    {
                        nonuniform.Add(new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitVariable((Variable)v.Clone()));
                    }
                }
            }

            VariableSeq result = uniform;
            result.AddRange(nonuniform);
            return result;
        }


        internal void DualiseImplementation(Implementation impl)
        {
            procName = impl.Name;

            bool HalfDualise = verifier.HalfDualisedProcedureNames.Contains(impl.Name);

            impl.InParams = DualiseVariableSequence(impl.InParams, HalfDualise);
            impl.OutParams = DualiseVariableSequence(impl.OutParams, HalfDualise);
            MakeDualLocalVariables(impl, HalfDualise);
            impl.StructuredStmts = MakeDual(impl.StructuredStmts, HalfDualise);

            procName = null;
        }

        private Expr Dualise(Expr expr, int thread)
        {
            return new VariableDualiser(thread, verifier.uniformityAnalyser, procName).VisitExpr(expr.Clone() as Expr);
        }

    }


}
