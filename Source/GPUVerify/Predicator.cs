using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class Predicator : StructuredProgramVisitor
    {
        private bool AddPredicateParameter;
        private int WhileLoopCounter;
        private int IfCounter;
        private static HashSet<Microsoft.Boogie.Type> RequiredHavocVariables;

        private Stack<Expr> predicate;
        private Stack<Expr> enclosingLoopPredicate;

        private IdentifierExpr returnPredicate;
        private bool hitNonuniformReturn;

        private Implementation impl = null;

        internal Predicator(GPUVerifier verifier, bool AddPredicateParameter) : base(verifier)
        {
            this.AddPredicateParameter = AddPredicateParameter;
            WhileLoopCounter = 0;
            IfCounter = 0;
            RequiredHavocVariables = new HashSet<Microsoft.Boogie.Type>();
            predicate = new Stack<Expr>();
            enclosingLoopPredicate = new Stack<Expr>();
        }

        internal void transform(Implementation impl)
        {
            this.impl = impl;
            Expr Predicate;

            if (AddPredicateParameter)
            {
                VariableSeq NewIns = new VariableSeq();
                Variable PredicateVariable = new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_P", Microsoft.Boogie.Type.Bool));
                NewIns.Add(PredicateVariable);
                foreach (Variable v in impl.InParams)
                {
                    NewIns.Add(v);
                }
                impl.InParams = NewIns;
                Predicate = new IdentifierExpr(impl.tok, PredicateVariable);
            }
            else
            {
                Predicate = Expr.True;
            }

            predicate.Push(Predicate);
            enclosingLoopPredicate.Push(Expr.True);

            Variable ReturnPredicateVariable = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "_R", Microsoft.Boogie.Type.Bool));
            returnPredicate = new IdentifierExpr(Token.NoToken, ReturnPredicateVariable);
            hitNonuniformReturn = false;

            impl.StructuredStmts = VisitStmtList(impl.StructuredStmts);

            AddPredicateLocalVariables(impl);

            if (hitNonuniformReturn)
            {
                impl.LocVars.Add(ReturnPredicateVariable);
                verifier.uniformityAnalyser.AddNonUniform(impl.Name, ReturnPredicateVariable.Name);

                CmdSeq newSimpleCmds = new CmdSeq();
                newSimpleCmds.Add(new AssignCmd(Token.NoToken,
                    new List<AssignLhs>(new AssignLhs[] { new SimpleAssignLhs(Token.NoToken, returnPredicate) }),
                    new List<Expr>(new Expr[] { Expr.True })));
                foreach (Cmd c in impl.StructuredStmts.BigBlocks[0].simpleCmds)
                {
                    newSimpleCmds.Add(c);
                }
                impl.StructuredStmts.BigBlocks[0].simpleCmds = newSimpleCmds;
            }

            this.impl = null;
        }

        public override CmdSeq VisitCmd(Cmd c)
        {
            if (c is CallCmd || !GetCurrentPredicate().Equals(Expr.True))
            {
                return base.VisitCmd(c);
            }

            return new CmdSeq(new Cmd[] { c });

        }

        public override CmdSeq VisitCallCmd(CallCmd Call)
        {
            List<Expr> NewIns = new List<Expr>();

            if (!verifier.uniformityAnalyser.IsUniform(Call.callee))
            {
                NewIns.Add(GetCurrentPredicate());
            }

            foreach (Expr e in Call.Ins)
            {
                NewIns.Add(e);
            }

            CallCmd newCallCmd = new CallCmd(Call.tok, Call.callee, NewIns, Call.Outs);
            newCallCmd.Proc = Call.Proc;

            return new CmdSeq(
                new Cmd[] { newCallCmd });

        }

        public override CmdSeq VisitAssignCmd(AssignCmd assign)
        {
            Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);

            ExprSeq iteArgs = new ExprSeq();
            iteArgs.Add(GetCurrentPredicate());
            iteArgs.Add(assign.Rhss.ElementAt(0));
            iteArgs.Add(assign.Lhss.ElementAt(0).AsExpr);
            NAryExpr ite = new NAryExpr(assign.tok, new IfThenElse(assign.tok), iteArgs);

            List<Expr> newRhs = new List<Expr>();
            newRhs.Add(ite);

            return new CmdSeq(new Cmd[] { new AssignCmd(assign.tok, assign.Lhss, newRhs) });

        }

        public override CmdSeq VisitHavocCmd(HavocCmd havoc)
        {
            CmdSeq result = new CmdSeq();

            Debug.Assert(havoc.Vars.Length == 1);

            if (GetCurrentPredicate().Equals(Expr.True))
            {
                result.Add(havoc);
                return result;
            }

            Microsoft.Boogie.Type type = havoc.Vars[0].Decl.TypedIdent.Type;
            Debug.Assert(type != null);

            IdentifierExpr HavocTempExpr = new IdentifierExpr(havoc.tok, new LocalVariable(havoc.tok, new TypedIdent(havoc.tok, "_HAVOC_" + type.ToString(), type)));

            if (!RequiredHavocVariables.Contains(type))
            {
                verifier.uniformityAnalyser.AddNonUniform(impl.Name, HavocTempExpr.Decl.Name);
            }

            RequiredHavocVariables.Add(type);

            result.Add(new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                        HavocTempExpr 
                    })));

            List<AssignLhs> lhss = new List<AssignLhs>();
            lhss.Add(new SimpleAssignLhs(havoc.tok, havoc.Vars[0]));

            List<Expr> rhss = new List<Expr>();
            rhss.Add(new NAryExpr(havoc.tok, new IfThenElse(havoc.tok), new ExprSeq(
                new Expr[] { GetCurrentPredicate(), HavocTempExpr, havoc.Vars[0] })));

            result.Add(new AssignCmd(havoc.tok, lhss, rhss));

            return result;

        }

        public override CmdSeq VisitAssertCmd(AssertCmd assert)
        {
            return new CmdSeq(new Cmd[] {
                new AssertCmd(assert.tok, Expr.Imp(GetCurrentPredicate(), assert.Expr))
            });
        }

        public override CmdSeq VisitAssumeCmd(AssumeCmd assume)
        {
            return new CmdSeq(new Cmd[] {
                new AssumeCmd(assume.tok, Expr.Imp(GetCurrentPredicate(), assume.Expr))
            });
        }

        public override List<BigBlock> VisitBigBlock(BigBlock bb)
        {
            BigBlock firstBigBlock = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            List<BigBlock> result = new List<BigBlock>();
            result.Add(firstBigBlock);

            firstBigBlock.simpleCmds = VisitCmdSeq(bb.simpleCmds);

            if (bb.ec is WhileCmd)
            {
                WhileCmd whileCmd = bb.ec as WhileCmd;

                if (!hitNonuniformReturn && verifier.uniformityAnalyser.HasNonuniformReturn(impl.Name, whileCmd))
                {
                    hitNonuniformReturn = true;
                }

                Expr PredicateExpr;
                Expr NewGuard;
                string LoopPredicate = null;
                List<AssignLhs> WhilePredicateLhss = new List<AssignLhs>();

                if (!enclosingLoopPredicate.Peek().Equals(Expr.True) || 
                    !verifier.uniformityAnalyser.IsUniform(impl.Name, whileCmd.Guard) ||
                    !verifier.uniformityAnalyser.IsUniform(impl.Name, whileCmd))
                {
                    LoopPredicate = "_LC" + WhileLoopCounter;
                    WhileLoopCounter++;

                    verifier.uniformityAnalyser.AddNonUniform(impl.Name, LoopPredicate);

                    TypedIdent LoopPredicateTypedIdent = new TypedIdent(whileCmd.tok, LoopPredicate, Microsoft.Boogie.Type.Bool);

                    PredicateExpr = new IdentifierExpr(whileCmd.tok, new LocalVariable(whileCmd.tok, LoopPredicateTypedIdent));

                    WhilePredicateLhss.Add(new SimpleAssignLhs(whileCmd.tok, PredicateExpr as IdentifierExpr));

                    List<Expr> WhilePredicateRhss = new List<Expr>();
                    WhilePredicateRhss.Add(GetCurrentPredicate().Equals(Expr.True) ? 
                        whileCmd.Guard : Expr.And(GetCurrentPredicate(), whileCmd.Guard));

                    firstBigBlock.simpleCmds.Add(new AssignCmd(whileCmd.tok, WhilePredicateLhss, WhilePredicateRhss));

                    NewGuard = PredicateExpr;
                }
                else
                {
                    PredicateExpr = enclosingLoopPredicate.Peek();
                    NewGuard = whileCmd.Guard;
                }

                predicate.Push(PredicateExpr);
                enclosingLoopPredicate.Push(PredicateExpr);
                WhileCmd NewWhile = new WhileCmd(whileCmd.tok, NewGuard,
                    VisitWhileInvariants(whileCmd.Invariants, NewGuard),
                    VisitStmtList(whileCmd.Body));
                enclosingLoopPredicate.Pop();
                predicate.Pop();

                if (!enclosingLoopPredicate.Peek().Equals(Expr.True) || !verifier.uniformityAnalyser.IsUniform(impl.Name, whileCmd.Guard))
                {
                    List<Expr> UpdatePredicateRhss = new List<Expr>();
                    UpdatePredicateRhss.Add(Expr.And(PredicateExpr, whileCmd.Guard));

                    CmdSeq updateCmd = new CmdSeq();
                    updateCmd.Add(new AssignCmd(whileCmd.tok, WhilePredicateLhss, UpdatePredicateRhss));

                    NewWhile.Body.BigBlocks.Add(new BigBlock(whileCmd.tok, "update_" + LoopPredicate, updateCmd, null, null));
                }

                firstBigBlock.ec = NewWhile;

            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;

                if (IfCommand.elseIf != null)
                {
                    throw new InvalidOperationException();
                }

                if (GetCurrentPredicate().Equals(Expr.True) && verifier.uniformityAnalyser.IsUniform(impl.Name, IfCommand.Guard))
                {
                    firstBigBlock.ec = 
                        new IfCmd(IfCommand.tok, IfCommand.Guard, VisitStmtList(IfCommand.thn),
                        null, IfCommand.elseBlock == null ? null : VisitStmtList(IfCommand.elseBlock));
                }
                else
                {
                    string IfPredicate = "_P" + IfCounter;
                    IfCounter++;

                    verifier.uniformityAnalyser.AddNonUniform(impl.Name, IfPredicate);

                    IdentifierExpr PredicateExpr = new IdentifierExpr(IfCommand.tok,
                        new LocalVariable(IfCommand.tok, new TypedIdent(IfCommand.tok, IfPredicate, Microsoft.Boogie.Type.Bool)));
                    Expr GuardExpr = IfCommand.Guard;

                    List<AssignLhs> IfPredicateLhss = new List<AssignLhs>();
                    IfPredicateLhss.Add(new SimpleAssignLhs(IfCommand.tok, PredicateExpr));

                    List<Expr> IfPredicateRhss = new List<Expr>();
                    IfPredicateRhss.Add(GuardExpr);

                    firstBigBlock.simpleCmds.Add(new AssignCmd(IfCommand.tok, IfPredicateLhss, IfPredicateRhss));

                    Debug.Assert(IfCommand.elseIf == null); // We need to preprocess these away

                    predicate.Push(Expr.And(predicate.Peek(), PredicateExpr));
                    StmtList PredicatedThen = VisitStmtList(IfCommand.thn);
                    predicate.Pop();
                    result.AddRange(PredicatedThen.BigBlocks);

                    if (IfCommand.elseBlock != null)
                    {
                        predicate.Push(Expr.And(predicate.Peek(), Expr.Not(PredicateExpr)));
                        StmtList PredicatedElse = VisitStmtList(IfCommand.elseBlock);
                        predicate.Pop();
                        result.AddRange(PredicatedElse.BigBlocks);
                    }
                }

            }
            else if (bb.ec is BreakCmd)
            {
                if (enclosingLoopPredicate.Peek().Equals(Expr.True))
                {
                    firstBigBlock.ec = bb.ec;
                }
                else
                {
                    firstBigBlock.simpleCmds.Add(new AssignCmd(bb.tok,
                        new List<AssignLhs>(new AssignLhs[] { 
                            new SimpleAssignLhs(bb.tok, enclosingLoopPredicate.Peek() as IdentifierExpr) }),
                        new List<Expr>(new Expr[] { new NAryExpr(bb.tok, new IfThenElse(bb.tok), new ExprSeq(
                            new Expr[] { GetCurrentPredicate(), Expr.False, enclosingLoopPredicate.Peek() })) })
                        ));
                    firstBigBlock.ec = null;
                }
            }
            else if (bb.ec != null)
            {
                throw new InvalidOperationException();
            }

            if (bb.tc is ReturnCmd)
            {
                if (!GetCurrentPredicate().Equals(Expr.True))
                {
                    hitNonuniformReturn = true;
                }

                if (hitNonuniformReturn)
                {
                    // Add a new big block with just the assignment
                    AssignCmd assignToReturnPredicate = new AssignCmd(Token.NoToken,
                        new List<AssignLhs>(new AssignLhs[] { new SimpleAssignLhs(Token.NoToken, returnPredicate) }),
                        new List<Expr>(new Expr[] { Expr.And(returnPredicate, Expr.Not(predicate.Peek ())) }));

                    result.Add(new BigBlock(Token.NoToken, null, new CmdSeq(new Cmd[] { assignToReturnPredicate }), null, null));
                    firstBigBlock.tc = null;
                }

            }

            result[result.Count - 1].tc = firstBigBlock.tc;

            if (result.Count > 1)
            {
                firstBigBlock.tc = null;
            }

            return result;

        }

        private Expr GetCurrentPredicate()
        {
            if (!hitNonuniformReturn)
            {
                return predicate.Peek();
            }

            return Expr.And(predicate.Peek(), returnPredicate);
        }

        public override IfCmd VisitIfCmd(IfCmd ifCmd)
        {
            throw new InvalidOperationException();
        }

        public override WhileCmd VisitWhileCmd(WhileCmd whileCmd)
        {
            throw new InvalidOperationException();
        }

        public override BreakCmd VisitBreakCmd(BreakCmd breakCmd)
        {
            throw new InvalidOperationException();
        }

        public override List<PredicateCmd> VisitWhileInvariants(List<PredicateCmd> invariants, Expr WhileGuard)
        {
            List<PredicateCmd> result = new List<PredicateCmd>();

            foreach (PredicateCmd cmd in invariants)
            {
                result.Add(new AssertCmd(cmd.tok, ProcessEnabledIntrinsics(
                    cmd.Expr, WhileGuard)));
            }

            return result;
        }

        internal static Expr ProcessEnabledIntrinsics(Expr expr, Expr currentPredicate)
        {
            return new EnabledToPredicateVisitor(currentPredicate).VisitExpr(expr);
        }


        private void AddPredicateLocalVariables(Implementation impl)
        {
            for (int i = 0; i < IfCounter; i++)
            {
                impl.LocVars.Add(new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_P" + i, Microsoft.Boogie.Type.Bool)));
            }
            for (int i = 0; i < WhileLoopCounter; i++)
            {
                impl.LocVars.Add(new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_LC" + i, Microsoft.Boogie.Type.Bool)));
            }
            foreach (Microsoft.Boogie.Type t in RequiredHavocVariables)
            {
                impl.LocVars.Add(new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_HAVOC_" + t.ToString(), t)));
            }

        }

    }
}
