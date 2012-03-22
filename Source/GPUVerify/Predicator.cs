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
        private Stack<IdentifierExpr> enclosingLoopPredicate;

        internal Predicator(GPUVerifier verifier, bool AddPredicateParameter) : base(verifier)
        {
            this.AddPredicateParameter = AddPredicateParameter;
            WhileLoopCounter = 0;
            IfCounter = 0;
            RequiredHavocVariables = new HashSet<Microsoft.Boogie.Type>();
            predicate = new Stack<Expr>();
            enclosingLoopPredicate = new Stack<IdentifierExpr>();
        }

        internal void transform(Implementation impl)
        {
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
            enclosingLoopPredicate.Push(null);

            impl.StructuredStmts = VisitStmtList(impl.StructuredStmts);

            AddPredicateLocalVariables(impl);            
        }

        public override CmdSeq VisitCmd(Cmd c)
        {
            if (c is CallCmd || !predicate.Peek().Equals(Expr.True))
            {
                return base.VisitCmd(c);
            }

            return new CmdSeq(new Cmd[] { c });

        }

        public override CmdSeq VisitCallCmd(CallCmd Call)
        {
            List<Expr> NewIns = new List<Expr>();
            NewIns.Add(predicate.Peek());

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
            iteArgs.Add(predicate.Peek());
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

            Microsoft.Boogie.Type type = havoc.Vars[0].Decl.TypedIdent.Type;
            Debug.Assert(type != null);

            RequiredHavocVariables.Add(type);

            IdentifierExpr HavocTempExpr = new IdentifierExpr(havoc.tok, new LocalVariable(havoc.tok, new TypedIdent(havoc.tok, "_HAVOC_" + type.ToString(), type)));
            result.Add(new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                        HavocTempExpr 
                    })));

            List<AssignLhs> lhss = new List<AssignLhs>();
            lhss.Add(new SimpleAssignLhs(havoc.tok, havoc.Vars[0]));

            List<Expr> rhss = new List<Expr>();
            rhss.Add(new NAryExpr(havoc.tok, new IfThenElse(havoc.tok), new ExprSeq(
                new Expr[] { predicate.Peek(), HavocTempExpr, havoc.Vars[0] })));

            result.Add(new AssignCmd(havoc.tok, lhss, rhss));

            return result;

        }

        public override CmdSeq VisitAssertCmd(AssertCmd assert)
        {
            return new CmdSeq(new Cmd[] {
                new AssertCmd(assert.tok, Expr.Imp(predicate.Peek(), assert.Expr))
            });
        }

        public override CmdSeq VisitAssumeCmd(AssumeCmd assume)
        {
            return new CmdSeq(new Cmd[] {
                new AssumeCmd(assume.tok, Expr.Imp(predicate.Peek(), assume.Expr))
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

                string LoopPredicate = "_LC" + WhileLoopCounter;
                WhileLoopCounter++;

                TypedIdent LoopPredicateTypedIdent = new TypedIdent(whileCmd.tok, LoopPredicate, Microsoft.Boogie.Type.Bool);

                IdentifierExpr PredicateExpr = new IdentifierExpr(whileCmd.tok, new LocalVariable(whileCmd.tok, LoopPredicateTypedIdent));
                Expr GuardExpr = whileCmd.Guard;

                List<AssignLhs> WhilePredicateLhss = new List<AssignLhs>();
                WhilePredicateLhss.Add(new SimpleAssignLhs(whileCmd.tok, PredicateExpr));

                List<Expr> WhilePredicateRhss = new List<Expr>();
                WhilePredicateRhss.Add(predicate.Peek().Equals(Expr.True) ? GuardExpr : Expr.And(predicate.Peek(), GuardExpr));

                firstBigBlock.simpleCmds.Add(new AssignCmd(whileCmd.tok, WhilePredicateLhss, WhilePredicateRhss));

                predicate.Push(PredicateExpr);
                enclosingLoopPredicate.Push(PredicateExpr);
                WhileCmd NewWhile = new WhileCmd(whileCmd.tok, PredicateExpr,
                    VisitWhileInvariants(whileCmd.Invariants),
                    VisitStmtList(whileCmd.Body));
                enclosingLoopPredicate.Pop();
                predicate.Pop();

                List<Expr> UpdatePredicateRhss = new List<Expr>();
                UpdatePredicateRhss.Add(Expr.And(PredicateExpr, GuardExpr));

                CmdSeq updateCmd = new CmdSeq();
                updateCmd.Add(new AssignCmd(whileCmd.tok, WhilePredicateLhss, UpdatePredicateRhss));

                NewWhile.Body.BigBlocks.Add(new BigBlock(whileCmd.tok, "update_" + LoopPredicate, updateCmd, null, null));

                firstBigBlock.ec = NewWhile;

            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;

                string IfPredicate = "_P" + IfCounter;
                IfCounter++;

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

                if(IfCommand.elseIf != null)
                {
                    throw new InvalidOperationException();
                }

                if (IfCommand.elseBlock != null)
                {
                    predicate.Push(Expr.And(predicate.Peek(), Expr.Not(PredicateExpr)));
                    StmtList PredicatedElse = VisitStmtList(IfCommand.elseBlock);
                    predicate.Pop();
                    result.AddRange(PredicatedElse.BigBlocks);
                }

            }
            else if (bb.ec is BreakCmd)
            {
                firstBigBlock.simpleCmds.Add(new AssignCmd(bb.tok,
                    new List<AssignLhs>(new AssignLhs[] { new SimpleAssignLhs(bb.tok, enclosingLoopPredicate.Peek()) }),
                    new List<Expr>(new Expr[] { new NAryExpr(bb.tok, new IfThenElse(bb.tok), new ExprSeq(
                        new Expr[] { predicate.Peek(), Expr.False, enclosingLoopPredicate.Peek() })) })
                    ));
                firstBigBlock.ec = null;
            }
            else if (bb.ec != null)
            {
                throw new InvalidOperationException();
            }

            return result;

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

        public override List<PredicateCmd> VisitWhileInvariants(List<PredicateCmd> invariants)
        {
            List<PredicateCmd> result = new List<PredicateCmd>();

            foreach (PredicateCmd cmd in invariants)
            {
                result.Add(new AssertCmd(cmd.tok, ProcessEnabledIntrinsics(cmd.Expr, enclosingLoopPredicate.Peek().Decl.TypedIdent)));
            }

            return result;
        }

        internal static Expr ProcessEnabledIntrinsics(Expr expr, TypedIdent currentPredicate)
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
