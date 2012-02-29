using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class Predicator
    {
        private bool AddPredicateParameter;
        private int WhileLoopCounter;
        private int IfCounter;
        private static HashSet<Microsoft.Boogie.Type> RequiredHavocVariables;

        internal Predicator(bool AddPredicateParameter)
        {
            this.AddPredicateParameter = AddPredicateParameter;
            WhileLoopCounter = 0;
            IfCounter = 0;
            RequiredHavocVariables = new HashSet<Microsoft.Boogie.Type>();
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

            impl.StructuredStmts = MakePredicated(impl.StructuredStmts, Predicate, null);
            AddPredicateLocalVariables(impl);            
        }


        private StmtList MakePredicated(StmtList sl, Expr predicate, IdentifierExpr EnclosingLoopPredicate)
        {
            StmtList result = new StmtList(new List<BigBlock>(), sl.EndCurly);

            foreach (BigBlock bodyBlock in sl.BigBlocks)
            {
                List<BigBlock> newBigBlocks = MakePredicated(bodyBlock, predicate, EnclosingLoopPredicate);
                foreach (BigBlock newBigBlock in newBigBlocks)
                {
                    result.BigBlocks.Add(newBigBlock);
                }
            }

            return result;

        }

        private List<BigBlock> MakePredicated(BigBlock b, Expr IncomingPredicate, IdentifierExpr EnclosingLoopPredicate)
        {
            // Not sure what to do about the transfer command

            List<BigBlock> result = new List<BigBlock>();

            BigBlock firstBigBlock = new BigBlock(b.tok, b.LabelName, new CmdSeq(), null, b.tc);
            result.Add(firstBigBlock);

            foreach (Cmd c in b.simpleCmds)
            {
                if (c is CallCmd)
                {

                    CallCmd Call = c as CallCmd;

                    List<Expr> NewIns = new List<Expr>();
                    NewIns.Add(IncomingPredicate);

                    foreach (Expr e in Call.Ins)
                    {
                        NewIns.Add(e);
                    }

                    CallCmd NewCallCmd = new CallCmd(Call.tok, Call.callee, NewIns, Call.Outs);

                    firstBigBlock.simpleCmds.Add(NewCallCmd);
                }
                else if (IncomingPredicate.Equals(Expr.True))
                {
                    firstBigBlock.simpleCmds.Add(c);
                }
                else if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);

                    ExprSeq iteArgs = new ExprSeq();
                    iteArgs.Add(IncomingPredicate);
                    iteArgs.Add(assign.Rhss.ElementAt(0));
                    iteArgs.Add(assign.Lhss.ElementAt(0).AsExpr);
                    NAryExpr ite = new NAryExpr(assign.tok, new IfThenElse(assign.tok), iteArgs);

                    List<Expr> newRhs = new List<Expr>();
                    newRhs.Add(ite);

                    AssignCmd newAssign = new AssignCmd(assign.tok, assign.Lhss, newRhs);

                    firstBigBlock.simpleCmds.Add(newAssign);
                }
                else if (c is HavocCmd)
                {
                    HavocCmd havoc = c as HavocCmd;
                    Debug.Assert(havoc.Vars.Length == 1);

                    Microsoft.Boogie.Type type = havoc.Vars[0].Decl.TypedIdent.Type;
                    Debug.Assert(type != null);

                    RequiredHavocVariables.Add(type);

                    IdentifierExpr HavocTempExpr = new IdentifierExpr(havoc.tok, new LocalVariable(havoc.tok, new TypedIdent(havoc.tok, "_HAVOC_" + type.ToString(), type)));
                    firstBigBlock.simpleCmds.Add(new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                        HavocTempExpr 
                    })));

                    List<AssignLhs> lhss = new List<AssignLhs>();
                    lhss.Add(new SimpleAssignLhs(havoc.tok, havoc.Vars[0]));

                    List<Expr> rhss = new List<Expr>();
                    rhss.Add(new NAryExpr(havoc.tok, new IfThenElse(havoc.tok), new ExprSeq(new Expr[] { IncomingPredicate, HavocTempExpr, havoc.Vars[0] })));

                    firstBigBlock.simpleCmds.Add(new AssignCmd(havoc.tok, lhss, rhss));

                }
                else if (c is AssertCmd)
                {
                    firstBigBlock.simpleCmds.Add(new AssertCmd(c.tok, Expr.Imp(IncomingPredicate, (c as AssertCmd).Expr)));
                }
                else if (c is AssumeCmd)
                {
                    firstBigBlock.simpleCmds.Add(new AssumeCmd(c.tok, Expr.Imp(IncomingPredicate, (c as AssumeCmd).Expr)));
                }
                else
                {
                    Debug.Assert(false);
                }
            }

            if (b.ec is WhileCmd)
            {
                string LoopPredicate = "_LC" + WhileLoopCounter;
                WhileLoopCounter++;

                TypedIdent LoopPredicateTypedIdent = new TypedIdent(b.ec.tok, LoopPredicate, Microsoft.Boogie.Type.Bool);

                IdentifierExpr PredicateExpr = new IdentifierExpr(b.ec.tok, new LocalVariable(b.ec.tok, LoopPredicateTypedIdent));
                Expr GuardExpr = (b.ec as WhileCmd).Guard;

                List<AssignLhs> WhilePredicateLhss = new List<AssignLhs>();
                WhilePredicateLhss.Add(new SimpleAssignLhs(b.ec.tok, PredicateExpr));

                List<Expr> WhilePredicateRhss = new List<Expr>();
                WhilePredicateRhss.Add(IncomingPredicate.Equals(Expr.True) ? GuardExpr : Expr.And(IncomingPredicate, GuardExpr));

                firstBigBlock.simpleCmds.Add(new AssignCmd(b.ec.tok, WhilePredicateLhss, WhilePredicateRhss));

                WhileCmd NewWhile = new WhileCmd(b.ec.tok, PredicateExpr, 
                    ProcessEnabledIntrinsics((b.ec as WhileCmd).Invariants, LoopPredicateTypedIdent), 
                    MakePredicated((b.ec as WhileCmd).Body, PredicateExpr, PredicateExpr));

                List<Expr> UpdatePredicateRhss = new List<Expr>();
                UpdatePredicateRhss.Add(Expr.And(PredicateExpr, GuardExpr));

                CmdSeq updateCmd = new CmdSeq();
                updateCmd.Add(new AssignCmd(b.ec.tok, WhilePredicateLhss, UpdatePredicateRhss));

                NewWhile.Body.BigBlocks.Add(new BigBlock(b.ec.tok, "update_" + LoopPredicate, updateCmd, null, null));

                firstBigBlock.ec = NewWhile;

            }
            else if (b.ec is IfCmd)
            {
                IfCmd IfCommand = b.ec as IfCmd;

                string IfPredicate = "_P" + IfCounter;
                IfCounter++;

                IdentifierExpr PredicateExpr = new IdentifierExpr(b.ec.tok, new LocalVariable(b.ec.tok, new TypedIdent(b.ec.tok, IfPredicate, Microsoft.Boogie.Type.Bool)));
                Expr GuardExpr = IfCommand.Guard;

                List<AssignLhs> IfPredicateLhss = new List<AssignLhs>();
                IfPredicateLhss.Add(new SimpleAssignLhs(b.ec.tok, PredicateExpr));

                List<Expr> IfPredicateRhss = new List<Expr>();
                IfPredicateRhss.Add(GuardExpr);

                firstBigBlock.simpleCmds.Add(new AssignCmd(b.ec.tok, IfPredicateLhss, IfPredicateRhss));

                Debug.Assert(IfCommand.elseIf == null); // We need to preprocess these away

                StmtList PredicatedThen = MakePredicated(IfCommand.thn, Expr.And(IncomingPredicate, PredicateExpr), EnclosingLoopPredicate);

                foreach (BigBlock bb in PredicatedThen.BigBlocks)
                {
                    result.Add(bb);
                }

                if (IfCommand.elseBlock != null)
                {
                    StmtList PredicatedElse = MakePredicated(IfCommand.elseBlock, Expr.And(IncomingPredicate, Expr.Not(PredicateExpr)), EnclosingLoopPredicate);

                    foreach (BigBlock bb in PredicatedElse.BigBlocks)
                    {
                        result.Add(bb);
                    }
                }




            }
            else if (b.ec is BreakCmd)
            {


                firstBigBlock.simpleCmds.Add(new AssignCmd(b.tok,
                    new List<AssignLhs>(new AssignLhs[] { new SimpleAssignLhs(b.tok, EnclosingLoopPredicate) }),
                    new List<Expr>(new Expr[] { new NAryExpr(b.tok, new IfThenElse(b.tok), new ExprSeq(new Expr[] { IncomingPredicate, Expr.False, EnclosingLoopPredicate })) })
                    ));
                firstBigBlock.ec = null;

            }
            else
            {
                Debug.Assert(b.ec == null);
            }

            return result;
        }

        private List<PredicateCmd> ProcessEnabledIntrinsics(List<PredicateCmd> invariants, TypedIdent currentPredicate)
        {
            List<PredicateCmd> result = new List<PredicateCmd>();

            foreach (PredicateCmd cmd in invariants)
            {
                result.Add(new AssertCmd(cmd.tok, ProcessEnabledIntrinsics(cmd.Expr, currentPredicate)));
            }

            return result;
        }

        private Expr ProcessEnabledIntrinsics(Expr expr, TypedIdent currentPredicate)
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
