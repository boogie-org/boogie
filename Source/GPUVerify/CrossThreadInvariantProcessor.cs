using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class CrossThreadInvariantProcessor : StandardVisitor
    {
        private GPUVerifier verifier;
        private string procName;

        public CrossThreadInvariantProcessor(GPUVerifier verifier, string procName)
        {
            this.verifier = verifier;
            this.procName = procName;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            
            if (node.Fun is FunctionCall)
            {
                FunctionCall call = node.Fun as FunctionCall;

                if (call.Func.Name.Equals("__uniform_bv32") || call.Func.Name.Equals("__uniform_bool"))
                {
                    return Expr.Eq(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr));
                }

                if (call.Func.Name.Equals("__distinct_bv32") || call.Func.Name.Equals("__distinct_bool"))
                {
                    return Expr.Neq(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr));
                }

                if (call.Func.Name.Equals("__all"))
                {
                    return Expr.And(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr));
                }

                if (call.Func.Name.Equals("__exclusive"))
                {
                    return Expr.Not(Expr.And(new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2, verifier.uniformityAnalyser, procName)
                                       .VisitExpr(node.Args[0].Clone() as Expr)));
                }


            }

            return base.VisitNAryExpr(node);
        }


        internal EnsuresSeq ProcessCrossThreadInvariants(EnsuresSeq ensuresSeq)
        {
            EnsuresSeq result = new EnsuresSeq();
            foreach (Ensures e in ensuresSeq)
            {
                result.Add(new Ensures(e.Free, VisitExpr(e.Condition.Clone() as Expr)));
            }
            return result;
        }

        internal RequiresSeq ProcessCrossThreadInvariants(RequiresSeq requiresSeq)
        {
            RequiresSeq result = new RequiresSeq();
            foreach (Requires r in requiresSeq)
            {
                result.Add(new Requires(r.Free, VisitExpr(r.Condition.Clone() as Expr)));
            }
            return result;
        }

        internal void ProcessCrossThreadInvariants(StmtList stmtList)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                ProcessCrossThreadInvariants(bb);
            }
        }

        internal void ProcessCrossThreadInvariants(List<Block> blocks)
        {
            foreach (Block b in blocks)
            {
                b.Cmds = ProcessCrossThreadInvariants(b.Cmds);
            }
        }

        private void ProcessCrossThreadInvariants(BigBlock bb)
        {
            bb.simpleCmds = ProcessCrossThreadInvariants(bb.simpleCmds);

            if (bb.ec is WhileCmd)
            {
                WhileCmd whileCmd = bb.ec as WhileCmd;
                List<PredicateCmd> newInvariants = new List<PredicateCmd>();
                foreach (PredicateCmd p in whileCmd.Invariants)
                {
                    newInvariants.Add(new AssertCmd(p.tok, VisitExpr(p.Expr)));
                }
                whileCmd.Invariants = newInvariants;
                ProcessCrossThreadInvariants(whileCmd.Body);
            }
        }

        private CmdSeq ProcessCrossThreadInvariants(CmdSeq cmds)
        {
            CmdSeq newCommands = new CmdSeq();

            foreach (Cmd c in cmds)
            {
                if (c is AssertCmd)
                {
                    newCommands.Add(new AssertCmd(c.tok, VisitExpr((c as AssertCmd).Expr.Clone() as Expr)));
                }
                else if (c is AssumeCmd)
                {
                    newCommands.Add(new AssumeCmd(c.tok, VisitExpr((c as AssumeCmd).Expr.Clone() as Expr)));
                }
                else
                {
                    newCommands.Add(c);
                }
            }
            return newCommands;
        }

    }
}
