using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    class StructuredProgramVisitor
    {

        protected GPUVerifier verifier;

        public StructuredProgramVisitor(GPUVerifier verifier)
        {
            this.verifier = verifier;
        }

        public virtual StmtList VisitStmtList(StmtList stmtList)
        {
            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                result.BigBlocks.AddRange(VisitBigBlock(bb));
            }

            return result;

        }

        public virtual List<BigBlock> VisitBigBlock(BigBlock bb)
        {
            BigBlock firstBigBlock = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            firstBigBlock.simpleCmds = VisitCmdSeq(bb.simpleCmds);

            if (bb.ec is WhileCmd)
            {
                firstBigBlock.ec = VisitWhileCmd(bb.ec as WhileCmd);
            }
            else if (bb.ec is IfCmd)
            {
                firstBigBlock.ec = VisitIfCmd(bb.ec as IfCmd);
            }
            else if (bb.ec is BreakCmd)
            {
                firstBigBlock.ec = VisitBreakCmd(bb.ec as BreakCmd);
            }
            else if (bb.ec != null)
            {
                throw new InvalidOperationException();
            }

            return new List<BigBlock>(new BigBlock[] { firstBigBlock });

        }

        public virtual IfCmd VisitIfCmd(IfCmd ifCmd)
        {
            if(ifCmd.elseIf != null)
            {
                throw new InvalidOperationException();
            }

            return new IfCmd(ifCmd.tok, VisitIfGuard(ifCmd.Guard), VisitStmtList(ifCmd.thn), ifCmd.elseIf,
                (ifCmd.elseBlock == null ? ifCmd.elseBlock : VisitStmtList(ifCmd.elseBlock)));

            throw new NotImplementedException();
        }

        public virtual Expr VisitIfGuard(Expr expr)
        {
            return expr;
        }

        public virtual WhileCmd VisitWhileCmd(WhileCmd whileCmd)
        {
            return new WhileCmd(whileCmd.tok, 
                VisitWhileGuard(whileCmd.Guard), VisitWhileInvariants(whileCmd.Invariants, whileCmd.Guard), VisitStmtList(whileCmd.Body));
        }

        public virtual BreakCmd VisitBreakCmd(BreakCmd breakCmd)
        {
            return breakCmd;
        }


        public virtual List<PredicateCmd> VisitWhileInvariants(List<PredicateCmd> invariants, Expr WhileGuard)
        {
            return invariants;
        }

        public virtual Expr VisitWhileGuard(Expr expr)
        {
            return expr;
        }

        public virtual CmdSeq VisitCmdSeq(CmdSeq cmdSeq)
        {
            CmdSeq result = new CmdSeq();
            foreach (Cmd c in cmdSeq)
            {
                result.AddRange(VisitCmd(c));
            }
            return result;
        }

        public virtual CmdSeq VisitCmd(Cmd c)
        {
            if (c is CallCmd)
            {
                return VisitCallCmd(c as CallCmd);
            }
            if (c is AssignCmd)
            {
                return VisitAssignCmd(c as AssignCmd);
            }
            if (c is HavocCmd)
            {
                return VisitHavocCmd(c as HavocCmd);
            }
            if (c is AssertCmd)
            {
                return VisitAssertCmd(c as AssertCmd);
            }
            if (c is AssumeCmd)
            {
                return VisitAssumeCmd(c as AssumeCmd);
            }
            throw new InvalidOperationException();
        }

        public virtual CmdSeq VisitAssumeCmd(AssumeCmd assumeCmd)
        {
            return new CmdSeq(new Cmd[] { assumeCmd });
        }

        public virtual CmdSeq VisitAssertCmd(AssertCmd assertCmd)
        {
            return new CmdSeq(new Cmd[] { assertCmd });
        }

        public virtual CmdSeq VisitHavocCmd(HavocCmd havocCmd)
        {
            return new CmdSeq(new Cmd[] { havocCmd });
        }

        public virtual CmdSeq VisitAssignCmd(AssignCmd assignCmd)
        {
            return new CmdSeq(new Cmd[] { assignCmd });
        }

        public virtual CmdSeq VisitCallCmd(CallCmd callCmd)
        {
            return new CmdSeq(new Cmd[] { callCmd });
        }

    }
}
