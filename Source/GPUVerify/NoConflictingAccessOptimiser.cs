using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;

namespace GPUVerify
{
    class NoConflictingAccessOptimiser
    {
        private Implementation impl;
        private IList<CallCmdPos> ccs;

        public NoConflictingAccessOptimiser(Implementation impl)
        {
            this.impl = impl;
            ccs = new List<CallCmdPos>();
            FindCallCmds();
        }

        private class CallCmdPos
        {
            public Block block;
            public int cmdIndex;
            public CallCmd cc;

            public CallCmdPos(Block block, int cmdIndex, CallCmd cc)
            {
                this.block = block;
                this.cmdIndex = cmdIndex;
                this.cc = cc;
            }
        }

        public int NumLogCalls()
        {
            return ccs.Count;
        }

        private void FindCallCmds()
        {
            foreach (Block b in impl.Blocks)
            {
                for(int i=0; i < b.Cmds.Length; i++)
                {
                    Cmd c = b.Cmds[i];
                    CallCmd cc = c as CallCmd;
                    if (cc != null)
                    {
                        if (cc.Proc.Name.Contains("_LOG"))
                        {
                            ccs.Add(new CallCmdPos(b, i, cc));
                        }
                    }
                }
            }
        }

        public bool HasConflicting()
        {
            Contract.Assert(ccs.Count == 2);

            return
                Reachable(ccs[0].block, ccs[0].cmdIndex, ccs[1].cc, new HashSet<Block>()) ||
                Reachable(ccs[1].block, ccs[1].cmdIndex, ccs[0].cc, new HashSet<Block>());
        }

        public bool Reachable(Block startBlock, int cmdStartIndex, CallCmd target, ISet<Block> visited)
        {
            Block currBlock = startBlock;
            int i = cmdStartIndex;

            if(i == 0)
            {
                visited.Add(currBlock);
            }

            while (i < currBlock.Cmds.Length)
            {
                CallCmd cc = currBlock.Cmds[i] as CallCmd;
                if (cc != null)
                {
                    if (cc.Proc.Name.Equals("BARRIER"))
                    {
                        return false;
                    }

                    if (target == cc)
                    {
                        return true;
                    }
                }
                i++;
            }
            
            
            //end of block
                
            GotoCmd gc = currBlock.TransferCmd as GotoCmd;
            Contract.Assert(gc != null);
            foreach (Block t in gc.labelTargets)
            {
                if(visited.Contains(t))
                    continue;

                if (Reachable(t, 0, target, visited))
                    return true;
            }

            return false;

        }

    }
}
