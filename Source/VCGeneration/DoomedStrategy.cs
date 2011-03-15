//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using System.IO;
using Microsoft.Boogie;
using Graphing;
using AI = Microsoft.AbstractInterpretationFramework;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
    #region SuperClass for different doomed code detection strategies
    abstract internal class DoomDetectionStrategy
    {
        public int __DEBUG_BlocksChecked = 0;
        public int __DEBUG_BlocksTotal = 0;
        public int __DEBUG_InfeasibleTraces = 0;
        public int __DEBUG_TracesChecked = 0;
        public int __DEBUG_TracesTotal = 0;
        public int __DEBUG_EQCTotal = 0;
        public int __DEBUG_EQCLeaf = 0;
        public int __DEBUG_EQCChecked = 0;

        //Please use this one to toggle your Debug output
        protected bool __DEBUGOUT = CommandLineOptions.Clo.DoomStrategy != -1;

        protected Implementation impl;
        protected BlockHierachy m_BlockH = null;

        protected int m_MaxBranchingDepth = 0;
        protected int m_MaxMinElemPerPath = 0;


        // This is the List with all detected doomed program points. This List is used by VCDoomed.cs to 
        // create an error message
        public List<List<Block/*!*/>/*!*/>/*!*/ DetectedBlock = new List<List<Block/*!*/>/*!*/>();

        // There is no default constructor, because these parameters are needed for most subclasses
        public DoomDetectionStrategy(Implementation imp, Block unifiedexit, List<Block> unreach) 
        {
            m_BlockH = new BlockHierachy(imp, unifiedexit);
            __DEBUG_EQCLeaf = m_BlockH.Leaves.Count;

            if (imp.Blocks.Count>0) m_GatherInfo(imp.Blocks[0], 0, 0,0);
            if (__DEBUGOUT)
            {
                Console.WriteLine("MaBranchingDepth {0}  MaxMinPP {1} ", m_MaxBranchingDepth, m_MaxMinElemPerPath);
                double avgplen = 0, avglpp=0;
                foreach (int i in __pathLength)
                { 
                    avgplen+=i;
                }
                foreach (int i in __leavespp)
                {
                    avglpp += i;
                }
                avglpp = (__leavespp.Count > 0) ? avglpp / (double)__leavespp.Count : 1;
                avgplen = (__pathLength.Count > 0) ? avgplen / (double)__pathLength.Count : 1;
                Console.WriteLine("AvgLeaverPerPath {0} AvgPLen {1}", avglpp, avgplen);
            }

            MaxBlocks = imp.Blocks.Count;
            MinBlocks = imp.Blocks.Count;
            HACK_NewCheck = false;
            __DEBUG_BlocksTotal = imp.Blocks.Count;
        }


        public int MaxBlocks, MinBlocks;
        public bool HACK_NewCheck;

        // This method is called by the prover while it returns true. The prover checks for each 
        // List lb if 
        //      |= !lb_1 /\ ... /\ !lb_n => wlp(Program, false) 
        // and passes the result to SetCurrentResult
        abstract public bool GetNextBlock(out  List<Block> passBlock);

        // This method is called to inform about the prover outcome for the previous GetNextBlock call.
        abstract public bool SetCurrentResult(List<Variable> reachvar, ProverInterface.Outcome outcome, DoomErrorHandler cb);

        protected List<Block> m_GetErrorTraceFromCE(DoomErrorHandler cb)
        {
            BlockHierachyNode tn=null;
            List<Block> errortrace = new List<Block>();
            foreach (Block b in cb.TraceNodes)
            {
                if (errortrace.Contains(b)) continue;
                if (m_BlockH.BlockToHierachyMap.TryGetValue(b, out tn))
                {
                    foreach (Block b_ in tn.Unavoidable)
                    {
                        if (!errortrace.Contains(b_)) errortrace.Add(b_);
                    }
                    foreach (Block b_ in tn.Content)
                    {
                        if (!errortrace.Contains(b_)) errortrace.Add(b_);
                    }
                }
            }
            return errortrace;
        }

        private List<int> __pathLength = new List<int>();
        private List<int> __leavespp = new List<int>();
        protected void m_GatherInfo(Block b, int branchingdepth, int leavespp, int plen)
        {
            if (b.Predecessors.Length > 1) branchingdepth--;

            GotoCmd gc = b.TransferCmd as GotoCmd;
            BlockHierachyNode bhn = null;
            if (m_BlockH.BlockToHierachyMap.TryGetValue(b, out bhn))
            {
                if (m_BlockH.Leaves.Contains(bhn)) leavespp++;
            }
            m_MaxMinElemPerPath = (leavespp > m_MaxMinElemPerPath) ? leavespp : m_MaxMinElemPerPath;
            plen++;
            if (gc != null)
            {
                if (gc.labelTargets.Length > 1) branchingdepth++;
                m_MaxBranchingDepth = (branchingdepth > m_MaxBranchingDepth) ? branchingdepth : m_MaxBranchingDepth;
                foreach (Block s in gc.labelTargets)
                {
                    m_GatherInfo(s, branchingdepth, leavespp,plen);
                }
            }
            else
            {
                __pathLength.Add(plen);
                __leavespp.Add(leavespp);
            }

        }


    }
    #endregion

    #region BruteForce Strategy
    internal class NoStrategy : DoomDetectionStrategy
    {
        private List<Block> m_Blocks = new List<Block>();
        private int m_Current = 0;

        public NoStrategy(Implementation imp, Block unifiedexit, List<Block> unreach)
            : base(imp, unifiedexit, unreach)
        {
            m_Blocks = imp.Blocks;
        }

        override public bool GetNextBlock(out  List<Block> lb)
        {
            if (m_Current < m_Blocks.Count)
            {
                lb = new List<Block>();
                lb.Add(m_Blocks[m_Current]);
                m_Current++;
                return true;
            }
            lb = null;
            return false;
        }

        // This method is called to inform about the prover outcome for the previous GetNextBlock call.
        override public bool SetCurrentResult(List<Variable> reachvar, ProverInterface.Outcome outcome, DoomErrorHandler cb)
        {
            this.__DEBUG_BlocksChecked++;
            // outcome==Valid means that there is no feasible execution for the current block/path (i.e., might be doomed)
            if (outcome == ProverInterface.Outcome.Valid && m_Current <= m_Blocks.Count)
            {
                List<Block> lb = new List<Block>();
                lb.Add(m_Blocks[m_Current - 1]);
                DetectedBlock.Add(lb);
            }
            return true;
        }
    }
    #endregion

    #region Only check the minimal elements of the Hasse diagram
    internal class HierachyStrategy : DoomDetectionStrategy
    {
        private List<Block> m_Blocks = new List<Block>();
        private List<Block> m_doomedBlocks = new List<Block>();
        private int m_Current = 0;

        public HierachyStrategy(Implementation imp, Block unifiedexit, List<Block> unreach)
            : base(imp, unifiedexit, unreach)
        {            
            foreach (BlockHierachyNode bhn in m_BlockH.Leaves)
            {
                if (bhn.Content.Count > 0)
                {
                    m_Blocks.Add(bhn.Content[0]);
                }
            }
        }

        override public bool GetNextBlock(out  List<Block> lb)
        {
            if (m_Current < m_Blocks.Count)
            {
                lb = new List<Block>();
                lb.Add(m_Blocks[m_Current]);
                m_Current++;
                return true;
            }
            else
            {
                DetectedBlock.Add(m_BlockH.GetOtherDoomedBlocks(m_doomedBlocks));
            }
            lb = null;
            return false;
        }

        // This method is called to inform about the prover outcome for the previous GetNextBlock call.
        override public bool SetCurrentResult(List<Variable> reachvar, ProverInterface.Outcome outcome, DoomErrorHandler cb)
        {
            this.__DEBUG_BlocksChecked++;
            // outcome==Valid means that there is no feasible execution for the current block/path (i.e., might be doomed)
            if (outcome == ProverInterface.Outcome.Valid && m_Current <= m_Blocks.Count)
            {
                m_doomedBlocks.Add(m_Blocks[m_Current - 1]);
            }
            return true;
        }
    }
    #endregion

    #region Only check the minimal elements of the Hasse diagram and use CEs
    internal class HierachyCEStrategy : DoomDetectionStrategy
    {
        private List<Block> m_Blocks = new List<Block>();
        private List<Block> m_doomedBlocks = new List<Block>();
        private Block m_Current = null;

        public HierachyCEStrategy(Implementation imp, Block unifiedexit, List<Block> unreach)
            : base(imp, unifiedexit, unreach)
        {            
            foreach (BlockHierachyNode bhn in m_BlockH.Leaves)
            {
                if (bhn.Content.Count > 0)
                {
                    m_Blocks.Add(bhn.Content[0]);
                }
            }
        }

        override public bool GetNextBlock(out  List<Block> lb)
        {
            m_Current = null;
            if (m_Blocks.Count > 0)
            {
                m_Current = m_Blocks[0];
                m_Blocks.Remove(m_Current);
                lb = new List<Block>();
                lb.Add(m_Current);
                return true;
            }
            else
            {
                DetectedBlock.Add(m_BlockH.GetOtherDoomedBlocks(m_doomedBlocks));
            }
            lb = null;
            return false;
        }

        // This method is called to inform about the prover outcome for the previous GetNextBlock call.
        override public bool SetCurrentResult(List<Variable> reachvar, ProverInterface.Outcome outcome, DoomErrorHandler cb)
        {
            this.__DEBUG_BlocksChecked++;
            // outcome==Valid means that there is no feasible execution for the current block/path (i.e., might be doomed)
            if (outcome == ProverInterface.Outcome.Valid && m_Current != null)
            {
                m_doomedBlocks.Add(m_Current);
            }
            else if (outcome == ProverInterface.Outcome.Invalid)
            {
                List<Block> errortrace = m_GetErrorTraceFromCE(cb);
                foreach (Block b in errortrace)
                {
                    if (m_Blocks.Contains(b))
                    {
                        m_Blocks.Remove(b);
                    }
                }
                cb.TraceNodes.Clear();
            }
            return true;
        }
    }
    #endregion

    #region Path Cover Optimization
    internal class PathCoverStrategy : DoomDetectionStrategy
    {
        List<Block> m_Uncheckedlocks = new List<Block>();
        List<Block> m_Ignore = new List<Block>();

        Random m_Random = new Random();
        bool m_NoMoreMoves = false;

        private List<Block> m_foundBlock = new List<Block>();

        public PathCoverStrategy(Implementation imp, Block unifiedexit, List<Block> unreach)
            : base(imp, unifiedexit, unreach)
        {
            m_Ignore = unreach;
            HACK_NewCheck = true;
            impl = imp;
            foreach (BlockHierachyNode bhn in m_BlockH.Leaves)
            {
                //foreach (Block b in h.Content)
                //{
                //    m_Uncheckedlocks.Add(b);
                //}
                if (bhn.Content.Count > 0)
                {
                    m_Uncheckedlocks.Add(bhn.Content[0]);
                }

            }
            MaxBlocks = m_Uncheckedlocks.Count;
        }

        public PathCoverStrategy(Implementation imp, Block unifiedexit, List<Block> unreach, bool test_alternativeK)
            : base(imp, unifiedexit, unreach)
        {
            m_Ignore = unreach;
            HACK_NewCheck = true;
            impl = imp;
            foreach (BlockHierachyNode bhn in m_BlockH.Leaves)
            {
                //foreach (Block b in h.Content)
                //{
                //    m_Uncheckedlocks.Add(b);
                //}
                if (bhn.Content.Count > 0)
                {
                    m_Uncheckedlocks.Add(bhn.Content[0]);
                }

            }            
            MaxBlocks = m_Uncheckedlocks.Count;
            if (test_alternativeK) 
            {
                m_CountUncheckedPP(impl.Blocks[0], 0);
                if (m_MaxK < m_Uncheckedlocks.Count && m_MaxK > 0)
                {
                    MaxBlocks = m_MaxK;
                }
                else if (m_MaxK >= m_Uncheckedlocks.Count)
                {
                    MaxBlocks = m_Uncheckedlocks.Count;
                }
                else
                {
                    MaxBlocks = 1;
                }
                Console.WriteLine("InitK {0}, Max {1}", m_MaxK, MaxBlocks);
            }                                
        }

        int m_MaxK = 0;

        private void m_CountUncheckedPP(Block b, int localmax)
        {
            if (m_Uncheckedlocks.Contains(b)) localmax++;

            GotoCmd gc = b.TransferCmd as GotoCmd;
            if (gc != null && gc.labelTargets.Length>0)
            {
                foreach (Block s in gc.labelTargets)
                {
                    m_CountUncheckedPP(s, localmax);
                }
            }
            else
            {
                m_MaxK = (localmax > m_MaxK) ? localmax : m_MaxK;
            }

        }

        override public bool GetNextBlock(out  List<Block> lb)
        {
            lb = new List<Block>();

            if (m_Uncheckedlocks.Count == 0 || m_NoMoreMoves)
            {
                if (m_Uncheckedlocks.Count > 0)
                {
                    DetectedBlock.Add(m_BlockH.GetOtherDoomedBlocks(m_Uncheckedlocks));
                }

                return false;
            }

            lb.AddRange(m_Uncheckedlocks);
            MaxBlocks = MaxBlocks > m_Uncheckedlocks.Count ? m_Uncheckedlocks.Count : MaxBlocks;
            MinBlocks = MaxBlocks / 2 + (MaxBlocks % 2 > 0 ? 1 : 0);                       

            return true;
        }

        override public bool SetCurrentResult(List<Variable> reachvar, ProverInterface.Outcome outcome, DoomErrorHandler cb)
        {
            this.__DEBUG_BlocksChecked++;
            //Console.WriteLine(outcome);
            // Valid means infeasible...
            if (outcome == ProverInterface.Outcome.Valid)
            {
                this.__DEBUG_InfeasibleTraces++;
                if (MaxBlocks == 1)
                {
                    m_NoMoreMoves = true;
                }
                else
                {
                    MaxBlocks /= 2;
                }
            }
            else if (outcome == ProverInterface.Outcome.Invalid)
            {
                this.__DEBUG_TracesChecked++;
                //int oldsize = m_Uncheckedlocks.Count;
                List<Block> errortrace = m_GetErrorTraceFromCE(cb);
                foreach (Block b in errortrace)
                {
                    if (m_Uncheckedlocks.Contains(b))
                    {
                        m_Uncheckedlocks.Remove(b);
                    }
                }
                cb.TraceNodes.Clear();
            }
            else
            {
                m_NoMoreMoves = true; m_Uncheckedlocks.Clear();
            }
            return true;
        }


    }
    #endregion

}