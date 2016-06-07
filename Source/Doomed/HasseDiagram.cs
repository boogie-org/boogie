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
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
    internal class BlockHierachyNode
    {
        public List<Block> Unavoidable;
        public List<Block> Content = new List<Block>();
        public List<BlockHierachyNode> Parents = new List<BlockHierachyNode>();
        public List<BlockHierachyNode> Children = new List<BlockHierachyNode>();

        public bool Checked, Doomed, DoubleChecked;

        public BlockHierachyNode(Block current, List<Block> unavoidable)
        {
            Checked = false; Doomed = false; DoubleChecked = false;
            Unavoidable = unavoidable;
            Content.Add(current);
        }

        public static bool operator <(BlockHierachyNode left, BlockHierachyNode right)
        {
            return Compare(left,right)>0;
        }

        public static bool operator >(BlockHierachyNode left, BlockHierachyNode right)
        {
            return Compare(left, right) < 0;
        }

        // Compare the unavoidable blocks of two BlockHierachyNodes. 
        // returns 0 if sets have the same size, -1 if l2 has an element 
        // that is not in l1, otherwise the size of the intersection.
        public static int Compare(BlockHierachyNode l1, BlockHierachyNode l2)
        {
            List<Block> tmp = new List<Block>();
            tmp.AddRange(l2.Unavoidable);
            foreach (Block b in l1.Unavoidable)
            {
                if (tmp.Contains(b)) tmp.Remove(b);
                else return -1;
            }
            return tmp.Count;
        }
    }

    internal class HasseDiagram
    {
        public readonly List<BlockHierachyNode> Leaves = new List<BlockHierachyNode>();
        public readonly List<BlockHierachyNode> Roots = new List<BlockHierachyNode>();

        public HasseDiagram(List<BlockHierachyNode> nodes)
        {
            Dictionary<BlockHierachyNode, List<BlockHierachyNode>> largerElements = new Dictionary<BlockHierachyNode, List<BlockHierachyNode>>();
            foreach (BlockHierachyNode left in nodes)
            {
                largerElements[left] = new List<BlockHierachyNode>();
                foreach (BlockHierachyNode right in nodes)
                {
                    if (left != right)
                    {
                        if (left < right)
                        {
                            largerElements[left].Add(right);
                        }
                    }
                }
                if (largerElements[left].Count == 0) Leaves.Add(left);
            }

            List<BlockHierachyNode> done = new List<BlockHierachyNode>();
            List<BlockHierachyNode> lastround = null;

            //Debugger.Break();

            // Now that we have the leaves, build the Hasse diagram
            while (done.Count < nodes.Count)
            {
                List<BlockHierachyNode> maxelements = new List<BlockHierachyNode>();
                maxelements.AddRange(nodes);
                foreach (BlockHierachyNode bhn in nodes)
                {
                    if (!done.Contains(bhn))
                    {
                        foreach (BlockHierachyNode tmp in largerElements[bhn])
                        {
                            if (maxelements.Contains(tmp)) maxelements.Remove(tmp);
                        }
                    }
                    else
                    {
                        maxelements.Remove(bhn);
                    }
                }

                done.AddRange(maxelements);

                if (lastround != null)
                {
                    foreach (BlockHierachyNode tmp in lastround)
                    {
                        foreach (BlockHierachyNode tmp2 in maxelements)
                        {
                            if (largerElements[tmp].Contains(tmp2))
                            {
                                if (!tmp.Children.Contains(tmp2)) tmp.Children.Add(tmp2);
                                if (!tmp2.Parents.Contains(tmp)) tmp2.Parents.Add(tmp);
                            }
                        }
                    }
                }
                else
                {
                    Roots.AddRange(maxelements);
                }
                lastround = maxelements;
            }
        }


    }

    internal class BlockHierachy
    {
        public BlockHierachyNode RootNode = null;
        readonly public Dictionary<Block, BlockHierachyNode> BlockToHierachyMap = new Dictionary<Block, BlockHierachyNode>();
        readonly public Dictionary<Block, List<Block>> Dominators = new Dictionary<Block, List<Block>>();
        readonly public Dictionary<Block, List<Block>> PostDominators = new Dictionary<Block, List<Block>>();
        readonly public List<BlockHierachyNode> Leaves = new List<BlockHierachyNode>();

        private Implementation m_Impl;

        public BlockHierachy(Implementation impl, Block unifiedExit)
        {
            m_Impl = impl;
            List<Block> blocks = impl.Blocks;
            List<BlockHierachyNode> tmp_hnodes = new List<BlockHierachyNode>();
            Dictionary<Block, List<Block>> unavoidable = new Dictionary<Block, List<Block>>();

            BfsTraverser(blocks[0], true, Dominators);
            BfsTraverser(unifiedExit, false, PostDominators);

            foreach (Block b in blocks)
            {
                List<Block> l1 = Dominators[b];
                List<Block> l2 = PostDominators[b];
                unavoidable[b] = m_MergeLists(l1, l2);

                BlockHierachyNode bhn = new BlockHierachyNode(b, unavoidable[b]);
                bool found = false;
                foreach (KeyValuePair<Block, BlockHierachyNode> kvp in BlockToHierachyMap)
                {
                    if (BlockHierachyNode.Compare(kvp.Value, bhn) == 0) // using the overloaded compare operator
                    {
                        kvp.Value.Content.AddRange(bhn.Content);
                        BlockToHierachyMap[b] = kvp.Value;
                        found = true;
                        break;
                    }
                }
                if (!found)
                {
                    BlockToHierachyMap[b] = bhn;
                    tmp_hnodes.Add(bhn);
                }
            }

            HasseDiagram hd = new HasseDiagram(tmp_hnodes);
            Leaves = hd.Leaves;            
        }

        public int GetMaxK(List<Block> blocks)
        {
            m_GetMaxK(blocks);
            return (m_MaxK>0) ? m_MaxK : 1;
        }

        private int m_MaxK = 0;
        private void m_GetMaxK(List<Block> blocks)
        {
            m_MaxK = 0;
            Dictionary<Block, int> kstore = new Dictionary<Block, int>();
            List<Block> todo = new List<Block>();
            List<Block> done = new List<Block>();
            todo.Add(m_Impl.Blocks[0]);
            kstore[m_Impl.Blocks[0]] = 0;
            int localmax;
            Block current = null;
            while (todo.Count > 0)
            {
                current = todo[0];
                todo.Remove(current);
                bool ready = true;
                localmax = 0;
                if (current.Predecessors!=null) {
                    foreach (Block p in current.Predecessors)
                    {
                        if (!done.Contains(p))
                        {
                            ready = false; break;
                        }
                        else localmax = (localmax > kstore[p]) ? localmax : kstore[p];
                    }
                }
                if (!ready)
                {
                    todo.Add(current); continue;
                }
                done.Add(current);
                kstore[current] =  (blocks.Contains(current)) ? localmax +1 : localmax;

                m_MaxK = (kstore[current] > m_MaxK) ? kstore[current] : m_MaxK;

                GotoCmd gc = current.TransferCmd as GotoCmd;
                if (gc != null)
                {
                    foreach (Block s in gc.labelTargets)
                    {
                        if (!todo.Contains(s)) todo.Add(s);
                    }
                }
            }

        }

        public List<Block> GetOtherDoomedBlocks(List<Block> doomedblocks)
        {
            List<Block> alsoDoomed = new List<Block>();
            List<BlockHierachyNode> todo = new List<BlockHierachyNode>();
            foreach (Block b in doomedblocks)
            {
                BlockToHierachyMap[b].Doomed = true;                
                todo.Add(BlockToHierachyMap[b]);
            }

            while (todo.Count > 0)
            {
                BlockHierachyNode current = todo[0];
                todo.Remove(current);
                if (!current.Doomed && current.Children.Count > 0)
                {
                    bool childrenDoomed = true;
                    foreach (BlockHierachyNode c in current.Children)
                    {
                        if (!c.Doomed) { childrenDoomed = false; break; }
                    }
                    if (childrenDoomed) current.Doomed = true;
                }

                if (current.Doomed)
                {
                    foreach (BlockHierachyNode p in current.Parents)
                    {
                        if (!todo.Contains(p)) todo.Add(p);
                    }
                    foreach (Block b in current.Content)
                    {
                        if (!alsoDoomed.Contains(b)) alsoDoomed.Add(b);
                    }
                }
            }

            return alsoDoomed;
        }

        public void Impl2Dot(string filename)
        {

            Contract.Requires(filename != null);
            List<string> nodes = new List<string>();
            List<string> edges = new List<string>();

            string nodestyle = "[shape=box];";

            List<BlockHierachyNode> nl = new List<BlockHierachyNode>();
            foreach (BlockHierachyNode h in BlockToHierachyMap.Values) if (!nl.Contains(h)) nl.Add(h);


            foreach (BlockHierachyNode b in nl)
            {
                String l1 = "";
                foreach (Block bl in b.Content) l1 = String.Format("{0}_{1}", l1, bl.Label);

                Contract.Assert(b != null);
                nodes.Add(string.Format("\"{0}\" {1}", l1, nodestyle));
                foreach (BlockHierachyNode b_ in b.Children)
                {

                    String l2 = "";
                    foreach (Block bl in b_.Content) l2 = String.Format("{0}_{1}", l2, bl.Label);
                    edges.Add(String.Format("\"{0}\" -> \"{1}\";", l1, l2));
                }

            }

            using (StreamWriter sw = new StreamWriter(filename))
            {
                sw.WriteLine(String.Format("digraph {0} {{", "DISCO"));
                //            foreach (string! s in nodes) {
                //                sw.WriteLine(s);
                //            }
                foreach (string s in edges)
                {
                    Contract.Assert(s != null);
                    sw.WriteLine(s);
                }
                sw.WriteLine("}}");
                sw.Close();
            }
        }
        
        private void BfsTraverser(Block current, bool forward, Dictionary<Block, List<Block>> unavoidableBlocks)
        {
            List<Block> todo = new List<Block>();
            List<Block> done = new List<Block>();
            unavoidableBlocks[current] = new List<Block>();
            //Debugger.Break();
            todo.Add(current);
            while (todo.Count > 0)
            {
                current = todo[0];
                todo.Remove(current);
                List<Block> pre = m_Predecessors(current, forward);
                bool ready = true;
                if (pre != null)
                {
                    foreach (Block bpre in pre)
                    {
                        if (!done.Contains(bpre))
                        {
                            ready = false;
                            break;
                        }
                    }
                }
                if (!ready)
                {
                    todo.Add(current);
                    continue;
                }
                done.Add(current);
                unavoidableBlocks[current].Add(current);

                List<Block> suc = m_Succecessors(current, forward);
                if (suc == null) continue;
                foreach (Block bsuc in suc)
                {
                    if (unavoidableBlocks.ContainsKey(bsuc))
                    {
                        unavoidableBlocks[bsuc] = m_IntersectLists(unavoidableBlocks[bsuc], unavoidableBlocks[current]);
                    }
                    else
                    {
                        todo.Add(bsuc);
                        unavoidableBlocks[bsuc] = new List<Block>();
                        unavoidableBlocks[bsuc].AddRange(unavoidableBlocks[current]);
                    }

                }
            }

        }

        private List<Block> m_MergeLists(List<Block> lb1, List<Block> lb2)
        {
            List<Block> ret = new List<Block>();
            ret.AddRange(lb1);
            foreach (Block b in lb2)
            {
                if (!ret.Contains(b)) ret.Add(b);
            }
            return ret;
        }

        private List<Block> m_IntersectLists(List<Block> lb1, List<Block> lb2)
        {
            List<Block> ret = new List<Block>();
            ret.AddRange(lb1);
            foreach (Block b in lb2)
            {
                if (!lb1.Contains(b)) ret.Remove(b);
            }
            foreach (Block b in lb1)
            {
                if (ret.Contains(b) && !lb2.Contains(b)) ret.Remove(b);
            }
            return ret;
        }

        private List<Block> m_Predecessors(Block b, bool forward)
        {
            if (forward) return b.Predecessors;
            GotoCmd gc = b.TransferCmd as GotoCmd;
            if (gc != null)
            {
                return gc.labelTargets;
            }
            return null;
        }

        private List<Block> m_Succecessors(Block b, bool forward)
        {
            return m_Predecessors(b, !forward);
        }


    }

}