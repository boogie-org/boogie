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
    #region Loop handeling for doomed code detection

    #region Loop Remover
    internal class LoopRemover
    {        
        GraphAnalyzer m_GraphAnalyzer;

        public LoopRemover(GraphAnalyzer ga)
        {
            m_GraphAnalyzer = ga;
        }

         private void m_RemoveBackEdge(Loop l)
        {
            // first remove the backedges of the nested loops
            foreach (Loop c in l.NestedLoops) m_RemoveBackEdge(c);
            //Debugger.Break();
            GraphNode loopSkip = null;
            foreach (GraphNode gn in l.Cutpoint.Suc)
            {
                if (l.LoopExitNodes.Contains(gn))
                {
                    loopSkip = gn; break;
                }
            }
            if (loopSkip == null)
            { // We didn't find a loop exit node. There must be a bug
                Debugger.Break();
            }
            foreach (GraphNode gn in l.Cutpoint.LoopingPred)
            {
                List<GraphNode> newsuc = new List<GraphNode>();
                foreach (GraphNode s in gn.Suc)
                {
                    if (s == l.Cutpoint) newsuc.Add(loopSkip);
                    else newsuc.Add(s);
                }
                gn.Suc = newsuc;
            }
        }

        private void m_AbstractLoop(Loop l)
        {
            foreach (Loop c in l.NestedLoops) m_AbstractLoop(c);
            m_HavocLoopBody(l);
            m_RemoveBackEdge(l);        
        }

        public void AbstractLoopUnrolling()
        {
            foreach (Loop l in m_GraphAnalyzer.Graphloops)
            {
                m_MarkLoopExitUncheckable(l);
                m_AbstractLoopUnrolling(l,null, "",true);                
            }
        }

        private void m_HavocLoopBody(Loop l)
        {
            List<Block> loopblocks = new List<Block>();
            foreach (GraphNode g in l.LoopNodes) loopblocks.Add(g.Label);
            HavocCmd hcmd = m_ComputHavocCmd(loopblocks, l.Cutpoint.Label.tok);

            //Add Havoc before and after the loop body
            foreach (GraphNode g in l.Cutpoint.Suc) // before
            {
                if (l.LoopNodes.Contains(g)) m_AddHavocCmdToFront(g.Label, hcmd);                
            }
            foreach (GraphNode g in l.Cutpoint.Pre) // and after
            {
                if (l.LoopNodes.Contains(g)) m_AddHavocCmdToFront(g.Label, hcmd);                
            }        
        }

        private void m_AddHavocCmdToFront(Block b, HavocCmd hcmd)
        {
            List<Cmd> cs = new List<Cmd>();
            cs.Add(hcmd); cs.AddRange(b.Cmds);
            b.Cmds = cs;
        }

        private HavocCmd m_ComputHavocCmd(List<Block> bl, IToken tok)
        {
            Contract.Requires(bl != null);
            Contract.Requires(tok != null);
            Contract.Ensures(Contract.Result<HavocCmd>() != null);

            List<Variable> varsToHavoc = new List<Variable>();
            foreach (Block b in bl)
            {
                Contract.Assert(b != null);
                foreach (Cmd c in b.Cmds)
                {
                    Contract.Assert(c != null);
                    c.AddAssignedVariables(varsToHavoc);
                }
            }
            List<IdentifierExpr> havocExprs = new List<IdentifierExpr>();
            foreach (Variable v in varsToHavoc)
            {
                Contract.Assert(v != null);
                IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                if (!havocExprs.Contains(ie))
                    havocExprs.Add(ie);
            }
            // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
            // the source location for this later on
            return new HavocCmd(tok, havocExprs);
        }

        private void m_AbstractLoopUnrolling(Loop l, Loop parent, string prefix, bool unfold)
        {            
            //Debugger.Break();
            if (unfold)
            {

                Loop first = new Loop(l, m_GraphAnalyzer,prefix+"FI_");
                Loop last = new Loop(l, m_GraphAnalyzer,prefix+"LA_");
                Loop abs = new Loop(l, m_GraphAnalyzer, prefix + "AB_");
                foreach (Loop c in first.NestedLoops) m_AbstractLoopUnrolling(c, first, prefix + "FI_", false);
                foreach (Loop c in last.NestedLoops)  m_AbstractLoopUnrolling(c, last, prefix + "LA_", false);
                foreach (Loop c in abs.NestedLoops)   m_AbstractLoopUnrolling(c, abs, prefix + "AB_", true);

                //Debugger.Break();

                if (parent != null)
                {
                    foreach (GraphNode gn in l.LoopNodes)
                    {
                        if (parent.LoopNodes.Contains(gn)) parent.LoopNodes.Remove(gn);
                    }
                    foreach (GraphNode gn in abs.LoopNodes)
                    {
                        if (!parent.LoopNodes.Contains(gn)) parent.LoopNodes.Add(gn);
                    }
                    foreach (GraphNode gn in first.LoopNodes)
                    {
                        if (!parent.LoopNodes.Contains(gn)) parent.LoopNodes.Add(gn);
                    }
                    foreach (GraphNode gn in last.LoopNodes)
                    {
                        if (!parent.LoopNodes.Contains(gn)) parent.LoopNodes.Add(gn);
                    }
                }
                
                m_HavocLoopBody(abs);
                List<GraphNode> backupPre = new List<GraphNode>();
                backupPre.AddRange(l.Cutpoint.Pre);
                foreach (GraphNode pre in backupPre)
                {
                    if (!l.Cutpoint.LoopingPred.Contains(pre))
                    {
                        pre.RemoveEdgeTo(l.Cutpoint);
                        pre.RemoveEdgeTo(abs.Cutpoint);
                        pre.AddEdgeTo(first.Cutpoint);
                    }
                }

                m_RemoveRegularLoopExit(last);
                m_RemoveRegularLoopExit(abs);

                m_ReplaceBackEdge(first, abs.Cutpoint);
                m_ReplaceBackEdge(abs, last.Cutpoint);
                foreach (GraphNode gn in first.Cutpoint.Suc)
                {
                    if (!first.LoopNodes.Contains(gn))
                    {
                        m_ReplaceBackEdge(last, gn);
                        break;
                    }
                }

                // Remove all remaining connections to the original loop
                foreach (GraphNode gn in l.LoopExitNodes)
                {
                    List<GraphNode> tmp = new List<GraphNode>();
                    tmp.AddRange(gn.Pre);
                    foreach (GraphNode g in tmp)
                    {
                        if (l.LoopNodes.Contains(g))
                        {
                            //Debugger.Break();
                            g.RemoveEdgeTo(gn);
                        }
                    }
                }
                foreach (GraphNode gn in l.LoopNodes)
                {
                    m_GraphAnalyzer.DeleteGraphNode(gn);
                }
                foreach (GraphNode gn in first.LoopNodes)
                {
                    if (gn != first.Cutpoint && !m_GraphAnalyzer.UncheckableNodes.Contains(gn) ) 
                        m_GraphAnalyzer.UncheckableNodes.Add(gn);
                }
                foreach (GraphNode gn in last.LoopNodes)
                {
                    if (gn != last.Cutpoint && !m_GraphAnalyzer.UncheckableNodes.Contains(gn))
                        m_GraphAnalyzer.UncheckableNodes.Add(gn);
                }
                MakeLoopExitUncheckable(last.LoopExitNodes);
            }
            else
            {
                foreach (Loop c in l.NestedLoops) m_AbstractLoopUnrolling(c, l, prefix, false);
                m_AbstractLoop(l);
                //MakeLoopExitUncheckable(l.LoopExitNodes);                
            }            
        }

        // the loop exit has to be marked uncheckable because otherwise
        // while(true) would report unreachable code.
        private void m_MarkLoopExitUncheckable(Loop l)
        {
            
            foreach (GraphNode g in l.Cutpoint.Suc)
            {
                if (!l.LoopNodes.Contains(g))
                {                    
                    foreach (GraphNode g_ in m_MarkLoopExitUncheckable(g, l))
                    {
                        if (!m_GraphAnalyzer.UncheckableNodes.Contains(g_))
                            m_GraphAnalyzer.UncheckableNodes.Add(g_);
                    }
                }
            }
        }

        private List<GraphNode> m_MarkLoopExitUncheckable(GraphNode g, Loop l)
        {
            List<GraphNode> ret = new List<GraphNode>();

            if (g.Pre.Count > 1) return ret;
            ret.Add(g);
            foreach (GraphNode gn in g.Suc)
            {
                ret.AddRange(m_MarkLoopExitUncheckable(gn, l));
            }

            return ret;
        }

        // to avoid problems with unreachable code after while(true) {}, try to make the loopexit nodes uncheckable.
        private void MakeLoopExitUncheckable(List<GraphNode> le)
        { 
            foreach (GraphNode gn in le) 
            {
                if (gn.Suc.Count==1)  m_GraphAnalyzer.UncheckableNodes.Add(gn);
            }
        }

        private void m_RemoveRegularLoopExit(Loop l)
        {
            List<GraphNode> lg = new List<GraphNode>();
            lg.AddRange( l.Cutpoint.Suc );
            foreach (GraphNode gn in lg)
            {
                if (l.LoopExitNodes.Contains(gn))
                {
                    l.Cutpoint.RemoveEdgeTo(gn);
                    l.LoopExitNodes.Remove(gn);
                }
            }
        }

        private void m_ReplaceBackEdge(Loop l, GraphNode loopSkip)
        {

            foreach (GraphNode gn in l.Cutpoint.LoopingPred)
            {
                List<GraphNode> newsuc = new List<GraphNode>();
                foreach (GraphNode s in gn.Suc)
                {
                    if (s == l.Cutpoint) newsuc.Add(loopSkip);
                    else newsuc.Add(s);
                }
                gn.Suc = newsuc;
            }
        }


    }
    #endregion

    #region Graph Analyzer
    internal class GraphAnalyzer
    {
        public List<GraphNode> UncheckableNodes = new List<GraphNode>();

        public Dictionary<Block, GraphNode> GraphMap = new Dictionary<Block, GraphNode>();

        public List<Loop> Graphloops = null;

        public GraphAnalyzer(List<Block> blocks)
        {
            //ExitBlock = dedicatedExitBlock;
            if (blocks.Count < 1) return;
            foreach (Block b in blocks) GraphMap[b] = new GraphNode(b);
            foreach (Block b in blocks)
            {
                foreach (Block pre in b.Predecessors) GraphMap[b].Pre.Add(GraphMap[pre]);
                GotoCmd gc = b.TransferCmd as GotoCmd;
                if (gc != null)
                {
                    foreach (Block suc in gc.labelTargets) GraphMap[b].Suc.Add(GraphMap[suc]);
                }
            }

            
            m_DetectCutPoints(GraphMap[blocks[0]]);
            
            //m_DetectCutPoints(GraphMap[blocks[0]], null, new List<GraphNode>());  
            Graphloops = m_CollectLoops(GraphMap[blocks[0]], null);
            
        }

        public List<Block> ToImplementation(out List<Block> uncheckables)
        {
            List<Block> blocks = new List<Block>();
            uncheckables = new List<Block>();

            foreach (KeyValuePair<Block, GraphNode> kvp in GraphMap)
            {
                Block b = kvp.Key;
                if (UncheckableNodes.Contains(GraphMap[b])) uncheckables.Add(b);
                blocks.Add(b);
                b.Predecessors = new List<Block>();
                foreach (GraphNode p in kvp.Value.Pre) b.Predecessors.Add(p.Label);
                if (kvp.Value.Suc.Count > 0)
                {
                    List<Block> bs = new List<Block>();                    
                    foreach (GraphNode s in kvp.Value.Suc) bs.Add(s.Label);                    
                    b.TransferCmd = new GotoCmd(b.tok, bs);
                }
                else
                {
                    b.TransferCmd = new ReturnCmd(b.tok);
                }
            }

            return blocks;
        }

        public GraphNode CloneGraphNode(GraphNode gn, string prefix)
        {
            List<Cmd> cmds = new List<Cmd>(gn.Label.Cmds);

            Block b = new Block(gn.Label.tok, prefix+gn.Label.Label, cmds, gn.Label.TransferCmd);
            GraphNode clone = new GraphNode(b);
            clone.IsCutpoint = gn.IsCutpoint;
            clone.Suc.AddRange(gn.Suc);
            clone.Pre.AddRange(gn.Pre);
            clone.LoopingPred.AddRange(gn.LoopingPred);
            GraphMap[b] = clone;
            //if (gn.Label == ExitBlock) ExitBlock = b;
            return clone;
        }

        public void DeleteGraphNode(GraphNode gn)
        {
            List<Block> affected = new List<Block>();
                        
            foreach (KeyValuePair<Block, GraphNode> kvp in GraphMap)
            {
                if (kvp.Value == gn && !affected.Contains(kvp.Key)) affected.Add(kvp.Key);
            }
            foreach (Block b in affected)
            {
                GraphMap.Remove(b);
            }
        }
/*
        private void m_DetectCutPoints(GraphNode gn, GraphNode pred, List<GraphNode> visited )
        {
            if (visited.Contains(gn) )
            {
                if (pred != null && !gn.LoopingPred.Contains(pred)) gn.LoopingPred.Add(pred);
                gn.IsCutpoint = true;
                Console.WriteLine("Normal RootNode {0}", gn.Label.Label);
                return;
            }
            else
            {
                List<GraphNode> visited_ = new List<GraphNode>();
                visited_.AddRange(visited);
                visited_.Add(gn);
                foreach (GraphNode next in gn.Suc)
                {
                    m_DetectCutPoints(next,gn,visited_);
                }
            }

        }
*/


        private void m_DetectCutPoints(GraphNode gn)
        {
            List<GraphNode> todo = new List<GraphNode>();
            List<GraphNode> done = new List<GraphNode>();
            todo.Add(gn);

            GraphNode current = null;
            todo[0].Index = 0;

            while (todo.Count > 0)
            {
                current = todo[0];
                todo.Remove(current);

                bool ready = true;
                foreach (GraphNode p in current.Pre)
                {                    
                    if (!done.Contains(p) )
                    {
                        _loopbacktracking.Clear();
                        if (!m_isLoop(current, p, todo, done))
                        {
                            todo.Add(current);
                            ready = false;
                            break;
                        }
                        else
                        {
                            if (!current.LoopingPred.Contains(p)) current.LoopingPred.Add(p);
                            current.IsCutpoint = true;
                        }
                    } 
                }
                if (!ready) continue;
                done.Add(current);
                foreach (GraphNode s in current.Suc)
                {
                    if (!todo.Contains(s) && !done.Contains(s)) todo.Add(s);
                }
            }

        }

        List<GraphNode> _loopbacktracking = new List<GraphNode>();
        private bool m_isLoop(GraphNode loophead, GraphNode gn, List<GraphNode> l1, List<GraphNode> l2)
        {
            if (loophead == gn) return true;
            if (l1.Contains(gn) || l2.Contains(gn) || _loopbacktracking.Contains(gn)) return false;
            _loopbacktracking.Add(gn);
            foreach (GraphNode p in gn.Pre)
            {
                if (m_isLoop(loophead, p, l1, l2)) return true;
            }
            return false;
        }

        private List<Loop> m_CollectLoops(GraphNode gn, Loop lastLoop)
        {
            List<Loop> ret = new List<Loop>();
            if (gn.Visited) return ret;
            gn.Visited = true;
            List<GraphNode> loopingSucs = new List<GraphNode>();
            if (gn.IsCutpoint)
            {                
                Loop l = new Loop(gn);
                if (lastLoop != null)
                {
                    lastLoop.SucLoops.Add(l);
                    l.PreLoops.Add(lastLoop);
                }
                loopingSucs = l.LoopNodes;
                lastLoop = l;
                ret.Add(lastLoop);
            }
            foreach (GraphNode suc in gn.Suc)
            {
                if (!loopingSucs.Contains(suc)) ret.AddRange(m_CollectLoops(suc, lastLoop));                
            }
            //Debugger.Break();
            return ret;
        }
    }
    #endregion

    #region GraphNodeStructure
    internal class GraphNode
    {
        public int Index = -1; // Used for scc detection
        public int LowLink = -1;  // Used for scc detection

        public GraphNode(Block b)
        {
            Label = b; IsCutpoint = false;
        }
        public Block Label;
        public List<GraphNode> Pre = new List<GraphNode>();
        public List<GraphNode> Suc = new List<GraphNode>();
        public bool IsCutpoint;
        public bool Visited = false;
        public List<GraphNode> LoopingPred = new List<GraphNode>();

        public void AddEdgeTo(GraphNode other)
        {
            if (!this.Suc.Contains(other)) this.Suc.Add(other);
            if (!other.Pre.Contains(this)) other.Pre.Add(this);
        }

        public void RemoveEdgeTo(GraphNode other)
        {
            if (this.Suc.Contains(other)) this.Suc.Remove(other);
            if (other.Pre.Contains(this)) other.Pre.Remove(this);         
        }

    }
    #endregion

    #region LoopStructure
    internal class Loop
    {
        public Loop(GraphNode cutpoint)
        {
            if (!cutpoint.IsCutpoint)
            {
                Debugger.Break();
            }
            Cutpoint = cutpoint;
            LoopNodes.Add(Cutpoint);
            foreach (GraphNode gn in Cutpoint.LoopingPred)
            {
                CollectLoopBody(gn);
            }
            CollectLoopExitNodes();
        }

        // Copy Constructor
        public Loop(Loop l, GraphAnalyzer ga, string prefix)
        {
            
            Dictionary<GraphNode, GraphNode> clonemap = new Dictionary<GraphNode, GraphNode>();
            GraphNode clonecutpoint = null;
            foreach (GraphNode gn in l.LoopNodes)
            {
                clonemap[gn] = ga.CloneGraphNode(gn, prefix);
                if (gn == l.Cutpoint) clonecutpoint = clonemap[gn];
            }

            if (clonecutpoint == null)
            {
                Debugger.Break();
                return;
            }
            // Replace the pre and post nodes by the corresponding clone
            foreach (GraphNode gn in l.LoopNodes)
            {
                List<GraphNode> newl = new List<GraphNode>();
                foreach (GraphNode g in clonemap[gn].Pre)
                {
                    if (clonemap.ContainsKey(g)) newl.Add(clonemap[g]);
                    else newl.Add(g);
                }
                clonemap[gn].Pre = newl;
                newl = new List<GraphNode>();
                foreach (GraphNode g in clonemap[gn].Suc)
                {
                    if (clonemap.ContainsKey(g)) newl.Add(clonemap[g]);
                    else newl.Add(g);
                }
                clonemap[gn].Suc = newl;
                newl = new List<GraphNode>();
                foreach (GraphNode g in clonemap[gn].LoopingPred)
                {
                    if (clonemap.ContainsKey(g)) newl.Add(clonemap[g]);
                    else newl.Add(g);
                }
                clonemap[gn].LoopingPred = newl;
            }

            foreach (GraphNode gn in l.Cutpoint.LoopingPred)
            {
                clonecutpoint.LoopingPred.Remove(gn);
                clonecutpoint.LoopingPred.Add(clonemap[gn]);
            }

            

            SucLoops.AddRange(l.SucLoops);
            PreLoops.AddRange(l.PreLoops);
            Cutpoint = clonecutpoint;
            LoopNodes.Add(Cutpoint);
            foreach (GraphNode gn in Cutpoint.LoopingPred)
            {
                CollectLoopBody(gn);
            }
            CollectLoopExitNodes();
        }

        private void CollectLoopBody(GraphNode gn)
        {
            if (gn == Cutpoint) return;
            if (!LoopNodes.Contains(gn))
            {
                if (gn.IsCutpoint) // nested loop found
                {
                    Loop lo = new Loop(gn);
                    foreach (GraphNode lgn in lo.LoopNodes)
                    {
                        if (!LoopNodes.Contains(lgn)) LoopNodes.Add(lgn);
                    }
                    NestedLoops.Add(lo);
                }
                else
                {
                    LoopNodes.Add(gn);
                }
                foreach (GraphNode pre in gn.Pre) if (!gn.LoopingPred.Contains(pre)) CollectLoopBody(pre);
            }
        }

        private void CollectLoopExitNodes()
        {
            foreach (GraphNode gn in LoopNodes)
            {
                foreach (GraphNode gn_ in gn.Suc)
                {
                    if (!LoopNodes.Contains(gn_) && !LoopExitNodes.Contains(gn_)) LoopExitNodes.Add(gn_);
                }
            }
        }

        public GraphNode Cutpoint;
        public List<GraphNode> LoopExitNodes = new List<GraphNode>();
        public List<Loop> NestedLoops = new List<Loop>();
        public List<Loop> SucLoops = new List<Loop>();
        public List<Loop> PreLoops = new List<Loop>();
        public List<GraphNode> LoopNodes = new List<GraphNode>();
    }
    #endregion

    #endregion
}