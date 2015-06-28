
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{

  public interface IInterproceduralReachabilityGraph {

    bool MayReach(Block src, Block dst);

    void dump();

    Block GetNewEntryBlock(string p);

    Block GetNewExitBlock(string p);

    Block GetNewBlock(Block block);
  }

  public class InterproceduralReachabilityGraph : IInterproceduralReachabilityGraph
  {

    private Program prog;
    private HashSet<Block> nodes;
    private Dictionary<Block, Block> originalToNew;
    private Dictionary<string, Block> newProcedureEntryNodes;
    private Dictionary<string, Block> newProcedureExitNodes;
    
    private Graph<Block> reachabilityGraph;

    public InterproceduralReachabilityGraph(Program prog) {
      this.prog = prog;
      originalToNew = new Dictionary<Block,Block>();
      newProcedureEntryNodes = new Dictionary<string,Block>();
      newProcedureExitNodes = new Dictionary<string,Block>();
      nodes = new HashSet<Block>();

      ProcessImplementations();

      ProcessBodilessProcedures();

      PatchUpGotoTargets();

      AddCallAndReturnEdges();

      reachabilityGraph = new Graph<Block>();

      foreach(var n in nodes) {
        GotoCmd gotoCmd = n.TransferCmd as GotoCmd;
        if(gotoCmd != null) {
          foreach(Block b in gotoCmd.labelTargets) {
            reachabilityGraph.AddEdge(n, b);
          }
        }
      }

      foreach(var n in nodes) {
        // If there are disconnected nodes, put them into the
        // graph as self-loops so that every node is represented in
        // the graph
        if(!reachabilityGraph.Nodes.Contains(n)) {
          reachabilityGraph.AddEdge(n, n);
        }
      }
    }

    private IEnumerable<Block> OriginalProgramBlocks()
    {
      return prog.Implementations.Select(Item => Item.Blocks).SelectMany(Item => Item);
    }

    private void AddCallAndReturnEdges()
    {
      #region Add call and return edges
      foreach (var n in nodes)
      {
        if (n.Cmds.Count == 1 && n.Cmds[0] is CallCmd)
        {
          string proc = ((CallCmd)n.Cmds[0]).callee;
          GotoCmd gotoCmd = n.TransferCmd as GotoCmd;
          Debug.Assert(gotoCmd != null);

          for (int i = 0; i < gotoCmd.labelTargets.Count; i++)
          {
            (newProcedureExitNodes[proc].TransferCmd as GotoCmd).labelTargets.Add(gotoCmd.labelTargets[i]);
            (newProcedureExitNodes[proc].TransferCmd as GotoCmd).labelNames.Add(gotoCmd.labelNames[i]);
          }
          gotoCmd.labelTargets = new List<Block> { newProcedureEntryNodes[proc] };
          gotoCmd.labelNames = new List<String> { newProcedureEntryNodes[proc].Label };
        }
      }
      #endregion
    }

    private void PatchUpGotoTargets()
    {
      #region Patch up goto targets
      foreach (var n in nodes)
      {
        var gotoCmd = n.TransferCmd as GotoCmd;
        if (gotoCmd != null)
        {
          List<Block> newTargets = new List<Block>();
          foreach (Block t in gotoCmd.labelTargets)
          {
            if (originalToNew.ContainsKey(t))
            {
              newTargets.Add(originalToNew[t]);
            }
            else
            {
              newTargets.Add(t);
            }
          }
          gotoCmd.labelTargets = newTargets;
        }
      }
      #endregion
    }

    private void ProcessBodilessProcedures()
    {
      #region Add single node CFG for procedures with no body
      foreach (var proc in prog.Procedures)
      {
        if (!newProcedureEntryNodes.ContainsKey(proc.Name))
        {
          Block newBlock = new Block(Token.NoToken, proc + "__dummy_node", new List<Cmd>(), new GotoCmd(Token.NoToken, new List<Block>()));
          nodes.Add(newBlock);
          newProcedureEntryNodes[proc.Name] = newBlock;
          newProcedureExitNodes[proc.Name] = newBlock;
        }
      }
      #endregion
    }

    private void ProcessImplementations()
    {
      #region Transform implementation CFGs so that every call is in its own basic block
      foreach (var impl in prog.Implementations)
      {
        string exitLabel = "__" + impl.Name + "_newExit";
        Block newExit = new Block(Token.NoToken, exitLabel, new List<Cmd>(), new GotoCmd(Token.NoToken, new List<Block>()));
        nodes.Add(newExit);
        newProcedureExitNodes[impl.Name] = newExit;
        foreach (Block b in impl.Blocks)
        {
          Block prev = null;
          int i = 0;
          foreach (List<Cmd> cmds in SeparateCallCmds(b.Cmds))
          {
            Block newBlock;
            if (prev == null)
            {
              newBlock = new Block(b.tok, "__" + impl.Name + "_" + b.Label, new List<Cmd>(cmds.ToArray()), null);
              nodes.Add(newBlock);
              originalToNew[b] = newBlock;
              if (impl.Blocks[0] == b)
              {
                newProcedureEntryNodes[impl.Name] = newBlock;
              }
            }
            else
            {
              string label = "__" + impl.Name + "_" + b.Label + "_call_" + i;
              newBlock = new Block(b.tok, label, new List<Cmd>(cmds.ToArray()), null);
              nodes.Add(newBlock);
              originalToNew[newBlock] = newBlock;
              prev.TransferCmd = new GotoCmd(Token.NoToken, new List<String> { label }, new List<Block> { newBlock });
            }
            prev = newBlock;
            i++;
          }
          Debug.Assert(prev != null);
          if (b.TransferCmd is ReturnCmd || (b.TransferCmd is GotoCmd &&
              ((GotoCmd)b.TransferCmd).labelTargets.Count == 0))
          {
            prev.TransferCmd = new GotoCmd(Token.NoToken, new List<String> { exitLabel }, new List<Block> { newExit });
          }
          else
          {
            if(b.TransferCmd is ReturnCmd) {
              prev.TransferCmd = new ReturnCmd(b.TransferCmd.tok);
            } else {
              var gotoCmd = b.TransferCmd as GotoCmd;
              Debug.Assert(gotoCmd != null);
              prev.TransferCmd = new GotoCmd(gotoCmd.tok, gotoCmd.labelNames, gotoCmd.labelTargets);
            }
          }
        }
      }
      #endregion
    }

    private static List<List<Cmd>> SeparateCallCmds(List<Cmd> Cmds) {
      List<List<Cmd>> result = new List<List<Cmd>>();
      int currentIndex = 0;
      while(currentIndex < Cmds.Count) {
        if(Cmds[currentIndex] is CallCmd) {
          result.Add(new List<Cmd> { Cmds[currentIndex] });
          currentIndex++;
        } else {
          List<Cmd> nonCallCmds = new List<Cmd>();
          while(currentIndex < Cmds.Count && !(Cmds[currentIndex] is CallCmd)) {
            nonCallCmds.Add(Cmds[currentIndex]);
            currentIndex++;
          }
          result.Add(nonCallCmds);
        }
      }
      if(result.Count == 0) {
        result.Add(new List<Cmd>());
      }
      return result;
    }

    private Graph<SCC<Block>> ReachabilityGraphSCCsDAG;
    private Dictionary<Block, SCC<Block>> BlockToSCC;

    private Dictionary<SCC<Block>, HashSet<Block>> MayReachCache = new Dictionary<SCC<Block>, HashSet<Block>>();

    public bool MayReach(Block src, Block dst) {
      if (ReachabilityGraphSCCsDAG == null) {
        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("Interprocedural reachability: computing SCCs");
        }
        Adjacency<Block> next = new Adjacency<Block>(reachabilityGraph.Successors);
        Adjacency<Block> prev = new Adjacency<Block>(reachabilityGraph.Predecessors);
        StronglyConnectedComponents<Block> ReachabilitySCCs = new StronglyConnectedComponents<Block>(
          reachabilityGraph.Nodes, next, prev);
        ReachabilitySCCs.Compute();

        BlockToSCC = new Dictionary<Block, SCC<Block>>();
        foreach (var scc in ReachabilitySCCs) {
          foreach (var s in scc) {
            BlockToSCC[s] = scc;
          }
        }

        ReachabilityGraphSCCsDAG = new Graph<SCC<Block>>();
        foreach (var edge in reachabilityGraph.Edges) {
          if (BlockToSCC[edge.Item1] != BlockToSCC[edge.Item2]) {
            ReachabilityGraphSCCsDAG.AddEdge(BlockToSCC[edge.Item1], BlockToSCC[edge.Item2]);
          }
        }

        SCC<Block> dummy = new SCC<Block>();
        foreach (var n in reachabilityGraph.Nodes) {
          ReachabilityGraphSCCsDAG.AddEdge(BlockToSCC[n], dummy);
        }

        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("Interprocedural reachability: SCCs computed!");
        }
      }
      return ReachableFrom(BlockToSCC[src]).Contains(dst);
    }

    private HashSet<Block> ReachableFrom(SCC<Block> scc) {
       if (!MayReachCache.ContainsKey(scc)) {
        HashSet<Block> result = new HashSet<Block>();
        if (scc.Count() > 0) {
          result.UnionWith(scc);
          foreach (var nextSCC in ReachabilityGraphSCCsDAG.Successors(scc)) {
            result.UnionWith(ReachableFrom(nextSCC));
          }
        }
        MayReachCache[scc] = result;
      }
      return MayReachCache[scc];
    }

    public void dump() {
      foreach(var n in nodes) {
        Console.WriteLine(n.Label + " -> {");
        GotoCmd gotoCmd = n.TransferCmd as GotoCmd;
        if(n != null) {
          foreach(Block m in gotoCmd.labelTargets) {
            Console.WriteLine("   " + m.Label);
          }
        }
        Console.WriteLine("}");
      }
    }

    public Block GetNewEntryBlock(string proc) {
      return newProcedureEntryNodes[proc];
    }

    public Block GetNewExitBlock(string proc) {
      return newProcedureExitNodes[proc];
    }

    public Block GetNewBlock(Block b) {
      return originalToNew[b];
    }

  }


}
