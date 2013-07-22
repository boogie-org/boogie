
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
      
    }

    private IEnumerable<Block> OriginalProgramBlocks()
    {
      return prog.TopLevelDeclarations.OfType<Implementation>().Select(Item => Item.Blocks).SelectMany(Item => Item);
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
          gotoCmd.labelTargets = new BlockSeq { newProcedureEntryNodes[proc] };
          gotoCmd.labelNames = new StringSeq { newProcedureEntryNodes[proc].Label };
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
          BlockSeq newTargets = new BlockSeq();
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
      foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>())
      {
        if (!newProcedureEntryNodes.ContainsKey(proc.Name))
        {
          Block newBlock = new Block(Token.NoToken, proc + "__dummy_node", new List<Cmd>(), new GotoCmd(Token.NoToken, new BlockSeq()));
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
      foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
      {
        string exitLabel = "__" + impl.Name + "_newExit";
        Block newExit = new Block(Token.NoToken, exitLabel, new List<Cmd>(), new GotoCmd(Token.NoToken, new BlockSeq()));
        nodes.Add(newExit);
        newProcedureExitNodes[impl.Name] = newExit;
        foreach (Block b in impl.Blocks)
        {
          List<List<Cmd>> partition = PartitionCmds(b.Cmds);
          Block prev = null;
          int i = 0;
          foreach (List<Cmd> cmds in partition)
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
              prev.TransferCmd = new GotoCmd(Token.NoToken, new StringSeq { label }, new BlockSeq { newBlock });
            }
            prev = newBlock;
            i++;
          }
          Debug.Assert(prev != null);
          if (b.TransferCmd is ReturnCmd || (b.TransferCmd is GotoCmd &&
              ((GotoCmd)b.TransferCmd).labelTargets.Count == 0))
          {
            prev.TransferCmd = new GotoCmd(Token.NoToken, new StringSeq { exitLabel }, new BlockSeq { newExit });
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

    private List<List<Cmd>> PartitionCmds(List<Cmd> cmds) {
      List<List<Cmd>> result = new List<List<Cmd>>();
      List<Cmd> current = new List<Cmd>();
      result.Add(current);
      foreach(Cmd cmd in cmds) {
        if(cmd is CallCmd && current.Count > 0) {
           current = new List<Cmd>();
           result.Add(current);
        }
        current.Add(cmd);
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
