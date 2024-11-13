using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie;

public class ImplementationControlFlowGraph
{
  public Graph<Block /*!*/> /*!*/
    graph;

  // Map from procedure to the list of blocks that call that procedure
  public Dictionary<string /*!*/, List<Block /*!*/> /*!*/> /*!*/
    procsCalled;

  public HashSet<Block /*!*/> /*!*/
    nodes;

  public Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/> /*!*/
    succEdges;

  public Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/> /*!*/
    predEdges;

  private Dictionary<Block /*!*/, int> /*!*/
    priority;

  public HashSet<Block /*!*/> /*!*/
    srcNodes;

  public HashSet<Block /*!*/> /*!*/
    exitNodes;

  public Dictionary<Block /*!*/, GenKillWeight /*!*/> /*!*/
    weightBefore;

  public Dictionary<Block /*!*/, GenKillWeight /*!*/> /*!*/
    weightAfter;

  public Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
    liveVarsAfter;

  public Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
    liveVarsBefore;

  public GenKillWeight /*!*/
    summary;

  private readonly CoreOptions options;

  public Implementation /*!*/
    impl;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(cce.NonNullElements(graph.Nodes));
    Contract.Invariant(cce.NonNullDictionaryAndValues(procsCalled));
    Contract.Invariant(cce.NonNullElements(nodes));
    Contract.Invariant(cce.NonNullDictionaryAndValues(succEdges));
    Contract.Invariant(cce.NonNullDictionaryAndValues(predEdges));
    Contract.Invariant(priority != null);
    Contract.Invariant(cce.NonNullElements(srcNodes));
    Contract.Invariant(cce.NonNullElements(exitNodes));
    Contract.Invariant(cce.NonNullDictionaryAndValues(weightBefore));
    Contract.Invariant(cce.NonNullDictionaryAndValues(weightAfter));
    Contract.Invariant(cce.NonNullDictionaryAndValues(liveVarsAfter));
    Contract.Invariant(cce.NonNullDictionaryAndValues(liveVarsBefore));
    Contract.Invariant(summary != null);
    Contract.Invariant(impl != null);
  }


  [NotDelayed]
  public ImplementationControlFlowGraph(CoreOptions options, Implementation impl)
  {
    Contract.Requires(impl != null);
    this.graph = new Graph<Block /*!*/>();
    this.procsCalled = new Dictionary<string /*!*/, List<Block /*!*/> /*!*/>();
    this.nodes = new HashSet<Block /*!*/>();
    this.succEdges = new Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/>();
    this.predEdges = new Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/>();

    this.priority = new Dictionary<Block /*!*/, int>();

    this.srcNodes = new HashSet<Block /*!*/>();
    this.exitNodes = new HashSet<Block /*!*/>();

    this.weightBefore = new Dictionary<Block /*!*/, GenKillWeight /*!*/>();
    this.weightAfter = new Dictionary<Block /*!*/, GenKillWeight /*!*/>();
    this.liveVarsAfter = new Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/>();
    this.liveVarsBefore = new Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/>();

    summary = GenKillWeight.zero();
    this.options = options;
    this.impl = impl;

    Initialize(impl);
  }

  private void Initialize(Implementation impl)
  {
    Contract.Requires(impl != null);
    addSource(impl.Blocks[0]);
    graph.AddSource(impl.Blocks[0]);

    foreach (Block /*!*/ b in impl.Blocks)
    {
      Contract.Assert(b != null);
      if (b.TransferCmd is ReturnCmd)
      {
        exitNodes.Add(b);
      }
      else
      {
        GotoCmd gc = b.TransferCmd as GotoCmd;
        Contract.Assert(gc != null);
        Contract.Assert(gc.LabelTargets != null);
        foreach (Block /*!*/ t in gc.LabelTargets)
        {
          Contract.Assert(t != null);
          addEdge(b, t);
          graph.AddEdge(b, t);
        }
      }

      weightBefore[b] = GenKillWeight.zero();
      weightAfter[b] = GenKillWeight.zero();

      foreach (Cmd /*!*/ c in b.Cmds)
      {
        Contract.Assert(c != null);
        if (c is CallCmd)
        {
          CallCmd /*!*/
            cc = cce.NonNull((CallCmd /*!*/) c);
          Contract.Assert(cc.Proc != null);
          string /*!*/
            procName = cc.Proc.Name;
          Contract.Assert(procName != null);
          if (!procsCalled.ContainsKey(procName))
          {
            procsCalled.Add(procName, new List<Block /*!*/>());
          }

          procsCalled[procName].Add(b);
        }
      }
    }

    graph.TarjanTopSort(out var acyclic, out var sortedNodes);

    if (!acyclic)
    {
      options.OutputWriter.WriteLine("Warning: graph is not a dag");
    }

    int num = sortedNodes.Count;
    foreach (Block /*!*/ b in sortedNodes)
    {
      Contract.Assert(b != null);
      priority.Add(b, num);
      num--;
    }
  }

  public int getPriority(Block b)
  {
    Contract.Requires(b != null);
    if (priority.ContainsKey(b))
    {
      return priority[b];
    }

    return Int32.MaxValue;
  }

  private void addSource(Block b)
  {
    Contract.Requires(b != null);
    registerNode(b);
    this.srcNodes.Add(b);
  }

  private void addExit(Block b)
  {
    Contract.Requires(b != null);
    registerNode(b);
    this.exitNodes.Add(b);
  }

  private void registerNode(Block b)
  {
    Contract.Requires(b != null);
    if (!succEdges.ContainsKey(b))
    {
      succEdges.Add(b, new HashSet<Block /*!*/>());
    }

    if (!predEdges.ContainsKey(b))
    {
      predEdges.Add(b, new HashSet<Block /*!*/>());
    }

    nodes.Add(b);
  }

  private void addEdge(Block src, Block tgt)
  {
    Contract.Requires(tgt != null);
    Contract.Requires(src != null);
    registerNode(src);
    registerNode(tgt);

    succEdges[src].Add(tgt);
    predEdges[tgt].Add(src);
  }
}