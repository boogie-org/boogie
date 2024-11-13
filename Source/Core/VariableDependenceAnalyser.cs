using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public interface IVariableDependenceAnalyser
  {
    void Analyse();
    VariableDescriptor MakeDescriptor(string proc, Variable v);
    HashSet<VariableDescriptor> DependsOn(VariableDescriptor v);
    void Dump();
    void ShowDependencyChain(VariableDescriptor source, VariableDescriptor target);
    bool VariableRelevantToAnalysis(Variable v, string proc);
    bool Ignoring(Variable v, string proc);
  }

  public abstract class VariableDescriptor : IComparable
  {
    internal readonly string Name;

    internal VariableDescriptor(string Name)
    {
      this.Name = Name;
    }

    public override string ToString()
    {
      return Name;
    }

    public override bool Equals(object that)
    {
      if (object.ReferenceEquals(this, that))
      {
        return true;
      }

      VariableDescriptor thatDescriptor = that as VariableDescriptor;

      if (thatDescriptor == null)
      {
        return false;
      }

      return this.Name.Equals(thatDescriptor.Name);
    }

    public override int GetHashCode()
    {
      return Name.GetHashCode();
    }

    public int CompareTo(object that)
    {
      return this.ToString().CompareTo(that.ToString());
    }
  }

  public class LocalDescriptor : VariableDescriptor
  {
    internal readonly string Proc;

    public LocalDescriptor(string Proc, string Name)
      : base(Name)
    {
      this.Proc = Proc;
    }

    public override string ToString()
    {
      return Proc + "." + base.ToString();
    }

    public override bool Equals(object that)
    {
      if (object.ReferenceEquals(this, that))
      {
        return true;
      }

      LocalDescriptor thatDescriptor = that as LocalDescriptor;

      if (thatDescriptor == null)
      {
        return false;
      }

      return base.Equals(thatDescriptor) &&
             this.Proc.Equals(thatDescriptor.Proc);
    }

    public override int GetHashCode()
    {
      return (33 * base.GetHashCode())
             + this.Proc.GetHashCode();
    }
  }

  public class GlobalDescriptor : VariableDescriptor
  {
    public GlobalDescriptor(string name) : base(name)
    {
    }

    public override bool Equals(object that)
    {
      if (object.ReferenceEquals(this, that))
      {
        return true;
      }

      GlobalDescriptor thatDescriptor = that as GlobalDescriptor;

      if (thatDescriptor == null)
      {
        return false;
      }

      return base.Equals(thatDescriptor);
    }

    public override int GetHashCode()
    {
      return base.GetHashCode();
    }
  }

  /// <summary>
  /// Given a Boogie program, computes a graph that over-approximates dependences
  /// between program variables.
  /// </summary>
  public class VariableDependenceAnalyser : IVariableDependenceAnalyser
  {
    private CoreOptions options;
    private Graph<VariableDescriptor> dependsOnNonTransitive;
    private Program prog;
    private Dictionary<Block, HashSet<Block>> blockToControllingBlocks;
    private Dictionary<Block, HashSet<VariableDescriptor>> controllingBlockToVariables;

    public VariableDependenceAnalyser(Program prog, CoreOptions options)
    {
      this.prog = prog;
      this.options = options;
      dependsOnNonTransitive = new Graph<VariableDescriptor>();
    }


    private void Initialise()
    {
      foreach (var descriptor in
        prog.Variables.Where(item => VariableRelevantToAnalysis(item, null)).Select(variable => variable.Name)
          .Select(name => new GlobalDescriptor(name)))
      {
        dependsOnNonTransitive.AddEdge(descriptor, descriptor);
      }

      foreach (var proc in prog.NonInlinedProcedures())
      {
        List<Variable> parameters = new List<Variable>();
        parameters.AddRange(proc.InParams);
        parameters.AddRange(proc.OutParams);
        foreach (var descriptor in
          parameters.Select(variable => variable.Name).Select(name => new LocalDescriptor(proc.Name, name)))
        {
          dependsOnNonTransitive.AddEdge(descriptor, descriptor);
        }
      }

      foreach (var impl in prog.NonInlinedImplementations())
      {
        List<Variable> locals = new List<Variable>();
        locals.AddRange(impl.LocVars);
        foreach (var descriptor in
          locals.Select(variable => variable.Name).Select(name => new LocalDescriptor(impl.Name, name)))
        {
          dependsOnNonTransitive.AddEdge(descriptor, descriptor);
        }
      }
    }

    private List<VariableDescriptor> ComputeDependencyChain(VariableDescriptor source, VariableDescriptor target,
      HashSet<VariableDescriptor> visited)
    {
      if (source.Equals(target))
      {
        return new List<VariableDescriptor> {target};
      }

      visited.Add(source);

      foreach (var w in dependsOnNonTransitive.Successors(source))
      {
        if (visited.Contains(w))
        {
          continue;
        }

        var result = ComputeDependencyChain(w, target, visited);
        if (result != null)
        {
          result.Insert(0, source);
          return result;
        }
      }

      return null;
    }

    public void ShowDependencyChain(VariableDescriptor source, VariableDescriptor target)
    {
      var chain = ComputeDependencyChain(source, target, new HashSet<VariableDescriptor>());
      if (chain == null)
      {
        options.OutputWriter.WriteLine("No chain between " + source + " and " + target);
      }
      else
      {
        bool first = true;
        foreach (var v in chain)
        {
          if (first)
          {
            first = false;
          }
          else
          {
            options.OutputWriter.Write(" -> ");
          }

          options.OutputWriter.Write(v);
        }
      }

      options.OutputWriter.WriteLine();
      options.OutputWriter.WriteLine();
    }

    public void Analyse()
    {
      /* The algorithm is as follows:
       * 
       * 1. Build global control dependence graph.  First build control dependence graph for each procedure,
       *    and union them.  Then examine each procedure.  If block B is control-dependent on block C, make
       *    every block that can be indirectly reached via a call from B control-dependent on C.
       *    
       * 2. Take transitive closure of global control dependence graph.
       * 
       * 3. For every block B such that some other block is control-dependent on B, determine those variables
       *    which B tests.  If B tests v, and C is control-depdendent on B, we say that v "controls" the
       *    statements appearing in C.
       *    
       * 4. Consider each statement to work out variable dependences.  v may depend on u if:
       *       - there is a statement v := e where u appears in e
       *       - there is a statement call ... := foo(..., e, ...) where v is formal in parameter of foo 
       *         corresponding to e and u appears in e
       *       - there is a statement call ..., v, ... := foo(...) where u is formal out parameter of foo 
       *         correspondnig to v
       *       - there is a statement v := ... controlled by u
       *       - there is a statement call ... := foo(...) controlled by u where v is a formal in parameter
       *         of foo
       *       - there is a statement call ..., v, ... := foo(...) controlled by u
       *       
       * 5. Finialise variable dependence graph by taking its transitive closure.
       * 
       */

      if (options.Trace)
      {
        options.OutputWriter.WriteLine("Variable dependence analysis: Initialising");
      }

      Initialise();

      if (options.Trace)
      {
        options.OutputWriter.WriteLine("Variable dependence analysis: Computing control dependence info");
      }

      blockToControllingBlocks = ComputeGlobalControlDependences();

      if (options.Trace)
      {
        options.OutputWriter.WriteLine("Variable dependence analysis: Computing control dependence variables");
      }

      controllingBlockToVariables = ComputeControllingVariables(blockToControllingBlocks);
      foreach (var impl in prog.NonInlinedImplementations())
      {
        if (options.Trace)
        {
          options.OutputWriter.WriteLine("Variable dependence analysis: Analysing " + impl.Name);
        }

        Analyse(impl);
      }
    }

    private void Analyse(Implementation impl)
    {
      string proc = impl.Name;
      foreach (Block b in impl.Blocks)
      {
        Analyse(proc, b);
      }
    }

    private void Analyse(string proc, Block b)
    {
      foreach (Cmd cmd in b.Cmds)
      {
        AssignCmd assign = cmd as AssignCmd;
        if (assign != null)
        {
          HandleAssign(proc, b, assign);
        }

        CallCmd call = cmd as CallCmd;
        if (call != null)
        {
          HandleCall(proc, b, call);
        }
      }
    }

    private void HandleCall(string proc, Block b, CallCmd call)
    {
      foreach (var formalActualPair in call.Proc.InParams.Zip(call.Ins))
      {
        var formalIn = MakeDescriptor(call.callee, formalActualPair.Item1);
        AddDependences(formalIn, GetReferencedVariables(formalActualPair.Item2, proc),
          "referenced in in-param in call to " + proc, call.tok);
        AddControlDependences(b, formalIn, " in param assigned under control dependence in call to " + proc, call.tok);
      }

      foreach (var formalActualPair in call.Proc.OutParams.Zip(call.Outs))
      {
        var actualOut = MakeDescriptor(proc, formalActualPair.Item2.Decl);
        AddDependences(actualOut,
          GetReferencedVariables(new IdentifierExpr(Token.NoToken, formalActualPair.Item1), call.callee),
          "receiving variable for out-param in call to " + proc, call.tok);
        AddControlDependences(b, actualOut, " receiving variable assigned under control dependence in call to " + proc,
          call.tok);
      }
    }

    private void HandleAssign(string proc, Block b, AssignCmd assign)
    {
      foreach (var assignPair in assign.Lhss.Zip(assign.Rhss).Where(
        item => VariableRelevantToAnalysis(item.Item1.DeepAssignedVariable, proc)))
      {
        VariableDescriptor assignedVariable = MakeDescriptor(proc, assignPair.Item1.DeepAssignedVariable);
        AddDependences(assignedVariable, GetReferencedVariables(assignPair.Item1, proc),
          "LHS of assignment", assign.tok);
        AddDependences(assignedVariable, GetReferencedVariables(assignPair.Item2, proc),
          "RHS of assignment", assign.tok);
        AddControlDependences(b, assignedVariable, "Variable assigned under control dependence", assign.tok);
      }
    }

    private void AddControlDependences(Block b, VariableDescriptor v, string reason, IToken tok)
    {
      if (!blockToControllingBlocks.ContainsKey(b))
      {
        return;
      }

      foreach (var controller in blockToControllingBlocks[b])
      {
        AddDependences(v, controllingBlockToVariables[controller],
          reason + " controlling block at (" + controller.tok.line + ":" + controller.tok.col + ")", tok);
      }
    }

    private IEnumerable<VariableDescriptor> GetReferencedVariables(Absy node, string proc)
    {
      var varCollector = new VariableCollector();
      varCollector.Visit(node);
      return varCollector.usedVars.Where(item => VariableRelevantToAnalysis(item, proc))
        .Select(item => MakeDescriptor(proc, item));
    }

    void AddDependences(VariableDescriptor v, IEnumerable<VariableDescriptor> vs, string reason, IToken tok)
    {
      foreach (var n in vs)
      {
        if (options.DebugStagedHoudini)
        {
          options.OutputWriter.WriteLine("Adding dependence " + v + " -> " + n + ", reason: " + reason + "(" + tok.line + ":" +
                                         tok.col + ")");
        }

        dependsOnNonTransitive.AddEdge(v, n);
      }
    }

    private Dictionary<Block, HashSet<VariableDescriptor>> ComputeControllingVariables(
      Dictionary<Block, HashSet<Block>> globalCtrlDep)
    {
      var result = new Dictionary<Block, HashSet<VariableDescriptor>>();
      foreach (var impl in prog.NonInlinedImplementations())
      {
        foreach (var b in impl.Blocks)
        {
          result[b] = GetControlDependencyVariables(impl.Name, b);
        }
      }

      return result;
    }

    private HashSet<VariableDescriptor> GetControlDependencyVariables(string proc, Block b)
    {
      // This method works under the assumption that assume statements
      // relevant to control flow between basic blocks have the "partition" attribute

      HashSet<VariableDescriptor> result = new HashSet<VariableDescriptor>();
      var gotoCmd = b.TransferCmd as GotoCmd;
      if (gotoCmd != null && gotoCmd.LabelTargets.Count >= 2)
      {
        foreach (Block succ in gotoCmd.LabelTargets)
        {
          foreach (Cmd c in succ.Cmds)
          {
            AssumeCmd a = c as AssumeCmd;
            if (a != null && a.Attributes.FindBoolAttribute("partition"))
            {
              var varCollector = new VariableCollector();
              varCollector.VisitExpr(a.Expr);
              result.UnionWith(varCollector.usedVars.Where(item => VariableRelevantToAnalysis(item, proc))
                .Select(item => MakeDescriptor(proc, item)));
            }
            else
            {
              break;
            }
          }
        }
      }

      return result;
    }

    private HashSet<VariableDescriptor> ignoredVariables;

    public bool Ignoring(Variable v, string proc)
    {
      if (ignoredVariables == null)
      {
        MakeIgnoreList();
      }

      if (proc != null && ignoredVariables.Contains(new LocalDescriptor(proc, v.Name)))
      {
        return true;
      }

      if (ignoredVariables.Contains(new GlobalDescriptor(v.Name)))
      {
        return true;
      }

      return false;
    }

    public bool VariableRelevantToAnalysis(Variable v, string proc)
    {
      return !(v is Constant || Ignoring(v, proc));
    }

    private void MakeIgnoreList()
    {
      ignoredVariables = new HashSet<VariableDescriptor>();
      if (options.VariableDependenceIgnore == null)
      {
        return;
      }

      try
      {
        var file = System.IO.File.OpenText(options.VariableDependenceIgnore);
        while (!file.EndOfStream)
        {
          string line = file.ReadLine();
          string[] tokens = line.Split(' ');
          if (tokens.Count() == 0)
          {
            continue;
          }

          if (tokens.Count() > 2)
          {
            Console.Error.WriteLine("Ignoring malformed line of ignored variables file: " + line);
            continue;
          }

          if (tokens.Count() == 1)
          {
            ignoredVariables.Add(new GlobalDescriptor(tokens[0]));
            continue;
          }

          Debug.Assert(tokens.Count() == 2);
          ignoredVariables.Add(new LocalDescriptor(tokens[0], tokens[1]));
        }
      }
      catch (System.IO.IOException e)
      {
        Console.Error.WriteLine("Error reading from ignored variables file " +
                                options.VariableDependenceIgnore + ": " + e);
      }
    }

    private Dictionary<Block, HashSet<Block>> ComputeGlobalControlDependences()
    {
      var globalCtrlDep = new Dictionary<Block, HashSet<Block>>();
      var localCtrlDeps =
        new Dictionary<Implementation, Dictionary<Block, HashSet<Block>>>();

      // Work out and union together local control dependences
      foreach (var impl in prog.NonInlinedImplementations())
      {
        var blockGraph = prog.ProcessLoops(options, impl);
        localCtrlDeps[impl] = blockGraph.ControlDependence(new Block(prog.tok, new ReturnCmd(prog.tok)));
        foreach (var keyValue in localCtrlDeps[impl])
        {
          globalCtrlDep.Add(keyValue.Key, keyValue.Value);
        }
      }

      Graph<Implementation> callGraph = Program.BuildCallGraph(options, prog);

      // Add inter-procedural control dependence nodes based on calls
      foreach (var impl in prog.NonInlinedImplementations())
      {
        foreach (var b in impl.Blocks)
        {
          foreach (var cmd in b.Cmds.OfType<CallCmd>())
          {
            var directCallee = GetImplementation(cmd.callee);
            if (directCallee == null)
            {
              continue;
            }

            var indirectCallees = ComputeIndirectCallees(callGraph, directCallee);
            foreach (var control in GetControllingBlocks(b, localCtrlDeps[impl]))
            {
              foreach (var c in indirectCallees.Select(item => item.Blocks).SelectMany(item => item))
              {
                globalCtrlDep[control].Add(c);
              }
            }
          }
        }
      }

      // Compute transitive closure
      globalCtrlDep.TransitiveClosure();

      // Finally reverse the dependences

      Dictionary<Block, HashSet<Block>> result = new Dictionary<Block, HashSet<Block>>();

      foreach (var KeyValue in globalCtrlDep)
      {
        foreach (var v in KeyValue.Value)
        {
          if (!result.ContainsKey(v))
          {
            result[v] = new HashSet<Block>();
          }

          result[v].Add(KeyValue.Key);
        }
      }

      return result;
    }

    private HashSet<Implementation> ComputeIndirectCallees(Graph<Implementation> callGraph, Implementation directCallee)
    {
      return ComputeIndirectCallees(callGraph, directCallee, new HashSet<Implementation>());
    }

    private HashSet<Implementation> ComputeIndirectCallees(Graph<Implementation> callGraph, Implementation directCallee,
      HashSet<Implementation> seen)
    {
      if (seen.Contains(directCallee))
      {
        return new HashSet<Implementation>();
      }

      HashSet<Implementation> result = new HashSet<Implementation>();
      result.Add(directCallee);
      seen.Add(directCallee);
      foreach (var succ in callGraph.Successors(directCallee))
      {
        result.UnionWith(ComputeIndirectCallees(callGraph, succ, seen));
      }

      return result;
    }

    private HashSet<Block> GetControllingBlocks(Block b, Dictionary<Block, HashSet<Block>> ctrlDep)
    {
      HashSet<Block> result = new HashSet<Block>();
      foreach (var keyValue in ctrlDep)
      {
        if (keyValue.Value.Contains(b))
        {
          result.Add(keyValue.Key);
        }
      }

      return result;
    }

    private Implementation GetImplementation(string proc)
    {
      foreach (var impl in prog.Implementations)
      {
        if (impl.Name.Equals(proc))
        {
          return impl;
        }
      }

      return null;
    }

    public VariableDescriptor MakeDescriptor(string proc, Variable v)
    {
      // Check whether there is an (Impl, v) match
      var matchingLocals = dependsOnNonTransitive.Nodes.Where(item => item is LocalDescriptor).Select(
        item => (LocalDescriptor) item).Where(item => item.Proc.Equals(proc) &&
                                                      item.Name.Equals(v.Name));
      if (matchingLocals.Count() > 0)
      {
        Debug.Assert(matchingLocals.Count() == 1);
        return matchingLocals.ToArray()[0];
      }

      // It must be a global with same name as v
      return dependsOnNonTransitive.Nodes.Where(item => item is GlobalDescriptor &&
                                                        item.Name.Equals(v.Name)).ToArray()[0];
    }

    private Dictionary<SCC<VariableDescriptor>, HashSet<VariableDescriptor>> dependsOnCache =
      new Dictionary<SCC<VariableDescriptor>, HashSet<VariableDescriptor>>();

    private Graph<SCC<VariableDescriptor>> dependsOnScCsDag;
    private Dictionary<VariableDescriptor, SCC<VariableDescriptor>> variableDescriptorToScc;

    public HashSet<VariableDescriptor> DependsOn(VariableDescriptor v)
    {
      if (dependsOnScCsDag == null)
      {
        if (options.Trace)
        {
          options.OutputWriter.WriteLine("Variable dependence: computing SCCs");
        }

        Adjacency<VariableDescriptor> next = new Adjacency<VariableDescriptor>(dependsOnNonTransitive.Successors);
        Adjacency<VariableDescriptor> prev = new Adjacency<VariableDescriptor>(dependsOnNonTransitive.Predecessors);
        StronglyConnectedComponents<VariableDescriptor> dependsOnScCs =
          new StronglyConnectedComponents<VariableDescriptor>(
            dependsOnNonTransitive.Nodes, next, prev);
        dependsOnScCs.Compute();

        variableDescriptorToScc = new Dictionary<VariableDescriptor, SCC<VariableDescriptor>>();
        foreach (var scc in dependsOnScCs)
        {
          foreach (var s in scc)
          {
            variableDescriptorToScc[s] = scc;
          }
        }

        dependsOnScCsDag = new Graph<SCC<VariableDescriptor>>();
        foreach (var edge in dependsOnNonTransitive.Edges)
        {
          if (variableDescriptorToScc[edge.Item1] != variableDescriptorToScc[edge.Item2])
          {
            dependsOnScCsDag.AddEdge(variableDescriptorToScc[edge.Item1], variableDescriptorToScc[edge.Item2]);
          }
        }

        SCC<VariableDescriptor> dummy = new SCC<VariableDescriptor>();
        foreach (var n in dependsOnNonTransitive.Nodes)
        {
          dependsOnScCsDag.AddEdge(variableDescriptorToScc[n], dummy);
        }

        if (options.Trace)
        {
          options.OutputWriter.WriteLine("Variable dependence: SCCs computed!");
        }
      }

      return DependsOn(variableDescriptorToScc[v]);
    }

    public HashSet<VariableDescriptor> DependsOn(SCC<VariableDescriptor> vScc)
    {
      if (!dependsOnCache.ContainsKey(vScc))
      {
        HashSet<VariableDescriptor> result = new HashSet<VariableDescriptor>();
        if (vScc.Count() > 0)
        {
          result.UnionWith(vScc);
          foreach (var wScc in dependsOnScCsDag.Successors(vScc))
          {
            result.UnionWith(DependsOn(wScc));
          }
        }

        dependsOnCache[vScc] = result;
      }

      return dependsOnCache[vScc];
    }

    public void Dump()
    {
      options.OutputWriter.WriteLine("Variable dependence information");
      options.OutputWriter.WriteLine("===============================");

      options.OutputWriter.WriteLine("Global variables");
      options.OutputWriter.WriteLine("================");

      foreach (var globalEntry in dependsOnNonTransitive.Nodes.Where(item => item is GlobalDescriptor))
      {
        Dump(globalEntry);
      }

      foreach (var proc in Procedures())
      {
        options.OutputWriter.WriteLine("Variables of " + proc);
        options.OutputWriter.WriteLine("=====================");
        foreach (var localEntry in dependsOnNonTransitive.Nodes.Where(item => item is LocalDescriptor
                                                                              && ((LocalDescriptor) item).Proc.Equals(
                                                                                proc)))
        {
          Dump(localEntry);
        }
      }
    }

    private void Dump(VariableDescriptor vd)
    {
      options.OutputWriter.Write(vd + " <- {");
      bool first = true;

      var sortedDependents = DependsOn(vd).ToList();
      sortedDependents.Sort();
      foreach (var descriptor in sortedDependents)
      {
        options.OutputWriter.Write((first ? "" : ",") + "\n  " + descriptor);
        if (first)
        {
          first = false;
        }
      }

      Debug.Assert(!first);
      options.OutputWriter.WriteLine("\n}\n");
    }

    private HashSet<string> Procedures()
    {
      return new HashSet<string>(dependsOnNonTransitive.Nodes.Where(item =>
        item is LocalDescriptor).Select(item => ((LocalDescriptor) item).Proc));
    }
  }

  public static class Helper
  {
    public static IEnumerable<Procedure> NonInlinedProcedures(this Program prog)
    {
      return prog.Procedures.Where(Item => QKeyValue.FindIntAttribute(Item.Attributes, "inline", -1) == -1);
    }

    public static IEnumerable<Implementation> NonInlinedImplementations(this Program prog)
    {
      return prog.Implementations.Where(Item => QKeyValue.FindIntAttribute(Item.Proc.Attributes, "inline", -1) == -1);
    }
  }
}