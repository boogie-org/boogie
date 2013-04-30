using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;


namespace Microsoft.Boogie {

  public interface IVariableDependenceAnalyser {

    void Analyse();
    VariableDescriptor MakeDescriptor(string proc, Variable v);
    HashSet<VariableDescriptor> DependsOn(VariableDescriptor v);
    void dump();

  }

  public abstract class VariableDescriptor : IComparable {
    internal readonly string Name;
    internal VariableDescriptor(string Name) {
      this.Name = Name;
    }

    public override string ToString() {
      return Name;
    }

    public override bool Equals(object that) {

      if (object.ReferenceEquals(this, that)) {
        return true;
      }

      VariableDescriptor thatDescriptor = that as VariableDescriptor;

      if (thatDescriptor == null) {
        return false;
      }

      return base.Equals(thatDescriptor) &&
        this.Name.Equals(thatDescriptor.Name);
    }

    public override int GetHashCode() {
      return Name.GetHashCode();
    }

    public int CompareTo(object that) {
      return this.ToString().CompareTo(that.ToString());
    }

  }

  class LocalDescriptor : VariableDescriptor {
    internal readonly string Proc;
    internal LocalDescriptor(string Proc, string Name)
      : base(Name) {
      this.Proc = Proc;
    }

    public override string ToString() {
      return Proc + "." + base.ToString();
    }

    public override bool Equals(object that) {

      if (object.ReferenceEquals(this, that)) {
        return true;
      }

      LocalDescriptor thatDescriptor = that as LocalDescriptor;

      if (thatDescriptor == null) {
        return false;
      }

      return base.Equals(thatDescriptor) &&
        this.Proc.Equals(thatDescriptor.Proc);

    }

    public override int GetHashCode() {
      return (33 * base.GetHashCode())
           + this.Proc.GetHashCode();
    }

  }

  class GlobalDescriptor : VariableDescriptor {
    internal GlobalDescriptor(string name) : base(name) { }

    public override bool Equals(object that) {

      if (object.ReferenceEquals(this, that)) {
        return true;
      }

      GlobalDescriptor thatDescriptor = that as GlobalDescriptor;

      if (thatDescriptor == null) {
        return false;
      }

      return base.Equals(thatDescriptor);

    }

    public override int GetHashCode() {
      return base.GetHashCode();
    }
  
  }

  /// <summary>
  /// Given a Boogie program, computes a graph that over-approximates dependences
  /// between program variables.
  /// </summary>
  public class VariableDependenceAnalyser : IVariableDependenceAnalyser {

    private Graph<VariableDescriptor> dependsOnNonTransitive;
    private Program prog;
    private Dictionary<Block, HashSet<Block>> BlockToControllingBlocks;
    private Dictionary<Block, HashSet<VariableDescriptor>> ControllingBlockToVariables;

    public VariableDependenceAnalyser(Program prog) {
      this.prog = prog;
      dependsOnNonTransitive = new Graph<VariableDescriptor>();
    }


    private void Initialise() {
      foreach (var descriptor in
        prog.TopLevelDeclarations.OfType<Variable>().Where(Item => !(Item is Constant)).
          Select(Variable => Variable.Name).
          Select(Name => new GlobalDescriptor(Name))) {
        dependsOnNonTransitive.AddEdge(descriptor, descriptor);
      }

      foreach (var Proc in NonInlinedProcedures()) {

        List<Variable> parameters = new List<Variable>();
        parameters.AddRange(Proc.InParams);
        parameters.AddRange(Proc.OutParams);
        foreach (var descriptor in
          parameters.Select(Variable => Variable.Name).Select(Name => new LocalDescriptor(Proc.Name, Name))) {
          dependsOnNonTransitive.AddEdge(descriptor, descriptor);
        }
      }

      foreach (var Impl in NonInlinedImplementations()) {

        List<Variable> locals = new List<Variable>();
        locals.AddRange(Impl.LocVars);
        foreach (var descriptor in
          locals.Select(Variable => Variable.Name).Select(Name => new LocalDescriptor(Impl.Name, Name))) {
          dependsOnNonTransitive.AddEdge(descriptor, descriptor);
        }
      }
    }

    private IEnumerable<Procedure> NonInlinedProcedures() {
      return prog.TopLevelDeclarations.OfType<Procedure>().
        Where(Item => QKeyValue.FindIntAttribute(Item.Attributes, "inline", -1) == -1);
    }

    private IEnumerable<Implementation> NonInlinedImplementations() {
      return prog.TopLevelDeclarations.OfType<Implementation>().
        Where(Item => QKeyValue.FindIntAttribute(Item.Proc.Attributes, "inline", -1) == -1);
    }

    public void Analyse() {

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

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Variable dependence analysis: Initialising");
      }

      Initialise();

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Variable dependence analysis: Computing control dependence info");
      }

      BlockToControllingBlocks = ComputeGlobalControlDependences();

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Variable dependence analysis: Computing control dependence variables");
      }

      ControllingBlockToVariables = ComputeControllingVariables(BlockToControllingBlocks);
      foreach (var Impl in NonInlinedImplementations()) {

        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("Variable dependence analysis: Analysing " + Impl.Name);
        }

        Analyse(Impl);
      }
    }

    private void Analyse(Implementation Impl) {
      string proc = Impl.Name;
      foreach (Block b in Impl.Blocks) {
        Analyse(proc, b);
      }
    }

    private void Analyse(string proc, Block b) {
      foreach (Cmd cmd in b.Cmds) {
        AssignCmd assign = cmd as AssignCmd;
        if (assign != null) {
          HandleAssign(proc, b, assign);
        }
        CallCmd call = cmd as CallCmd;
        if (call != null) {
          HandleCall(proc, b, call);
        }
      }
    }

    private void HandleCall(string proc, Block b, CallCmd call) {
      foreach (var formalActualPair in call.Proc.InParams.Zip(call.Ins)) {
        var formalIn = MakeDescriptor(call.callee, formalActualPair.Item1);
        AddDependences(formalIn, GetReferencedVariables(formalActualPair.Item2, proc));
        AddControlDependences(b, formalIn);
      }

      foreach (var formalActualPair in call.Proc.OutParams.Zip(call.Outs)) {
        var actualOut = MakeDescriptor(proc, formalActualPair.Item2.Decl);
        AddDependences(actualOut, GetReferencedVariables(new IdentifierExpr(Token.NoToken, formalActualPair.Item1), call.callee));
        AddControlDependences(b, actualOut);
      }

    }

    private void HandleAssign(string proc, Block b, AssignCmd assign) {
      foreach (var assignPair in assign.Lhss.Zip(assign.Rhss)) {
        VariableDescriptor assignedVariable = MakeDescriptor(proc, assignPair.Item1.DeepAssignedVariable);
        AddDependences(assignedVariable, GetReferencedVariables(assignPair.Item1, proc));
        AddDependences(assignedVariable, GetReferencedVariables(assignPair.Item2, proc));
        AddControlDependences(b, assignedVariable);
      }
    }

    private void AddControlDependences(Block b, VariableDescriptor v) {
      if (!BlockToControllingBlocks.ContainsKey(b)) {
        return;
      }
      foreach (var controller in BlockToControllingBlocks[b]) {
        AddDependences(v, ControllingBlockToVariables[controller]);
      }
    }

    private IEnumerable<VariableDescriptor> GetReferencedVariables(Absy node, string proc) {
      var VarCollector = new VariableCollector();
      VarCollector.Visit(node);
      return VarCollector.usedVars.Where(Item => !(Item is Constant)).Select(Item => MakeDescriptor(proc, Item));
    }

    void AddDependences(VariableDescriptor v, IEnumerable<VariableDescriptor> vs) {
      foreach (var n in vs) {
        dependsOnNonTransitive.AddEdge(v, n);
      }
    }

    private Dictionary<Block, HashSet<VariableDescriptor>> ComputeControllingVariables(Dictionary<Block, HashSet<Block>> GlobalCtrlDep) {
      Dictionary<Block, HashSet<VariableDescriptor>> result = new Dictionary<Block, HashSet<VariableDescriptor>>();
      foreach (var Impl in NonInlinedImplementations()) {
        foreach (var b in Impl.Blocks) {
          result[b] = GetControlDependencyVariables(Impl.Name, b);
        }
      }
      return result;
    }

    private HashSet<VariableDescriptor> GetControlDependencyVariables(string proc, Block b) {

      // This method works under the assumption that assume statements
      // relevant to control flow between basic blocks have the "partition" attribute

      HashSet<VariableDescriptor> result = new HashSet<VariableDescriptor>();
      var gotoCmd = b.TransferCmd as GotoCmd;
      if (gotoCmd != null && gotoCmd.labelTargets.Length >= 2) {
        foreach (Block succ in gotoCmd.labelTargets) {
          foreach (Cmd c in succ.Cmds) {
            AssumeCmd a = c as AssumeCmd;
            if (a != null && QKeyValue.FindBoolAttribute(a.Attributes, "partition")) {
              var VarCollector = new VariableCollector();
              VarCollector.VisitExpr(a.Expr);
              result.UnionWith(VarCollector.usedVars.Where(Item => !(Item is Constant)).Select(
                Item => MakeDescriptor(proc, Item)));
            }
            else {
              break;
            }
          }
        }
      }
      return result;
    }

    private Dictionary<Block, HashSet<Block>> ComputeGlobalControlDependences() {

      Dictionary<Block, HashSet<Block>> GlobalCtrlDep = new Dictionary<Block, HashSet<Block>>();
      Dictionary<Implementation, Dictionary<Block, HashSet<Block>>> LocalCtrlDeps = new Dictionary<Implementation, Dictionary<Block, HashSet<Block>>>();

      // Work out and union together local control dependences
      foreach (var Impl in prog.TopLevelDeclarations.OfType<Implementation>()) {
        Graph<Block> blockGraph = prog.ProcessLoops(Impl);
        LocalCtrlDeps[Impl] = blockGraph.ControlDependence();
        foreach (var KeyValue in LocalCtrlDeps[Impl]) {
          GlobalCtrlDep.Add(KeyValue.Key, KeyValue.Value);
        }
      }

      Graph<Implementation> callGraph = Program.BuildCallGraph(prog);

      // Add inter-procedural control dependence nodes based on calls
      foreach (var Impl in prog.TopLevelDeclarations.OfType<Implementation>()) {
        foreach (var b in Impl.Blocks) {
          foreach (var cmd in b.Cmds.OfType<CallCmd>()) {
            var DirectCallee = GetImplementation(cmd.callee);
            if (DirectCallee != null) {
              HashSet<Implementation> IndirectCallees = ComputeIndirectCallees(callGraph, DirectCallee);
              foreach (var control in GetControllingBlocks(b, LocalCtrlDeps[Impl])) {
                foreach (var c in IndirectCallees.Select(Item => Item.Blocks).SelectMany(Item => Item)) {
                  GlobalCtrlDep[control].Add(c);
                }
              }
            }
          }
        }
      }

      // Compute transitive closure
      GlobalCtrlDep.TransitiveClosure();

      // Finally reverse the dependences

      Dictionary<Block, HashSet<Block>> result = new Dictionary<Block, HashSet<Block>>();

      foreach (var KeyValue in GlobalCtrlDep) {
        foreach (var v in KeyValue.Value) {
          if (!result.ContainsKey(v)) {
            result[v] = new HashSet<Block>();
          }
          result[v].Add(KeyValue.Key);
        }
      }

      return result;
    }

    private HashSet<Implementation> ComputeIndirectCallees(Graph<Implementation> callGraph, Implementation DirectCallee) {
      return ComputeIndirectCallees(callGraph, DirectCallee, new HashSet<Implementation>());
    }

    private HashSet<Implementation> ComputeIndirectCallees(Graph<Implementation> callGraph, Implementation DirectCallee, HashSet<Implementation> seen) {
      if (seen.Contains(DirectCallee)) {
        return new HashSet<Implementation>();
      }
      HashSet<Implementation> result = new HashSet<Implementation>();
      result.Add(DirectCallee);
      seen.Add(DirectCallee);
      foreach (var succ in callGraph.Successors(DirectCallee)) {
        result.UnionWith(ComputeIndirectCallees(callGraph, succ, seen));
      }
      return result;
    }

    private HashSet<Block> GetControllingBlocks(Block b, Dictionary<Block, HashSet<Block>> ctrlDep) {
      HashSet<Block> result = new HashSet<Block>();
      foreach (var KeyValue in ctrlDep) {
        if (KeyValue.Value.Contains(b)) {
          result.Add(KeyValue.Key);
        }
      }
      return result;
    }

    private Implementation GetImplementation(string proc) {
      foreach (var Impl in prog.TopLevelDeclarations.OfType<Implementation>()) {
        if (Impl.Name.Equals(proc)) {
          return Impl;
        }
      }
      return null;
    }

    public VariableDescriptor MakeDescriptor(string proc, Variable v) {

      // Check whether there is an (Impl, v) match
      var MatchingLocals = dependsOnNonTransitive.Nodes.Where(Item => Item is LocalDescriptor).Select(
        Item => (LocalDescriptor)Item).Where(Item => Item.Proc.Equals(proc) &&
          Item.Name.Equals(v.Name));
      if (MatchingLocals.Count() > 0) {
        Debug.Assert(MatchingLocals.Count() == 1);
        return MatchingLocals.ToArray()[0];
      }

      // It must be a global with same name as v
      return dependsOnNonTransitive.Nodes.Where(Item => Item is GlobalDescriptor &&
        Item.Name.Equals(v.Name)).ToArray()[0];
    }

    private Dictionary<SCC<VariableDescriptor>, HashSet<VariableDescriptor>> DependsOnCache = new Dictionary<SCC<VariableDescriptor>, HashSet<VariableDescriptor>>();

    private Graph<SCC<VariableDescriptor>> DependsOnSCCsDAG;
    private Dictionary<VariableDescriptor, SCC<VariableDescriptor>> VariableDescriptorToSCC;

    public HashSet<VariableDescriptor> DependsOn(VariableDescriptor v) {
      if (DependsOnSCCsDAG == null) {
        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("Variable dependence: computing SCCs");
        }
        Adjacency<VariableDescriptor> next = new Adjacency<VariableDescriptor>(dependsOnNonTransitive.Successors);
        Adjacency<VariableDescriptor> prev = new Adjacency<VariableDescriptor>(dependsOnNonTransitive.Predecessors);
        StronglyConnectedComponents<VariableDescriptor> DependsOnSCCs = new StronglyConnectedComponents<VariableDescriptor>(
          dependsOnNonTransitive.Nodes, next, prev);
        DependsOnSCCs.Compute();

        VariableDescriptorToSCC = new Dictionary<VariableDescriptor, SCC<VariableDescriptor>>();
        foreach (var scc in DependsOnSCCs) {
          foreach (var s in scc) {
            VariableDescriptorToSCC[s] = scc;
          }
        }

        DependsOnSCCsDAG = new Graph<SCC<VariableDescriptor>>();
        foreach (var edge in dependsOnNonTransitive.Edges) {
          if (VariableDescriptorToSCC[edge.Item1] != VariableDescriptorToSCC[edge.Item2]) {
            DependsOnSCCsDAG.AddEdge(VariableDescriptorToSCC[edge.Item1], VariableDescriptorToSCC[edge.Item2]);
          }
        }

        SCC<VariableDescriptor> dummy = new SCC<VariableDescriptor>();
        foreach (var n in dependsOnNonTransitive.Nodes) {
          DependsOnSCCsDAG.AddEdge(VariableDescriptorToSCC[n], dummy);
        }

        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("Variable dependence: SCCs computed!");
        }
      }
      return DependsOn(VariableDescriptorToSCC[v]);
    }

    public HashSet<VariableDescriptor> DependsOn(SCC<VariableDescriptor> vSCC) {

      if (!DependsOnCache.ContainsKey(vSCC)) {
        HashSet<VariableDescriptor> result = new HashSet<VariableDescriptor>();
        if (vSCC.Count() > 0) {
          result.UnionWith(vSCC);
          foreach (var wSCC in DependsOnSCCsDAG.Successors(vSCC)) {
            result.UnionWith(DependsOn(wSCC));
          }
        }
        DependsOnCache[vSCC] = result;
      }
      return DependsOnCache[vSCC];
    }

    public void dump() {

      Console.WriteLine("Variable dependence information");
      Console.WriteLine("===============================");

      Console.WriteLine("Global variables");
      Console.WriteLine("================");

      foreach (var GlobalEntry in dependsOnNonTransitive.Nodes.Where(Item => Item is GlobalDescriptor)) {
        dump(GlobalEntry);
      }

      foreach (var proc in Procedures()) {
        Console.WriteLine("Variables of " + proc);
        Console.WriteLine("=====================");
        foreach (var LocalEntry in dependsOnNonTransitive.Nodes.Where(Item => Item is LocalDescriptor
          && ((LocalDescriptor)Item).Proc.Equals(proc))) {
          dump(LocalEntry);
        }
      }
    }

    private void dump(VariableDescriptor vd) {
      Console.Write(vd + " <- {");
      bool first = true;

      var SortedDependents = DependsOn(vd).ToList();
      SortedDependents.Sort();
      foreach (var Descriptor in SortedDependents) {
        Console.Write((first ? "" : ",") + "\n  " + Descriptor);
        if (first) {
          first = false;
        }
      }
      Debug.Assert(!first);
      Console.WriteLine("\n}\n");
    }

    private HashSet<string> Procedures() {
      return new HashSet<string>(dependsOnNonTransitive.Nodes.Where(Item =>
              Item is LocalDescriptor).Select(Item => ((LocalDescriptor)Item).Proc));
    }

  }
  

  /// <summary>
  /// Given a Boogie program, computes a graph that over-approximates dependences
  /// between program variables.
  /// </summary>
  public class OldVariableDependenceAnalyser : IVariableDependenceAnalyser {

    private Program prog;

    public Dictionary<VariableDescriptor, HashSet<VariableDescriptor>> dependsOn;

    private Dictionary<string, HashSet<VariableDescriptor>> callControlDependences;

    private bool ProcedureChanged;

    public OldVariableDependenceAnalyser(Program prog) {
      this.prog = prog;
      dependsOn = new Dictionary<VariableDescriptor, HashSet<VariableDescriptor>>();
      callControlDependences = new Dictionary<string, HashSet<VariableDescriptor>>();
    }
    
    public void Analyse() {

      Initialise();

      ProcedureChanged = true;
      while (ProcedureChanged) {
        ProcedureChanged = false;

        foreach (var Impl in NonInlinedImplementations()) {
          Analyse(Impl);
        }

      }

    }

    private Dictionary<string, int> temp = new Dictionary<string,int>();

    private void Analyse(Implementation Impl) {

      if (!temp.ContainsKey(Impl.Name)) {
        temp[Impl.Name] = 0;
      }

      temp[Impl.Name]++;

      var ctrlDep = GetControlDependenceTransitiveClosure(Impl);

      var orderedBlocks = GetOrderedBlocks(Impl);

      bool changed;
      do {
        changed = false;
        foreach (Block block in orderedBlocks) {
          Analyse(Impl, block, ctrlDep, ref changed);
        }
      } while (changed);

    }

    private void Analyse(Implementation Impl, Block block, 
          Dictionary<Block, HashSet<Block>> ctrlDep, ref bool changed) {

      // First, work out the set of all variables that are involved in tests on which
      // this block is control-dependent
      HashSet<VariableDescriptor> ctrlDepVars = GetControlDependencyVariables(block, Impl.Name, ctrlDep);
      // Take incoming control dependences for the procedure
      ctrlDepVars.UnionWith(callControlDependences[Impl.Name]);

      var ControlInflucencingVariables = GetDependentVariables(ctrlDepVars);

      foreach (var c in block.Cmds) {

        var assign = c as AssignCmd;
        if (assign != null) {

          foreach (var assignPair in assign.Lhss.Zip(assign.Rhss)) {
            VariableDescriptor assignedVariable = MakeDescriptor(Impl.Name, assignPair.Item1.DeepAssignedVariable);
            AddDependences(assignedVariable, GetDependentVariables(GetReferencedVariables(assignPair.Item1, Impl.Name)), ref changed);
            AddDependences(assignedVariable, GetDependentVariables(GetReferencedVariables(assignPair.Item2, Impl.Name)), ref changed);
            AddDependences(assignedVariable, ControlInflucencingVariables, ref changed);
          }
        }

        var call = c as CallCmd;
        if (call != null) {
          AddCallControlDependences(call.callee, ctrlDepVars);

          foreach(var formalActualPair in call.Proc.InParams.Zip(call.Ins)) {
            bool unused = false; // When we find that the in parameters of the called procedure have been changed, we do not need to necessarily continue processing this procedure
            AddDependences(MakeDescriptor(call.callee, formalActualPair.Item1),
              GetDependentVariables(GetReferencedVariables(formalActualPair.Item2, Impl.Name)), ref unused);
            AddDependences(MakeDescriptor(call.callee, formalActualPair.Item1),
              ControlInflucencingVariables, ref unused);
          }

          foreach (var formalActualPair in call.Proc.OutParams.Zip(call.Outs)) {
            AddDependences(MakeDescriptor(Impl.Name, formalActualPair.Item2.Decl),
              GetDependentVariables(GetReferencedVariables(new IdentifierExpr(Token.NoToken, formalActualPair.Item1), call.callee)), ref changed);
            AddDependences(MakeDescriptor(Impl.Name, formalActualPair.Item2.Decl),
              ControlInflucencingVariables, ref changed);
          }

        }

      }

    }

    private IEnumerable<VariableDescriptor> GetDependentVariables(IEnumerable<VariableDescriptor> vars) {
      HashSet<VariableDescriptor> result = new HashSet<VariableDescriptor>();
      foreach (var v in vars) {
        result.UnionWith(dependsOn[v]);
      }
      return result;
    }

    private IEnumerable<VariableDescriptor> GetReferencedVariables(Absy node, string proc) {
      var VarCollector = new VariableCollector();
      VarCollector.Visit(node);
      IEnumerable<VariableDescriptor> result = VarCollector.usedVars.Where(Item => !(Item is Constant)).Select(Item => MakeDescriptor(proc, Item));
      return result;
    }

    public VariableDescriptor MakeDescriptor(string proc, Variable v) {

      // Check whether there is an (Impl, v) match
      var MatchingLocals = dependsOn.Keys.Where(Item => Item is LocalDescriptor).Select(
        Item => (LocalDescriptor)Item).Where(Item => Item.Proc.Equals(proc) &&
          Item.Name.Equals(v.Name));
      if(MatchingLocals.Count() > 0) {
        Debug.Assert(MatchingLocals.Count() == 1);
        return MatchingLocals.ToArray()[0];
      }

      // It must be a global with same name as v
      return dependsOn.Keys.Where(Item => Item is GlobalDescriptor &&
        Item.Name.Equals(v.Name)).ToArray()[0];
    }

    private Dictionary<Block, HashSet<VariableDescriptor>> ControlDependencyVariablesCache = new Dictionary<Block,HashSet<VariableDescriptor>>();

    private HashSet<VariableDescriptor> GetControlDependencyVariables(Block b, string proc, Dictionary<Block, HashSet<Block>> ctrlDep) {

      if (!ControlDependencyVariablesCache.ContainsKey(b)) {
        HashSet<VariableDescriptor> ctrlDepVars = new HashSet<VariableDescriptor>();
        foreach (var k in ctrlDep.Keys) {
          if (ctrlDep[k].Contains(b)) {
            foreach (Variable v in GetControlDependencyVariables(k)) {
              ctrlDepVars.Add(MakeDescriptor(proc, v));
            }
          }
        }
        ControlDependencyVariablesCache[b] = ctrlDepVars;
      }

      return ControlDependencyVariablesCache[b];
    }

    private static HashSet<Variable> GetControlDependencyVariables(Block b) {

      // This method works under the assumption that assume statements
      // relevant to control flow between basic blocks have the "partition" attribute

      HashSet<Variable> result = new HashSet<Variable>();
      if (b.TransferCmd is GotoCmd) {
        foreach (Block succ in ((GotoCmd)b.TransferCmd).labelTargets) {
          foreach (Cmd c in succ.Cmds) {
            AssumeCmd a = c as AssumeCmd;
            if (a != null && QKeyValue.FindBoolAttribute(a.Attributes, "partition")) {
              var VarCollector = new VariableCollector();
              VarCollector.VisitExpr(a.Expr);
              result.UnionWith(VarCollector.usedVars.Where(Item => !(Item is Constant)));
            }
            else {
              break;
            }
          }
        }
      }
      return result;
    }

    private void Initialise() {
      foreach (var descriptor in
        prog.TopLevelDeclarations.OfType<Variable>().Where(Item => !(Item is Constant)).
          Select(Variable => Variable.Name).
          Select(Name => new GlobalDescriptor(Name))) {
        dependsOn.Add(descriptor, new HashSet<VariableDescriptor> { descriptor });
      }

      foreach (var Proc in NonInlinedProcedures()) {

        callControlDependences[Proc.Name] = new HashSet<VariableDescriptor>();

        List<Variable> parameters = new List<Variable>();
        parameters.AddRange(Proc.InParams);
        parameters.AddRange(Proc.OutParams);
        foreach (var descriptor in
          parameters.Select(Variable => Variable.Name).Select(Name => new LocalDescriptor(Proc.Name, Name))) {
          dependsOn.Add(descriptor, new HashSet<VariableDescriptor> { descriptor });
        }
      }

      foreach (var Impl in NonInlinedImplementations()) {

        List<Variable> locals = new List<Variable>();
        locals.AddRange(Impl.LocVars);
        foreach (var descriptor in
          locals.Select(Variable => Variable.Name).Select(Name => new LocalDescriptor(Impl.Name, Name))) {
          dependsOn.Add(descriptor, new HashSet<VariableDescriptor> { descriptor });
        }
      }
    }

    private IEnumerable<Procedure> NonInlinedProcedures() {
      return prog.TopLevelDeclarations.OfType<Procedure>().
        Where(Item => QKeyValue.FindIntAttribute(Item.Attributes, "inline", -1) == -1);
    }

    private IEnumerable<Implementation> NonInlinedImplementations() {
      return prog.TopLevelDeclarations.OfType<Implementation>().
        Where(Item => QKeyValue.FindIntAttribute(Item.Proc.Attributes, "inline", -1) == -1);
    }



    public void dump() {

      Console.WriteLine("Variable dependence information");
      Console.WriteLine("===============================");

      Console.WriteLine("Global variables");
      Console.WriteLine("================");

      foreach (var GlobalEntry in dependsOn.Where(Item => Item.Key is GlobalDescriptor)) {
        dump(GlobalEntry);
      }

      foreach (var proc in Procedures()) {
        Console.WriteLine("Variables of " + proc);
        Console.WriteLine("=====================");
        foreach (var LocalEntry in dependsOn.Where(Item => Item.Key is LocalDescriptor
          && ((LocalDescriptor)Item.Key).Proc.Equals(proc))) {
          dump(LocalEntry);
        }
      }
    }

    private static void dump(KeyValuePair<VariableDescriptor,HashSet<VariableDescriptor>> Entry)
    {
        Console.Write(Entry.Key + " <- {");
        bool first = true;

        var SortedDependents = Entry.Value.ToList();
        SortedDependents.Sort();
      
        foreach(var Descriptor in SortedDependents) {
          Console.Write((first ? "" : ",") + "\n  " + Descriptor);
          if (first) {
            first = false;
          }
        }
        Console.WriteLine("\n}\n");
    }
    
    private HashSet<string> Procedures() {
      return new HashSet<string>(dependsOn.Where(Item =>
              Item.Key is LocalDescriptor).Select(Item => ((LocalDescriptor)Item.Key).Proc));
    }

    void AddDependences(VariableDescriptor v, IEnumerable<VariableDescriptor> vs, ref bool Changed) {
      foreach (var n in vs) {
        if (!dependsOn[v].Contains(n)) {
          dependsOn[v].Add(n);
          ProcedureChanged = true;
          Changed = true;
        }
      }
    }

    private void AddCallControlDependences(string Proc, HashSet<VariableDescriptor> ctrlDepVars) {
      foreach (var n in ctrlDepVars) {
        if (!callControlDependences[Proc].Contains(n)) {
          callControlDependences[Proc].Add(n);
          ProcedureChanged = true;
        }
      }
    }


    private Dictionary<string, Dictionary<Block, HashSet<Block>>> ControlDependenceCache = new Dictionary<string, Dictionary<Block, HashSet<Block>>>();

    private Dictionary<Block, HashSet<Block>> GetControlDependenceTransitiveClosure(Implementation Impl) {
      if (!ControlDependenceCache.ContainsKey(Impl.Name)) {
        Graph<Block> blockGraph = prog.ProcessLoops(Impl);
        Dictionary<Block, HashSet<Block>> ctrlDep = blockGraph.ControlDependence();
        ctrlDep.TransitiveClosure();
        ControlDependenceCache[Impl.Name] = ctrlDep;
      }
      return ControlDependenceCache[Impl.Name];
    }

    private Dictionary<string, List<Block>> OrderedBlocksCache = new Dictionary<string,List<Block>>();

    private List<Block> GetOrderedBlocks(Implementation Impl) {
      if (!OrderedBlocksCache.ContainsKey(Impl.Name)) {
        List<Block> orderedBlocks = PostOrder(Impl.Blocks[0], new HashSet<Block>());
        Debug.Assert(orderedBlocks.Count() == Impl.Blocks.Count());
        orderedBlocks.Reverse();
        OrderedBlocksCache[Impl.Name] = orderedBlocks;
      }
      return OrderedBlocksCache[Impl.Name];
    }

    private List<Block> PostOrder(Block b, HashSet<Block> seen) {
      seen.Add(b);
      List<Block> result = new List<Block>();
      if(b.TransferCmd is GotoCmd) {
        foreach (Block c in ((GotoCmd)b.TransferCmd).labelTargets) {
          if (!seen.Contains(c)) {
            result.AddRange(PostOrder(c, seen));
          }
        }
      }
      result.Add(b);
      return result;
    }

    public HashSet<VariableDescriptor> DependsOn(VariableDescriptor vd) {
      return dependsOn[vd];
    }

  }
}
