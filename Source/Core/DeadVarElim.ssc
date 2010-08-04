using System;
using System.Collections.Generic;
using Graphing;
using PureCollections;
using Microsoft.Contracts;

namespace Microsoft.Boogie
{
  public class UnusedVarEliminator : VariableCollector {
    public static void Eliminate(Program! program) {
      UnusedVarEliminator elim = new UnusedVarEliminator();
      elim.Visit(program);
    }
  
    private UnusedVarEliminator() {
      base();
    }
      
	public override Implementation! VisitImplementation(Implementation! node) {
	  //Console.WriteLine("Procedure {0}", node.Name);
	  Implementation! impl = base.VisitImplementation(node);
	  //Console.WriteLine("Old number of local variables = {0}", impl.LocVars.Length);
	  Microsoft.Boogie.VariableSeq! vars = new Microsoft.Boogie.VariableSeq();
	  foreach (Variable! var in impl.LocVars) {
	    if (usedVars.Contains(var))
	      vars.Add(var);
	  }
	  impl.LocVars = vars;
	  //Console.WriteLine("New number of local variables = {0}", impl.LocVars.Length);
	  //Console.WriteLine("---------------------------------");
	  usedVars.Clear();
	  return impl;
	}
  }
  
  public class ModSetCollector : StandardVisitor {
    static Procedure proc;
    static Dictionary<Procedure!, Set<Variable!>!>! modSets;
    static bool moreProcessingRequired;
    
    public static void DoModSetAnalysis(Program! program) {
      int procCount = 0;
      foreach (Declaration! decl in program.TopLevelDeclarations) {
        if (decl is Procedure)
          procCount++;
      }
      Console.WriteLine("Number of procedures = {0}", procCount);
      
      modSets = new Dictionary<Procedure!, Set<Variable!>!>();
      
      Set<Procedure!> implementedProcs = new Set<Procedure!> ();
      foreach (Declaration! decl in program.TopLevelDeclarations) {
        if (decl is Implementation) {
          Implementation impl = (Implementation) decl;
          if (impl.Proc != null)
            implementedProcs.Add(impl.Proc);
        }
      }
      foreach (Declaration! decl in program.TopLevelDeclarations) {
        if (decl is Procedure && !implementedProcs.Contains((Procedure!) decl)) {
          proc = (Procedure) decl;
          foreach (IdentifierExpr! expr in proc.Modifies) {
            ProcessVariable(expr.Decl);
          }
          proc = null;
        }
      }
      
      moreProcessingRequired = true;
      while (moreProcessingRequired) {
        moreProcessingRequired = false;
        ModSetCollector modSetCollector = new ModSetCollector();
        modSetCollector.Visit(program);
      }
      
      procCount = 0;
      foreach (Procedure! x in modSets.Keys) {
        procCount++;
        Console.Write("{0} : ", x.Name);
        foreach (Variable! y in modSets[x]) {
          Console.Write("{0}, ", y.Name);
        }
        Console.WriteLine("");
      }
      Console.WriteLine("Number of procedures with nonempty modsets = {0}", procCount);
    }
    
    public override Implementation! VisitImplementation(Implementation! node) {
      proc = node.Proc;
      Implementation! ret = base.VisitImplementation(node);
      proc = null;
      
      return ret;
    }
    public override Cmd! VisitAssignCmd(AssignCmd! assignCmd) {
      Cmd ret = base.VisitAssignCmd(assignCmd);
      foreach (AssignLhs! lhs in assignCmd.Lhss) {
	    ProcessVariable(lhs.DeepAssignedVariable);
	  }
      return ret;
    }
    public override Cmd! VisitHavocCmd(HavocCmd! havocCmd) {
      Cmd ret = base.VisitHavocCmd(havocCmd);
      foreach (IdentifierExpr! expr in havocCmd.Vars) {
        ProcessVariable(expr.Decl);
	  }
	  return ret;
    }
    public override Cmd! VisitCallCmd(CallCmd! callCmd) {
      Cmd ret = base.VisitCallCmd(callCmd);
      Procedure callee = callCmd.Proc;
      if (callee != null && modSets.ContainsKey(callee)) {
        foreach (Variable var in modSets[callee]) {
          ProcessVariable(var);
        }
      }
      return ret;
    }
    private static void ProcessVariable(Variable var) {
      Procedure! localProc = (!)proc;
      if (var == null) return;
	  if (!(var is GlobalVariable)) return;
	  if (var.Name == "alloc") return;
	  if (!modSets.ContainsKey(localProc)) {
	    modSets[localProc] = new Set<Variable!> ();
	  }
	  if (modSets[localProc].Contains(var)) return;
	  moreProcessingRequired = true;
	  modSets[localProc].Add(var);
    }
  }
  
  public class VariableCollector : StandardVisitor {
	public System.Collections.Generic.Set<Variable!>! usedVars;
	public System.Collections.Generic.Set<Variable!>! oldVarsUsed;
	int insideOldExpr;
	
	public VariableCollector() {
	  usedVars = new System.Collections.Generic.Set<Variable!>();
	  oldVarsUsed = new System.Collections.Generic.Set<Variable!>();
	  insideOldExpr = 0;
	}
	
    public override Expr! VisitOldExpr(OldExpr! node)
    {
      insideOldExpr ++;
      node.Expr = this.VisitExpr(node.Expr);
      insideOldExpr --;
      return node;
    }
    
    public override Expr! VisitIdentifierExpr(IdentifierExpr! node) {
      if (node.Decl != null) {
        usedVars.Add(node.Decl);
        if(insideOldExpr > 0) {
          oldVarsUsed.Add(node.Decl);
        }
      }
      return node;
    }
  } 
  
  public class BlockCoalescer : StandardVisitor { 
    public static void CoalesceBlocks(Program! program) {
      BlockCoalescer blockCoalescer = new BlockCoalescer();
      blockCoalescer.Visit(program);
    }
    
    private static Set<Block!>! ComputeMultiPredecessorBlocks(Implementation !impl) {
      Set<Block!> visitedBlocks = new Set<Block!>();
      Set<Block!> multiPredBlocks = new Set<Block!>();
      Stack<Block!> dfsStack = new Stack<Block!>();
      dfsStack.Push(impl.Blocks[0]);
      while (dfsStack.Count > 0) {
        Block! b = dfsStack.Pop();
        if (visitedBlocks.Contains(b)) {
          multiPredBlocks.Add(b);
          continue;
        }
        visitedBlocks.Add(b);
        if (b.TransferCmd == null) continue;
        if (b.TransferCmd is ReturnCmd) continue;
        assert b.TransferCmd is GotoCmd;
        GotoCmd gotoCmd = (GotoCmd) b.TransferCmd;
        if (gotoCmd.labelTargets == null) continue;
        foreach (Block! succ in gotoCmd.labelTargets) {
          dfsStack.Push(succ);
        }
      }
      return multiPredBlocks;
    }
    
    public override Implementation! VisitImplementation(Implementation! impl) {
      //Console.WriteLine("Procedure {0}", impl.Name);
      //Console.WriteLine("Initial number of blocks = {0}", impl.Blocks.Count);
      
      Set<Block!> multiPredBlocks = ComputeMultiPredecessorBlocks(impl);
      Set<Block!> visitedBlocks = new Set<Block!>();
      Set<Block!> removedBlocks = new Set<Block!>();
      Stack<Block!> dfsStack = new Stack<Block!>();
      dfsStack.Push(impl.Blocks[0]);
      while (dfsStack.Count > 0) {
        Block! b = dfsStack.Pop();
        if (visitedBlocks.Contains(b)) continue;
        visitedBlocks.Add(b);
        if (b.TransferCmd == null) continue;
        if (b.TransferCmd is ReturnCmd) continue;
        assert b.TransferCmd is GotoCmd;
        GotoCmd gotoCmd = (GotoCmd) b.TransferCmd;
        if (gotoCmd.labelTargets == null) continue;
        if (gotoCmd.labelTargets.Length == 1) {
          Block! succ = (!)gotoCmd.labelTargets[0];
          if (!multiPredBlocks.Contains(succ)) {
            foreach (Cmd! cmd in succ.Cmds) {
              b.Cmds.Add(cmd);
            }
            b.TransferCmd = succ.TransferCmd;
            if (!b.tok.IsValid && succ.tok.IsValid) {
              b.tok = succ.tok;
              b.Label = succ.Label;
            }
            removedBlocks.Add(succ);
            dfsStack.Push(b);
            visitedBlocks.Remove(b);
            continue;
          }
        } 
        foreach (Block! succ in gotoCmd.labelTargets) {
          dfsStack.Push(succ);
        }
      }
      
      List<Block!> newBlocks = new List<Block!>();
      foreach (Block! b in impl.Blocks) {
        if (!removedBlocks.Contains(b)) {
          newBlocks.Add(b);
        }
      }
      impl.Blocks = newBlocks;
      
      // Console.WriteLine("Final number of blocks = {0}", impl.Blocks.Count);
      return impl;
    }
  }
  
  public class LiveVariableAnalysis {
    public static void ClearLiveVariables(Implementation! impl) {
      foreach (Block! block in impl.Blocks) {
        block.liveVarsBefore = null;
      }
    }
    
	public static void ComputeLiveVariables(Implementation! impl) {
	  Microsoft.Boogie.Helpers.ExtraTraceInformation("Starting live variable analysis");
	  Graphing.Graph<Block> dag = new Graph<Block>();
      dag.AddSource((!)impl.Blocks[0]); // there is always at least one node in the graph
      foreach (Block b in impl.Blocks)
      {
        GotoCmd gtc = b.TransferCmd as GotoCmd;
        if (gtc != null)
        {
          assume gtc.labelTargets != null;
          foreach (Block! dest in gtc.labelTargets)
          {
            dag.AddEdge(dest, b);
          }
        }
      }
      
      IEnumerable<Block> sortedNodes = dag.TopologicalSort();
	  foreach (Block! block in sortedNodes) {
	    Set<Variable!>! liveVarsAfter = new Set<Variable!>();
	    if (block.TransferCmd is GotoCmd) {
	      GotoCmd gotoCmd = (GotoCmd) block.TransferCmd;
	      if (gotoCmd.labelTargets != null) {
	        foreach (Block! succ in gotoCmd.labelTargets) {
	          assert succ.liveVarsBefore != null;
	          liveVarsAfter.AddRange(succ.liveVarsBefore);
	        }
	      }
	    } 
	    
        CmdSeq cmds = block.Cmds;
	    int len = cmds.Length;
	    for (int i = len - 1; i >= 0; i--) {
	      if(cmds[i] is CallCmd) {
	        Procedure! proc = (!)((CallCmd!)cmds[i]).Proc;
	        if(InterProcGenKill.HasSummary(proc.Name)) {
	          liveVarsAfter = 
	            InterProcGenKill.PropagateLiveVarsAcrossCall((CallCmd!)cmds[i], liveVarsAfter);
	          continue;
	        }
	      }
	      Propagate(cmds[i], liveVarsAfter);
	    }
	    
	    block.liveVarsBefore = liveVarsAfter;
	    	    
	  }
	}
	
	// perform in place update of liveSet
	public static void Propagate(Cmd! cmd, Set<Variable!>! liveSet) {
	  if (cmd is AssignCmd) {
	    AssignCmd! assignCmd = (AssignCmd) cmd;
	    // I must first iterate over all the targets and remove the live ones.
	    // After the removals are done, I must add the variables referred on 
	    // the right side of the removed targets
	    Set<int> indexSet = new Set<int>();
	    int index = 0;
	    foreach (AssignLhs! lhs in assignCmd.Lhss) {
	      Variable var = lhs.DeepAssignedVariable;
	      if (var != null && liveSet.Contains(var)) {
	        indexSet.Add(index);
	        if (lhs is SimpleAssignLhs) {
	          // we should only remove non-map target variables because there is an implicit
	          // read of a map variable in an assignment to it
			  liveSet.Remove(var);
			}
	      }
	      index++;
	    }
	    index = 0;
	    foreach (Expr! expr in assignCmd.Rhss) {
	      if (indexSet.Contains(index)) {
	        VariableCollector! collector = new VariableCollector();
	        collector.Visit(expr);
	        liveSet.AddRange(collector.usedVars);
	        AssignLhs lhs = assignCmd.Lhss[index];
	        if (lhs is MapAssignLhs) {
	          // If the target is a map, then all indices are also read
	          MapAssignLhs malhs = (MapAssignLhs) lhs;
	          foreach (Expr e in malhs.Indexes) {
	            VariableCollector! c = new VariableCollector();
	            c.Visit(e);
	            liveSet.AddRange(c.usedVars);
	          }
	        }
	      }
	      index++;
	    }
	  } else if (cmd is HavocCmd) {
	    HavocCmd! havocCmd = (HavocCmd) cmd;
	    foreach (IdentifierExpr! expr in havocCmd.Vars) {
	      if (expr.Decl != null) {
	        liveSet.Remove(expr.Decl);
	      }
	    }
	  } else if (cmd is PredicateCmd) {
	    assert (cmd is AssertCmd || cmd is AssumeCmd);
	    PredicateCmd! predicateCmd = (PredicateCmd) cmd;
	    if (predicateCmd.Expr is LiteralExpr) {
	      LiteralExpr le = (LiteralExpr) predicateCmd.Expr;
	      if (le.IsFalse) {
	        liveSet.Clear();
	      }
	    } else {
	      VariableCollector! collector = new VariableCollector();
	      collector.Visit(predicateCmd.Expr);
	      liveSet.AddRange(collector.usedVars);
	    }
	  } else if (cmd is CommentCmd) {
        // comments are just for debugging and don't affect verification
      } else if (cmd is SugaredCmd) {
        SugaredCmd! sugCmd = (SugaredCmd) cmd;
        Propagate(sugCmd.Desugaring, liveSet);
      } else if (cmd is StateCmd) {
        StateCmd! stCmd = (StateCmd) cmd;
        CmdSeq! cmds = stCmd.Cmds;
        int len = cmds.Length;
        for (int i = len - 1; i >= 0; i--) {
          Propagate(cmds[i], liveSet);
        }
        foreach (Variable! v in stCmd.Locals) {
          liveSet.Remove(v);
        }
      } else {
        assert false;
      }
	}
  }
  
  /*
  // An idempotent semiring interface
  abstract public class Weight {
     abstract public Weight! one();
     abstract public Weight! zero();
     abstract public Weight! extend(Weight! w1, Weight! w2);
     abstract public Weight! combine(Weight! w1, Weight! w2);
     abstract public Weight! isEqual(Weight! w);
     abstract public Weight! projectLocals()
  }
  */
  
  // Weight domain for LiveVariableAnalysis (Gen/Kill)
  
  public class GenKillWeight {
     // lambda S. (S - kill) union gen
     Set<Variable!>! gen;
     Set<Variable!>! kill;
     bool isZero;
     
     public static GenKillWeight! oneWeight = new GenKillWeight(new Set<Variable!>(), new Set<Variable!>());
     public static GenKillWeight! zeroWeight = new GenKillWeight();
     
     // initializes to zero
     public GenKillWeight() {
        this.isZero = true;
        this.gen = new Set<Variable!>();
        this.kill = new Set<Variable!>();
     }
     
     public GenKillWeight(Set<Variable!> gen, Set<Variable!> kill) {
        assert gen != null;
        assert kill != null;
        this.gen = gen;
        this.kill = kill;
        this.isZero = false;
     }
     
     public static GenKillWeight! one() {
        return oneWeight;
     }
     
     public static GenKillWeight! zero() {
        return zeroWeight;
     }
     
     public static GenKillWeight! extend(GenKillWeight! w1, GenKillWeight! w2) {       
        if(w1.isZero || w2.isZero) return zero();
        
        return new GenKillWeight(w1.gen.Union(w2.gen.Difference(w1.kill)), w1.kill.Union(w2.kill));
     }
     
     public static GenKillWeight! combine(GenKillWeight! w1, GenKillWeight! w2) {
        if(w1.isZero) return w2;
        if(w2.isZero) return w1;
        
        return new GenKillWeight(w1.gen.Union(w2.gen), w1.kill.Intersection(w2.kill));
     }
     
     public static GenKillWeight! projectLocals(GenKillWeight! w) {
        Set<Variable!> gen = w.gen.FindAll(isGlobal);
        Set<Variable!> kill = w.kill.FindAll(isGlobal);
        
        return new GenKillWeight(gen, kill);
     }
     
     public static bool isEqual(GenKillWeight! w1, GenKillWeight! w2) {
        if(w1.isZero) return w2.isZero;
        if(w2.isZero) return w1.isZero;
        
        return (w1.gen.Equals(w2.gen) && w1.kill.Equals(w2.kill));
     }
        
     private static bool isGlobal(Variable! v) 
     {
        return (v is GlobalVariable);
     } 
     
     [Pure]
     public override string! ToString() {
       return string.Format("({0},{1})", gen.ToString(), kill.ToString());
     }
     
     public Set<Variable!>! getLiveVars() {
       return gen;
     }
     
     public Set<Variable!>! getLiveVars(Set<Variable!>! lv) {
       Set<Variable!>! temp = (!)lv.Difference(kill);
       return (!)temp.Union(gen);
     }
  
  }
  
  public class ICFG 
  {
      public Graph<Block!>! graph;
      // Map from procedure to the list of blocks that call that procedure
      public Dictionary<string!, List<Block!>!>! procsCalled;
      public Set<Block!>! nodes;
      public Dictionary<Block!, Set<Block!>!>! succEdges;
      public Dictionary<Block!, Set<Block!>!>! predEdges;
      private Dictionary<Block!, int>! priority;
      
      public Set<Block!>! srcNodes;
      public Set<Block!>! exitNodes;
      
      public Dictionary<Block!, GenKillWeight!>! weightBefore;
      public Dictionary<Block!, GenKillWeight!>! weightAfter;
      public Dictionary<Block!, Set<Variable!>!>! liveVarsAfter;
      public Dictionary<Block!, Set<Variable!>!>! liveVarsBefore;
      
      public GenKillWeight! summary;
      public Implementation! impl;
      
      [NotDelayed]
      public ICFG(Implementation! impl) {
         this.graph = new Graph<Block!>();
         this.procsCalled = new Dictionary<string!, List<Block!>!>();
         this.nodes = new Set<Block!>();
         this.succEdges = new Dictionary<Block!, Set<Block!>!>();
         this.predEdges = new Dictionary<Block!, Set<Block!>!>();
         
         this.priority = new Dictionary<Block!, int>();
         
         this.srcNodes = new Set<Block!>();
         this.exitNodes = new Set<Block!>();
         
         this.weightBefore = new Dictionary<Block!, GenKillWeight!>();
         this.weightAfter = new Dictionary<Block!, GenKillWeight!>();
         this.liveVarsAfter = new Dictionary<Block!, Set<Variable!>!>();
         this.liveVarsBefore = new Dictionary<Block!, Set<Variable!>!>();
         
         summary = GenKillWeight.zero();
         this.impl = impl;
         
         base();
         
         Initialize(impl);
         
      }
      
      private void Initialize(Implementation! impl) {   
         addSource(impl.Blocks[0]);
         graph.AddSource(impl.Blocks[0]);
         
         foreach(Block! b in impl.Blocks) {
            if(b.TransferCmd is ReturnCmd) {
               exitNodes.Add(b);
            } else {
               GotoCmd gc = b.TransferCmd as GotoCmd;
               assert gc != null;
               assert gc.labelTargets != null;
               foreach(Block! t in gc.labelTargets) {
                  addEdge(b,t);
                  graph.AddEdge(b,t);
               }
            }
            
            weightBefore[b] = GenKillWeight.zero();
            weightAfter[b] = GenKillWeight.zero();
            
            foreach(Cmd! c in b.Cmds) {
               if(c is CallCmd) {
                  CallCmd! cc = (CallCmd!)c;
                  assert cc.Proc != null;
                  string! procName = cc.Proc.Name;
                  if(!procsCalled.ContainsKey(procName)) {
                    procsCalled.Add(procName, new List<Block!>());
                  }
                  procsCalled[procName].Add(b);
               }
            }
         }
         
         List<Block>! sortedNodes;
         bool acyclic;
         
         graph.TarjanTopSort(out acyclic, out sortedNodes);
         
         if(!acyclic) {
            Console.WriteLine("Warning: graph is not a dag");
         }    
              
         int num = sortedNodes.Count;
         foreach(Block! b in sortedNodes) {
            priority.Add(b,num);
            num--;
         }

      }
      
      public int getPriority(Block! b) {
         if(priority.ContainsKey(b)) return priority[b];
         return Int32.MaxValue;
      }
      
      private void addSource(Block! b) {
         registerNode(b);
         this.srcNodes.Add(b);
      }
      
      private void addExit(Block! b) {
         registerNode(b);
         this.exitNodes.Add(b);
      }
      
      private void registerNode(Block! b) {
          if(!succEdges.ContainsKey(b)) {
            succEdges.Add(b, new Set<Block!>());
         }

         if(!predEdges.ContainsKey(b)) {
            predEdges.Add(b, new Set<Block!>());
         }     
         
         nodes.Add(b);
      }
      
      private void addEdge(Block! src, Block! tgt) {
         registerNode(src);
         registerNode(tgt);
         
         succEdges[src].Add(tgt);
         predEdges[tgt].Add(src);
      }   
      
  
  }
  
  // Interprocedural Gen/Kill Analysis
  public class InterProcGenKill
  {
     Program! program;
     Dictionary<string!, ICFG!>! procICFG;
     Dictionary<string!, Procedure!>! name2Proc;
     Dictionary<string!, List<WorkItem!>!>! callers;
     Graph<string!>! callGraph;
     Dictionary<string!, int>! procPriority;
     int maxBlocksInProc;
     
     WorkList! workList;
     
     Implementation! mainImpl;
     
     static Dictionary<string!, Set<Variable!>!>! varsLiveAtExit = new Dictionary<string!, Set<Variable!>!>();
     static Dictionary<string!, Set<Variable!>!>! varsLiveAtEntry = new Dictionary<string!, Set<Variable!>!>();
     static Dictionary<string!, GenKillWeight!>! varsLiveSummary = new Dictionary<string!, GenKillWeight!>();
     
     [NotDelayed]
     public InterProcGenKill(Implementation! impl, Program! program) {
        this.program = program;
        procICFG = new Dictionary<string!, ICFG!>();
        name2Proc = new Dictionary<string!, Procedure!>();
        workList = new WorkList();
        this.callers = new Dictionary<string!, List<WorkItem!>!>();
        this.callGraph = new Graph<string!>();
        this.procPriority = new Dictionary<string!, int>();
        this.maxBlocksInProc = 0;
        this.mainImpl = impl;
        
        Dictionary<string!, Implementation!>! name2Impl = new Dictionary<string!, Implementation!>();
        varsLiveAtExit.Clear();
        varsLiveAtEntry.Clear();
        varsLiveSummary.Clear();
        
        base();
        
        foreach(Declaration! decl in program.TopLevelDeclarations) {
           if(decl is Implementation) {
             Implementation! imp = (Implementation!)decl;
             name2Impl[imp.Name] = imp;
           } else if(decl is Procedure) {
             Procedure! proc = (!)(decl as Procedure);
             name2Proc[proc.Name] = proc;
           }
        }
        
        ICFG! mainICFG = new ICFG(mainImpl);
        procICFG.Add(mainICFG.impl.Name, mainICFG);
        callGraph.AddSource(mainICFG.impl.Name);
        
        List<ICFG!>! procsToConsider = new List<ICFG!>();
        procsToConsider.Add(mainICFG);
        
        while(procsToConsider.Count != 0) {
           ICFG! p = procsToConsider[0];
           procsToConsider.RemoveAt(0);
           
           foreach(string! callee in p.procsCalled.Keys) {   
              if(!name2Impl.ContainsKey(callee)) continue;

              callGraph.AddEdge(p.impl.Name, callee);
              
              if(maxBlocksInProc < p.nodes.Count) {
                maxBlocksInProc = p.nodes.Count;
              }
              
              if(!callers.ContainsKey(callee)) {
                callers.Add(callee, new List<WorkItem!>());
              }
              foreach(Block!  b in p.procsCalled[callee]) {
                callers[callee].Add(new WorkItem(p, b));
              }
              
              if(procICFG.ContainsKey(callee)) continue;
              ICFG! ncfg = new ICFG(name2Impl[callee]);
              procICFG.Add(callee, ncfg);
              procsToConsider.Add(ncfg);
           }
        }
        
        bool acyclic;
        List<string>! sortedNodes;
        callGraph.TarjanTopSort(out acyclic, out sortedNodes);
        
        assert acyclic;
        
        int cnt = 0;
        for(int i  = sortedNodes.Count - 1; i >= 0; i--) {
          string s = sortedNodes[i];
          if(s == null) continue;
          procPriority.Add(s, cnt);
          cnt++;
        }
        
     }
     
     public static Set<Variable!>! GetVarsLiveAtExit(Implementation! impl, Program! prog) {
       if(varsLiveAtExit.ContainsKey(impl.Name)) {
         return varsLiveAtExit[impl.Name];
       }
       // Return default: all globals and out params
       Set<Variable!>! lv = new Set<Variable!>();
       foreach(Variable! v in prog.GlobalVariables()) {
         lv.Add(v);
       }
       foreach(Variable! v in impl.OutParams) {
         lv.Add(v);
       }
       return lv;
     }
     
     public static Set<Variable!>! GetVarsLiveAtEntry(Implementation! impl, Program! prog) {
       if(varsLiveAtEntry.ContainsKey(impl.Name)) {
         return varsLiveAtEntry[impl.Name];
       }
       // Return default: all globals and in params
       Set<Variable!>! lv = new Set<Variable!>();
       foreach(Variable! v in prog.GlobalVariables()) {
         lv.Add(v);
       }
       foreach(Variable! v in impl.InParams) {
         lv.Add(v);
       }
       return lv;
     }
     
     public static bool HasSummary(string! name) {
        return varsLiveSummary.ContainsKey(name);
     }
     
     public static Set<Variable!>! PropagateLiveVarsAcrossCall(CallCmd! cmd, Set<Variable!>! lvAfter) {
        Procedure! proc = (!)cmd.Proc;
        if(varsLiveSummary.ContainsKey(proc.Name)) {
          GenKillWeight! w1 = getWeightBeforeCall(cmd);
          GenKillWeight! w2 = varsLiveSummary[proc.Name];
          GenKillWeight! w3 = getWeightAfterCall(cmd);
          GenKillWeight! w = GenKillWeight.extend(w1, GenKillWeight.extend(w2, w3));
          return w.getLiveVars(lvAfter);
        }
        Set<Variable!>! ret = new Set<Variable!>();
        ret.AddRange(lvAfter);
        LiveVariableAnalysis.Propagate(cmd, ret);
        return ret;
     }
              
     class WorkItem {
       public ICFG! cfg;
       public Block! block;
       
       public WorkItem(ICFG! cfg, Block! block) {
          this.cfg = cfg;
          this.block = block;
       }
       
       public GenKillWeight! getWeightAfter() {
         return cfg.weightAfter[block];
       }
       
       public bool setWeightBefore(GenKillWeight! w) {
         GenKillWeight! prev = cfg.weightBefore[block];
         GenKillWeight! curr = GenKillWeight.combine(w, prev);
         if(GenKillWeight.isEqual(prev, curr)) return false;
         cfg.weightBefore[block] = curr;
         return true;
       }
       
        [Pure][Reads(ReadsAttribute.Reads.Nothing)]
        public override bool Equals(object other)
        {
            WorkItem! wi = (WorkItem!)(other);
            return (wi.cfg == cfg && wi.block == block);
        }
        
        [Pure]
        public override int GetHashCode()
        {
            return 0;
        }
       
        public string! getLabel() {
           return cfg.impl.Name + "::" + block.Label;
        }
        
     }
       
     private void AddToWorkList(WorkItem! wi) {
        int i = procPriority[wi.cfg.impl.Name];
        int j = wi.cfg.getPriority(wi.block);
        int priority = (i * maxBlocksInProc) + j;
             
        workList.Add(wi, priority);
     }

     private void AddToWorkListReverse(WorkItem! wi) {
        int i = procPriority[wi.cfg.impl.Name];
        int j = wi.cfg.getPriority(wi.block);
        int priority = (procPriority.Count - i) * maxBlocksInProc + j;
        workList.Add(wi, priority);
     }
           
     class WorkList {
        SortedList<int,int>! priorities;
        Set<string!>! labels;
        
        Dictionary<int, List<WorkItem!>!>! workList;
        
        public WorkList() {
          labels = new Set<string!>();
          priorities = new SortedList<int,int>();
          workList = new Dictionary<int, List<WorkItem!>!>();
        }
        
        public void Add(WorkItem! wi, int priority) {
          string! lab = wi.getLabel();
          if(labels.Contains(lab)) {
            // Already on worklist
            return;
          }
          labels.Add(lab);
          if(!workList.ContainsKey(priority)) {
             workList.Add(priority, new List<WorkItem!>());
          }
          workList[priority].Add(wi);
          if(!priorities.ContainsKey(priority)) {
            priorities.Add(priority,0);
          }
          
          priorities[priority] = priorities[priority] + 1;
        }
        
        public WorkItem! Get() {
          // Get minimum priority
          int p = ((!)priorities.Keys)[0];
          priorities[p] = priorities[p] - 1;
          if(priorities[p] == 0) {
            priorities.Remove(p);
          }
          
          // Get a WI with this priority
          WorkItem! wi = workList[p][0];
          workList[p].RemoveAt(0);
          
          // update labels
          labels.Remove(wi.getLabel());
          return wi;
        }
        
        public int Count {
          get {
            return labels.Count;
          }
        }
     }
     
     private GenKillWeight! getSummary(CallCmd! cmd) {
       assert cmd.Proc != null;
       string! procName = cmd.Proc.Name;
       if(procICFG.ContainsKey(procName)) {
         ICFG! cfg = procICFG[procName];
         return GenKillWeight.projectLocals(cfg.summary);
       }
       assert false;
     }
     
     public static void ComputeLiveVars(Implementation! impl, Program !prog) {
       InterProcGenKill! ipgk = new InterProcGenKill(impl, prog);
       ipgk.Compute();
     }
     
     public void Compute() {
       // Put all exit nodes in the worklist
       foreach(ICFG! cfg in procICFG.Values) {
         foreach(Block! eb in cfg.exitNodes) {
           WorkItem! wi = new WorkItem(cfg, eb);
           cfg.weightAfter[eb] = GenKillWeight.one();
           AddToWorkList(wi);
         }
       }
     
       while(workList.Count != 0) {
         WorkItem! wi = workList.Get();
         process(wi);
       }
       
       // Propagate LV to all procedures
       foreach(ICFG! cfg in procICFG.Values) {
         foreach(Block! b in cfg.nodes) {
           cfg.liveVarsAfter.Add(b, new Set<Variable!>());
           cfg.liveVarsBefore.Add(b, new Set<Variable!>());
         }
       }
       
       ICFG! mainCfg = procICFG[mainImpl.Name];
       foreach(Block! eb in mainCfg.exitNodes) {
         WorkItem! wi = new WorkItem(mainCfg, eb);
         AddToWorkListReverse(wi);
       }
       
       while(workList.Count != 0) {
         WorkItem! wi = workList.Get();
         processLV(wi);
       }

       // Set live variable info
       foreach(ICFG! cfg in procICFG.Values) {
          Set<Variable!>! lv = new Set<Variable!>();
          foreach(Block! eb in cfg.exitNodes) {
            lv.AddRange(cfg.liveVarsAfter[eb]);
          }
          varsLiveAtExit.Add(cfg.impl.Name, lv);
          lv = new Set<Variable!>();
          foreach(Block! eb in cfg.srcNodes) {
            lv.AddRange(cfg.liveVarsBefore[eb]);
          }
          varsLiveAtEntry.Add(cfg.impl.Name, lv);
          varsLiveSummary.Add(cfg.impl.Name, cfg.summary);
       }
       
       /*
       foreach(Block! b in mainImpl.Blocks) {
         //Set<Variable!> lv = cfg.weightBefore[b].getLiveVars();
         b.liveVarsBefore = procICFG[mainImpl.Name].liveVarsAfter[b];
         //foreach(GlobalVariable! v in program.GlobalVariables()) {
         //  b.liveVarsBefore.Add(v);
         //}
       }
       */
     }
          
     // Called when summaries have already been computed
     private void processLV(WorkItem! wi) {
        ICFG! cfg = wi.cfg;
        Block! block = wi.block;
        
        Set<Variable!>! lv = cfg.liveVarsAfter[block];
        
        // Propagate backwards in the block
        Set<Variable!>! prop = new Set<Variable!>();
        prop.AddRange(lv);
        for(int i = block.Cmds.Length - 1; i >= 0; i--) {
           Cmd! cmd = block.Cmds[i];
           if(cmd is CallCmd) {
              string! procName = ((!)((CallCmd!)cmd).Proc).Name;
              if(procICFG.ContainsKey(procName)) {
                 ICFG! callee = procICFG[procName];
                 // Inter propagation
                 // Remove local variables; add return variables
                 Set<Variable!>! elv = new Set<Variable!>();
                 foreach(Variable! v in prop) {
                   if(v is GlobalVariable) elv.Add(v);
                 }
                 foreach(Variable! v in callee.impl.OutParams) {
                   elv.Add(v);
                 }
           
                 foreach(Block! eb in callee.exitNodes) {
                   callee.liveVarsAfter[eb].AddRange(elv);
                   // TODO: check if modified before inserting
                   AddToWorkListReverse(new WorkItem(callee, eb));
                 }
                 
                 // Continue with intra propagation
                 GenKillWeight! summary = getWeightCall((CallCmd!)cmd);
                 prop = summary.getLiveVars(prop);
              } else {
                 LiveVariableAnalysis.Propagate(cmd, prop);
              }
           } else {
             LiveVariableAnalysis.Propagate(cmd, prop);
           }
        }
        
        cfg.liveVarsBefore[block].AddRange(prop);
        
        foreach(Block! b in cfg.predEdges[block]) {
           Set<Variable!>! prev = cfg.liveVarsAfter[b];
           Set<Variable!>! curr = (!)prev.Union(cfg.liveVarsBefore[block]);
           if(curr.Count != prev.Count) {
             cfg.liveVarsAfter[b] = curr;
             AddToWorkListReverse(new WorkItem(cfg, b));
           }
        }
     }
     
     private void process(WorkItem! wi) 
     {
       GenKillWeight! w = wi.getWeightAfter();
       
       for(int i = wi.block.Cmds.Length - 1; i >= 0; i--) {
          Cmd! c = wi.block.Cmds[i];
          if(c is CallCmd && procICFG.ContainsKey( ((!)((CallCmd!)c).Proc).Name ) ){
            w = GenKillWeight.extend(getWeightCall((CallCmd!)c), w);
          } else {
            GenKillWeight! cweight = getWeight(c, wi.cfg.impl, program);
            w = GenKillWeight.extend(cweight, w);
          }
       }
       
       bool change = wi.setWeightBefore(w);
       
       if(change && wi.cfg.srcNodes.Contains(wi.block)) {
         GenKillWeight! prev = wi.cfg.summary;
         GenKillWeight! curr = GenKillWeight.combine(prev, wi.cfg.weightBefore[wi.block]);
         if(!GenKillWeight.isEqual(prev, curr)) {
           wi.cfg.summary = curr;
           // push callers onto the worklist
           if(callers.ContainsKey(wi.cfg.impl.Name)) {
             foreach(WorkItem! caller in callers[wi.cfg.impl.Name]) {
               AddToWorkList(caller);
             }
           }
         } 
       }
       
       foreach(Block! b in wi.cfg.predEdges[wi.block]) {
          GenKillWeight! prev = wi.cfg.weightAfter[b];
          GenKillWeight! curr = GenKillWeight.combine(prev, w);
          if(!GenKillWeight.isEqual(prev, curr)) {
            wi.cfg.weightAfter[b] = curr;
            AddToWorkList(new WorkItem(wi.cfg, b));
          }
       }
     
     }

     static Dictionary<Cmd!, GenKillWeight!>! weightCache = new Dictionary<Cmd!, GenKillWeight!>();

     private static GenKillWeight! getWeight(Cmd! cmd) {
       return getWeight(cmd, null, null);
     }

     private GenKillWeight! getWeightCall(CallCmd! cmd) {
        GenKillWeight! w1 = getWeightBeforeCall(cmd);
        GenKillWeight! w2 = getSummary(cmd);
        GenKillWeight! w3 = getWeightAfterCall(cmd);
        return GenKillWeight.extend(w1, GenKillWeight.extend(w2, w3));
     }

     private static GenKillWeight! getWeight(Cmd! cmd, Implementation impl, Program prog) {

      if(weightCache.ContainsKey(cmd))
        return weightCache[cmd];
        
      Set<Variable!>! gen = new Set<Variable!>();
      Set<Variable!>! kill = new Set<Variable!>();
      GenKillWeight! ret;
      
	  if (cmd is AssignCmd) {
	    AssignCmd! assignCmd = (AssignCmd) cmd;
	    // I must first iterate over all the targets and remove the live ones.
	    // After the removals are done, I must add the variables referred on 
	    // the right side of the removed targets
	    foreach (AssignLhs! lhs in assignCmd.Lhss) {
	      Variable var = lhs.DeepAssignedVariable;
	      if (var != null) {
	        if (lhs is SimpleAssignLhs) {
	          // we should only remove non-map target variables because there is an implicit
	          // read of a map variable in an assignment to it
			  kill.Add(var);
			}
	      }
	    }
	    int index = 0;
	    foreach (Expr! expr in assignCmd.Rhss) {
		  VariableCollector! collector = new VariableCollector();
		  collector.Visit(expr);
		  gen.AddRange(collector.usedVars);
		  AssignLhs lhs = assignCmd.Lhss[index];
		  if (lhs is MapAssignLhs) {
		    // If the target is a map, then all indices are also read
		    MapAssignLhs malhs = (MapAssignLhs) lhs;
		    foreach (Expr e in malhs.Indexes) {
		  	VariableCollector! c = new VariableCollector();
		 	c.Visit(e);
			gen.AddRange(c.usedVars);
		    } 
		  }
	      index++;
	    }
	    ret = new GenKillWeight(gen, kill);
	  } else if (cmd is HavocCmd) {
	    HavocCmd! havocCmd = (HavocCmd) cmd;
	    foreach (IdentifierExpr! expr in havocCmd.Vars) {
	      if (expr.Decl != null) {
	        kill.Add(expr.Decl);
	      }
	    }
	    ret = new GenKillWeight(gen, kill);
	  } else if (cmd is PredicateCmd) {
	    assert (cmd is AssertCmd || cmd is AssumeCmd);
	    PredicateCmd! predicateCmd = (PredicateCmd) cmd;
	    if (predicateCmd.Expr is LiteralExpr && prog != null && impl != null) {
	      LiteralExpr le = (LiteralExpr) predicateCmd.Expr;
	      if (le.IsFalse) {
	        List<GlobalVariable!>! globals = prog.GlobalVariables();
	        foreach(Variable! v in globals) {
	          kill.Add(v);
	        }
	        foreach(Variable! v in impl.LocVars) {
	          kill.Add(v);
	        }
	        foreach(Variable! v in impl.OutParams) {
	          kill.Add(v);
	        }
	      }
	    } else {
	      VariableCollector! collector = new VariableCollector();
	      collector.Visit(predicateCmd.Expr);
	      gen.AddRange(collector.usedVars);
	    }
	    ret = new GenKillWeight(gen, kill);
	  } else if (cmd is CommentCmd) {
	    ret = new GenKillWeight(gen, kill);
        // comments are just for debugging and don't affect verification
      } else if (cmd is SugaredCmd) {
        SugaredCmd! sugCmd = (SugaredCmd) cmd;
        ret = getWeight(sugCmd.Desugaring, impl, prog);
      } else if (cmd is StateCmd) {
        StateCmd! stCmd = (StateCmd) cmd;
        CmdSeq! cmds = stCmd.Cmds;
        int len = cmds.Length;
        ret = GenKillWeight.one();
        for (int i = len - 1; i >= 0; i--) {
          GenKillWeight! w = getWeight(cmds[i], impl, prog);
          ret = GenKillWeight.extend(w, ret);
        }
        foreach (Variable! v in stCmd.Locals) {
          kill.Add(v);
        }
        ret = GenKillWeight.extend(new GenKillWeight(gen, kill), ret);
      } else {
        assert false;
      }
      
      weightCache[cmd] = ret;
      return ret;
	}
     
    static Dictionary<Cmd!, GenKillWeight!>! weightCacheAfterCall = new Dictionary<Cmd!, GenKillWeight!>();
    static Dictionary<Cmd!, GenKillWeight!>! weightCacheBeforeCall = new Dictionary<Cmd!, GenKillWeight!>();

    private static GenKillWeight! getWeightAfterCall(Cmd! cmd) {
      
      if(weightCacheAfterCall.ContainsKey(cmd))
        return weightCacheAfterCall[cmd];
      
      Set<Variable!>! gen = new Set<Variable!>();
      Set<Variable!>! kill = new Set<Variable!>();
      
      assert (cmd is CallCmd);
	  CallCmd! ccmd = (CallCmd!)cmd;
	  
	  foreach(IdentifierExpr! ie in ccmd.Outs) {
	    if(ie.Decl != null) kill.Add(ie.Decl);
	  }

      // Variables in ensures are considered as "read"
      foreach(Ensures! re in ((!)ccmd.Proc).Ensures) {
		VariableCollector! collector = new VariableCollector();
		collector.Visit(re.Condition);
		foreach(Variable! v in collector.usedVars) {
		  if(v is GlobalVariable) {
		    gen.Add(v);
		  }
		}  
      }
      	  
	  GenKillWeight! ret = new GenKillWeight(gen, kill);
	  weightCacheAfterCall[cmd] = ret;
	  return ret;
	}
	
	private static GenKillWeight! getWeightBeforeCall(Cmd! cmd) {
      assert (cmd is CallCmd);
      if(weightCacheBeforeCall.ContainsKey(cmd))
        return weightCacheBeforeCall[cmd];
      
      Set<Variable!>! gen = new Set<Variable!>();
      Set<Variable!>! kill = new Set<Variable!>();
      CallCmd! ccmd = (CallCmd!)cmd;
      
      foreach (Expr! expr in ccmd.Ins) {
		VariableCollector! collector = new VariableCollector();
		collector.Visit(expr);
		gen.AddRange(collector.usedVars);
      }
      
      assert ccmd.Proc != null;
      
      // Variables in requires are considered as "read"
      foreach(Requires! re in ccmd.Proc.Requires) {
		VariableCollector! collector = new VariableCollector();
		collector.Visit(re.Condition);
		foreach(Variable! v in collector.usedVars) {
		  if(v is GlobalVariable) {
		    gen.Add(v);
		  }
		}
      }

      // Old variables in ensures are considered as "read"
      foreach(Ensures! re in ccmd.Proc.Ensures) {
		VariableCollector! collector = new VariableCollector();
		collector.Visit(re.Condition);
		foreach(Variable! v in collector.oldVarsUsed) {
		  if(v is GlobalVariable) {
		    gen.Add(v);
		  }
		}
      }
            
      GenKillWeight! ret = new GenKillWeight(gen, kill);
	  weightCacheAfterCall[cmd] = ret;
	  return ret;
	}      
		
  
  }
  
}