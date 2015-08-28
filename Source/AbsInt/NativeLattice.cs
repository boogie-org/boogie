//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Boogie.AbstractInterpretation
{
  /// <summary>
  ///  Specifies the operations (e.g., join) on a mathematical lattice that depend
  ///  only on the elements of the lattice.
  /// </summary>
  public abstract class NativeLattice
  {
    /// <summary>
    ///  An element of the lattice.  This class should be derived from in any
    ///  implementation of MathematicalLattice.
    /// </summary>
    public abstract class Element
    {
      public abstract Expr ToExpr();
    }

    public abstract Element Top { get; }
    public abstract Element Bottom { get; }

    public abstract bool IsTop(Element element);
    public abstract bool IsBottom(Element element);

    /// <summary>
    /// Is 'a' better (or equal) information than 'b'?  That is, is 'a' below 'b' in the lattice?
    /// </summary>
    public abstract bool Below(Element a, Element b);

    public abstract Element Meet(Element a, Element b);
    public abstract Element Join(Element a, Element b);
    public abstract Element Widen(Element a, Element b);

    public abstract Element Constrain(Element element, Expr expr);
    public abstract Element Update(Element element, AssignCmd cmd);  // requiers 'cmd' to be a simple (possibly parallel) assignment command
    public abstract Element Eliminate(Element element, Variable v);

    /// <summary>
    /// Specialize the lattice to implementation "impl", if non-null.
    /// If "impl" is null, remove specialization.
    /// </summary>
    public virtual void Specialize(Implementation impl) {
    }

    public virtual void Validate() {
      Contract.Assert(IsTop(Top));
      Contract.Assert(IsBottom(Bottom));
      Contract.Assert(!IsBottom(Top));
      Contract.Assert(!IsTop(Bottom));

      Contract.Assert(Below(Top, Top));
      Contract.Assert(Below(Bottom, Top));
      Contract.Assert(Below(Bottom, Bottom));

      Contract.Assert(IsTop(Join(Top, Top)));
      Contract.Assert(IsBottom(Join(Bottom, Bottom)));
    }
  }

  public class NativeAbstractInterpretation
  {
    public static void RunAbstractInterpretation(Program program) {
      Contract.Requires(program != null);

      if (!CommandLineOptions.Clo.UseAbstractInterpretation) {
        return;
      }
      Helpers.ExtraTraceInformation("Starting abstract interpretation");

      DateTime start = new DateTime();  // to please compiler's definite assignment rules
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine();
        Console.WriteLine("Running abstract interpretation...");
        start = DateTime.UtcNow;
      }

      WidenPoints.Compute(program);

      NativeLattice lattice = null;
      if (CommandLineOptions.Clo.Ai.J_Trivial) {
        lattice = new TrivialDomain();
      } else if (CommandLineOptions.Clo.Ai.J_Intervals) {
        lattice = new NativeIntervallDomain();
      }

      if (lattice != null) {
        Dictionary<Procedure, Implementation[]> procedureImplementations = ComputeProcImplMap(program);
        ComputeProgramInvariants(program, procedureImplementations, lattice);
        if (CommandLineOptions.Clo.Ai.DebugStatistics) {
          Console.Error.WriteLine(lattice);
        }
      }

      if (CommandLineOptions.Clo.Trace) {
        DateTime end = DateTime.UtcNow;
        TimeSpan elapsed = end - start;
        Console.WriteLine("  [{0} s]", elapsed.TotalSeconds);
        Console.Out.Flush();
      }
    }

    private static Dictionary<Procedure, Implementation[]> ComputeProcImplMap(Program program) {
      Contract.Requires(program != null);
      // Since implementations call procedures (impl. signatures) 
      // rather than directly calling other implementations, we first
      // need to compute which implementations implement which
      // procedures and remember which implementations call which
      // procedures.

      return program
            .Implementations
            .GroupBy(i => i.Proc).Select(g => g.ToArray()).ToDictionary(a => a[0].Proc);
    }

    /// <summary>
    /// Compute and apply the invariants for the program using the underlying abstract domain.
    /// </summary>
    public static void ComputeProgramInvariants(Program program, Dictionary<Procedure, Implementation[]> procedureImplementations, NativeLattice lattice) {
      Contract.Requires(program != null);
      Contract.Requires(procedureImplementations != null);
      Contract.Requires(lattice != null);

      // Gather all the axioms to create the initial lattice element
      // Differently stated, it is the \alpha from axioms (i.e. first order formulae) to the underlyng abstract domain
      var initialElement = lattice.Top;
      Contract.Assert(initialElement != null);
      foreach (var ax in program.Axioms) {
        initialElement = lattice.Constrain(initialElement, ax.Expr);
      }

      // analyze each procedure
      foreach (var proc in program.Procedures) {
        if (procedureImplementations.ContainsKey(proc)) {
          // analyze each implementation of the procedure
          foreach (var impl in procedureImplementations[proc]) {
            // add the precondition to the axioms
            Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());
            var start = initialElement;
            foreach (Requires pre in proc.Requires) {
              Expr e = Substituter.Apply(formalProcImplSubst, pre.Condition);
              start = lattice.Constrain(start, e);
            }

            lattice.Specialize(impl);
            Analyze(impl, lattice, start);
            lattice.Specialize(null);
          }
        }
      }
    }

    public static void Analyze(Implementation impl, NativeLattice lattice, NativeLattice.Element start) {
      // We need to keep track of some information for each(some) block(s).  To do that efficiently,
      // we number the implementation's blocks sequentially, and then we can use arrays to store
      // the additional information.
      var pre = new NativeLattice.Element[impl.Blocks.Count];  // set to null if we never compute a join/widen at this block
      var post = CommandLineOptions.Clo.InstrumentInfer == CommandLineOptions.InstrumentationPlaces.Everywhere ? new NativeLattice.Element[impl.Blocks.Count] : null;
      var iterations = new int[impl.Blocks.Count];
      var bottom = lattice.Bottom;
      int n = 0;
      foreach (var block in impl.Blocks) {
        block.aiId = n;
        // Note:  The forward analysis below will store lattice elements in pre[n] if pre[n] is non-null.
        // Thus, the assignment "pre[n] = bottom;" below must be done under the following condition:
        //    n == 0 || block.widenBlock
        // One possible strategy would be to do it only under that condition.  Alternatively,
        // one could do the assignment under the following condition:
        //    n == 0 || block.widenBlock || block.Predecessors.Length != 1
        // (which would require first setting the Predecessors field).  In any case, if
        //    CommandLineOptions.Clo.InstrumentInfer == CommandLineOptions.InstrumentationPlaces.Everywhere
        // then all pre[n] should be set.
        pre[n] = bottom;
        n++;
      }
      Contract.Assert(n == impl.Blocks.Count);

      var workItems = new Queue<Tuple<Block, NativeLattice.Element>>();
      workItems.Enqueue(new Tuple<Block, NativeLattice.Element>(impl.Blocks[0], start));
      //ComputeBlockInvariantsNative(impl, );
      // compute a fixpoint here
      while (workItems.Count > 0) {
        var workItem = workItems.Dequeue();
        var b = workItem.Item1;
        var id = b.aiId;
        var e = workItem.Item2;
        if (pre[id] == null) {
          // no pre information stored here, so just go ahead through the block
        } else if (lattice.Below(e, pre[id])) {
          // no change
          continue;
        } else if (b.widenBlock && CommandLineOptions.Clo.StepsBeforeWidening <= iterations[id]) {
          e = lattice.Widen(pre[id], e);
          pre[id] = e;
          iterations[id]++;
        } else {
          e = lattice.Join(pre[id], e);
          pre[id] = e;
          iterations[id]++;
        }

        // propagate'e' through b.Cmds
        foreach (Cmd cmd in b.Cmds) {
          e = Step(lattice, cmd, e);
        }

        if (post != null && pre[id] != null) {
          post[id] = e;
        }

        var g = b.TransferCmd as GotoCmd;
        if (g != null) {  // if g==null, it's a pity we didn't pay attention to that earlier, because then we could have skipped analyzing the code in this block
          foreach (Block succ in g.labelTargets) {
            workItems.Enqueue(new Tuple<Block, NativeLattice.Element>(succ, e));
          }
        }
      }

      Instrument(impl, pre, post);
    }

    static void Instrument(Implementation impl, NativeLattice.Element[] pre, NativeLattice.Element[] post) {
      Contract.Requires(impl != null);
      Contract.Requires(pre != null);

      foreach (var b in impl.Blocks) {
        var element = pre[b.aiId];
        if (element != null && (b.widenBlock || CommandLineOptions.Clo.InstrumentInfer == CommandLineOptions.InstrumentationPlaces.Everywhere)) {
          List<Cmd> newCommands = new List<Cmd>();
          Expr inv = element.ToExpr();
          PredicateCmd cmd;
          var kv = new QKeyValue(Token.NoToken, "inferred", new List<object>(), null);
          if (CommandLineOptions.Clo.InstrumentWithAsserts) {
            cmd = new AssertCmd(Token.NoToken, inv, kv);
          } else {
            cmd = new AssumeCmd(Token.NoToken, inv, kv);
          }
          newCommands.Add(cmd);
          newCommands.AddRange(b.Cmds);
          if (post != null && post[b.aiId] != null) {
            inv = post[b.aiId].ToExpr();
            kv = new QKeyValue(Token.NoToken, "inferred", new List<object>(), null);
            if (CommandLineOptions.Clo.InstrumentWithAsserts) {
              cmd = new AssertCmd(Token.NoToken, inv, kv);
            } else {
              cmd = new AssumeCmd(Token.NoToken, inv, kv);
            }
            newCommands.Add(cmd);
          }
          b.Cmds = newCommands;  // destructively replace the commands of the block
        }
      }
    }

    /// <summary>
    /// The abstract transition relation.
    /// 'cmd' is allowed to be a StateCmd.
    /// </summary>
    static NativeLattice.Element Step(NativeLattice lattice, Cmd cmd, NativeLattice.Element elmt) {
      Contract.Requires(lattice != null);
      Contract.Requires(cmd != null);
      Contract.Requires(elmt != null);
      Contract.Ensures(Contract.Result<NativeLattice.Element>() != null);

      if (cmd is AssignCmd) { // parallel assignment
        var c = (AssignCmd)cmd;
        elmt = lattice.Update(elmt, c.AsSimpleAssignCmd);
      } else if (cmd is HavocCmd) {
        var c = (HavocCmd)cmd;
        foreach (IdentifierExpr id in c.Vars) {
          Contract.Assert(id != null);
          elmt = lattice.Eliminate(elmt, id.Decl);
        }
      } else if (cmd is PredicateCmd) {
        var c = (PredicateCmd)cmd;
        var conjuncts = new List<Expr>();
        foreach (var ee in Conjuncts(c.Expr)) {
          Contract.Assert(ee != null);
          elmt = lattice.Constrain(elmt, ee);
        }
      } else if (cmd is StateCmd) {
        var c = (StateCmd)cmd;
        // Iterate the abstract transition on all the commands in the desugaring of the call
        foreach (Cmd callDesug in c.Cmds) {
          Contract.Assert(callDesug != null);
          elmt = Step(lattice, callDesug, elmt);
        }
        // Project out the local variables of the StateCmd
        foreach (Variable local in c.Locals) {
          Contract.Assert(local != null);
          elmt = lattice.Eliminate(elmt, local);
        }
      } else if (cmd is SugaredCmd) {
        var c = (SugaredCmd)cmd;
        elmt = Step(lattice, c.Desugaring, elmt);
      } else if (cmd is CommentCmd) {
        // skip
      } else {
        Contract.Assert(false);  // unknown command
      }
      return elmt;
    }

    /// <summary>
    /// Yields the conjuncts of 'expr'.
    /// </summary>
    public static IEnumerable<Expr> Conjuncts(Expr expr) {
      Contract.Requires(expr != null);

      var e = expr as NAryExpr;
      if (e != null && e.Fun.FunctionName == "&&") {    // if it is a conjunction
        foreach (Expr ee in e.Args) {
          Contract.Assert(ee != null);
          foreach (var c in Conjuncts(ee)) {
            yield return c;
          }
        }
      } else {
        yield return expr;
      }
    }

  }
}
