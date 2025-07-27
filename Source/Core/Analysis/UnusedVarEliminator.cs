using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class UnusedVarEliminator : VariableCollector
{
  public static void Eliminate(Program program)
  {
    Contract.Requires(program != null);
    UnusedVarEliminator elim = new UnusedVarEliminator();
    elim.Visit(program);
  }

  private UnusedVarEliminator()
    : base()
  {
  }

  public override Implementation VisitImplementation(Implementation node)
  {
    Contract.Ensures(Contract.Result<Implementation>() != null);
    //Console.WriteLine("Procedure {0}", node.Name);
    Implementation
      impl = base.VisitImplementation(node);
    Contract.Assert(impl != null);
    //Console.WriteLine("Old number of local variables = {0}", impl.LocVars.Length);
    List<Variable>
      vars = new List<Variable>();
    foreach (Variable var in impl.LocVars)
    {
      Contract.Assert(var != null);
      if (_usedVars.Contains(var))
      {
        vars.Add(var);
      }
    }

    impl.LocVars = vars;
    //Console.WriteLine("New number of local variables = {0}", impl.LocVars.Length);
    //Console.WriteLine("---------------------------------");
    _usedVars.Clear();
    return impl;
  }
}