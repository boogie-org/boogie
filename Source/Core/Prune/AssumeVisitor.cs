using System.Collections.Generic;

namespace Microsoft.Boogie
{
  internal class AssumeVisitor : ReadOnlyVisitor
  {
    public AssumeCmd ac;
    public HashSet<Variable> RelVars;

    public AssumeVisitor(AssumeCmd assumeCmd) : base(null)
    {
      this.ac = assumeCmd;
      this.RelVars = new HashSet<Variable>();
    }

    public override Variable VisitVariable(Variable v) {
      RelVars.Add(v);
      return base.VisitVariable(v);
    }
  }
}