using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class DependencyEvaluator : ReadOnlyVisitor
  {
    // For each declaration, we compute incoming and outgoing dependents.
    // Incoming dependents are functions or constants that the declaration may help the solver with.
    // Most incoming dependents correspond to exactly one function or constant, but some of them are tuples.
    // For example, consider an axiom of the form:
    //                        axiom forall x, y :: {P(x, y), Q(y)} {R(x)} P(x, y) ==> R(x)
    // The axiom may (only) be triggerd by a declaration/implementation that either mentions
    // both P and Q or mentions function R.
    // Thus, it has two incoming dependents:
    // 1) the tuple (P, Q) and 2) the function R. I store tuples in the variable incomingTuples.
    // Outgoing dependents consist of functions and constants that a declaration mentions.
    // For the axiom above, there are 2 outgoing dependents: P and R.
    // (notice that Q is excluded because the axiom itself does not mention it.)
    // Now, a declaration A depends on B, if the outgoing dependents of A match
    // with some incoming dependent of B (see method depends).

    public readonly Declaration node; // a node could either be a function or an axiom.
    public HashSet<Declaration> outgoing; // an edge can either be a function or a constant.
    public List<HashSet<Declaration>> incomingTuples;
    public HashSet<Type> types;

    private static bool ExcludeDep(Declaration d)
    {
      return d.Attributes != null && QKeyValue.FindBoolAttribute(d.Attributes, "exclude_dep");
    }
    
    public void AddIncoming(Declaration declaration)
    {
      if (!ExcludeDep(declaration)) {
        incomingTuples.Add(new[] { declaration }.ToHashSet());
      }
    }
    
    public void AddIncoming(HashSet<Declaration> declarations)
    {
      incomingTuples.Add(declarations);
    }
    
    public DependencyEvaluator(Declaration d)
    {
      node = d;
      incomingTuples = new List<HashSet<Declaration>>();
      outgoing = new HashSet<Declaration>();
      types = new HashSet<Type>();
    }
  }
}