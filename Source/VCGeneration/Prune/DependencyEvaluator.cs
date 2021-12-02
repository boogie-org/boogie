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

    public readonly Declaration declaration; // a node could either be a function or an axiom.
    public readonly HashSet<Declaration> outgoing = new(); // an edge can either be a function or a constant.
    public List<Declaration[]> incomingSets = new();
    public HashSet<Type> types = new();

    protected void AddIncoming(Declaration newIncoming)
    {
      if (QKeyValue.FindBoolAttribute(declaration.Attributes, "include_dep")) {
        incomingSets.Add(new[] { newIncoming });
      }
    }

    protected void AddOutgoing(Declaration newOutgoing)
    {
      outgoing.Add(newOutgoing);
    }

    protected void AddIncoming(Declaration[] declarations)
    {
      incomingSets.Add(declarations);
    }

    protected DependencyEvaluator(Declaration declaration)
    {
      this.declaration = declaration;
    }
  }
}