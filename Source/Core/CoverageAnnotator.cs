using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Boogie;

/// <summary>
/// Add `{:id ...}` attributes to all assertions, assumptions, requires
/// clauses, ensures clauses, and call statements so that verification
/// coverage tracking is possible. This exists primarily to support the
/// automatic detection of vacuous proofs in the case where no front
/// end has added these already.
/// </summary>
public class CoverageAnnotator : StandardVisitor
{
  private int idCount = 0;
  private string currentImplementation;
  private Dictionary<string, ISet<string>> implementationGoalIds = new();
  private Dictionary<string, Absy> idMap = new();

  private void AddImplementationGoalId(string id)
  {
    implementationGoalIds[currentImplementation].Add(id);
  }
  
  private void AddIdIfMissing(ICarriesAttributes node, bool isGoal)
  {
    Absy absy = node as Absy;
    if (absy == null) {
      return;
    }
    var idStr = node.FindStringAttribute("id");
    if (idStr == null) {
      idStr = $"id_l{absy.tok.line}_c{absy.tok.col}_{NodeType(node)}_{idCount}";
      idCount++;
    }
    idMap.Add(idStr, absy);
    if (isGoal) {
      AddImplementationGoalId(idStr);
    }
    node.AddStringAttribute(absy.tok, "id", idStr);
  }

  private string NodeType(ICarriesAttributes node)
  {
    return node switch
    {
      Requires _ => "requires",
      Ensures _ => "ensures",
      AssertCmd _ => "assert",
      AssumeCmd _ => "assume",
      CallCmd _ => "call",
      _ => "other"
    };
  }
  
  /// <summary>
  /// Get the set of IDs that correspond to goals within the named
  /// implementation.
  /// </summary>
  /// <param name="implName">The name of the implementation.</param>
  /// <returns>The IDs for all goal elements within the implementation.</returns>
  public ISet<string> GetImplementationGoalIds(string implName) => implementationGoalIds[implName];
  
  /// <summary>
  /// Get the AST node corresponding to the given ID.
  /// </summary>
  /// <param name="idStr">The `id` attribute placed on an AST node.</param>
  /// <returns>The node where that `id` occurs.</returns>
  public Absy GetIdNode(string idStr) => idMap[idStr];

  public override Implementation VisitImplementation(Implementation node)
  {
    currentImplementation = node.Name;
    implementationGoalIds.TryAdd(currentImplementation, new HashSet<string>());
    return base.VisitImplementation(node);
  }
  
  public override Cmd VisitAssertCmd(AssertCmd node)
  {
    if (node.Expr is LiteralExpr {IsTrue: true}) {
      return node;
    }

    AddIdIfMissing(node, true);
    return base.VisitAssertCmd(node);
  }
  
  public override Cmd VisitAssumeCmd(AssumeCmd node)
  {
    AddIdIfMissing(node, false);
    return base.VisitAssumeCmd(node);
  }
  
  public override Cmd VisitCallCmd(CallCmd node)
  {
    AddIdIfMissing(node, false);
    return base.VisitCallCmd(node);
  }
  
  public override Requires VisitRequires(Requires requires)
  {
    AddIdIfMissing(requires, false);
    return base.VisitRequires(requires);
  }
  
  public override Ensures VisitEnsures(Ensures ensures)
  {
    if (ensures.Free) {
      return ensures;
    }

    AddIdIfMissing(ensures, true);
    return base.VisitEnsures(ensures);
  }
}