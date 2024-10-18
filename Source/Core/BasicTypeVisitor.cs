using System;
using System.Collections.Generic;

namespace Microsoft.Boogie;

public class BasicTypeVisitor : ReadOnlyVisitor
{
  private readonly Func<Absy, bool> enterNode;
  private HashSet<Type> basicTypes = new();
  public BasicTypeVisitor(Absy absy, Func<Absy, bool> enterNode) {
    this.enterNode = enterNode;
    Visit(absy);
  }

  public override Absy Visit(Absy node) {
    if (enterNode(node)) {
      return base.Visit(node);
    }

    return node;
  }

  public override Type VisitBasicType(BasicType node)
  {
    basicTypes.Add(node);
    return node;
  }

  public HashSet<Type> GetBasicTypes()
  {
    return basicTypes;
  }
}