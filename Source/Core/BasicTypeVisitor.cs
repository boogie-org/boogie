using System.Collections.Generic;

namespace Microsoft.Boogie;

public class BasicTypeVisitor : ReadOnlyVisitor
{
  private HashSet<Type> basicTypes = new();
  public BasicTypeVisitor(Absy absy)
  {
    Visit(absy);
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