using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie;

public interface ICarriesAttributes
{
  QKeyValue Attributes { get; set; }

  public void ResolveAttributes(ResolutionContext rc)
  {
    for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
    {
      kv.Resolve(rc);
    }
  }

  public void TypecheckAttributes(TypecheckingContext tc)
  {
    var oldGlobalAccessOnlyInOld = tc.GlobalAccessOnlyInOld;
    tc.GlobalAccessOnlyInOld = false;
    for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
    {
      kv.Typecheck(tc);
    }
    tc.GlobalAccessOnlyInOld = oldGlobalAccessOnlyInOld;
  }

  public List<int> FindLayers()
  {
    List<int> layers = new List<int>();
    for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
    {
      if (kv.Key == CivlAttributes.LAYER)
      {
        layers.AddRange(kv.Params.Select(o => ((LiteralExpr)o).asBigNum.ToIntSafe));
      }
    }
    return layers.Distinct().OrderBy(l => l).ToList();
  }

  // Look for {:name string} in list of attributes.
  public string FindStringAttribute(string name)
  {
    return QKeyValue.FindStringAttribute(Attributes, name);
  }

  public void AddStringAttribute(IToken tok, string name, string parameter)
  {
    Attributes = new QKeyValue(tok, name, new List<object>() {parameter}, Attributes);
  }

}

public static class CarriesAttributesExtensions
{
  

  public static void CopyIdFrom(this ICarriesAttributes dest, IToken tok, ICarriesAttributes src)
  {
    var id = src.FindStringAttribute("id");
    if (id is not null) {
      dest.AddStringAttribute(tok, "id", id);
    }
  }

  public static void CopyIdWithModificationsFrom(this ICarriesAttributes dest, IToken tok, ICarriesAttributes src, Func<string,TrackedNodeComponent> modifier)
  {
    var id = src.FindStringAttribute("id");
    if (id is not null) {
      dest.AddStringAttribute(tok, "id", modifier(id).SolverLabel);
    }
  }
}