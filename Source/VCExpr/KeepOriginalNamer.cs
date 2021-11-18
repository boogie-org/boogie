using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  /**
   * Visitor that establishes unique variable (or constant) names in a VCExpr.
   * This is done by adding a counter as suffix if name clashes occur
   * TODO: also handle type variables here
   */
  public class KeepOriginalNamer : ScopedNamer, UniqueNamer
  {
    public override string GetOriginalName(string newName)
    {
      return newName;
    }

    public override UniqueNamer Clone()
    {
      Contract.Ensures(Contract.Result<Object>() != null);
      return new KeepOriginalNamer(this);
    }
    
    public KeepOriginalNamer() : base()
    {
    }

    protected KeepOriginalNamer(KeepOriginalNamer namer) : base(namer)
    {
    }

    ////////////////////////////////////////////////////////////////////////////

    // dictionary of all names that have already been used
    // (locally or globally)

    ////////////////////////////////////////////////////////////////////////////

    ////////////////////////////////////////////////////////////////////////////

    // retrieve the name of a thingie; if it does not have a name yet,
    // generate a unique name for it (as close as possible to its inherent
    // name) and register it globally
    public override string GetName(Object thingie, string inherentName)
    {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = this[thingie];

      if (res != null)
      {
        return res;
      }

      // if the object is not yet registered, create a name for it
      res = NextFreeName(thingie, inherentName);
      GlobalNames.Add(thingie, res);

      return res;
    }

    public override string GetLocalName(Object thingie, string inherentName)
    {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = NextFreeName(thingie, inherentName);
      LocalNames[^1][thingie] = res;
      return res;
    }
  }
}