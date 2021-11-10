using System;

namespace Microsoft.Boogie.VCExprAST
{
  public interface IUniqueNamer : ICloneable
  {
    string Lookup(Object thingie);
    
    void Reset();

    string GetName(Object thingie, string name);
    void PopScope();
    void PushScope();
    string GetLocalName(object thingie, string name);
    void ResetLabelCount();
  }
}