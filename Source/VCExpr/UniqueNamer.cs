using System;

namespace Microsoft.Boogie.VCExprAST
{
  public interface UniqueNamer
  {
    string Lookup(Object thingie);
    
    void Reset();

    string GetName(Object thingie, string name);
    void PopScope();
    void PushScope();
    string GetLocalName(object thingie, string name);

    string GetOriginalName(string newName);
    UniqueNamer Clone();
  }
}