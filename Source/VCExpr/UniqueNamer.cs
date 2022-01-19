using System;

namespace Microsoft.Boogie.VCExprAST
{
  public interface UniqueNamer
  {
    string Lookup(Object thingie);
    
    void Reset();

    string GetName(Object thing, string name);
    void PopScope();
    void PushScope();
    string GetLocalName(object thing, string name);

    string GetOriginalName(string newName);

    UniqueNamer Clone();
  }
}