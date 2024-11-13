using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public static class QKeyValueExtensions {

  // Return 'true' if {:name true} or {:name} is an attribute in 'kv'
  public static bool FindBoolAttribute(this QKeyValue kv, string name)
  {
    Contract.Requires(name != null);
    kv = QKeyValue.FindAttribute(kv, qkv => qkv.Key == name && (qkv.Params.Count == 0 ||
                                                                (qkv.Params.Count == 1 && qkv.Params[0] is LiteralExpr &&
                                                                 ((LiteralExpr) qkv.Params[0]).IsTrue)));
    return kv != null;
  }
}