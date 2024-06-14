using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.TypeErasure;

[ContractClassFor(typeof(TypeEraser))]
public abstract class TypeEraserContracts : TypeEraser {
  public TypeEraserContracts()
    : base(null, null) {
  }

  protected override OpTypeEraser OpEraser {
    get {
      Contract.Ensures(Contract.Result<OpTypeEraser>() != null);
      throw new NotImplementedException();
    }
  }
}