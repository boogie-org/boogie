using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

[ContractClassFor(typeof(StructuredCmd))]
public abstract class StructuredCmdContracts : StructuredCmd
{
  public override void Emit(TokenTextWriter stream, int level)
  {
    
    throw new NotImplementedException();
  }

  public StructuredCmdContracts() : base(null)
  {
  }
}