using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

[ContractClassFor(typeof(TransferCmd))]
public abstract class TransferCmdContracts : TransferCmd
{
  public TransferCmdContracts() : base(null)
  {
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    Contract.Requires(stream != null);
    throw new NotImplementedException();
  }
}