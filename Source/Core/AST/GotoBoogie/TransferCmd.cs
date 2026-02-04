using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

[ContractClass(typeof(TransferCmdContracts))]
public abstract class TransferCmd : Absy
{
  public ProofObligationDescription Description { get; set; } = new PostconditionDescription();

  internal TransferCmd(IToken tok)
    : base(tok)
  {
    
  }

  public abstract void Emit(TokenTextWriter stream, int level);

  public override void Typecheck(TypecheckingContext tc)
  {
    // nothing to typecheck
  }

  public override string ToString()
  {
    
    System.IO.StringWriter buffer = new System.IO.StringWriter();
    using TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false, false, PrintOptions.Default);
    this.Emit(stream, 0);

    return buffer.ToString();
  }
}