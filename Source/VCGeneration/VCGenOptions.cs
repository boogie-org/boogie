namespace Microsoft.Boogie;

public interface VCGenOptions : SMTLibOptions
{
  ProverFactory TheProverFactory { get; }

}