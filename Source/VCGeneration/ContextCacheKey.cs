using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public readonly struct ContextCacheKey
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(program != null);
    }

    public readonly Program program;

    public ContextCacheKey(Program prog)
    {
      Contract.Requires(prog != null);
      this.program = prog;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (that is ContextCacheKey)
      {
        ContextCacheKey thatKey = (ContextCacheKey) that;
        return this.program.Equals(thatKey.program);
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return this.program.GetHashCode();
    }
  }
}