using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST;

public class RandomiseNamer : ScopedNamer
{
  private readonly Random random;

  public RandomiseNamer(Random random)
  {
    this.random = random;
  }

  private RandomiseNamer(RandomiseNamer namer) : base(namer)
  {
    random = namer.random;
  }
    
  public override UniqueNamer Clone()
  {
    return new RandomiseNamer(this);
  }

  protected override string GetModifiedName(string uniqueInherentName)
  {
    return random.NextInt64().ToString();
  }
}