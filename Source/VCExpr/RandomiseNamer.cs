using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST;

public class RandomiseNamer : ScopedNamer
{
  private Random random;

  public RandomiseNamer(Random random)
  {
    this.random = random;
  }

  public RandomiseNamer(ScopedNamer namer, Random random) : base(namer)
  {
    this.random = random;
  }
  
  private RandomiseNamer(RandomiseNamer namer) : base(namer)
  {
    random = namer.random;
  }

  public void SetRandom(Random random)
  {
    this.random = random;
  }
    
  public override UniqueNamer Clone()
  {
    return new RandomiseNamer(this);
  }

  protected override string GetModifiedName(string uniqueInherentName)
  {
    return $"random{random.Next()}";
  }
}