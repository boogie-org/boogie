using System;

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

  public static RandomiseNamer Create(Random random, ScopedNamer namer = null) {
    return namer != null ? new RandomiseNamer(namer, random) : new RandomiseNamer(random);
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