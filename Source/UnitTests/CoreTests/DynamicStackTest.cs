using System;
using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests; 

[TestFixture()]
public class DynamicStackTest {
  
  [Test]
  public void SmallStackTest() {
    MutuallyRecursiveA(2).Run();
  }
  
  [Test]
  public void LargeStackTest() {
    MutuallyRecursiveA(100_000).Run();
  }

  private async DynamicStack MutuallyRecursiveA(int iterations) {
    if (iterations > 0) {
      await MutuallyRecursiveB(iterations - 1);
    }
  }

  private async DynamicStack MutuallyRecursiveB(int iterations) {
    if (iterations > 0) {
      await MutuallyRecursiveA(iterations - 1);
    }
  }
}