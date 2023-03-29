using Microsoft.Boogie.DynamicStack;
using NUnit.Framework;

namespace CoreTests; 

[TestFixture()]
public class DynamicStackReturnValueTest {
  
  [Test]
  public void SmallStackTest() {
    var iterations = 2;
    var dynamicStack = MutuallyRecursiveA(iterations);
    dynamicStack.Run();
    Assert.AreEqual(iterations, dynamicStack.Result);
  }
  
  [Test]
  public void LargeStackTest() {
    var iterations = 100_000;
    var dynamicStack = MutuallyRecursiveA(iterations);
    dynamicStack.Run();
    Assert.AreEqual(iterations, dynamicStack.Result);
  }

  private async DynamicStack<int> MutuallyRecursiveA(int iterations) {
    var result = 1;
    if (iterations > 1) {
      result += await MutuallyRecursiveB(iterations - 1);
    }
    return result;
  }

  private async DynamicStack<int> MutuallyRecursiveB(int iterations) {
    var result = 1;
    if (iterations > 1) {
      result += await MutuallyRecursiveA(iterations - 1);
    }
    return result;
  }
}