using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests; 

[TestFixture()]
public class DynamicStackReturnValueTest {
  
  [Test]
  public void SmallStackTest() {
    var iterations = 2;
    var dynamicStack = MutuallyRecursiveAB(iterations);
    dynamicStack.Run();
    Assert.AreEqual(iterations, dynamicStack.Result);
  }
  
  [Test]
  public void LargeStackTest() {
    var iterations = 100_000;
    var dynamicStack = MutuallyRecursiveAB(iterations);
    dynamicStack.Run();
    Assert.AreEqual(iterations, dynamicStack.Result);
  }

  private async DynamicStack<int> MutuallyRecursiveAB(int iterations) {
    var result = 1;
    if (iterations > 1) {
      result += await MutuallyRecursiveBA(iterations - 1);
    }

    var value  = await Recursive(10);
    Assert.AreEqual(10, value);
    
    Assert.AreEqual(3, await FromResultTest());
    return result;
  }

  private async DynamicStack<int> MutuallyRecursiveBA(int iterations) {
    var result = 1;
    if (iterations > 1) {
      result += await MutuallyRecursiveAB(iterations - 1);
    }
    return result;
  }
  
  private async DynamicStack<int> Recursive(int iterations) {
    var result = 1;
    if (iterations > 1) {
      result += await Recursive(iterations - 1);
    }
    return result;
  }
  
  
  private DynamicStack<int> FromResultTest() {
    return DynamicStack.FromResult(3);
  }
  
}