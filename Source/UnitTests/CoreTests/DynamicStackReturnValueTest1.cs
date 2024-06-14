using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests; 

[TestFixture()]
public class DynamicStackReturnValueTest1 {

  [Test]
  public void SmallStackRecursiveTest() {
    var value  = Recursive(10).Result;
    Assert.AreEqual(10, value);
  }
  
  private async DynamicStack<int> Recursive(int iterations) {
    var result = 1;
    if (iterations > 1) {
      var recValue = await Recursive(iterations - 1);
      result += recValue;
    }
    return result;
  }
  
  
  private DynamicStack<int> FromResultTest() {
    return DynamicStack.FromResult(3);
  }
  
}