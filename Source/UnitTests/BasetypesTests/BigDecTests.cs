using Microsoft.Basetypes;
using NUnit.Framework;
using System.Numerics;

namespace BasetypesTests
{
  [TestFixture()]
  public class BigDecTests {

    [Test()]
    public void FromStringNegative() {
      // This tests for a Bug in Boogie that used to be present where BigDec
      // would not parse strings with negative numbers correctly
      //
      // If this bug is present this test will fail when checking the mantissa
      var v = BigDec.FromString("-1.5");
      Assert.AreEqual(-1, v.Exponent);
      Assert.AreEqual(new BigInteger(-15.0), v.Mantissa);
    }

    [Test()]
    public void FromStringPositive() {
      var v = BigDec.FromString("1.5");
      Assert.AreEqual(-1, v.Exponent);
      Assert.AreEqual(new BigInteger(15.0), v.Mantissa);
    }
  }
}

