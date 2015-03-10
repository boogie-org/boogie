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

        [TestCase("0.0", 0, 0)]
        [TestCase("5.0", 5, 5)]
        [TestCase("5.5", 5, 6)]
        [TestCase("5.9", 5, 6)]
        [TestCase("15e1", 150, 150)]
        [TestCase("15e-1", 1, 2)]
        // Negative values
        // Note we expect floor to round towards negative infinity
        // and ceiling to round towards positive infinity
        [TestCase("-15e-1", -2, -1)]
        [TestCase("-5.0", -5, -5)]
        [TestCase("-5e0", -5, -5)]
        [TestCase("-5e1", -50, -50)]
        [TestCase("-5e-1", -1, 0)]
        [TestCase("-5.5", -6, -5)]
        [TestCase("-5.9", -6, -5)]
        public void FloorAndCeil(string value, int expectedFloor, int expectedCeiling)
        {
            var v = BigDec.FromString(value);
            if (value.StartsWith ("-"))
                Assert.IsTrue(v.IsNegative);
            else
                Assert.IsTrue(v.IsPositive || v.IsZero);

            BigInteger floor = 0;
            BigInteger ceiling = 0;
            v.FloorCeiling(out floor, out ceiling);
            Assert.AreEqual(new BigInteger(expectedFloor), floor);
            Assert.AreEqual(new BigInteger(expectedCeiling), ceiling);
        }
  }
}

