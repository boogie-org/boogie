using Microsoft.BaseTypes;
using NUnit.Framework;
using System.Numerics;

namespace BaseTypesTests
{
  [TestFixture()]
  public class BigDecTests
  {
    [Test()]
    public void FromStringNegative()
    {
      // This tests for a Bug in Boogie that used to be present where BigDec
      // would not parse strings with negative numbers correctly
      //
      // If this bug is present this test will fail when checking the mantissa
      var v = BigDec.FromString("-1.5");
      Assert.AreEqual(-1, v.Exponent);
      Assert.AreEqual(new BigInteger(-15.0), v.Mantissa);
    }

    [TestCase("-0.5", -5, -1)]
    [TestCase("-0.05", -5, -2)]
    [TestCase("-0.0625", -625, -4)]
    [TestCase("-0.50", -5, -1)]
    [TestCase("-00.5", -5, -1)]
    [TestCase("-0.5e3", -5, 2)]
    [TestCase("-0.5e-3", -5, -4)]
    // Spelled with a non-zero integral part these always worked: "-5e-1" is the "-0.5" above.
    [TestCase("-5e-1", -5, -1)]
    [TestCase("-1.5", -15, -1)]
    public void FromStringNegativeBelowOne(string value, int expectedMantissa, int expectedExponent)
    {
      // These all came back positive, since "-0" parses with Sign 0.
      var v = BigDec.FromString(value);
      Assert.AreEqual(new BigInteger(expectedMantissa), v.Mantissa, "mantissa");
      Assert.AreEqual(expectedExponent, v.Exponent, "exponent");
      Assert.IsTrue(v.IsNegative, "the sign should survive parsing");
    }

    [Test()]
    public void FromStringPositive()
    {
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
      if (value.StartsWith("-"))
      {
        Assert.IsTrue(v.IsNegative);
      }
      else
      {
        Assert.IsTrue(v.IsPositive || v.IsZero);
      }

      BigInteger floor = 0;
      BigInteger ceiling = 0;
      v.FloorCeiling(out floor, out ceiling);
      Assert.AreEqual(new BigInteger(expectedFloor), floor);
      Assert.AreEqual(new BigInteger(expectedCeiling), ceiling);
    }
  }
}