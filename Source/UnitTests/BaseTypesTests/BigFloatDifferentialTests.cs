using System;
using System.Collections.Generic;
using System.Numerics;
using System.Reflection;
using NUnit.Framework;
using Microsoft.BaseTypes;

namespace BaseTypesTests
{
    /// <summary>
    /// Checks BigFloat against expectations that share no code with it, since every conversion and operator
    /// routes through the same rounding helpers and so cannot catch an error in them:
    ///
    ///   1. ExactRoundToNearestEven - a rational rounded in BigInteger with exactly one rounding step.
    ///   2. Hardware - float is bit-for-bit BigFloat(24,8) and double is bit-for-bit BigFloat(53,11).
    ///      Arithmetic must be done in the target precision, since computing a float result via double
    ///      rounds twice and reproduces the defect under test.
    ///   3. Closed forms, where the format makes the answer derivable by hand. These are the only ones that
    ///      reach the wide exponent sizes, since both oracles above are limited to the narrow formats.
    ///
    /// The two oracles are cross-checked against each other in <see cref="OraclesAgreeWithEachOther"/>.
    /// </summary>
    [TestFixture]
    public class BigFloatDifferentialTests
    {
        private const int SingleSignificand = 24;
        private const int SingleExponent = 8;

        /// <summary>
        /// Correctly rounded round-to-nearest-even value of numerator/denominator in the given format,
        /// shaped like <see cref="Internals"/> so the two compare directly, or null if it overflows to
        /// infinity. The scale is kept in an int, which bounds this to the narrow formats.
        /// </summary>
        private static (BigInteger exponent, BigInteger significand, bool signBit)? ExactRoundToNearestEven(
            BigInteger numerator, BigInteger denominator, int significandSize, int exponentSize)
        {
            var signBit = (numerator < 0) != (denominator < 0);
            numerator = BigInteger.Abs(numerator);
            denominator = BigInteger.Abs(denominator);

            if (numerator.IsZero)
            {
                return (BigInteger.Zero, BigInteger.Zero, signBit);
            }

            BigInteger bias = (BigInteger.One << (exponentSize - 1)) - 1;
            BigInteger maxExponent = (BigInteger.One << exponentSize) - 1;
            var scale = 0;

            // Scale until the quotient occupies exactly significandSize bits.
            while (numerator / denominator >= BigInteger.One << significandSize)
            {
                denominator <<= 1;
                scale++;
            }

            while (numerator / denominator < BigInteger.One << (significandSize - 1))
            {
                numerator <<= 1;
                scale--;
            }

            // Below the smallest normal, every value shares one exponent, so clamp onto that grid.
            var minScale = (int)(1 - bias - (significandSize - 1));
            if (scale < minScale)
            {
                denominator <<= minScale - scale;
                scale = minScale;
            }

            var quotient = BigInteger.DivRem(numerator, denominator, out var remainder);

            // The single rounding, decided against the exact residual.
            if (remainder * 2 > denominator || (remainder * 2 == denominator && !quotient.IsEven))
            {
                quotient++;
            }

            if (quotient >= BigInteger.One << significandSize)
            {
                quotient >>= 1;
                scale++;
            }

            if (quotient < BigInteger.One << (significandSize - 1))
            {
                return (BigInteger.Zero, quotient, signBit); // subnormal
            }

            var biasedExponent = scale + significandSize - 1 + bias;
            return biasedExponent >= maxExponent
                ? null
                : (biasedExponent, quotient - (BigInteger.One << (significandSize - 1)), signBit);
        }

        /// <summary>
        /// The stored exponent, significand and sign. Only ToSMTLibString exposes these publicly, and only
        /// as text, so reading the fields is what makes a 1-ULP difference visible as a value.
        /// </summary>
        private static (BigInteger exponent, BigInteger significand, bool signBit) Internals(BigFloat value)
        {
            return ((BigInteger)Field("exponent").GetValue(value),
                    (BigInteger)Field("significand").GetValue(value),
                    (bool)Field("signBit").GetValue(value));
        }

        /// <summary>
        /// Looks up a private BigFloat field, failing with the field's name rather than a
        /// NullReferenceException from the caller if it has been renamed.
        /// </summary>
        private static FieldInfo Field(string name)
        {
            var field = typeof(BigFloat).GetField(name, BindingFlags.NonPublic | BindingFlags.Instance);
            Assert.NotNull(field,
                $"BigFloat has no private field '{name}'. This fixture reads the stored exponent, "
                + "significand and sign directly, since no public member exposes them; update Internals "
                + "if the fields were renamed.");
            return field;
        }

        /// <summary>float is bit-for-bit BigFloat(24,8).</summary>
        private static BigFloat FromSingle(float value)
        {
            var bits = BitConverter.SingleToInt32Bits(value);
            return new BigFloat((bits >> 31) != 0, bits & 0x7FFFFF, (bits >> 23) & 0xFF,
                SingleSignificand, SingleExponent);
        }

        /// <summary>double is bit-for-bit BigFloat(53,11).</summary>
        private static BigFloat FromDouble(double value)
        {
            var bits = BitConverter.DoubleToInt64Bits(value);
            return new BigFloat(bits < 0, (BigInteger)(bits & 0xFFFFFFFFFFFFFL),
                (BigInteger)((bits >> 52) & 0x7FF), 53, 11);
        }

        /// <summary>
        /// Renders a value for comparison and for failure output, collapsing the special values that have
        /// no (exponent, significand) meaning.
        /// </summary>
        private static string Describe(BigFloat value)
        {
            if (value.IsNaN)
            {
                return "NaN";
            }

            if (value.IsInfinity)
            {
                return value.IsNegative ? "-inf" : "+inf";
            }

            var (exponent, significand, signBit) = Internals(value);
            return $"{(signBit ? "-" : "+")}(exp {exponent}, sig {significand})";
        }

        private static string DescribeSingle(float value)
        {
            if (float.IsNaN(value))
            {
                return "NaN";
            }

            return float.IsInfinity(value)
                ? (value < 0 ? "-inf" : "+inf")
                : Describe(FromSingle(value));
        }

        private static string DescribeDouble(double value)
        {
            if (double.IsNaN(value))
            {
                return "NaN";
            }

            return double.IsInfinity(value)
                ? (value < 0 ? "-inf" : "+inf")
                : Describe(FromDouble(value));
        }

        private static float Apply(char op, float left, float right)
        {
            return op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
        }

        private static double Apply(char op, double left, double right)
        {
            return op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
        }

        /// <summary>
        /// Describes how BigFloat and hardware differ on one operation, or null if they agree.
        /// </summary>
        private static string Mismatch(char op, float left, float right)
        {
            var expected = DescribeSingle(Apply(op, left, right));
            var actual = Describe(Apply(op, FromSingle(left), FromSingle(right)));
            return expected == actual ? null : $"{left:R} {op} {right:R}: got {actual}, want {expected}";
        }

        private static string Mismatch(char op, double left, double right)
        {
            var expected = DescribeDouble(Apply(op, left, right));
            var actual = Describe(Apply(op, FromDouble(left), FromDouble(right)));
            return expected == actual ? null : $"{left:R} {op} {right:R}: got {actual}, want {expected}";
        }

        private static void AssertMatchesHardware(char op, float left, float right, string label = null)
        {
            Assert.IsNull(Mismatch(op, left, right), label ?? $"{left:R} {op} {right:R}");
        }

        /// <summary>
        /// Asserts that a result is the subnormal with the given significand. Zero counts as significand 0.
        /// </summary>
        private static void AssertSubnormal(BigFloat value, BigInteger expectedSignificand, string label)
        {
            var (exponent, significand, _) = Internals(value);
            Assert.AreEqual(BigInteger.Zero, exponent, $"{label}: should have stayed subnormal");
            Assert.AreEqual(expectedSignificand, significand, label);
        }

        /// <summary>
        /// If the two oracles disagree, no other result in this fixture means anything.
        /// </summary>
        [Test]
        public void OraclesAgreeWithEachOther()
        {
            var disagreements = new List<string>();

            for (var a = 1; a <= 200; a++)
            {
                for (var b = 1; b <= 200; b++)
                {
                    var hardware = (float)a / b;
                    if (hardware == 0 || float.IsInfinity(hardware))
                    {
                        continue;
                    }

                    var exact = ExactRoundToNearestEven(a, b, SingleSignificand, SingleExponent);

                    if (exact != Internals(FromSingle(hardware)))
                    {
                        disagreements.Add($"{a}/{b}");
                    }
                }
            }

            Assert.IsEmpty(disagreements,
                $"the exact oracle and hardware disagree on {disagreements.Count} rationals; "
                + "one of the two oracles is wrong, so no other test here means anything");
        }

        /// <summary>
        /// Rationals whose correctly rounded value can be checked by hand, without trusting either oracle.
        /// For 1/15 at (24,8): 2^27/15 = 8947848 remainder 8; 2*8 > 15, so round up to 8947849; less the
        /// implicit 2^23 that leaves a trailing significand of 559241. Rounding 1/15 twice gives 559240.
        ///
        /// The last case carries: 1 - 2^-25 has 24-bit significand exactly 16777215.5, a tie that rounds to
        /// the even 2^24 and so lands on 1.0.
        /// </summary>
        private static IEnumerable<TestCaseData> HandCheckedRationals()
        {
            yield return new TestCaseData(1, 15, 123, 559241).SetArgDisplayNames("OneFifteenth");
            yield return new TestCaseData(1, 3, 125, 2796203).SetArgDisplayNames("OneThird");
            yield return new TestCaseData(2, 3, 126, 2796203).SetArgDisplayNames("TwoThirds");
            yield return new TestCaseData(1, 10, 123, 5033165).SetArgDisplayNames("OneTenth");
            yield return new TestCaseData(1, 2, 126, 0).SetArgDisplayNames("Half");
            yield return new TestCaseData(3, 1, 128, 4194304).SetArgDisplayNames("Three");
            yield return new TestCaseData(33554431, 33554432, 127, 0).SetArgDisplayNames("JustBelowOneCarries");
        }

        [TestCaseSource(nameof(HandCheckedRationals))]
        public void FromRationalMatchesHandCheckedValue(int numerator, int denominator,
            int expectedExponent, int expectedSignificand)
        {
            BigFloat.FromRational(numerator, denominator, SingleSignificand, SingleExponent, out var actual);
            var (exponent, significand, _) = Internals(actual);

            Assert.AreEqual((BigInteger)expectedExponent, exponent,
                $"{numerator}/{denominator}: wrong exponent");
            Assert.AreEqual((BigInteger)expectedSignificand, significand,
                $"{numerator}/{denominator}: wrong significand (off by {significand - expectedSignificand})");
        }

        [Test]
        public void FromRationalIsCorrectlyRounded()
        {
            var wrong = new List<string>();

            // Both precisions, since the rate at which rounding goes wrong differs between them, and both
            // signs, since the oracle carries the sign and FromRational derives it from both operands.
            foreach (var (significandSize, exponentSize) in new[] { (SingleSignificand, SingleExponent), (53, 11) })
            {
                foreach (var sign in new[] { 1, -1 })
                {
                    for (var a = 1; a <= 200; a++)
                    {
                        for (var b = 1; b <= 200; b++)
                        {
                            var exact = ExactRoundToNearestEven(sign * a, b, significandSize, exponentSize);
                            if (exact == null)
                            {
                                continue;
                            }

                            BigFloat.FromRational(sign * a, b, significandSize, exponentSize, out var actual);

                            if (Internals(actual) != exact)
                            {
                                wrong.Add($"({significandSize},{exponentSize}) {sign * a}/{b}: got "
                                          + $"{Describe(actual)}, want (exp {exact.Value.exponent}, "
                                          + $"sig {exact.Value.significand})");
                            }
                        }
                    }
                }
            }

            Assert.IsEmpty(wrong, $"{wrong.Count} rationals mis-rounded, e.g. {string.Join("; ", wrong.GetRange(0, Math.Min(5, wrong.Count)))}");
        }

        /// <summary>
        /// Exactly representable results, where no rounding is required, so a failure here is worse than a
        /// last-bit disagreement.
        /// </summary>
        [Test]
        public void ExactResultsNeedNoRounding()
        {
            var cases = new (float Left, float Right, char Op)[]
            {
                (1f, 1f, '+'), (2f, 3f, '*'), (1f, 2f, '/'), (0.5f, 0.25f, '+'),
                (1000000f, 1f, '+'), (6f, 2f, '/'), (0.75f, 0.25f, '-'), (16777216f, 1f, '+')
            };

            foreach (var (left, right, op) in cases)
            {
                AssertMatchesHardware(op, left, right);
            }
        }

        /// <summary>
        /// Special values, signed zeros and the range boundaries, pinned so that rewriting the rounding
        /// paths cannot disturb them.
        /// </summary>
        [Test]
        public void BoundariesAndSignedZerosMatchHardware()
        {
            const float smallestSubnormal = float.Epsilon;
            const float smallestNormal = 1.17549435e-38f;
            var max = float.MaxValue;

            var cases = new (string Name, float Left, float Right, char Op)[]
            {
                ("max + max", max, max, '+'),
                ("-max - max", -max, max, '-'),
                ("max * 2", max, 2f, '*'),
                ("max / 0.5", max, 0.5f, '/'),
                ("smallestSubnormal / 2", smallestSubnormal, 2f, '/'),
                ("smallestNormal / 2", smallestNormal, 2f, '/'),
                ("smallestNormal - smallestSubnormal", smallestNormal, smallestSubnormal, '-'),
                ("smallestSubnormal + smallestSubnormal", smallestSubnormal, smallestSubnormal, '+'),
                ("+0 + -0", 0f, -0f, '+'),
                ("-0 + -0", -0f, -0f, '+'),
                ("+0 - -0", 0f, -0f, '-'),
                ("-0 - +0", -0f, 0f, '-'),
                ("subnormal - subnormal", smallestSubnormal, smallestSubnormal, '-'),
                ("-subnormal + subnormal", -smallestSubnormal, smallestSubnormal, '+'),
                // Equal magnitudes cancelling to a zero, whose sign IEEE 754 fixes at +0
                ("1 - 1", 1f, 1f, '-'),
                ("-1 + 1", -1f, 1f, '+'),
                ("-1 - -1", -1f, -1f, '-'),
                ("2 - 2", 2f, 2f, '-'),
                ("-2.5 + 2.5", -2.5f, 2.5f, '+')
            };

            foreach (var (name, left, right, op) in cases)
            {
                AssertMatchesHardware(op, left, right, name);
            }
        }

        /// <summary>
        /// At 2^24 the gap between representable values is 2, so 2^24+1 is exactly halfway and must round
        /// down to the even 2^24, while 2^24+3 must round up to 2^24+4.
        /// </summary>
        [Test]
        public void TiesRoundToEven()
        {
            const float twoTo24 = 16777216f;

            foreach (var addend in new[] { 1f, 2f, 3f, 5f })
            {
                AssertMatchesHardware('+', twoTo24, addend, $"2^24 + {addend}");
            }
        }

        private static IEnumerable<TestCaseData> Operators()
        {
            yield return new TestCaseData('+').SetArgDisplayNames("Addition");
            yield return new TestCaseData('-').SetArgDisplayNames("Subtraction");
            yield return new TestCaseData('*').SetArgDisplayNames("Multiplication");
            yield return new TestCaseData('/').SetArgDisplayNames("Division");
        }

        /// <summary>
        /// Random bit patterns through every operator, including subnormals, against hardware. The seed is
        /// fixed so a failure is reproducible.
        /// </summary>
        [TestCaseSource(nameof(Operators))]
        public void OperatorMatchesHardwareOverRandomInputs(char op)
        {
            var random = new Random(31415);
            var wrong = new List<string>();
            var tested = 0;

            for (var i = 0; i < 200000 && wrong.Count < 10; i++)
            {
                var left = BitConverter.Int32BitsToSingle(random.Next(int.MinValue, int.MaxValue));
                var right = BitConverter.Int32BitsToSingle(random.Next(int.MinValue, int.MaxValue));

                if (float.IsNaN(left) || float.IsNaN(right) || float.IsInfinity(left) || float.IsInfinity(right))
                {
                    continue;
                }

                if (op == '/' && right == 0)
                {
                    continue;
                }

                tested++;
                var mismatch = Mismatch(op, left, right);
                if (mismatch != null)
                {
                    wrong.Add(mismatch);
                }
            }

            Assert.IsEmpty(wrong, $"of {tested} inputs: {string.Join("; ", wrong)}");
        }

        /// <summary>
        /// The same sweep at double precision, where the error rates differ enough that single precision
        /// alone would not settle the question.
        /// </summary>
        [TestCaseSource(nameof(Operators))]
        public void OperatorMatchesHardwareAtDoublePrecision(char op)
        {
            var random = new Random(9001);
            var buffer = new byte[8];
            var wrong = new List<string>();
            var tested = 0;

            for (var i = 0; i < 100000 && wrong.Count < 10; i++)
            {
                random.NextBytes(buffer);
                var left = BitConverter.ToDouble(buffer, 0);
                random.NextBytes(buffer);
                var right = BitConverter.ToDouble(buffer, 0);

                if (double.IsNaN(left) || double.IsNaN(right) || double.IsInfinity(left) || double.IsInfinity(right))
                {
                    continue;
                }

                if (op == '/' && right == 0)
                {
                    continue;
                }

                tested++;
                var mismatch = Mismatch(op, left, right);
                if (mismatch != null)
                {
                    wrong.Add(mismatch);
                }
            }

            Assert.IsEmpty(wrong, $"of {tested} inputs: {string.Join("; ", wrong)}");
        }

        /// <summary>
        /// FromBigDec inherits FromRational's rounding. A sweep is needed because the familiar decimals
        /// (0.1, 0.3, 3.14159) all happen to round correctly.
        /// </summary>
        [Test]
        public void FromBigDecIsCorrectlyRounded()
        {
            var random = new Random(8080);
            var wrong = new List<string>();
            var tested = 0;

            for (var i = 0; i < 20000 && wrong.Count < 10; i++)
            {
                var text = $"{(random.Next(2) == 0 ? "-" : "")}{random.Next(1, 1000000)}e{random.Next(-12, 13)}";
                BigDec value;

                try
                {
                    value = BigDec.FromString(text);
                }
                catch (FormatException)
                {
                    continue;
                }

                BigInteger numerator, denominator;
                if (value.Exponent >= 0)
                {
                    numerator = value.Mantissa * BigInteger.Pow(10, value.Exponent);
                    denominator = BigInteger.One;
                }
                else
                {
                    numerator = value.Mantissa;
                    denominator = BigInteger.Pow(10, -value.Exponent);
                }

                if (numerator.IsZero)
                {
                    continue;
                }

                var exact = ExactRoundToNearestEven(numerator, denominator, SingleSignificand, SingleExponent);
                if (exact == null)
                {
                    continue;
                }

                tested++;
                BigFloat.FromBigDec(value, SingleSignificand, SingleExponent, out var actual);

                if (Internals(actual) != exact)
                {
                    wrong.Add($"{text}: got {Describe(actual)}, want (exp {exact.Value.exponent}, "
                              + $"sig {exact.Value.significand})");
                }
            }

            Assert.IsEmpty(wrong, $"of {tested} decimals: {string.Join("; ", wrong)}");
        }

        /// <summary>
        /// Alternating multiply and divide, so that per-operation errors accumulate the way they would in
        /// a consumer that chains arithmetic.
        /// </summary>
        [Test]
        public void ChainedOperationsDoNotDrift()
        {
            var random = new Random(1234);
            var drifted = new List<string>();
            var completed = 0;

            for (var trial = 0; trial < 500; trial++)
            {
                var expected = 1.0f + (float)random.NextDouble() * 10f;
                var actual = FromSingle(expected);
                var bailed = false;

                for (var step = 0; step < 50; step++)
                {
                    var factor = 1.0f + (float)random.NextDouble();
                    var factorFloat = FromSingle(factor);

                    if (step % 2 == 0)
                    {
                        expected *= factor;
                        actual *= factorFloat;
                    }
                    else
                    {
                        expected /= factor;
                        actual /= factorFloat;
                    }

                    if (float.IsNaN(expected) || float.IsInfinity(expected) || expected == 0)
                    {
                        bailed = true;
                        break;
                    }
                }

                if (bailed)
                {
                    continue;
                }

                completed++;
                if (DescribeSingle(expected) != Describe(actual))
                {
                    drifted.Add($"trial {trial}: got {Describe(actual)}, want {DescribeSingle(expected)}");
                }
            }

            Assert.IsEmpty(drifted, $"of {completed} chains: {string.Join("; ", drifted)}");
            Assert.Greater(completed, 400, "almost every chain should run to the end without leaving the range");
        }

        /// <summary>
        /// FromRational over values whose rounding carries the significand from all-ones into the next
        /// binade. Random sampling rarely hits these, so they are constructed rather than sampled.
        /// </summary>
        [Test]
        public void FromRationalIsCorrectlyRoundedAtDoublePrecision()
        {
            var wrong = new List<string>();

            // Values just below each power of two, where the significand is all ones before rounding.
            for (var power = -60; power <= 60 && wrong.Count < 10; power++)
            {
                BigInteger numerator, denominator;
                if (power >= 0)
                {
                    numerator = BigInteger.Pow(2, power);
                    denominator = BigInteger.One;
                }
                else
                {
                    numerator = BigInteger.One;
                    denominator = BigInteger.Pow(2, -power);
                }

                // Approach the power from below, so the retained bits fill with ones and the discarded
                // tail decides whether they carry.
                foreach (var nudge in new[] { 1, 3, 7, 1023, 1048575 })
                {
                    var scaledNumerator = numerator * ((BigInteger.One << 54) - nudge);
                    var scaledDenominator = denominator << 54;

                    var exact = ExactRoundToNearestEven(scaledNumerator, scaledDenominator, 53, 11);
                    if (exact == null)
                    {
                        continue;
                    }

                    BigFloat.FromRational(scaledNumerator, scaledDenominator, 53, 11, out var actual);

                    if (Internals(actual) != exact)
                    {
                        wrong.Add($"2^{power} * (2^54-{nudge})/2^54: got {Describe(actual)}, want (exp "
                                  + $"{exact.Value.exponent}, sig {exact.Value.significand})");
                    }
                }
            }

            Assert.IsEmpty(wrong, string.Join("; ", wrong));
        }

        /// <summary>
        /// Subnormals in one format share a single exponent, so arithmetic on them is exact integer
        /// arithmetic on the significand, and the bias never enters -- every size must give the same answer.
        /// The expectations are therefore closed forms, which they have to be: at a 40-bit exponent the
        /// smallest normal is 2^-549755813886, so the oracle cannot reach these formats.
        /// </summary>
        [Test]
        public void SubnormalArithmeticIsBiasIndependent()
        {
            const int leftSignificand = 12345;
            const int rightSignificand = 6789;
            var largestSubnormal = (BigInteger.One << (SingleSignificand - 1)) - 1;

            foreach (var exponentSize in new[] { 8, 16, 20, 33, 40, 64, 100 })
            {
                var left = new BigFloat(false, leftSignificand, 0, SingleSignificand, exponentSize);
                var right = new BigFloat(false, rightSignificand, 0, SingleSignificand, exponentSize);
                var two = new BigFloat(false, 0, BigFloat.GetBias(exponentSize) + 1, SingleSignificand, exponentSize);
                var label = $"exponentSize {exponentSize}";

                AssertSubnormal(left + right, leftSignificand + rightSignificand, $"{label}: sum");
                AssertSubnormal(left - right, leftSignificand - rightSignificand, $"{label}: difference");
                AssertSubnormal(left * two, 2 * leftSignificand, $"{label}: doubled");

                // Signs come through the same way, since only the significand is at stake.
                var negatedLeft = new BigFloat(true, leftSignificand, 0, SingleSignificand, exponentSize);
                Assert.AreEqual((BigInteger.Zero, (BigInteger)(leftSignificand - rightSignificand), true),
                    Internals(negatedLeft + right), $"{label}: negative sum");

                // The product falls below the grid entirely, however wide the exponent.
                Assert.IsTrue((left * right).IsZero, $"{label}: subnormal product should underflow to zero");

                // These two significands divide to a ratio in [1,2), so the quotient lands at the format's
                // own bias, with a significand that does not depend on the exponent size either.
                Assert.AreEqual((BigFloat.GetBias(exponentSize), (BigInteger)6865091, false),
                    Internals(left / right), $"{label}: quotient");

                // Halving lands between grid points, where a tie goes to the even neighbour.
                foreach (var (significand, halved) in new[] { (1, 0), (3, 2), (5, 2), (7, 4) })
                {
                    var subnormal = new BigFloat(false, significand, 0, SingleSignificand, exponentSize);
                    AssertSubnormal(subnormal / two, halved, $"{label}: {significand}/2 ties to even");
                }

                // Carrying out of the grid gives the smallest normal, at exponent 1 with no stored bits.
                var carried = new BigFloat(false, largestSubnormal, 0, SingleSignificand, exponentSize)
                    + new BigFloat(false, 1, 0, SingleSignificand, exponentSize);
                Assert.AreEqual((BigInteger.One, BigInteger.Zero, false), Internals(carried),
                    $"{label}: largest subnormal + 1 should be the smallest normal");

                // Rounding a rational into a wide format must not attempt the oversized shift either. A
                // wider exponent only relocates the range, so the significand is the one HandCheckedRationals
                // derives for 1/3 at (24,8), whatever the exponent size.
                Assert.IsFalse(BigFloat.FromRational(1, 3, SingleSignificand, exponentSize, out var third), label);
                Assert.AreEqual((BigFloat.GetBias(exponentSize) - 2, (BigInteger)2796203, false), Internals(third),
                    $"{label}: 1/3");
            }
        }

        /// <summary>
        /// A wider exponent field moves the range without changing how values inside it round, so the same
        /// operands shifted by the difference in bias must give the same significand at any exponent size.
        /// </summary>
        [Test]
        public void WideExponentSizesRoundLikeSinglePrecision()
        {
            var random = new Random(777);
            var mismatches = new List<string>();

            foreach (var exponentSize in new[] { 9, 12, 16, 20, 33, 40, 64 })
            {
                var biasDifference = ((BigInteger.One << (exponentSize - 1)) - 1) - 127;

                for (var i = 0; i < 2000 && mismatches.Count < 5; i++)
                {
                    var leftBits = random.Next(int.MinValue, int.MaxValue);
                    var rightBits = random.Next(int.MinValue, int.MaxValue);
                    var leftExponent = (leftBits >> 23) & 0xFF;
                    var rightExponent = (rightBits >> 23) & 0xFF;

                    // Keep both operands normal, so shifting the exponent is an exact relabelling.
                    if (leftExponent == 0 || leftExponent == 0xFF || rightExponent == 0 || rightExponent == 0xFF)
                    {
                        continue;
                    }

                    var leftNegative = (leftBits >> 31) != 0;
                    var rightNegative = (rightBits >> 31) != 0;
                    var leftSignificand = leftBits & 0x7FFFFF;
                    var rightSignificand = rightBits & 0x7FFFFF;

                    var narrowLeft = new BigFloat(leftNegative, leftSignificand, leftExponent, SingleSignificand, SingleExponent);
                    var narrowRight = new BigFloat(rightNegative, rightSignificand, rightExponent, SingleSignificand, SingleExponent);
                    var wideLeft = new BigFloat(leftNegative, leftSignificand, leftExponent + biasDifference, SingleSignificand, exponentSize);
                    var wideRight = new BigFloat(rightNegative, rightSignificand, rightExponent + biasDifference, SingleSignificand, exponentSize);

                    foreach (var op in new[] { '+', '-', '*', '/' })
                    {
                        var narrow = Apply(op, narrowLeft, narrowRight);
                        var wide = Apply(op, wideLeft, wideRight);

                        // Only comparable where both are normal: at the edges the narrow format
                        // underflows or overflows while the wide one still has room.
                        if (!narrow.IsNormal || !wide.IsNormal)
                        {
                            continue;
                        }

                        var (narrowExponent, narrowFraction, narrowSign) = Internals(narrow);
                        var (wideExponent, wideFraction, wideSign) = Internals(wide);

                        if (narrowFraction != wideFraction || wideExponent - narrowExponent != biasDifference
                            || narrowSign != wideSign)
                        {
                            mismatches.Add($"exponentSize {exponentSize}, {op}: (24,8) gave "
                                + $"(exp {narrowExponent}, sig {narrowFraction}), wide gave "
                                + $"(exp {wideExponent}, sig {wideFraction})");
                        }
                    }
                }
            }

            Assert.IsEmpty(mismatches, string.Join("; ", mismatches));
        }

        /// <summary>
        /// Printing and parsing must be inverse: <see cref="BigFloat.ToString"/> emits an exact literal, so
        /// parsing it back has nothing to round and must reproduce the value in both modes. Needing no
        /// oracle, this reaches the wide formats.
        /// </summary>
        [Test]
        public void PrintingAndParsingAreInverse()
        {
            var random = new Random(1618);
            var mismatches = new List<string>();

            foreach (var exponentSize in new[] { SingleExponent, 11, 16, 40, 100 })
            {
                var maxExponent = (BigInteger.One << exponentSize) - 1;

                // ToString splits the binary exponent into hex digits and handles a negative remainder on
                // its own, so at (24,8) every exponent is covered rather than a sample of them. Wider
                // formats take subnormals, the smallest normals, the middle and the top of the range.
                var exponents = new List<BigInteger>();
                if (exponentSize == SingleExponent)
                {
                    for (var exponent = BigInteger.Zero; exponent < maxExponent; exponent++)
                    {
                        exponents.Add(exponent);
                    }
                }
                else
                {
                    exponents.AddRange(new[]
                    {
                        BigInteger.Zero, BigInteger.One, BigInteger.One << 1,
                        BigFloat.GetBias(exponentSize), maxExponent - 1
                    });
                }

                foreach (var exponent in exponents)
                {
                    for (var i = 0; i < (exponents.Count > 8 ? 6 : 40) && mismatches.Count < 10; i++)
                    {
                        var significand = i switch
                        {
                            0 => BigInteger.Zero,
                            1 => (BigInteger.One << (SingleSignificand - 1)) - 1,
                            _ => new BigInteger(random.Next(1 << (SingleSignificand - 1)))
                        };

                        var value = new BigFloat(i % 2 == 0, significand, exponent, SingleSignificand, exponentSize);
                        var text = value.ToString();

                        if (!BigFloat.TryParse(text, out var loose) || Internals(loose) != Internals(value))
                        {
                            mismatches.Add($"{text} parsed back as {Describe(loose)}, want {Describe(value)}");
                        }

                        // An exact literal is precisely what strict mode exists to accept.
                        if (!BigFloat.TryParseExact(text, out var strict) || Internals(strict) != Internals(value))
                        {
                            mismatches.Add($"{text} rejected or altered by strict parsing: {Describe(strict)}");
                        }
                    }
                }

                // The infinities round-trip with their sign. A NaN does not: it prints as 0NaN<s>e<e> with
                // no sign, so parsing any NaN back gives the positive one.
                foreach (var infinity in new[] { false, true })
                {
                    var value = BigFloat.CreateInfinity(infinity, SingleSignificand, exponentSize);
                    Assert.IsTrue(BigFloat.TryParse(value.ToString(), out var back), value.ToString());
                    Assert.AreEqual(Internals(value), Internals(back), $"{value} should round-trip");
                }

                var positiveNaN = BigFloat.CreateNaN(false, SingleSignificand, exponentSize);
                foreach (var negative in new[] { false, true })
                {
                    var nan = BigFloat.CreateNaN(negative, SingleSignificand, exponentSize);
                    Assert.IsTrue(BigFloat.TryParse(nan.ToString(), out var back), nan.ToString());
                    Assert.AreEqual(Internals(positiveNaN), Internals(back),
                        $"{nan} should round-trip to the positive NaN, since its sign is not printed");
                }
            }

            Assert.IsEmpty(mismatches, string.Join("; ", mismatches));
        }

        /// <summary>
        /// A 24-bit significand occupies exactly six hex digits, so one further digit weighs that many
        /// sixteenths of an ULP: below eight rounds down, above eight rounds up, and eight is an exact tie
        /// that must go to the even neighbour. Every rounding decision in the parser is therefore a closed
        /// form, with no oracle in the way -- and since only the significand's width matters, the same
        /// construction checks the wide exponent sizes that no oracle can reach.
        /// </summary>
        [Test]
        public void ParsedLiteralRoundsItsTailCorrectly()
        {
            const string hexDigits = "0123456789ABCDEF";
            var random = new Random(2718);
            var wrong = new List<string>();
            var exercised = new List<string>();

            foreach (var exponentSize in new[] { SingleExponent, 11, 16, 40 })
            {
                for (var i = 0; i < 6000 && wrong.Count < 10; i++)
                {
                    // The leading bit is set, so the value formats as exactly six hex digits.
                    var significand = i switch
                    {
                        0 => 1 << (SingleSignificand - 1),           // 0x800000, even
                        1 => (1 << (SingleSignificand - 1)) + 1,     // 0x800001, odd
                        2 => (1 << SingleSignificand) - 1,           // 0xFFFFFF, the case that carries
                        _ => (1 << (SingleSignificand - 1)) + random.Next(1 << (SingleSignificand - 1))
                    };
                    var tail = i < 3 ? 8 : random.Next(16);
                    // Kept well inside the narrowest format's normal range, so no case here over- or
                    // underflows; the boundaries have their own tests.
                    var hexExponent = i < 3 ? 0 : random.Next(-25, 26);
                    var negative = random.Next(2) == 0;

                    var digits = significand.ToString("X6");
                    var literal = $"{(negative ? "-" : "")}0x{digits[0]}.{digits[1..]}{hexDigits[tail]}"
                                  + $"e{hexExponent}f{SingleSignificand}e{exponentSize}";

                    // Ties to even, so an exact half only moves an odd significand.
                    var roundsUp = tail > 8 || (tail == 8 && (significand & 1) != 0);
                    var rounded = roundsUp ? significand + 1 : significand;

                    // Bit 0 of the seven printed digits weighs 2^(4*hexExponent - 24), so the retained
                    // significand weighs four bits more; a carry moves its leading bit up by one.
                    var carried = rounded == 1 << SingleSignificand;
                    var leadingBit = carried ? SingleSignificand : SingleSignificand - 1;
                    var expected = (
                        exponent: 4 * hexExponent - 20 + leadingBit + BigFloat.GetBias(exponentSize),
                        significand: carried ? BigInteger.Zero : rounded - (1 << (SingleSignificand - 1)),
                        signBit: negative);

                    var rounding = carried ? "carry"
                        : tail < 8 ? "down"
                        : tail > 8 ? "up"
                        : roundsUp ? "tie to even, upward" : "tie to even, downward";
                    if (!exercised.Contains(rounding))
                    {
                        exercised.Add(rounding);
                    }

                    if (!BigFloat.TryParse(literal, out var actual) || Internals(actual) != expected)
                    {
                        wrong.Add($"{literal}: got {Describe(actual)}, want (exp {expected.exponent}, "
                                  + $"sig {expected.significand})");
                    }
                }
            }

            Assert.IsEmpty(wrong, string.Join("; ", wrong));

            // A sampled sweep is worth only the cases it happens to draw, so say which ones it needed.
            foreach (var rounding in new[]
                     { "down", "up", "tie to even, upward", "tie to even, downward", "carry" })
            {
                Assert.IsTrue(exercised.Contains(rounding), $"the sweep never exercised: {rounding}");
            }

            // Past the top of the range the same construction must give infinity rather than wrapping.
            Assert.IsTrue(BigFloat.TryParse("0x8.000000e31f24e8", out var largest));
            Assert.IsFalse(largest.IsInfinity, "0x8.000000e31f24e8 is still finite at (24,8)");
            Assert.IsTrue(BigFloat.TryParse("0x8.000000e32f24e8", out var overflowed));
            Assert.IsTrue(overflowed.IsInfinity, "0x8.000000e32f24e8 overflows at (24,8)");
        }

        /// <summary>
        /// Literals below the subnormal grid round to nearest rather than flushing to zero. The smallest
        /// subnormal at (24,8) is 2^-149, which 0x8.0e-38f24e8 names exactly, so each literal below is the
        /// stated fraction of it: above half rounds up to it, half itself is a tie that goes to the even
        /// zero, and below half rounds down. Deciding "below the grid" from the exponent before rounding
        /// would flush the whole band to zero instead.
        /// </summary>
        [Test]
        public void LiteralsBelowTheSubnormalGridRoundToNearest()
        {
            foreach (var (literal, fraction, expected, strictAccepts) in new[]
                     {
                         ("0x2.0e-38f24e8", "a quarter", 0, false),
                         ("0x4.0e-38f24e8", "half, an exact tie", 0, false),
                         ("0x5.0e-38f24e8", "five eighths", 1, true),
                         ("0x6.0e-38f24e8", "three quarters", 1, true),
                         ("0x7.FFFFFFe-38f24e8", "a hair under one", 1, true),
                         ("0x8.0e-38f24e8", "exactly one", 1, true),
                         ("0xC.0e-38f24e8", "one and a half, an exact tie", 2, true)
                     })
            {
                foreach (var sign in new[] { "", "-" })
                {
                    // Underflow keeps the sign, so a literal that flushes to zero gives a signed zero.
                    Assert.IsTrue(BigFloat.TryParse(sign + literal, out var value), sign + literal);
                    AssertSubnormal(value, expected, $"{sign}{literal} is {sign}{fraction} of 2^-149");
                    Assert.AreEqual(sign == "-", Internals(value).signBit, $"{sign}{literal}: sign");

                    // Strict mode rejects exactly those that lose everything, which is a consequence of the
                    // rounding rather than a rule of its own: it accepts inexact subnormals either way.
                    Assert.AreEqual(strictAccepts, BigFloat.TryParseExact(sign + literal, out _),
                        $"{sign}{literal}: strict mode");
                }
            }
        }

        /// <summary>
        /// The mirror of the case above, at the top of the subnormal range rather than the bottom. The
        /// largest subnormal is (2^23-1)*2^-149 and the smallest normal is 2^-126, so (2^24-1)*2^-150 sits
        /// exactly halfway between them and must tie to the even neighbour, which is the normal one. Strict
        /// mode draws its line here too, rejecting a literal that rounds up out of the subnormal range.
        /// </summary>
        [Test]
        public void LiteralsAtTheTopOfTheSubnormalRangeCarryIntoNormal()
        {
            var largestSubnormal = (BigInteger.One << (SingleSignificand - 1)) - 1;

            foreach (var (literal, what, exponent, significand, strictAccepts) in new[]
                     {
                         ("0x3.FFFFF8e-32f24e8", "the largest subnormal exactly",
                             0, largestSubnormal, true),
                         ("0x3.FFFFFCe-32f24e8", "halfway to the smallest normal, so it ties to it",
                             1, BigInteger.Zero, false),
                         ("0x3.FFFFFEe-32f24e8", "past halfway, so it rounds up to the smallest normal",
                             1, BigInteger.Zero, false)
                     })
            {
                Assert.IsTrue(BigFloat.TryParse(literal, out var value), literal);
                Assert.AreEqual(((BigInteger)exponent, significand, false), Internals(value),
                    $"{literal} is {what}");
                Assert.AreEqual(strictAccepts, BigFloat.TryParseExact(literal, out _),
                    $"{literal}: strict mode");
            }
        }

        private static BigFloat Apply(char op, BigFloat left, BigFloat right)
        {
            return op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
        }
    }
}
