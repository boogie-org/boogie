using System;
using System.Collections.Generic;
using System.Numerics;
using System.Reflection;
using NUnit.Framework;
using Microsoft.BaseTypes;

namespace BaseTypesTests
{
    /// <summary>
    /// Compares BigFloat against an oracle that shares no code with it.
    ///
    /// This matters because BigFloat cannot check itself: FromRational, FromBigDec, FromString and all
    /// four arithmetic operators route through the same rounding helpers, so a systematic error in those
    /// helpers makes every one of them agree while all are wrong. Tests written against FromRational
    /// expectations therefore cannot detect it, which is why BigFloatTests passes at full strength while
    /// division disagrees with IEEE 754 on roughly one input in five.
    ///
    /// Two oracles are used, and cross-checked against each other before either is trusted:
    ///
    ///   1. ExactRoundToNearestEven - the correctly rounded value of a rational, computed entirely in
    ///      BigInteger with exactly one rounding step. Independent of BigFloat and valid at any precision.
    ///   2. Hardware - float is bit-for-bit BigFloat(24,8) and double is bit-for-bit BigFloat(53,11).
    ///      Arithmetic must be done *in the target precision*: computing a float result via double
    ///      ((float)((double)a / b)) rounds twice and reproduces the very defect under test.
    /// </summary>
    [TestFixture]
    public class BigFloatDifferentialTests
    {
        private const int SingleSignificand = 24;
        private const int SingleExponent = 8;

        /// <summary>
        /// Correctly rounded round-to-nearest-even value of numerator/denominator in the given format,
        /// as (biasedExponent, trailingSignificand). Pure BigInteger, one rounding step, no floating
        /// point anywhere. Returns null when the value overflows to infinity.
        /// </summary>
        private static (BigInteger exponent, BigInteger significand)? ExactRoundToNearestEven(
            BigInteger numerator, BigInteger denominator, int significandSize, int exponentSize)
        {
            if (numerator.IsZero)
            {
                return (BigInteger.Zero, BigInteger.Zero);
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
            if (scale + significandSize - 1 < 1 - bias)
            {
                while (scale < minScale)
                {
                    denominator <<= 1;
                    scale++;
                }

                while (scale > minScale)
                {
                    numerator <<= 1;
                    scale--;
                }
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
                return (BigInteger.Zero, quotient); // subnormal
            }

            var biasedExponent = scale + significandSize - 1 + bias;
            return biasedExponent >= maxExponent
                ? null
                : (biasedExponent, quotient - (BigInteger.One << (significandSize - 1)));
        }

        private static (BigInteger exponent, BigInteger significand, bool signBit) Internals(BigFloat value)
        {
            Type type = typeof(BigFloat);
            return ((BigInteger)type.GetField("exponent", BindingFlags.NonPublic | BindingFlags.Instance).GetValue(value),
                    (BigInteger)type.GetField("significand", BindingFlags.NonPublic | BindingFlags.Instance).GetValue(value),
                    (bool)type.GetField("signBit", BindingFlags.NonPublic | BindingFlags.Instance).GetValue(value));
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
        /// Renders a value so that expected and actual are comparable and readable in failure output,
        /// collapsing the special values that have no (exponent, significand) meaning.
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

        /// <summary>
        /// Neither oracle is trusted until they agree with each other. If this fails, every other
        /// result in this fixture is meaningless, so it is the first thing to check.
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
                    var (exponent, significand, _) = Internals(FromSingle(hardware));

                    if (exact == null || exact.Value.exponent != exponent || exact.Value.significand != significand)
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
        /// Rationals whose correctly rounded value is hand-checkable, so a reader can confirm the
        /// expectations without running or trusting either oracle. For 1/15 at (24,8):
        /// 2^27/15 = 8947848 remainder 8; 2*8 > 15, so round up to 8947849; less the implicit
        /// 2^23 that leaves a trailing significand of 559241.
        /// </summary>
        private static IEnumerable<TestCaseData> HandCheckedRationals()
        {
            yield return new TestCaseData(1, 15, 123, 559241).SetName("OneFifteenth");
            yield return new TestCaseData(1, 3, 125, 2796203).SetName("OneThird");
            yield return new TestCaseData(2, 3, 126, 2796203).SetName("TwoThirds");
            yield return new TestCaseData(1, 10, 123, 5033165).SetName("OneTenth");
            yield return new TestCaseData(1, 2, 126, 0).SetName("Half");
            yield return new TestCaseData(3, 1, 128, 4194304).SetName("Three");
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

        /// <summary>
        /// The smallest hand-checkable case BigFloat currently gets wrong, kept separate so the exact
        /// arithmetic sits next to the expectation: 2^27/15 = 8947848 remainder 8, and 2*8 > 15, so the
        /// correctly rounded significand is 8947849 - 2^23 = 559241.
        /// </summary>
        [Test]
        public void FromRationalRoundsOneFifteenthCorrectly()
        {
            BigFloat.FromRational(1, 15, SingleSignificand, SingleExponent, out var actual);
            var (exponent, significand, _) = Internals(actual);

            Assert.AreEqual((BigInteger)123, exponent);
            Assert.AreEqual((BigInteger)559241, significand, $"off by {significand - 559241}");
        }

        [Test]
        public void FromRationalIsCorrectlyRounded()
        {
            var wrong = new List<string>();

            for (var a = 1; a <= 200; a++)
            {
                for (var b = 1; b <= 200; b++)
                {
                    var exact = ExactRoundToNearestEven(a, b, SingleSignificand, SingleExponent);
                    if (exact == null)
                    {
                        continue;
                    }

                    BigFloat.FromRational(a, b, SingleSignificand, SingleExponent, out var actual);
                    var (exponent, significand, _) = Internals(actual);

                    if (exponent != exact.Value.exponent || significand != exact.Value.significand)
                    {
                        wrong.Add($"{a}/{b}: got (exp {exponent}, sig {significand}), "
                                  + $"want (exp {exact.Value.exponent}, sig {exact.Value.significand})");
                    }
                }
            }

            Assert.IsEmpty(wrong, $"{wrong.Count} rationals mis-rounded, e.g. {string.Join("; ", wrong.GetRange(0, Math.Min(5, wrong.Count)))}");
        }

        /// <summary>
        /// Exactly representable results, where no rounding is required and every operator should already
        /// agree. Kept separate from the rounding tests so that a failure here means something much worse
        /// than a last-bit disagreement.
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
                var expected = op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
                var actual = op switch
                {
                    '+' => FromSingle(left) + FromSingle(right),
                    '-' => FromSingle(left) - FromSingle(right),
                    '*' => FromSingle(left) * FromSingle(right),
                    _ => FromSingle(left) / FromSingle(right)
                };

                Assert.AreEqual(DescribeSingle(expected), Describe(actual), $"{left} {op} {right}");
            }
        }

        /// <summary>
        /// Special values, signed zeros and the range boundaries. These are structural rather than
        /// rounding properties, and BigFloat gets all of them right - the point of pinning them is to
        /// keep it that way while the rounding paths are rewritten.
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
                // Cancellation of equal magnitudes: IEEE 754 gives -0 only when both operands are
                // negative, so these pin the sign that a naive "either operand negative" test gets wrong.
                ("1 - 1", 1f, 1f, '-'),
                ("-1 + 1", -1f, 1f, '+'),
                ("-1 - -1", -1f, -1f, '-'),
                ("-1 + -1 magnitudes cancel", -1f, 1f, '+'),
                ("2 - 2", 2f, 2f, '-'),
                ("-2.5 + 2.5", -2.5f, 2.5f, '+')
            };

            foreach (var (name, left, right, op) in cases)
            {
                var expected = op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
                var actual = op switch
                {
                    '+' => FromSingle(left) + FromSingle(right),
                    '-' => FromSingle(left) - FromSingle(right),
                    '*' => FromSingle(left) * FromSingle(right),
                    _ => FromSingle(left) / FromSingle(right)
                };

                Assert.AreEqual(DescribeSingle(expected), Describe(actual), name);
            }
        }

        /// <summary>
        /// Ties, where rounding to nearest-even is the only correct answer and off-by-one-ULP shows up
        /// immediately. At 2^24 the gap between representable values is 2, so 2^24+1 is exactly halfway
        /// and must round down to the even 2^24, while 2^24+3 must round up to 2^24+4.
        /// </summary>
        [Test]
        public void TiesRoundToEven()
        {
            const float twoTo24 = 16777216f;

            foreach (var addend in new[] { 1f, 2f, 3f, 5f })
            {
                var actual = FromSingle(twoTo24) + FromSingle(addend);
                Assert.AreEqual(DescribeSingle(twoTo24 + addend), Describe(actual), $"2^24 + {addend}");
            }
        }

        private static IEnumerable<TestCaseData> Operators()
        {
            yield return new TestCaseData('+').SetName("Addition");
            yield return new TestCaseData('-').SetName("Subtraction");
            yield return new TestCaseData('*').SetName("Multiplication");
            yield return new TestCaseData('/').SetName("Division");
        }

        /// <summary>
        /// The broad sweep: random bit patterns through every operator, compared against hardware. Uses a
        /// fixed seed so a failure is reproducible. Subnormal operands and results are included, since
        /// that is where two of the known defects live.
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
                var expected = op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
                var actual = op switch
                {
                    '+' => FromSingle(left) + FromSingle(right),
                    '-' => FromSingle(left) - FromSingle(right),
                    '*' => FromSingle(left) * FromSingle(right),
                    _ => FromSingle(left) / FromSingle(right)
                };

                if (DescribeSingle(expected) != Describe(actual))
                {
                    wrong.Add($"{left:R} {op} {right:R}: got {Describe(actual)}, want {DescribeSingle(expected)}");
                }
            }

            Assert.IsEmpty(wrong, $"of {tested} inputs: {string.Join("; ", wrong)}");
        }

        /// <summary>
        /// The same sweep at double precision. Rates differ by precision - addition is far worse at
        /// (24,8) than at (53,11) - so a fix verified only at single precision proves less than it looks.
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
                var expected = op switch { '+' => left + right, '-' => left - right, '*' => left * right, _ => left / right };
                var actual = op switch
                {
                    '+' => FromDouble(left) + FromDouble(right),
                    '-' => FromDouble(left) - FromDouble(right),
                    '*' => FromDouble(left) * FromDouble(right),
                    _ => FromDouble(left) / FromDouble(right)
                };

                var expectedText = double.IsInfinity(expected)
                    ? (expected < 0 ? "-inf" : "+inf")
                    : (double.IsNaN(expected) ? "NaN" : Describe(FromDouble(expected)));

                if (expectedText != Describe(actual))
                {
                    wrong.Add($"{left:R} {op} {right:R}: got {Describe(actual)}, want {expectedText}");
                }
            }

            Assert.IsEmpty(wrong, $"of {tested} inputs: {string.Join("; ", wrong)}");
        }

        /// <summary>
        /// Decimal literals are the most natural way to write a float value, and FromBigDec inherits
        /// FromRational's rounding. Note that a handful of familiar decimals (0.1, 0.3, 3.14159) all
        /// happen to round correctly, so only a sweep exposes this.
        /// </summary>
        [Test]
        public void FromBigDecIsCorrectlyRounded()
        {
            var random = new Random(8080);
            var wrong = new List<string>();
            var tested = 0;

            for (var i = 0; i < 20000 && wrong.Count < 10; i++)
            {
                var text = $"{random.Next(1, 1000000)}e{random.Next(-12, 13)}";
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
                var (exponent, significand, _) = Internals(actual);

                if (exponent != exact.Value.exponent || significand != exact.Value.significand)
                {
                    wrong.Add($"{text}: got (exp {exponent}, sig {significand}), "
                              + $"want (exp {exact.Value.exponent}, sig {exact.Value.significand})");
                }
            }

            Assert.IsEmpty(wrong, $"of {tested} decimals: {string.Join("; ", wrong)}");
        }

        /// <summary>
        /// Single-operation error understates the effect on a consumer that chains arithmetic, which is
        /// how the operators would be used if anything called them. Alternating multiply and divide lets
        /// the per-operation errors accumulate.
        /// </summary>
        [Test]
        public void ChainedOperationsDoNotDrift()
        {
            var random = new Random(1234);
            var worst = 0L;

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

                var (exponent, significand, signBit) = Internals(actual);
                var actualBits = ((signBit ? 1 : 0) << 31) | (((int)exponent & 0xFF) << 23) | ((int)significand & 0x7FFFFF);
                worst = Math.Max(worst, Math.Abs((long)BitConverter.SingleToInt32Bits(expected) - actualBits));
            }

            Assert.AreEqual(0L, worst, $"chained arithmetic drifted by up to {worst} ULP from hardware");
        }

    }
}
