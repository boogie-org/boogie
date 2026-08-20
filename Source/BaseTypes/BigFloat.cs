using System;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.BaseTypes
{
  /// <summary>
  /// A representation of a floating-point value using IEEE 754-2019 format.
  /// Note that this value has a 1-bit sign, along with an exponent and significand whose sizes must be greater than 1.
  /// Uses IEEE 754-2019 representation internally with configurable significand and exponent sizes.
  /// </summary>
  public readonly struct BigFloat
  {
    #region Fields and Properties

    // IEEE 754 representation fields
    private readonly BigInteger significand;    // Trailing significand field (without leading bit for normal numbers)
    private readonly BigInteger exponent;       // Biased exponent value
    private readonly bool signBit;              // Sign bit: true = negative, false = positive

    // Cached values for performance
    private readonly BigInteger bias;           // Exponent bias value
    private readonly BigInteger maxExponent;    // Maximum exponent value
    private readonly BigInteger leadingBit;      // Power value for the implicit leading significand bit

    // The precision: the trailing significand field's width plus the implicit leading bit, so 53 for an
    // IEEE 754 double. The stored field always uses SignificandSize - 1 bits.
    public int SignificandSize { get; }
    public int ExponentSize { get; }            // Total bits for exponent
    public bool IsZero => significand == 0 && exponent == 0;
    public bool IsNaN => exponent == maxExponent && significand != 0;
    public bool IsInfinity => exponent == maxExponent && significand == 0;
    public bool IsSubnormal => exponent == 0 && significand != 0;
    public bool IsNormal => exponent > 0 && exponent < maxExponent;
    public bool IsNegative => signBit;
    public bool IsPositive => !signBit;
    public bool IsFinite => !IsNaN && !IsInfinity;

    #endregion

    #region Constructors and Factory Methods

    /// <summary>Initializes a new instance of the <see cref="BigFloat"/> struct from its IEEE 754 fields.</summary>
    /// <param name="signBit">The sign bit: true for negative, false for positive</param>
    /// <param name="significand">The trailing significand field (without implicit leading significand bit for normal numbers)</param>
    /// <param name="exponent">The biased exponent value</param>
    public BigFloat(bool signBit, BigInteger significand, BigInteger exponent, int significandSize, int exponentSize)
      : this(signBit, significand, exponent, significandSize, exponentSize, false)
    {
    }

    /// <summary>
    /// Initializes a new instance of the <see cref="BigFloat"/> struct.
    /// Internal constructor with optional validation bypass
    /// </summary>
    private BigFloat(bool signBit, BigInteger significand, BigInteger exponent, int significandSize, int exponentSize, bool skipValidation)
    {
      if (!skipValidation)
      {
        ValidateSizeParameters(significandSize, exponentSize);
        if (significand < 0) {
          throw new ArgumentException("Significand must be non-negative (IEEE 754 significands are unsigned)", nameof(significand));
        }
        if (exponent < 0) {
          throw new ArgumentException("Exponent must be non-negative (biased representation)", nameof(exponent));
        }

        // IEEE 754: The trailing significand field width is significandSize - 1 bits
        // For normal numbers, the leading bit of the significand is implicitly encoded in the biased exponent
        if (significand.GetBitLength() > significandSize - 1) {
          throw new ArgumentException($"Trailing significand field requires {significand.GetBitLength()} bits but only {significandSize - 1} bits are available", nameof(significand));
        }

        if (exponent > GetMaxExponent(exponentSize)) {
          throw new ArgumentException($"Exponent {exponent} exceeds maximum value {GetMaxExponent(exponentSize)} for {exponentSize}-bit exponent size", nameof(exponent));
        }
      }

      this.signBit = signBit;
      this.significand = significand;
      this.exponent = exponent;
      SignificandSize = significandSize;
      ExponentSize = exponentSize;

      bias = GetBias(exponentSize);
      maxExponent = GetMaxExponent(exponentSize);
      leadingBit = GetLeadingBitPower(significandSize);
    }

    /// <summary>Tries to parse a string representation of a BigFloat with IEEE 754 compliant behavior</summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    [Pure]
    public static bool TryParse(string s, out BigFloat result)
    {
      return TryParseFloatString(s, strict: false, out result);
    }

    /// <summary>
    /// As <see cref="TryParse"/>, but rejects a literal the format cannot hold: one with a nonzero tail
    /// below the retained significand, one that overflows to infinity, and one that underflows to zero or
    /// rounds up out of the subnormal range. A literal that rounds onto a subnormal is accepted, so this
    /// is not quite exactness. Boogie's parser uses this mode.
    /// </summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    [Pure]
    public static bool TryParseExact(string s, out BigFloat result)
    {
      return TryParseFloatString(s, strict: true, out result);
    }

    /// <summary>Parses a string representation of a BigFloat with IEEE 754 compliant behavior</summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    [Pure]
    public static BigFloat FromString(string s)
    {
      if (TryParse(s, out var result))
      {
        return result;
      }
      throw new FormatException($"Unable to parse '{s}' as BigFloat");
    }

    /// <summary>As <see cref="TryParseExact"/>, but throws instead of returning false.</summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    [Pure]
    public static BigFloat FromStringStrict(string s)
    {
      if (TryParseExact(s, out var result)) {
        return result;
      }
      throw new FormatException($"Unable to parse '{s}' as BigFloat in strict mode");
    }

    /// <summary>Core parsing logic that handles both IEEE 754 compliant and Boogie strict parsing modes</summary>
    /// <param name="strict">When true, applies the restrictions described on <see cref="TryParseExact"/>;
    /// when false, rounds and underflows as IEEE 754 prescribes</param>
    private static bool TryParseFloatString(string s, bool strict, out BigFloat result)
    {
      result = default;

      if (string.IsNullOrEmpty(s)) {
        return false;
      }

      // Reject any leading or trailing whitespace
      if (s != s.Trim()) {
        return false;
      }

      // Parse size specifiers: f[sigSize]e[expSize]
      var posLastE = s.LastIndexOf('e');
      if (posLastE == -1) {
        return false;
      }

      var expSizeStr = s[(posLastE + 1)..];

      if (!int.TryParse(expSizeStr, out var exponentSize)) {
        return false;
      }

      // Extract significand size
      var posLastF = s.LastIndexOf('f');
      var sigSizeStart = posLastF == -1 ? 4 : posLastF + 1;  // Special values start at 4, normal after 'f'

      var sigSizeStr = s[sigSizeStart..posLastE];

      if (sigSizeStart >= posLastE ||
          !int.TryParse(sigSizeStr, out var significandSize) ||
          !(significandSize > 1 && exponentSize > 1)) {
        return false;
      }

      // Parse content: hex format or special value
      return posLastF != -1 ?
        TryParseHexFormat(s[..posLastF], significandSize, exponentSize, strict, out result) :
        TryCreateSpecialFromString(s[1..4], significandSize, exponentSize, out result);
    }

    /// <summary>Creates a BigFloat from an integer value (default: double precision)</summary>
    [Pure] public static BigFloat FromInt(int v) => ConvertIntegerToBigFloat(v, 53, 11);
    [Pure] public static BigFloat FromInt(int v, int significandSize, int exponentSize) => ConvertIntegerToBigFloat(v, significandSize, exponentSize);
    public static BigFloat FromBigInt(BigInteger v, int significandSize, int exponentSize) => ConvertIntegerToBigFloat(v, significandSize, exponentSize);

    /// <summary>
    /// Converts a rational number to a BigFloat.
    /// Returns false if the number cannot be accurately represented as a BigFloat.
    /// </summary>
    /// <returns>True if the conversion is exact, false otherwise</returns>
    [Pure]
    public static bool FromRational(
      BigInteger numerator,
      BigInteger denominator,
      int significandSize,
      int exponentSize,
      out BigFloat result)
    {
      ValidateSizeParameters(significandSize, exponentSize);

      // Handle sign and zero
      var isNegative = (numerator < 0) != (denominator < 0);
      if (numerator.IsZero) {
        result = CreateZero(isNegative, significandSize, exponentSize);
        return true;
      }

      // Work with absolute values
      numerator = BigInteger.Abs(numerator);
      denominator = BigInteger.Abs(denominator);

      // Pre-scale so the quotient carries three bits more than the format keeps: a guard bit, a sticky
      // bit and one of slack. No scaling is needed when the numerator already dwarfs the denominator,
      // since the quotient is then wide on its own.
      var scaleBitsLong = (long)significandSize + 3 + (denominator.GetBitLength() - numerator.GetBitLength());
      var scaleBits = scaleBitsLong < 0 ? BigInteger.Zero : new BigInteger(scaleBitsLong);
      var scaledNumerator = BigIntegerMath.LeftShift(numerator, scaleBits);
      var quotient = BigInteger.DivRem(scaledNumerator, denominator, out var remainder);

      // Bit 0 of the scaled quotient has weight 2^-scaleBits; RoundToFormat does the single rounding.
      result = RoundToFormat(WithStickyBit(quotient, remainder), -scaleBits, isNegative,
        significandSize, exponentSize);

      // Exactness is a property of the input, so check the result against it rather than observing the
      // rounding.
      return RepresentsExactly(result, numerator, denominator);
    }

    /// <summary>
    /// Converts a BigDec (decimal) value to a BigFloat.
    /// Returns false if the number cannot be accurately represented as a BigFloat.
    /// </summary>
    /// <returns>True if the conversion is exact, false otherwise</returns>
    [Pure]
    public static bool FromBigDec(
      BigDec value,
      int significandSize,
      int exponentSize,
      out BigFloat result)
    {
      BigInteger numerator, denominator;

      if (value.Exponent >= 0) {
        numerator = value.Mantissa * BigInteger.Pow(10, value.Exponent);
        denominator = BigInteger.One;
      } else {
        numerator = value.Mantissa;
        denominator = BigInteger.Pow(10, -value.Exponent);
      }

      return FromRational(numerator, denominator, significandSize, exponentSize, out result);
    }

    #endregion

    #region Validation and Parameter Checking

    /// <summary>Validates that significand and exponent sizes meet minimum requirements (must be > 1)</summary>
    private static void ValidateSizeParameters(int significandSize, int exponentSize)
    {
      if (significandSize <= 1) {
        throw new ArgumentException($"Significand size must be greater than 1, got {significandSize}", nameof(significandSize));
      }
      if (exponentSize <= 1) {
        throw new ArgumentException($"Exponent size must be greater than 1, got {exponentSize}", nameof(exponentSize));
      }
    }

    private static void ValidateSizeCompatibility(BigFloat x, BigFloat y)
    {
      if (x.ExponentSize != y.ExponentSize) {
        throw new ArgumentException($"Exponent sizes must match: {x.ExponentSize} != {y.ExponentSize}");
      }

      if (x.SignificandSize != y.SignificandSize) {
        throw new ArgumentException($"Significand sizes must match: {x.SignificandSize} != {y.SignificandSize}");
      }
    }

    /// <summary>
    /// Gets the mathematical exponent value (E for use in E - bias), handling subnormal numbers correctly
    /// For subnormal numbers, returns 1 as per IEEE 754 specification
    /// </summary>
    private BigInteger GetActualExponent() => exponent == 0 ? BigInteger.One : exponent;

    /// <summary>
    /// This value's magnitude as significand * 2^scale, with the implicit leading bit restored and the
    /// sign dropped. Zero, the infinities and NaN do not decompose this way. The scale needs no subnormal
    /// case, since a subnormal shares its actual exponent with the smallest normal.
    /// </summary>
    private (BigInteger Significand, BigInteger Scale) AsScaledInteger()
    {
      Contract.Requires(!IsZero && !IsInfinity && !IsNaN);
      return (exponent == 0 ? significand : significand | leadingBit,
        ScaleOfPreparedOperand(GetActualExponent(), bias, SignificandSize));
    }

    #endregion

    #region Arithmetic Helpers

    private static (BigInteger significand, BigInteger exponent) PrepareOperand(BigFloat operand, BigInteger leadingBit)
    {
      var sig = operand.significand;
      var exp = operand.GetActualExponent();
      if (operand.exponent > 0) {
        sig |= leadingBit;
      }
      return (sig, exp);
    }

    /// <summary>Prepares operands for multiplication/division operations (with combined sign calculation)</summary>
    private static ((BigInteger sig, BigInteger exp) x, (BigInteger sig, BigInteger exp) y, bool resultSign) PrepareOperandsForMultDiv(BigFloat x, BigFloat y)
    {
      var leadingBit = x.leadingBit;
      var resultSign = x.signBit ^ y.signBit;
      var (xSig, xExp) = PrepareOperand(x, leadingBit);
      var (ySig, yExp) = PrepareOperand(y, leadingBit);

      return ((xSig, xExp), (ySig, yExp), resultSign);
    }
    /// <summary>The low "bits" bits set, i.e. 2^bits - 1, and zero for a non-positive width.</summary>
    private static BigInteger GetMask(BigInteger bits)
    {
      return bits <= 0 ? BigInteger.Zero : BigIntegerMath.LeftShift(BigInteger.One, bits) - 1;
    }
    /// <summary>
    /// Shifts "value" right by "shift" bits, rounding the discarded tail to nearest with ties to even.
    /// A negative shift shifts left, which discards nothing and so needs no rounding.
    /// </summary>
    private static BigInteger ApplyShiftWithRounding(BigInteger value, BigInteger shift)
    {
      if (shift <= 0) {
        return BigIntegerMath.LeftShift(value, -shift);
      }

      // A shift can exceed the value's width by an astronomical margin, since exponent sizes are
      // unbounded: at a 40-bit exponent the smallest normal is 2^-549755813886. Compare against the
      // halfway point instead, since neither 2^shift nor the shifted value fits.
      if (shift > value.GetBitLength()) {
        // Everything is discarded. The result is 1 only if the value exceeded half of the discarded
        // range, i.e. 2^(shift-1); a value exactly at the halfway point ties to the even 0.
        return value.GetBitLength() == shift && (value & (value - 1)) != 0
          ? BigInteger.One
          : BigInteger.Zero;
      }

      // Split the value at the rounding position. The tail is whatever the retained part does not
      // account for, and both shifts here are bounded by the value's own width.
      var retained = BigIntegerMath.RightShift(value, shift);
      var tail = value - BigIntegerMath.LeftShift(retained, shift);

      if (tail.IsZero) {
        return retained;
      }

      // Round to nearest, ties to even. Comparing twice the tail against the discarded range avoids
      // materializing the halfway value itself.
      var tailRange = BigIntegerMath.LeftShift(BigInteger.One, shift);
      var doubledTail = tail * 2;

      return doubledTail > tailRange || (doubledTail == tailRange && !retained.IsEven)
        ? retained + 1
        : retained;
    }

    // Public convenience methods for special values
    public static BigFloat CreateZero(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, 0, 0, significandSize, exponentSize, true);
    public static BigFloat CreateInfinity(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, 0, GetMaxExponent(exponentSize), significandSize, exponentSize);
    public static BigFloat CreateNaN(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, GetSignificandMask(significandSize - 1), GetMaxExponent(exponentSize), significandSize, exponentSize);

    /// <summary>
    /// Creates one of the five special values the SMT-LIB FloatingPoint theory can name, which a solver may
    /// return from (get-value ...) as ((x (_ &lt;special&gt; &lt;eb&gt; &lt;sb&gt;))). Case insensitive.
    /// </summary>
    /// <param name="specialValue">Special value string ("NaN", "+oo", "-oo", "+zero", "-zero")</param>
    /// <returns>True if the special value was recognized and created; false otherwise</returns>
    public static bool TryCreateSpecialFromString(string specialValue, int sigSize, int expSize, out BigFloat result) {
      switch (specialValue.ToLowerInvariant()) {
        case "nan":
          result = CreateNaN(false, sigSize, expSize);
          return true;
        case "+oo":
          result = CreateInfinity(false, sigSize, expSize);
          return true;
        case "-oo":
          result = CreateInfinity(true, sigSize, expSize);
          return true;
        case "+zero":
          result = CreateZero(false, sigSize, expSize);
          return true;
        case "-zero":
          result = CreateZero(true, sigSize, expSize);
          return true;
        default:
          result = default;
          return false;
      }
    }

    /// <summary>Convert integer to BigFloat using direct IEEE 754 conversion</summary>
    private static BigFloat ConvertIntegerToBigFloat(BigInteger value, int significandSize, int exponentSize)
    {
      ValidateSizeParameters(significandSize, exponentSize);
      if (!FromRational(value, 1, significandSize, exponentSize, out var f)) {
        throw new ArgumentException($"The value {value} cannot be represented exactly with {significandSize}-bit significand and {exponentSize}-bit exponent", nameof(value));
      }

      return f;
    }

    #endregion

    #region IEEE 754 Operations

    // IEEE 754 helper methods
    public static BigInteger GetBias(int exponentSize) => (BigInteger.One << (exponentSize - 1)) - 1;
    public static BigInteger GetMaxExponent(int exponentSize) => (BigInteger.One << exponentSize) - 1;
    public static BigInteger GetLeadingBitPower(int significandSize) => BigInteger.One << (significandSize - 1);  // Returns power value for the implicit leading significand bit
    public static BigInteger GetSignificandMask(int significandSize) => GetMask(significandSize);

    #endregion

    #region Arithmetic Operations

    [Pure] public static BigFloat operator -(BigFloat x) => new (!x.signBit, x.significand, x.exponent, x.SignificandSize, x.ExponentSize);
    [Pure] public static BigFloat Abs(BigFloat x) => x.signBit ? -x : x;
    [Pure] public static BigFloat Max(BigFloat x, BigFloat y) => x.IsNaN || y.IsNaN ? (x.IsNaN ? x : y) : (x >= y ? x : y);
    [Pure] public static BigFloat Min(BigFloat x, BigFloat y) => x.IsNaN || y.IsNaN ? (x.IsNaN ? x : y) : (x <= y ? x : y);
    /// <summary>
    /// Returns "x" with the sign of "y". Both must have the same format.
    /// </summary>
    [Pure] public static BigFloat CopySign(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);
      return x.signBit == y.signBit ? x : -x;
    }

    /// <summary>Returns the sign: -1 for negative, 0 for zero/NaN, 1 for positive</summary>
    public int Sign() => IsNaN || IsZero ? 0 : (signBit ? -1 : 1);

    [Pure]
    public static BigFloat operator +(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Addition);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      // Handle zeros
      if (x.IsZero && y.IsZero) {
        // IEEE 754: opposite signs sum to +0
        var zeroResult = x.signBit != y.signBit ? CreateZero(false, x.SignificandSize, x.ExponentSize) : x;
        return zeroResult;
      }
      if (x.IsZero) {
        return y;
      }
      if (y.IsZero) {
        return x;
      }

      // Prepare signed operands
      var (xSig, xExp) = PrepareOperand(x, x.leadingBit);
      var (ySig, yExp) = PrepareOperand(y, y.leadingBit);

      var xSigned = x.signBit ? -xSig : xSig;
      var ySigned = y.signBit ? -ySig : ySig;

      var expDiff = xExp - yExp;

      // Beyond significandSize + 1 apart, the smaller operand shifts out of range entirely and cannot
      // affect the larger, whatever the signs.
      if (BigInteger.Abs(expDiff) > x.SignificandSize + 1) {
        var farApartResult = expDiff > 0 ? x : y;
        return farApartResult;
      }

      // Align by scaling the operand with the larger exponent up, rather than shifting the smaller one
      // down. Shifting down truncates the low bits before the sum is formed, and no later rounding can
      // recover them; scaling up keeps the sum exact.
      var absDiff = BigInteger.Abs(expDiff);
      var sum = expDiff == 0 ? xSigned + ySigned :
        expDiff > 0 ? BigIntegerMath.LeftShift(xSigned, absDiff) + ySigned :
        xSigned + BigIntegerMath.LeftShift(ySigned, absDiff);

      if (sum == 0) {
        // IEEE 754: cancellation gives -0 only when both operands are negative.
        return CreateZero(x.signBit && y.signBit, x.SignificandSize, x.ExponentSize);
      }

      // Aligning upward left both significands weighted by the smaller of the two exponents, so the
      // exact sum carries that operand's scale.
      var sumScale = ScaleOfPreparedOperand(BigInteger.Min(xExp, yExp), x.bias, x.SignificandSize);
      return RoundToFormat(BigInteger.Abs(sum), sumScale, sum < 0, x.SignificandSize, x.ExponentSize);
    }

    [Pure] public static BigFloat operator -(BigFloat x, BigFloat y) => x + -y;

    [Pure]
    public static BigFloat operator *(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Multiplication);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      // Handle multiplication by zero - should always produce zero
      if (x.IsZero || y.IsZero) {
        return CreateZero(x.signBit ^ y.signBit, x.SignificandSize, x.ExponentSize);
      }

      var ((xSig, xExp), (ySig, yExp), resultSign) = PrepareOperandsForMultDiv(x, y);

      // Multiply and check for zero
      var product = xSig * ySig;
      if (product == 0) {
        return CreateZero(resultSign, x.SignificandSize, x.ExponentSize);
      }

      // The product is exact, so RoundToFormat performs the only rounding. Multiplying two values adds
      // their scales.
      var productScale = ScaleOfPreparedOperand(xExp, x.bias, x.SignificandSize)
                       + ScaleOfPreparedOperand(yExp, x.bias, x.SignificandSize);
      return RoundToFormat(product, productScale, resultSign, x.SignificandSize, x.ExponentSize);
    }

    [Pure]
    public static BigFloat operator /(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Division);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      var ((xSig, xExp), (ySig, yExp), resultSign) = PrepareOperandsForMultDiv(x, y);

      // Long division produces bits from the top down, so pre-shift the dividend by as many quotient
      // bits as are wanted: the format's width plus a guard bit and a sticky bit. The quotient loses one
      // bit for every bit by which the dividend is narrower than the divisor, as a subnormal dividend is,
      // so add that shortfall.
      var dividendShortfall = BigInteger.Max(ySig.GetBitLength() - xSig.GetBitLength(), BigInteger.Zero);
      var guardShift = x.SignificandSize + 2 + dividendShortfall;
      var shiftedDividend = BigIntegerMath.LeftShift(xSig, guardShift);
      var quotient = BigInteger.DivRem(shiftedDividend, ySig, out var remainder);

      quotient = WithStickyBit(quotient, remainder);

      // Dividing subtracts the operands' scales; pre-shifting the dividend by guardShift lowered its
      // scale by the same amount, and the two bias terms cancel.
      var quotientScale = ScaleOfPreparedOperand(xExp, x.bias, x.SignificandSize)
                        - ScaleOfPreparedOperand(yExp, x.bias, x.SignificandSize)
                        - guardShift;
      return RoundToFormat(quotient, quotientScale, resultSign, x.SignificandSize, x.ExponentSize);
    }

    /// <summary>
    /// Power-of-two weight of bit 0 of the significand <see cref="PrepareOperand"/> returns. That
    /// significand is a plain integer rather than a 1.f fraction, hence the significandSize - 1 term.
    /// </summary>
    private static BigInteger ScaleOfPreparedOperand(BigInteger biasedExponent, BigInteger bias, int significandSize)
    {
      return biasedExponent - bias - (significandSize - 1);
    }

    /// <summary>
    /// Folds an inexact residual into bit 0 of a value destined for <see cref="RoundToFormat"/>, so that
    /// rounding can still tell a tail above half from one exactly at half. Callers must have computed more
    /// bits than the format keeps, so that bit 0 is among the bits rounding shifts away.
    /// </summary>
    private static BigInteger WithStickyBit(BigInteger value, BigInteger remainder)
    {
      return remainder.IsZero ? value : value | BigInteger.One;
    }

    /// <summary>
    /// True if "value" is exactly numerator/denominator, with both taken as positive. Cross-multiplying
    /// turns this into one BigInteger equality, with no rounding of its own.
    /// </summary>
    private static bool RepresentsExactly(BigFloat value, BigInteger numerator, BigInteger denominator)
    {
      if (value.IsInfinity || value.IsNaN) {
        return false;
      }

      if (value.IsZero) {
        return numerator.IsZero;
      }

      var (significand, scale) = value.AsScaledInteger();

      // significand * 2^scale == numerator / denominator, rearranged to avoid division.
      return scale >= 0
        ? BigIntegerMath.LeftShift(significand, scale) * denominator == numerator
        : significand * denominator == BigIntegerMath.LeftShift(numerator, -scale);
    }

    /// <summary>
    /// Biased exponent of the value "significand * 2^scale", where the significand is "width" bits wide,
    /// as if it were normalized so that its leading bit is the implicit one. A result at or below zero
    /// means the value is below the smallest normal and must be stored as a subnormal instead.
    /// </summary>
    private static BigInteger BiasedExponentOf(BigInteger scale, long width, BigInteger bias)
    {
      return scale + width - 1 + bias;
    }

    /// <summary>
    /// Rounds the exact value "significand * 2^scale" into the given format, performing the single
    /// IEEE 754 round-to-nearest-even the standard requires. Callers must hand over an exact, full-width
    /// value: rounding on the way in as well loses the residual that decides ties.
    /// </summary>
    /// <param name="significand">Exact significand, which may be wider than the format holds.</param>
    /// <param name="scale">Power-of-two weight of bit 0 of "significand" (unbiased).</param>
    private static BigFloat RoundToFormat(BigInteger significand, BigInteger scale, bool isNegative,
      int significandSize, int exponentSize)
    {
      if (significand.IsZero) {
        return CreateZero(isNegative, significandSize, exponentSize);
      }

      var bias = GetBias(exponentSize);

      // BiasedExponentOf gives the exponent this value would have if normalized where it stands. At or
      // below zero means it is subnormal, i.e. below what the format holds without shifting onto its grid.
      var biasedExp = BiasedExponentOf(scale, significand.GetBitLength(), bias);

      // A normal result keeps significandSize bits. A subnormal one instead lands on the grid every
      // subnormal shares, whose least significant bit has scale (1 - bias) - (significandSize - 1).
      // Either way there is one shift, and therefore one rounding.
      var shift = biasedExp > 0
        ? significand.GetBitLength() - significandSize
        : BigInteger.One - bias - (significandSize - 1) - scale;

      // A rounding carry needs no correction, since the exponent below is recomputed from the rounded
      // value's own width. That covers a subnormal reaching the smallest normal as well as a normal
      // carrying into the next binade.
      var rounded = ApplyShiftWithRounding(significand, shift);
      if (rounded.IsZero) {
        return CreateZero(isNegative, significandSize, exponentSize);
      }

      biasedExp = BiasedExponentOf(scale + shift, rounded.GetBitLength(), bias);

      if (biasedExp >= GetMaxExponent(exponentSize)) {
        return CreateInfinity(isNegative, significandSize, exponentSize);
      }

      // A normal number stores only the trailing significand, its leading bit being implied by the
      // nonzero exponent, so mask that bit off. A subnormal stores every bit it has, at exponent zero.
      return biasedExp > 0
        ? new BigFloat(isNegative, rounded & (GetLeadingBitPower(significandSize) - 1), biasedExp,
            significandSize, exponentSize)
        : new BigFloat(isNegative, rounded, 0, significandSize, exponentSize);
    }

    /// <summary>Arithmetic operation types for special value handling</summary>
    private enum ArithmeticOperation
    {
      Addition,
      Multiplication,
      Division
    }

    /// <summary>
    /// Handles special value cases for all arithmetic operations
    /// Returns null if no special case applies
    /// </summary>
    private static BigFloat? HandleSpecialValues(BigFloat x, BigFloat y, ArithmeticOperation operation)
    {
      // NaN propagation - always first priority
      if (x.IsNaN || y.IsNaN) {
        return CreateNaN(false, x.SignificandSize, x.ExponentSize);
      }

      var resultSign = x.signBit ^ y.signBit;
      var sigSize = x.SignificandSize;
      var expSize = x.ExponentSize;

      switch (operation)
      {
        case ArithmeticOperation.Addition:
          if (x.IsInfinity && y.IsInfinity) {
            return x.signBit != y.signBit ? CreateNaN(false, sigSize, expSize) : x;
          }

          if (x.IsInfinity) {
            return x;
          }

          if (y.IsInfinity) {
            return y;
          }

          break;

        case ArithmeticOperation.Multiplication:
          if ((x.IsInfinity && y.IsZero) || (y.IsInfinity && x.IsZero)) {
            return CreateNaN(false, sigSize, expSize);
          }

          if (x.IsInfinity || y.IsInfinity) {
            return CreateInfinity(resultSign, sigSize, expSize);
          }

          break;

        case ArithmeticOperation.Division:
          if (y.IsZero) {
            return x.IsZero ? CreateNaN(false, sigSize, expSize) : CreateInfinity(resultSign, sigSize, expSize);
          }

          if (x.IsZero) {
            return CreateZero(resultSign, sigSize, expSize);
          }

          if (x.IsInfinity && y.IsInfinity) {
            return CreateNaN(false, sigSize, expSize);
          }

          if (x.IsInfinity) {
            return CreateInfinity(resultSign, sigSize, expSize);
          }

          if (y.IsInfinity) {
            return CreateZero(resultSign, sigSize, expSize);
          }

          break;
      }

      return null; // No special case applies
    }

    #endregion

    #region Mathematical Operations

    /// <summary>
    /// Bound on the width of the integers <see cref="TryFloorCeiling"/> will produce. Since exponent sizes
    /// are unbounded, so are integer parts: the floor of a large float24e32 has 256 million bits. The bound
    /// is well above the widest standard format's integer part, which is bias + 1 bits (262144 for octuple).
    /// </summary>
    public const int MaxFloorCeilingBits = 1 << 20;

    /// <summary>
    /// As <see cref="FloorCeiling"/>, but returns false instead of throwing on NaN and the infinities or
    /// producing a result wider than <see cref="MaxFloorCeilingBits"/>.
    /// </summary>
    public bool TryFloorCeiling(out BigInteger floor, out BigInteger ceiling)
    {
      floor = ceiling = BigInteger.Zero;

      if (IsNaN || IsInfinity) {
        return false;
      }

      // The magnitude is below 2^(exponent - bias + 1), so that bounds the width of the integer part.
      if (!IsZero && GetActualExponent() - bias + 1 > MaxFloorCeilingBits) {
        return false;
      }

      FloorCeiling(out floor, out ceiling);
      return true;
    }

    /// <summary>
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// See <see cref="TryFloorCeiling"/> for a variant that declines instead of returning huge integers.
    /// </summary>
    /// <param name="floor">Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BigInteger floor, out BigInteger ceiling)
    {
      // Handle special cases
      if (IsNaN || IsInfinity) {
        throw new InvalidOperationException($"Cannot compute floor/ceiling of {(IsNaN ? "NaN" : "infinity")} value");
      }

      if (IsZero) {
        floor = ceiling = 0;
        return;
      }

      // Convert to rational and compute integer part
      var (significandValue, shift) = AsScaledInteger();

      BigInteger integerPart;
      bool hasRemainder;

      if (shift >= 0) {
        integerPart = BigIntegerMath.LeftShift(significandValue, shift);
        hasRemainder = false;
      } else if (-shift >= SignificandSize) {
        integerPart = 0;
        hasRemainder = true;
      } else {
        var absShift = -shift;
        integerPart = BigIntegerMath.RightShift(significandValue, absShift);
        hasRemainder = (significandValue & GetMask(absShift)) != 0;
      }

      // Apply sign and compute floor/ceiling
      if (signBit) {
        floor = hasRemainder ? -integerPart - 1 : -integerPart;
        ceiling = -integerPart;
      } else {
        floor = integerPart;
        ceiling = hasRemainder ? integerPart + 1 : integerPart;
      }
    }

    #endregion

    #region Comparison Operations

    /// <summary>
    /// Orders two values as C#'s Single.CompareTo does, which means a total order in which a NaN compares
    /// equal to itself so that collections containing one can be sorted. The comparison operators keep
    /// IEEE 754 semantics instead, where every NaN comparison is false; the difference is deliberate.
    /// </summary>
    /// <returns>
    /// Less than zero: This instance is less than 'that'
    /// Zero: This instance equals 'that' (including NaN == NaN for ordering)
    /// Greater than zero: This instance is greater than 'that'
    /// </returns>
    public int CompareTo(BigFloat that)
    {
      ValidateSizeCompatibility(this, that);

      // NaN handling - special ordering for collections
      if (IsNaN || that.IsNaN) {
        if (IsNaN && that.IsNaN) {
          return 0;
        }
        return IsNaN ? 1 : -1;
      }

      // Infinity handling
      if (IsInfinity || that.IsInfinity) {
        if (IsInfinity && that.IsInfinity && signBit == that.signBit) {
          return 0;
        }
        if (IsInfinity) {
          return signBit ? -1 : 1;
        }
        return that.signBit ? 1 : -1;
      }

      // Zero handling - IEEE 754: +0 == -0
      if (IsZero && that.IsZero) {
        return 0;
      }

      // Sign comparison
      if (signBit != that.signBit) {
        return signBit ? -1 : 1;
      }

      // Same sign - compare magnitude
      var cmp = exponent.CompareTo(that.exponent);
      if (cmp == 0) {
        cmp = significand.CompareTo(that.significand);
      }

      return signBit ? -cmp : cmp;
    }

    [Pure] public static bool operator ==(BigFloat x, BigFloat y) =>
      (!x.IsNaN && !y.IsNaN) && ((x.IsZero && y.IsZero) || x.CompareTo(y) == 0);

    [Pure] public static bool operator !=(BigFloat x, BigFloat y) => !(x == y);

    [Pure] public static bool operator <(BigFloat x, BigFloat y) =>
      (!x.IsNaN && !y.IsNaN) && x.CompareTo(y) < 0;

    [Pure] public static bool operator >(BigFloat x, BigFloat y) =>
      (!x.IsNaN && !y.IsNaN) && x.CompareTo(y) > 0;

    [Pure] public static bool operator <=(BigFloat x, BigFloat y) =>
      (!x.IsNaN && !y.IsNaN) && x.CompareTo(y) <= 0;

    [Pure] public static bool operator >=(BigFloat x, BigFloat y) =>
      (!x.IsNaN && !y.IsNaN) && x.CompareTo(y) >= 0;

    [Pure] public override bool Equals(object obj) => obj is BigFloat bigFloat && this == bigFloat;

    [Pure] public override int GetHashCode() =>
      HashCode.Combine(significand, exponent, signBit, SignificandSize, ExponentSize);

    #endregion

    #region String Representation

    [Pure]
    public string ToDecimalString()
    {
      // Handle special values
      if (IsNaN) {
        return "NaN";
      }
      if (IsInfinity) {
        return signBit ? "-Infinity" : "Infinity";
      }
      if (IsZero) {
        return signBit ? "-0" : "0";
      }

      // Convert to rational number
      var (significandValue, shift) = AsScaledInteger();

      // Calculate numerator and denominator
      var (numerator, denominator) = shift >= 0
        ? (BigIntegerMath.LeftShift(significandValue, shift), BigInteger.One)
        : (significandValue, BigIntegerMath.LeftShift(BigInteger.One, -shift));

      if (signBit) {
        numerator = -numerator;
      }

      // Convert to decimal with appropriate scale
      var desiredScale = denominator.GetBitLength() * 0.31; // Approximate decimal digits needed
      if (desiredScale > int.MaxValue - 1) {
        throw new OverflowException($"Cannot convert to decimal string: required scale {desiredScale:E} exceeds maximum supported scale {int.MaxValue}");
      }
      var scale = (int)desiredScale;
      var scaled = BigInteger.Abs(numerator) * BigInteger.Pow(10, scale) / denominator;
      var str = scaled.ToString().PadLeft(scale + 1, '0');

      // Format with decimal point
      if (scale == 0) {
        return signBit && !IsZero ? "-" + str : str;
      }

      var intPart = str[..^scale];
      var fracPart = str[^scale..].TrimEnd('0');
      var result = fracPart.Length > 0 ? $"{intPart}.{fracPart}" : intPart;

      return signBit ? "-" + result : result;
    }

    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);

      // NaN and the infinities name their sizes without the leading "f", so they cannot reuse "format".
      var format = $"f{SignificandSize}e{ExponentSize}";
      var sign = signBit ? "-" : "";

      if (IsNaN) {
        return $"0NaN{SignificandSize}e{ExponentSize}";
      }

      if (IsInfinity) {
        return $"0{(signBit ? "-" : "+")}oo{SignificandSize}e{ExponentSize}";
      }

      if (IsZero) {
        return $"{sign}0x0.0e0{format}";
      }

      var (significandBits, binaryExp) = AsScaledInteger();

      // Calculate hex exponent and adjust significand for bit remainder
      var hexExp = binaryExp / 4;
      var bitRemainder = (int)(binaryExp % 4);

      if (bitRemainder < 0) {
        significandBits <<= (4 + bitRemainder);
        hexExp--;
      } else if (bitRemainder > 0) {
        significandBits <<= bitRemainder;
      }

      // Convert to hex and format as H.HHH
      var hexStr = significandBits.ToString("X");
      if (hexStr.Length == 1) {
        return $"{sign}0x{hexStr}.0e{hexExp}{format}";
      }

      // Format with decimal point after first digit
      var fracPart = hexStr[1..].TrimEnd('0');
      if (fracPart.Length == 0) {
        fracPart = "0";
      }
      hexExp += hexStr.Length - 1;

      return $"{sign}0x{hexStr[0]}.{fracPart}e{hexExp}{format}";
    }

    #endregion

    #region String Parsing

    /// <summary>Tries to parse hex format BigFloat strings according to the specification</summary>
    /// <param name="s">The hex format string to parse (without size suffixes)</param>
    /// <param name="strict">When true, enforces Boogie's strict parsing rules (no precision loss, no extreme underflow);
    /// when false, follows IEEE 754 standard behavior</param>
    private static bool TryParseHexFormat(string s, int sigSize, int expSize, bool strict, out BigFloat result)
    {
      result = default;

      // Parse format: [-]0x<hex>.<hex>e<dec>
      var posX = s.IndexOf("0x", StringComparison.Ordinal);
      var posE = s.LastIndexOf('e');
      if (posX < 0 || posE <= posX + 2) {
        return false;
      }

      // Extract hex significand and find decimal point
      var hexPart = s[(posX + 2)..posE];
      var dotPos = hexPart.IndexOf('.');
      var exponentPart = s[(posE + 1)..];

      // Check for spaces in the exponent part
      if (exponentPart.Contains(' ')) {
        return false;
      }

      if (dotPos < 0 ||
          !TryParseHex(hexPart[..dotPos], out var intPart) ||
          !TryParseHex(hexPart[(dotPos + 1)..], out var fracPart) ||
          !BigInteger.TryParse(exponentPart, out var decExp)) {
        return false;
      }

      // Build significand from hex parts
      var fracBits = ((long)hexPart.Length - dotPos - 1) * 4;
      var sig = BigIntegerMath.LeftShift(intPart, fracBits) | fracPart;
      var isNegative = s.Length > 0 && s[0] == '-';

      if (sig == 0) {
        result = CreateZero(isNegative, sigSize, expSize);
        return true;
      }

      // Calculate biased exponent
      var msbPos = sig.GetBitLength() - 1;
      var biasedExp = new BigInteger(msbPos - fracBits) + (decExp * 4) + GetBias(expSize);

      // Handle overflow/underflow/normal cases
      if (biasedExp >= GetMaxExponent(expSize)) {
        if (strict) {
          return false;
        }
        result = CreateInfinity(isNegative, sigSize, expSize);
        return true;
      }

      if (biasedExp <= 0) {
        return HandleUnderflow(isNegative, sig, biasedExp, sigSize, expSize, strict, out result);
      }

      // Strict mode rejects any literal that would not survive the round trip, so a nonzero tail below
      // the retained bits is an error rather than something to round away.
      var shift = new BigInteger(msbPos) - (sigSize - 1);
      if (strict && shift > 0 && shift < sig.GetBitLength() && (sig & GetMask(shift)) != 0) {
        return false;
      }

      // Bit 0 of "sig" sits fracBits below the hex point, which decExp scales by four bits per digit.
      var scale = (decExp * 4) - fracBits;
      result = RoundToFormat(sig, scale, isNegative, sigSize, expSize);

      if (strict && result.IsInfinity) {
        return false;
      }

      return true;
    }

    private static bool TryParseHex(string hex, out BigInteger value)
    {
      value = 0;
      // Boogie spec requires at least one hex digit, so empty strings are invalid
      if (hex.Length == 0) {
        return false;
      }
      return BigInteger.TryParse("0" + hex, System.Globalization.NumberStyles.HexNumber, null, out value);
    }
    /// <summary>
    /// Handles a literal whose exponent falls at or below the subnormal range. RoundToFormat does the
    /// rounding; what is specific here is strict mode, which accepts only a literal that lands on a nonzero
    /// subnormal, whether or not it got there exactly.
    /// </summary>
    private static bool HandleUnderflow(bool signBit, BigInteger sig, BigInteger biasedExp, int sigSize, int expSize, bool strict, out BigFloat result)
    {
      // Bit 0 of "sig" has weight 2^(actualExp - msb), since the caller placed the leading bit at
      // actualExp.
      var actualExp = biasedExp - GetBias(expSize);
      var scale = actualExp - (sig.GetBitLength() - 1);

      result = RoundToFormat(sig, scale, signBit, sigSize, expSize);

      if (!strict) {
        return true;
      }

      // Rejected in strict mode: flushed to zero, or rounded up out of the subnormal range.
      return !result.IsZero && result.exponent == 0;
    }

    /// <summary>Converts to SMT-LIB format string</summary>
    public string ToSMTLibString() =>
      exponent == maxExponent ?
        $"_ {(significand == 0 ? $"{(signBit ? "-" : "+")}oo" : "NaN")} {ExponentSize} {SignificandSize}" :
        $"fp (_ bv{(signBit ? "1" : "0")} 1) (_ bv{exponent} {ExponentSize}) (_ bv{significand} {SignificandSize - 1})";

    #endregion
  }

  /// <summary>Helper class for BigInteger arithmetic operations that require shift amounts larger than int.MaxValue</summary>
  internal static class BigIntegerMath
  {
    /// <summary>Left shift operation that handles BigInteger shift amounts</summary>
    /// <param name="shift">The number of bits to shift left (can be negative for right shift)</param>
    /// <returns>The result of value << shift, handling shifts larger than int.MaxValue</returns>
    public static BigInteger LeftShift(BigInteger value, BigInteger shift)
    {
      if (shift < 0) {
        return RightShift(value, -shift);
      }
      if (shift == 0 || value == 0) {
        return value;
      }

      // Perform shift in chunks of int.MaxValue
      var result = value;
      var remaining = shift;

      while (remaining > 0) {
        var currentShift = remaining > int.MaxValue ? int.MaxValue : (int)remaining;
        result <<= currentShift;
        remaining -= currentShift;
      }

      return result;
    }

    /// <summary>Right shift operation that handles BigInteger shift amounts</summary>
    /// <param name="shift">The number of bits to shift right (can be negative for left shift)</param>
    /// <returns>The result of value >> shift, handling shifts larger than int.MaxValue</returns>
    public static BigInteger RightShift(BigInteger value, BigInteger shift)
    {
      if (shift < 0) {
        return LeftShift(value, -shift);
      }
      if (shift == 0) {
        return value;
      }

      // Early exit if result would be zero
      if (value.GetBitLength() <= shift) {
        return BigInteger.Zero;
      }

      // Perform shift in chunks of int.MaxValue
      var result = value;
      var remaining = shift;

      while (remaining > 0) {
        var currentShift = remaining > int.MaxValue ? int.MaxValue : (int)remaining;
        result >>= currentShift;
        remaining -= currentShift;

        // Early exit if we've shifted to zero
        if (result.IsZero) {
          return BigInteger.Zero;
        }
      }

      return result;
    }
  }
}