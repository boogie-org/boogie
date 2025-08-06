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

    // SignificandSize represents the precision: trailing significand field width + 1 (for the implicit leading significand bit)
    // For IEEE 754 double: SignificandSize = 53 (52-bit trailing significand field + 1 implicit leading significand bit)
    // The trailing significand field always uses SignificandSize - 1 bits
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

    // ============================================================================
    // PUBLIC INTERFACE
    // ============================================================================

    #region Constructors and Factory Methods

    /// <summary>
    /// Initializes a new instance of the <see cref="BigFloat"/> struct.
    /// Primary constructor for IEEE 754 representation
    /// </summary>
    /// <param name="signBit">The sign bit: true for negative, false for positive</param>
    /// <param name="significand">The trailing significand field (without implicit leading significand bit for normal numbers)</param>
    /// <param name="exponent">The biased exponent value</param>
    /// <param name="significandSize">Total bits for significand (including implicit leading significand bit)</param>
    /// <param name="exponentSize">Total bits for exponent</param>
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

      // Initialize cached values
      bias = GetBias(exponentSize);
      maxExponent = GetMaxExponent(exponentSize);
      leadingBit = GetLeadingBitPower(significandSize);
    }

    /// <summary>
    /// Tries to parse a string representation of a BigFloat with IEEE 754 compliant behavior
    /// </summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    /// <param name="result">The parsed BigFloat value if successful; default(BigFloat) otherwise</param>
    /// <returns>True if the parse was successful; false otherwise</returns>
    [Pure]
    public static bool TryParse(string s, out BigFloat result)
    {
      return TryParseFloatString(s, strict: false, out result);
    }

    /// <summary>
    /// Tries to parse a string representation of a BigFloat with strict Boogie verification requirements.
    /// This method enforces:
    /// - No precision loss (significand must have trailing zeros for full nibble inclusion)
    /// - No extreme underflow (rejects values that would underflow to zero)
    /// - Strict size validation
    ///
    /// DESIGN NOTE: This "strict" mode is arguably overly restrictive. It rejects:
    /// - ALL extreme underflow, even representable subnormals (e.g., 0x0.8e-126f24e8)
    /// - ANY precision loss, even standard IEEE 754 rounding
    ///
    /// </summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    /// <param name="result">The parsed BigFloat value if successful; default(BigFloat) otherwise</param>
    /// <returns>True if the parse was successful; false otherwise</returns>
    [Pure]
    public static bool TryParseExact(string s, out BigFloat result)
    {
      return TryParseFloatString(s, strict: true, out result);
    }

    /// <summary>
    /// Parses a string representation of a BigFloat with IEEE 754 compliant behavior
    /// </summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    /// <returns>The parsed BigFloat value</returns>
    [Pure]
    public static BigFloat FromString(string s)
    {
      if (TryParse(s, out var result))
      {
        return result;
      }
      throw new FormatException($"Unable to parse '{s}' as BigFloat");
    }

    /// <summary>
    /// Parses a string representation of a BigFloat with strict Boogie verification requirements.
    /// This method enforces:
    /// - No precision loss (significand must have trailing zeros for full nibble inclusion)
    /// - No extreme underflow (rejects values that would underflow to zero)
    /// - Strict size validation with FormatException
    ///
    /// DESIGN NOTE: This "strict" mode is arguably overly restrictive. It rejects:
    /// - ALL extreme underflow, even representable subnormals (e.g., 0x0.8e-126f24e8)
    /// - ANY precision loss, even standard IEEE 754 rounding
    ///
    /// </summary>
    /// <param name="s">The string to parse in format: [-]0x^.^e*f*e* or 0NaN*e* or 0+/-oo*e*</param>
    /// <returns>The parsed BigFloat value</returns>
    [Pure]
    public static BigFloat FromStringStrict(string s)
    {
      if (TryParseExact(s, out var result)) {
        return result;
      }
      throw new FormatException($"Unable to parse '{s}' as BigFloat in strict mode");
    }

    /// <summary>
    /// Core parsing logic that handles both IEEE 754 compliant and Boogie strict parsing modes
    /// </summary>
    /// <param name="s">The string to parse</param>
    /// <param name="strict">When true, enforces Boogie's verification requirements (no precision loss, no extreme underflow);
    /// when false, follows IEEE 754 standard (allows graceful underflow and rounding)</param>
    /// <param name="result">The parsed BigFloat value if successful; default(BigFloat) otherwise</param>
    /// <returns>True if the parse was successful; false otherwise</returns>
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

    /// <summary>
    /// Creates a BigFloat from an integer value (default: double precision)
    /// </summary>
    [Pure] public static BigFloat FromInt(int v) => ConvertIntegerToBigFloat(v, 53, 11);
    [Pure] public static BigFloat FromInt(int v, int significandSize, int exponentSize) => ConvertIntegerToBigFloat(v, significandSize, exponentSize);
    public static BigFloat FromBigInt(BigInteger v, int significandSize, int exponentSize) => ConvertIntegerToBigFloat(v, significandSize, exponentSize);

    /// <summary>
    /// Converts a rational number to a BigFloat.
    /// Returns false if the number cannot be accurately represented as a BigFloat.
    /// </summary>
    /// <param name="numerator">The numerator of the rational number</param>
    /// <param name="denominator">The denominator of the rational number</param>
    /// <param name="significandSize">The size of the significand in bits</param>
    /// <param name="exponentSize">The size of the exponent in bits</param>
    /// <param name="result">The resulting BigFloat</param>
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

      // Scale numerator for precision
      // Use long to avoid overflow in bit length calculation
      var scaleBitsLong = (long)significandSize + 3 + (denominator.GetBitLength() - numerator.GetBitLength());
      var scaleBits = scaleBitsLong < 0 ? BigInteger.Zero : new BigInteger(scaleBitsLong);
      var scaledNumerator = BigIntegerMath.LeftShift(numerator, scaleBits);
      var quotient = BigInteger.DivRem(scaledNumerator, denominator, out var remainder);

      // Apply rounding if inexact
      var isExact = remainder.IsZero;
      if (!isExact) {
        quotient = ApplyRoundToNearestEven(quotient, remainder, denominator);
      }

      var quotientBits = quotient.GetBitLength();
      var biasedExp = GetBias(exponentSize) + quotientBits - scaleBits - 1;
      if (biasedExp > GetMaxExponent(exponentSize) - 1) {
        result = CreateInfinity(isNegative, significandSize, exponentSize);
        return false;
      }
      var targetBits = significandSize - 1;
      var minBiasedExp = 2 - significandSize;

      if (biasedExp <= 0) {
        if (biasedExp < minBiasedExp) {
          isExact = false;

          if (biasedExp == minBiasedExp - 1) {
            if (quotient == BigIntegerMath.LeftShift(BigInteger.One, quotientBits - 1)) {
              result = CreateZero(isNegative, significandSize, exponentSize);
            } else {
              var (boundaryShifted, _, _) = ApplyShiftWithRounding(quotient, BigInteger.One);
              result = boundaryShifted > 0
                ? new BigFloat(isNegative, 1, 0, significandSize, exponentSize)
                : CreateZero(isNegative, significandSize, exponentSize);
            }
          } else {
            result = CreateZero(isNegative, significandSize, exponentSize);
          }
        } else {
          var shiftAmount = (quotientBits - targetBits) - biasedExp;
          var (shifted, _, _) = ApplyShiftWithRounding(quotient, shiftAmount);

          if (shifted >= BigInteger.One << targetBits) {
            result = new BigFloat(isNegative, 0, 1, significandSize, exponentSize);
          } else {
            result = new BigFloat(isNegative, shifted, 0, significandSize, exponentSize);
          }
        }
      } else {
        var (normalShifted, wasExact, overflow) = ApplyShiftWithRounding(quotient, quotientBits - significandSize);
        isExact &= wasExact;

        if (overflow) {
          normalShifted >>= 1;
          biasedExp++;
        }

        var leadingBitMask = GetLeadingBitPower(significandSize) - 1;
        result = new BigFloat(isNegative, normalShifted & leadingBitMask, biasedExp, significandSize, exponentSize);
      }

      return isExact;
    }

    /// <summary>
    /// Converts a BigDec (decimal) value to a BigFloat.
    /// Returns false if the number cannot be accurately represented as a BigFloat.
    /// </summary>
    /// <param name="value">The BigDec value to convert</param>
    /// <param name="significandSize">The size of the significand in bits</param>
    /// <param name="exponentSize">The size of the exponent in bits</param>
    /// <param name="result">The resulting BigFloat</param>
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

    /// <summary>
    /// Validates that significand and exponent sizes meet minimum requirements (must be > 1)
    /// </summary>
    /// <param name="significandSize">The size of the significand in bits</param>
    /// <param name="exponentSize">The size of the exponent in bits</param>
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

    /// <summary>
    /// Prepares operands for multiplication/division operations (with combined sign calculation)
    /// </summary>
    private static ((BigInteger sig, BigInteger exp) x, (BigInteger sig, BigInteger exp) y, bool resultSign) PrepareOperandsForMultDiv(BigFloat x, BigFloat y)
    {
      var leadingBit = x.leadingBit;
      var resultSign = x.signBit ^ y.signBit;
      var (xSig, xExp) = PrepareOperand(x, leadingBit);
      var (ySig, yExp) = PrepareOperand(y, leadingBit);

      return ((xSig, xExp), (ySig, yExp), resultSign);
    }

    private static BigInteger ApplyRoundToNearestEven(BigInteger quotient, BigInteger remainder, BigInteger denominator)
    {
      // Round up if remainder > denominator/2, or if remainder == denominator/2 and quotient is odd
      if (remainder * 2 > denominator || (remainder * 2 == denominator && !quotient.IsEven)) {
        quotient++;
      }

      return quotient;
    }

    private static BigInteger GetMask(BigInteger bits)
    {
      if (bits <= 0) {
        return BigInteger.Zero;
      }
      return BigIntegerMath.LeftShift(BigInteger.One, bits) - 1;
    }

    /// <summary>
    /// Applies a shift with IEEE 754 round-to-nearest-even rounding.
    /// </summary>
    /// <param name="value">The value to shift</param>
    /// <param name="shift">The shift amount (positive for right shift, negative for left shift)</param>
    /// <returns>A tuple containing:
    /// - result: The shifted and rounded value
    /// - isExact: Whether the operation was exact (no bits were lost)
    /// - overflow: Whether rounding caused the result to gain an extra bit (e.g., 111...111 -> 1000...000)
    /// </returns>
    private static (BigInteger result, bool isExact, bool overflow) ApplyShiftWithRounding(BigInteger value, BigInteger shift)
    {
      // Handle left shifts (no rounding needed, no overflow possible)
      if (shift <= 0) {
        return (BigIntegerMath.LeftShift(value, -shift), true, false);
      }

      // Handle very large shifts - but still need to check for rounding
      if (value.GetBitLength() < shift) {
        // All bits shifted out, but check if we need to round up
        // For round-to-nearest-even, we round up if value > 2^(shift-1)
        var halfValue = BigIntegerMath.LeftShift(BigInteger.One, shift - 1);
        if (value > halfValue) {
          return (BigInteger.One, false, false); // Result is 1, no overflow
        }
        return (BigInteger.Zero, !value.IsZero, false);
      }

      // For very large right shifts, perform in chunks
      var remaining = shift;
      var current = value;

      // Shift by int.MaxValue chunks if needed
      while (remaining > int.MaxValue) {
        current >>= int.MaxValue;
        remaining -= int.MaxValue;
        if (current.IsZero) {
          return (BigInteger.Zero, false, false);
        }
      }

      // Perform final shift with IEEE 754 round-to-nearest-even
      var intShift = (int)remaining;
      var mask = (BigInteger.One << intShift) - 1;
      var lostBits = current & mask;
      var result = current >> intShift;

      // If no bits lost, result is exact, no overflow
      if (lostBits.IsZero) {
        return (result, true, false);
      }

      // Round to nearest even
      var halfBit = BigInteger.One << (intShift - 1);
      var needsRounding = lostBits > halfBit || (lostBits == halfBit && !result.IsEven);

      // Check for overflow: when rounding up causes bit length to increase
      var overflow = false;
      if (needsRounding) {
        var originalBitLength = result.GetBitLength();
        result++;
        overflow = result.GetBitLength() > originalBitLength;
      }

      return (result, false, overflow);
    }

    // Public convenience methods for special values
    public static BigFloat CreateZero(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, 0, 0, significandSize, exponentSize, true);
    public static BigFloat CreateInfinity(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, 0, GetMaxExponent(exponentSize), significandSize, exponentSize);
    public static BigFloat CreateNaN(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, GetSignificandMask(significandSize - 1), GetMaxExponent(exponentSize), significandSize, exponentSize);

    /// <summary>
    /// Tries to create special values from string representation for SMT-LIB integration.
    /// Supports: "NaN", "+oo", "-oo" (case insensitive)
    /// </summary>
    /// <param name="specialValue">Special value string ("NaN", "+oo", "-oo")</param>
    /// <param name="sigSize">Significand size in bits</param>
    /// <param name="expSize">Exponent size in bits</param>
    /// <param name="result">The resulting BigFloat if successful; default(BigFloat) otherwise</param>
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
        default:
          result = default;
          return false;
      }
    }

    /// <summary>
    /// Convert integer to BigFloat using direct IEEE 754 conversion
    /// </summary>
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
    public static BigInteger GetSignificandMask(int significandSize) => (BigInteger.One << significandSize) - 1;

    #endregion

    // ============================================================================
    // ARITHMETIC AND COMPARISON OPERATIONS
    // ============================================================================

    #region Arithmetic Operations

    [Pure] public static BigFloat operator -(BigFloat x) => new (!x.signBit, x.significand, x.exponent, x.SignificandSize, x.ExponentSize);
    [Pure] public static BigFloat Abs(BigFloat x) => x.signBit ? -x : x;
    [Pure] public static BigFloat Max(BigFloat x, BigFloat y) => x.IsNaN || y.IsNaN ? (x.IsNaN ? x : y) : (x >= y ? x : y);
    [Pure] public static BigFloat Min(BigFloat x, BigFloat y) => x.IsNaN || y.IsNaN ? (x.IsNaN ? x : y) : (x <= y ? x : y);
    [Pure] public static BigFloat CopySign(BigFloat x, BigFloat y) => x.signBit == y.signBit ? x : -x;

    /// <summary>
    /// Returns the sign: -1 for negative, 0 for zero/NaN, 1 for positive
    /// </summary>
    public int Sign() => IsNaN || IsZero ? 0 : (signBit ? -1 : 1);

    [Pure]
    public static BigFloat operator +(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      // Handle special values
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

      // If operands are far apart, the smaller cannot affect the larger
      // For same sign: no cancellation possible
      // For opposite signs: when difference > significandSize + 1, the smaller value
      // shifts completely out of range and doesn't affect the result
      if (BigInteger.Abs(expDiff) > x.SignificandSize + 1) {
        var farApartResult = expDiff > 0 ? x : y;
        return farApartResult;
      }

      // Align significands and add
      var sum = expDiff == 0 ? xSigned + ySigned :
        expDiff > 0 ? xSigned + BigIntegerMath.RightShift(ySigned, expDiff) :
        BigIntegerMath.RightShift(xSigned, -expDiff) + ySigned;

      if (sum == 0) {
        var zeroSumResult = CreateZero(x.signBit && y.signBit, x.SignificandSize, x.ExponentSize);
        return zeroSumResult;
      }

      // Normalize result
      var isNegative = sum < 0;
      var absSum = isNegative ? -sum : sum;

      var baseExp = xExp > yExp ? xExp : yExp;
      var (normSig, normExp) = NormalizeAndRound(absSum, baseExp, x.SignificandSize);

      var result = HandleExponentBounds(normSig, normExp, isNegative, x.SignificandSize, x.ExponentSize);
      return result;
    }

    [Pure] public static BigFloat operator -(BigFloat x, BigFloat y) => x + -y;

    [Pure]
    public static BigFloat operator *(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      // Handle special values
      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Multiplication);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      // Handle multiplication by zero - should always produce zero
      if (x.IsZero || y.IsZero) {
        return CreateZero(x.signBit ^ y.signBit, x.SignificandSize, x.ExponentSize);
      }

      // Prepare operands and calculate result sign
      var ((xSig, xExp), (ySig, yExp), resultSign) = PrepareOperandsForMultDiv(x, y);

      // Multiply and check for zero
      var product = xSig * ySig;
      if (product == 0) {
        return CreateZero(resultSign, x.SignificandSize, x.ExponentSize);
      }

      // Normalize and round the product
      var (normalizedProduct, normalShift) = NormalizeAndRound(product, BigInteger.Zero, x.SignificandSize);

      // Calculate the final exponent - all values are already BigInteger
      var bias = x.bias;
      var resultExp = xExp + yExp - bias + normalShift - (x.SignificandSize - 1);

      // Handle overflow, underflow, and create final result
      return HandleExponentBounds(normalizedProduct, resultExp, resultSign, x.SignificandSize, x.ExponentSize);
    }

    [Pure]
    public static BigFloat operator /(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      // Handle special cases
      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Division);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      // Prepare operands and calculate result sign
      var ((xSig, xExp), (ySig, yExp), resultSign) = PrepareOperandsForMultDiv(x, y);

      // Shift dividend left for precision and divide with rounding
      var shiftedDividend = BigIntegerMath.LeftShift(xSig, x.SignificandSize + 1);
      var quotient = BigInteger.DivRem(shiftedDividend, ySig, out var remainder);
      quotient = ApplyRoundToNearestEven(quotient, remainder, ySig);

      if (quotient == 0) {
        return CreateZero(resultSign, x.SignificandSize, x.ExponentSize);
      }

      // Normalize and calculate final exponent
      var (normalizedQuotient, normalShift) = NormalizeAndRound(quotient, BigInteger.Zero, x.SignificandSize);
      var resultExp = xExp - yExp + x.bias + normalShift - 2;

      return HandleExponentBounds(normalizedQuotient, resultExp, resultSign, x.SignificandSize, x.ExponentSize);
    }

    private static (BigInteger significand, BigInteger exponent) NormalizeAndRound(BigInteger value, BigInteger exponent, int targetBits)
    {
      var valueBits = value.GetBitLength();
      var shift = valueBits - targetBits;

      // Use IEEE 754 compliant shift and round method
      var (shiftedValue, _, overflow) = ApplyShiftWithRounding(value, shift);
      var adjustedExponent = exponent + shift;

      // Handle potential overflow from rounding (only for right shifts)
      if (overflow) {
        shiftedValue >>= 1;
        adjustedExponent++;
      }

      return (shiftedValue, adjustedExponent);
    }

    private static BigFloat HandleExponentBounds(BigInteger significand, BigInteger exponent, bool isNegative, int significandSize, int exponentSize)
    {
      var maxExponent = GetMaxExponent(exponentSize);

      // Handle overflow to infinity
      if (exponent >= maxExponent) {
        return CreateInfinity(isNegative, significandSize, exponentSize);
      }

      // Handle normal numbers
      if (exponent > 0) {
        // Remove implicit leading bit for storage (it's encoded in the biased exponent)
        var leadingBitMask = GetLeadingBitPower(significandSize) - 1;
        return new BigFloat(isNegative, significand & leadingBitMask, exponent, significandSize, exponentSize);
      }

      // Handle complete underflow to zero
      var bias = GetBias(exponentSize);
      if (exponent < BigInteger.One - bias - (significandSize - 1)) {
        return CreateZero(isNegative, significandSize, exponentSize);
      }

      // Handle subnormal numbers with gradual underflow
      var (shiftedSig, _, _) = ApplyShiftWithRounding(significand, BigInteger.One - exponent);

      // Check if rounding caused overflow back to smallest normal number
      if (shiftedSig.GetBitLength() == significandSize) {
        return new BigFloat(isNegative, 0, 1, significandSize, exponentSize);
      }

      return new BigFloat(isNegative, shiftedSig, 0, significandSize, exponentSize);
    }

    /// <summary>
    /// Arithmetic operation types for special value handling
    /// </summary>
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
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
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
      var significandValue = IsNormal ? (significand | leadingBit) : significand;
      var shift = (IsNormal ? GetActualExponent() : BigInteger.One) - bias - (SignificandSize - 1);

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
    /// Compares this BigFloat with another BigFloat for ordering purposes.
    /// This method follows the specification for C#'s Single.CompareTo method.
    /// As a result, it handles NaNs differently than how the ==, !=, <, >, <=, and >= operators do.
    /// For example, the expression (0.0f / 0.0f).CompareTo(0.0f / 0.0f) should return 0,
    /// whereas the expression (0.0f / 0.0f) == (0.0f / 0.0f) should return false.
    ///
    /// IMPORTANT: This dual behavior is intentional and correct:
    /// - CompareTo: Provides consistent total ordering for sorting (NaN == NaN returns 0)
    /// - == operator: Follows IEEE 754 mathematical semantics (NaN == NaN returns false)
    ///
    /// This allows collections containing NaN values to be sorted while maintaining
    /// IEEE 754 compliance for mathematical operations.
    /// </summary>
    /// <param name="that">The BigFloat to compare with</param>
    /// <returns>
    /// Less than zero: This instance is less than 'that'
    /// Zero: This instance equals 'that' (including NaN == NaN for ordering)
    /// Greater than zero: This instance is greater than 'that'
    /// </returns>
    public int CompareTo(BigFloat that)
    {
      // Validate size compatibility first
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
      var significandValue = IsNormal ? (significand | leadingBit) : significand;
      var shift = (IsNormal ? GetActualExponent() : BigInteger.One) - bias - (SignificandSize - 1);

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

      // Handle special values
      if (exponent == maxExponent) {
        return $"0{(significand == 0 ? $"{(signBit ? "-" : "+")}oo" : "NaN")}{SignificandSize}e{ExponentSize}";
      }

      // Handle zero
      if (IsZero) {
        return $"{(signBit ? "-" : "")}0x0.0e0f{SignificandSize}e{ExponentSize}";
      }

      // Get significand and binary exponent
      var significandBits = IsSubnormal ? significand : (significand | leadingBit);
      var binaryExp = (IsSubnormal ? BigInteger.One - bias : exponent - bias) - (SignificandSize - 1);

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
        return $"{(signBit ? "-" : "")}0x{hexStr}.0e{hexExp}f{SignificandSize}e{ExponentSize}";
      }

      // Format with decimal point after first digit
      var fracPart = hexStr[1..].TrimEnd('0');
      if (fracPart.Length == 0) {
        fracPart = "0";
      }
      hexExp += hexStr.Length - 1;

      return $"{(signBit ? "-" : "")}0x{hexStr[0]}.{fracPart}e{hexExp}f{SignificandSize}e{ExponentSize}";
    }

    #endregion

    #region String Parsing

    /// <summary>
    /// Tries to parse hex format BigFloat strings according to the specification
    /// </summary>
    /// <param name="s">The hex format string to parse (without size suffixes)</param>
    /// <param name="sigSize">The significand size in bits</param>
    /// <param name="expSize">The exponent size in bits</param>
    /// <param name="strict">When true, enforces Boogie's strict parsing rules (no precision loss, no extreme underflow);
    /// when false, follows IEEE 754 standard behavior</param>
    /// <param name="result">The parsed BigFloat value if successful; default(BigFloat) otherwise</param>
    /// <returns>True if the parse was successful; false otherwise</returns>
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

      // Normal number - check precision loss and normalize
      var shift = new BigInteger(msbPos) - (sigSize - 1);
      if (strict && shift > 0 && shift < sig.GetBitLength() && (sig & GetMask(shift)) != 0) {
        return false;
      }

      // Apply IEEE 754 rounding instead of truncation
      BigInteger roundedSig;
      BigInteger adjustedBiasedExp = biasedExp;

      if (shift > 0) {
        var (shifted, _, overflow) = ApplyShiftWithRounding(sig, shift);
        roundedSig = shifted;

        // Check if rounding caused overflow to next power of 2
        if (overflow) {
          roundedSig >>= 1;
          adjustedBiasedExp++;

          // Check for exponent overflow
          if (adjustedBiasedExp >= GetMaxExponent(expSize)) {
            if (strict) {
              return false;
            }
            result = CreateInfinity(isNegative, sigSize, expSize);
            return true;
          }
        }

        roundedSig &= (GetLeadingBitPower(sigSize) - 1);
      } else {
        roundedSig = BigIntegerMath.RightShift(sig, shift) & (GetLeadingBitPower(sigSize) - 1);
      }

      result = new BigFloat(isNegative, roundedSig, adjustedBiasedExp, sigSize, expSize);
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

    private static bool HandleUnderflow(bool signBit, BigInteger sig, BigInteger biasedExp, int sigSize, int expSize, bool strict, out BigFloat result)
    {
      result = default;
      var bias = GetBias(expSize);
      var minSubnormalExp = BigInteger.One - bias - (sigSize - 1);
      var actualExp = biasedExp - bias;

      // Complete underflow to zero
      if (actualExp < minSubnormalExp) {
        if (strict) {
          return false;
        }
        result = CreateZero(signBit, sigSize, expSize);
        return true;
      }

      // Calculate required shift for subnormal representation
      var currentMsb = sig.GetBitLength() - 1;
      var targetPosition = actualExp - minSubnormalExp;
      var shiftAmount = new BigInteger(currentMsb) - targetPosition;

      // Apply shift with IEEE 754 rounding
      var (subnormalSig, _, _) = ApplyShiftWithRounding(sig, shiftAmount);

      if (subnormalSig.IsZero) {
        if (strict) {
          return false;
        }
        result = CreateZero(signBit, sigSize, expSize);
        return true;
      }

      // Check if rounding caused overflow to normal range
      if (subnormalSig.GetBitLength() > sigSize - 1) {
        if (strict) {
          return false;
        }
        // Overflow to smallest normal number
        result = new BigFloat(signBit, 0, 1, sigSize, expSize);
        return true;
      }

      result = new BigFloat(signBit, subnormalSig, 0, sigSize, expSize);
      return true;
    }

    /// <summary>
    /// Converts to SMT-LIB format string
    /// </summary>
    public string ToSMTLibString() =>
      exponent == maxExponent ?
        $"_ {(significand == 0 ? $"{(signBit ? "-" : "+")}oo" : "NaN")} {ExponentSize} {SignificandSize}" :
        $"fp (_ bv{(signBit ? "1" : "0")} 1) (_ bv{exponent} {ExponentSize}) (_ bv{significand} {SignificandSize - 1})";

    #endregion
  }

  /// <summary>
  /// Helper class for BigInteger arithmetic operations that require shift amounts larger than int.MaxValue
  /// </summary>
  internal static class BigIntegerMath
  {
    /// <summary>
    /// Left shift operation that handles BigInteger shift amounts
    /// </summary>
    /// <param name="value">The value to shift</param>
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

    /// <summary>
    /// Right shift operation that handles BigInteger shift amounts
    /// </summary>
    /// <param name="value">The value to shift</param>
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