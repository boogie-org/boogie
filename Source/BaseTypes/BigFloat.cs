using System;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.BaseTypes
{
  /// <summary>
  /// A representation of a floating-point value using IEEE 754 format.
  /// Note that this value has a 1-bit sign, along with an exponent and significand whose sizes must be greater than 1.
  /// Uses IEEE 754 representation internally with configurable significand and exponent sizes.
  /// </summary>
  public readonly struct BigFloat
  {
    #region Fields and Properties

    // IEEE 754 representation fields
    private readonly BigInteger significand;    // Mantissa bits (without hidden bit for normal numbers)
    private readonly BigInteger exponent;       // Biased exponent value
    private readonly bool signBit;              // Sign bit: true = negative, false = positive

    // Cached values for performance
    private readonly BigInteger bias;           // Exponent bias value
    private readonly BigInteger maxExponent;    // Maximum exponent value
    private readonly BigInteger hiddenBit;      // Hidden bit power value

    public int SignificandSize { get; }         // Total bits for significand (including hidden bit)
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
    /// <param name="significand">The significand bits (without hidden bit for normal numbers)</param>
    /// <param name="exponent">The biased exponent value</param>
    /// <param name="significandSize">Total bits for significand (including hidden bit)</param>
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

        var sigBitLength = significand.GetBitLength();
        if (sigBitLength > significandSize) {
          throw new ArgumentException($"Significand requires {sigBitLength} bits but only {significandSize} declared. This creates inconsistent internal state.", nameof(significand));
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
      this.maxExponent = GetMaxExponent(exponentSize);
      hiddenBit = GetHiddenBitPower(significandSize);
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

      s = s.Trim();

      // Parse size specifiers: f[sigSize]e[expSize]
      var posLastE = s.LastIndexOf('e');
      if (posLastE == -1 || !int.TryParse(s[(posLastE + 1)..], out var exponentSize)) {
        return false;
      }

      // Extract significand size
      var posLastF = s.LastIndexOf('f');
      var sigSizeStart = posLastF == -1 ? 4 : posLastF + 1;  // Special values start at 4, normal after 'f'

      if (sigSizeStart >= posLastE ||
          !int.TryParse(s[sigSizeStart..posLastE], out var significandSize) ||
          !TryValidateSizeParameters(significandSize, exponentSize)) {
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
      var scaleBits = Math.Max(0, significandSize + 3 + (int)denominator.GetBitLength() - (int)numerator.GetBitLength());
      var quotient = BigInteger.DivRem(numerator << scaleBits, denominator, out var remainder);

      // Apply rounding if inexact
      var isExact = remainder.IsZero;
      if (!isExact) {
        quotient = ApplyRoundToNearestEven(quotient, remainder, denominator);
      }

      // Calculate exponent
      var quotientBits = (int)quotient.GetBitLength();
      var biasedExp = GetBias(exponentSize) + quotientBits - scaleBits - 1;

      // Handle overflow
      if (biasedExp > ((1 << exponentSize) - 2)) {
        result = CreateInfinity(isNegative, significandSize, exponentSize);
        return false;
      }

      // Handle underflow/subnormal
      if (biasedExp <= 0) {
        if (biasedExp > -significandSize) {
          // Subnormal - shift right to fit
          var (shifted, _) = ApplyShiftWithRounding(quotient, 1 - (int)biasedExp);
          var excess = (int)shifted.GetBitLength() - significandSize;
          if (excess > 0) {
            shifted >>= excess;
          }
          result = new BigFloat(isNegative, shifted, 0, significandSize, exponentSize);
          return isExact;
        }
        // Complete underflow
        result = CreateZero(isNegative, significandSize, exponentSize);
        return false;
      }

      // Normal number - normalize significand
      var shift = quotientBits - significandSize;
      if (shift > 0) {
        var (shifted, wasExact) = ApplyShiftWithRounding(quotient, shift);
        quotient = shifted;
        isExact &= wasExact;
      }

      result = new BigFloat(isNegative, quotient & (GetHiddenBitPower(significandSize) - 1), biasedExp, significandSize, exponentSize);
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

    /// <summary>
    /// Validates that significand and exponent sizes meet minimum requirements (must be > 1)
    /// </summary>
    /// <param name="significandSize">The size of the significand in bits</param>
    /// <param name="exponentSize">The size of the exponent in bits</param>
    private static void ValidateSizeParameters(int significandSize, int exponentSize)
    {
      if (!TryValidateSizeParameters(significandSize, exponentSize)) {
        if (significandSize <= 1) {
          throw new ArgumentException($"Significand size must be greater than 1, got {significandSize}", nameof(significandSize));
        }
        throw new ArgumentException($"Exponent size must be greater than 1, got {exponentSize}", nameof(exponentSize));
      }
    }

    /// <summary>
    /// Validates that significand and exponent sizes meet minimum requirements (must be > 1)
    /// </summary>
    /// <param name="significandSize">The size of the significand in bits</param>
    /// <param name="exponentSize">The size of the exponent in bits</param>
    /// <returns>True if the sizes are valid; false otherwise</returns>
    private static bool TryValidateSizeParameters(int significandSize, int exponentSize)
    {
      return significandSize > 1 && exponentSize > 1;
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
    /// Gets the actual (unbiased) exponent, handling subnormal numbers correctly
    /// </summary>
    private int GetActualExponent() => exponent == 0 ? 1 : (int)exponent;

    private static (BigInteger significand, int exponent) PrepareOperand(BigFloat operand, BigInteger hiddenBit)
    {
      var sig = operand.significand;
      var exp = operand.GetActualExponent();
      if (operand.exponent > 0) {
        sig |= hiddenBit;
      }
      return (sig, exp);
    }

    /// <summary>
    /// Prepares operands for multiplication/division operations (with combined sign calculation)
    /// </summary>
    private static ((BigInteger sig, int exp) x, (BigInteger sig, int exp) y, bool resultSign) PrepareOperandsForMultDiv(BigFloat x, BigFloat y)
    {
      var hiddenBit = x.hiddenBit;
      var resultSign = x.signBit ^ y.signBit;
      var (xSig, xExp) = PrepareOperand(x, hiddenBit);
      var (ySig, yExp) = PrepareOperand(y, hiddenBit);

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

    private static BigInteger GetMask(int bits) => (BigInteger.One << bits) - 1;

    private static (BigInteger result, bool isExact) ApplyShiftWithRounding(BigInteger value, int shift)
    {
      // Handle left shifts (no rounding needed)
      if (shift <= 0) {
        return (value << -shift, true);
      }

      // Right shift with round-to-nearest-even
      var mask = GetMask(shift);
      var lostBits = value & mask;
      var result = value >> shift;

      // If no bits lost, result is exact
      if (lostBits == 0) {
        return (result, true);
      }

      // Round to nearest even - correct IEEE 754 behavior
      var half = BigInteger.One << (shift - 1);
      if (lostBits > half || (lostBits == half && !result.IsEven)) {
        result++;
      }

      return (result, false);
    }

    // Public convenience methods for special values
    public static BigFloat CreateZero(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, 0, 0, significandSize, exponentSize, true);
    public static BigFloat CreateInfinity(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, 0, GetMaxExponent(exponentSize), significandSize, exponentSize);
    public static BigFloat CreateNaN(bool isNegative, int significandSize, int exponentSize) =>
      new (isNegative, GetSignificandMask(significandSize), GetMaxExponent(exponentSize), significandSize, exponentSize);

    /// <summary>
    /// Creates special values from string representation for SMT-LIB integration.
    /// Supports: "NaN", "+oo", "-oo" (case insensitive)
    /// </summary>
    /// <param name="specialValue">Special value string ("NaN", "+oo", "-oo")</param>
    /// <param name="sigSize">Significand size in bits</param>
    /// <param name="expSize">Exponent size in bits</param>
    /// <returns>BigFloat representing the special value</returns>
    /// <exception cref="ArgumentException">Thrown when specialValue is not supported</exception>
    public static BigFloat CreateSpecialFromString(string specialValue, int sigSize, int expSize) {
      if (TryCreateSpecialFromString(specialValue, sigSize, expSize, out var result)) {
        return result;
      }
      throw new ArgumentException($"Unknown special value: '{specialValue}'", nameof(specialValue));
    }

    /// <summary>
    /// Tries to create special values from string representation for SMT-LIB integration.
    /// Supports: "NaN", "+oo", "-oo" (case insensitive)
    /// </summary>
    /// <param name="specialValue">Special value string ("NaN", "+oo", "-oo")</param>
    /// <param name="sigSize">Significand size in bits</param>
    /// <param name="expSize">Exponent size in bits</param>
    /// <param name="result">The resulting BigFloat if successful; default(BigFloat) otherwise</param>
    /// <returns>True if the special value was recognized and created; false otherwise</returns>
    private static bool TryCreateSpecialFromString(string specialValue, int sigSize, int expSize, out BigFloat result) {
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
    public static BigInteger GetHiddenBitPower(int significandSize) => BigInteger.One << (significandSize - 1);
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

      // Handle special values and zeros
      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Addition);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      if (x.IsZero) {
        return y;
      }

      if (y.IsZero) {
        return x;
      }

      // Prepare operands with sign
      var (xSig, xExp) = PrepareOperand(x, x.hiddenBit);
      var (ySig, yExp) = PrepareOperand(y, y.hiddenBit);
      if (x.signBit) {
        xSig = -xSig;
      }

      if (y.signBit) {
        ySig = -ySig;
      }

      // Return larger operand if difference is too large
      // +3 accounts for possible carry bits and rounding during addition
      var expDiff = xExp - yExp;
      if (Math.Abs(expDiff) > x.SignificandSize + 3) {
        return expDiff > 0 ? x : y;
      }

      // Align and add
      var sum = expDiff == 0 ? xSig + ySig :
                expDiff > 0 ? xSig + (ySig >> expDiff) :
                              (xSig >> -expDiff) + ySig;
      var resultExp = Math.Max(xExp, yExp);

      // Handle zero sum
      if (sum == 0) {
        return CreateZero(x.signBit && y.signBit, x.SignificandSize, x.ExponentSize);
      }

      // Normalize and create result
      var isNegative = sum < 0;
      if (isNegative) {
        sum = -sum;
      }

      var (normSig, normExp) = NormalizeAndRound(sum, resultExp, x.SignificandSize);
      return HandleExponentBounds(normSig, normExp, isNegative, x.SignificandSize, x.ExponentSize);
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
      var (normalizedProduct, normalShift) = NormalizeAndRound(product, 0, x.SignificandSize);

      // Calculate the final exponent
      var bias = x.bias;
      var resultExp = xExp + yExp - (int)bias + normalShift - (x.SignificandSize - 1);

      // Handle overflow, underflow, and create final result
      return HandleExponentBounds(normalizedProduct, resultExp, resultSign, x.SignificandSize, x.ExponentSize);
    }

    [Pure]
    public static BigFloat operator /(BigFloat x, BigFloat y)
    {
      ValidateSizeCompatibility(x, y);

      // Handle all special cases (NaN, infinity, zero)
      var specialResult = HandleSpecialValues(x, y, ArithmeticOperation.Division);
      if (specialResult.HasValue) {
        return specialResult.Value;
      }

      // Prepare operands and calculate result sign
      var ((xSig, xExp), (ySig, yExp), resultSign) = PrepareOperandsForMultDiv(x, y);

      // For division, we need extra precision to ensure accurate rounding
      // Shift dividend left by significandSize + 1 bits to maintain precision
      var shiftedDividend = xSig << (x.SignificandSize + 1);
      var quotient = shiftedDividend / ySig;
      var remainder = shiftedDividend % ySig;

      // Apply rounding if needed
      quotient = ApplyRoundToNearestEven(quotient, remainder, ySig);

      // Check for zero result
      if (quotient == 0) {
        return CreateZero(resultSign, x.SignificandSize, x.ExponentSize);
      }

      // Normalize and round the quotient
      var (normalizedQuotient, normalShift) = NormalizeAndRound(quotient, 0, x.SignificandSize);

      // Calculate the final exponent
      // Division inherently gives us xExp - yExp, and we need to adjust for the shift we applied
      var bias = x.bias;
      var resultExp = xExp - yExp + (int)bias + normalShift - 2;

      // Handle overflow, underflow, and create final result
      return HandleExponentBounds(normalizedQuotient, resultExp, resultSign, x.SignificandSize, x.ExponentSize);
    }

    private static (BigInteger significand, int exponent) NormalizeAndRound(BigInteger value, int exponent, int targetBits)
    {
      var valueBits = (int)value.GetBitLength();
      var shift = valueBits - targetBits;

      // Use IEEE 754 compliant shift and round method
      var (shiftedValue, _) = ApplyShiftWithRounding(value, shift);
      var adjustedExponent = exponent + shift;

      // Handle potential overflow from rounding (only for right shifts)
      if (shift > 0 && (int)shiftedValue.GetBitLength() > targetBits) {
        shiftedValue >>= 1;
        adjustedExponent++;
      }

      return (shiftedValue, adjustedExponent);
    }

    private static BigFloat HandleExponentBounds(BigInteger significand, int exponent, bool isNegative, int significandSize, int exponentSize)
    {
      // Check overflow
      if (exponent > ((1 << exponentSize) - 2)) {
        return CreateInfinity(isNegative, significandSize, exponentSize);
      }

      // Handle underflow/subnormal
      if (exponent <= 0) {
        // Too small even for subnormal
        if (exponent <= -significandSize) {
          return CreateZero(isNegative, significandSize, exponentSize);
        }

        // Create subnormal
        var (shiftedSig, _) = ApplyShiftWithRounding(significand, 1 - exponent);

        // Handle rounding overflow
        if (shiftedSig.GetBitLength() > significandSize) {
          shiftedSig >>= 1;
        }

        return new BigFloat(isNegative, shiftedSig, 0, significandSize, exponentSize);
      }

      // Normal number - mask hidden bit
      return new BigFloat(isNegative, significand & (GetHiddenBitPower(significandSize) - 1), exponent, significandSize, exponentSize);
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
      var mantissaValue = IsNormal ? (significand | hiddenBit) : significand;
      var shift = (IsNormal ? GetActualExponent() : 1) - (int)bias - (SignificandSize - 1);

      BigInteger integerPart;
      bool hasRemainder;

      if (shift >= 0) {
        integerPart = mantissaValue << shift;
        hasRemainder = false;
      } else if (-shift >= SignificandSize) {
        integerPart = 0;
        hasRemainder = true;
      } else {
        integerPart = mantissaValue >> -shift;
        hasRemainder = (mantissaValue & ((BigInteger.One << -shift) - 1)) != 0;
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
    /// <summary>
    /// Converts the BigFloat to a decimal string representation.
    /// </summary>
    /// <returns>A decimal string representation of the value</returns>
    public string ToDecimalString()
    {
      // Handle special values per IEEE 754-2019 Section 5.12.1
      if (IsNaN) {
        return "NaN";
      }
      if (IsInfinity) {
        return signBit ? "-Infinity" : "Infinity";
      }
      if (IsZero) {
        return signBit ? "-0" : "0";
      }

      // Convert binary float to rational number
      var mantissaValue = IsNormal ? (significand | hiddenBit) : significand;
      var shift = (IsNormal ? GetActualExponent() : 1) - (int)bias - (SignificandSize - 1);

      BigInteger numerator, denominator;
      if (shift >= 0) {
        numerator = signBit ? -(mantissaValue << shift) : mantissaValue << shift;
        denominator = BigInteger.One;
      } else {
        numerator = signBit ? -mantissaValue : mantissaValue;
        denominator = BigInteger.One << -shift;
      }

      // Convert to decimal string with appropriate scale
      var scale = Math.Max(0, (int)(denominator.GetBitLength() * 0.31));
      var scaled = BigInteger.Abs(numerator * BigInteger.Pow(10, scale) / denominator);
      var str = scaled.ToString().PadLeft(scale + 1, '0');

      // Format with decimal point
      var result = str[..^scale] + (scale > 0 ? "." + str[^scale..].TrimEnd('0') : "");
      return numerator < 0 ? "-" + result.TrimEnd('.') : result.TrimEnd('.');
    }

    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      if (exponent == maxExponent) {
        return $"0{(significand == 0 ? $"{(signBit ? "-" : "+")}oo" : "NaN")}{SignificandSize}e{ExponentSize}";
      }

      // Format as hex string
      if (IsZero) {
        return $"{(signBit ? "-" : "")}0x0.0e0f{SignificandSize}e{ExponentSize}";
      }

      // Get mantissa with hidden bit and actual exponent
      var mantissa = exponent == 0 ? significand : significand | hiddenBit;
      var binaryExp = GetActualExponent() - (int)bias - (SignificandSize - 1);

      // Calculate hex alignment
      var mantissaHex = mantissa.ToString("X");
      var totalShift = binaryExp + 4 * (mantissaHex.Length - 1);
      var hexExp = Math.DivRem(totalShift, 4, out var remainder);

      // Realign if needed
      if (remainder != 0) {
        mantissa <<= remainder > 0 ? remainder : 4 + remainder;
        hexExp -= remainder < 0 ? 1 : 0;
        mantissaHex = mantissa.ToString("X");
      }

      // Format as x.y
      var hex = mantissaHex.TrimStart('0');
      if (string.IsNullOrEmpty(hex)) {
        hex = "0";
      }

      var frac = hex.Length > 1 ? hex[1..].TrimEnd('0') : "";
      var formatted = $"{hex[0]}.{(string.IsNullOrEmpty(frac) ? "0" : frac)}";

      return $"{(signBit ? "-" : "")}0x{formatted}e{hexExp}f{SignificandSize}e{ExponentSize}";
    }

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

      // Find key positions: [-]0x<hex>.<hex>e<dec>
      var posX = s.IndexOf('x');
      var posE = s.LastIndexOf('e');
      if (posX < 0 || posE <= posX) {
        return false;
      }

      // Extract hex parts
      var hexPart = s[(posX + 1)..posE];
      var dotPos = hexPart.IndexOf('.');
      if (dotPos < 0) {
        return false;
      }

      // Parse components
      if (!TryParseHex(hexPart[..dotPos], out var intPart) ||
          !TryParseHex(hexPart[(dotPos + 1)..], out var fracPart) ||
          !int.TryParse(s[(posE + 1)..], out var decExp)) {
        return false;
      }

      // Build significand
      var fracBits = (hexPart.Length - dotPos - 1) * 4;
      var sig = (intPart << fracBits) | fracPart;
      if (sig == 0) {
        result = CreateZero(s[0] == '-', sigSize, expSize);
        return true;
      }

      // Calculate exponent
      var msbPos = (int)sig.GetBitLength() - 1;
      var biasedExp = msbPos - fracBits + (decExp * 4) + (int)GetBias(expSize);

      // Handle overflow
      if (biasedExp >= GetMaxExponent(expSize)) {
        return false;
      }

      // Handle underflow/subnormal
      if (biasedExp <= 0) {
        return HandleUnderflow(s[0] == '-', sig, biasedExp, sigSize, expSize, strict, out result);
      }

      // Normal number
      var shift = msbPos - (sigSize - 1);
      if (strict && shift > 0 && (sig & GetMask(shift)) != 0) {
        return false;
      }

      var normalizedSig = shift >= 0 ? sig >> shift : sig << (-shift);
      result = new BigFloat(s[0] == '-', normalizedSig & (GetHiddenBitPower(sigSize) - 1), biasedExp, sigSize, expSize);
      return true;
    }

    private static bool TryParseHex(string hex, out BigInteger value)
    {
      value = 0;
      return hex.Length == 0 || BigInteger.TryParse("0" + hex, System.Globalization.NumberStyles.HexNumber, null, out value);
    }

    private static bool HandleUnderflow(bool signBit, BigInteger sig, int biasedExp, int sigSize, int expSize, bool strict, out BigFloat result)
    {
      result = default;
      var bias = GetBias(expSize);
      var actualExp = biasedExp - (int)bias;

      // Check if value is too small to represent
      if (actualExp < 1 - (int)bias - (sigSize - 1)) {
        if (strict) {
          return false;
        }
        result = CreateZero(signBit, sigSize, expSize);
        return true;
      }

      // Calculate shift for subnormal representation
      var msbPos = (int)sig.GetBitLength() - 1;
      var shiftAmount = (1 - (int)bias) - actualExp + msbPos;

      // Apply shift and check result
      var subnormalSig = shiftAmount > 0 ? sig >> shiftAmount : sig << (-shiftAmount);
      if (subnormalSig == 0 || subnormalSig.GetBitLength() > sigSize - 1) {
        if (strict) {
          return false;
        }
        result = CreateZero(signBit, sigSize, expSize);
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
}