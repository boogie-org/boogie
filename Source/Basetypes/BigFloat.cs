//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.Diagnostics;

namespace Microsoft.Basetypes
{
  using BIM = System.Numerics.BigInteger;
    
  /// <summary>
  /// A representation of a 32-bit floating point value
  /// Note that this value has a 1-bit sign, 8-bit exponent, and 24-bit significand
  /// </summary>
  public struct BigFloat
  {
    //Please note that this code outline is copy-pasted from BigDec.cs

    // the internal representation
    internal readonly BIM significand; //Note that the significand arrangement matches standard fp arrangement (most significant bit is farthest left)
    internal readonly int significandSize;
    internal readonly BIM exponent; //The value of the exponent is always positive as per fp representation requirements
    internal readonly int exponentSize; //The bit size of the exponent
    internal readonly String value; //Only used with second syntax
    internal readonly bool isNeg;

    public BIM Significand {
      get {
        return significand;
      }
    }

    public BIM Exponent {
      get {
        return exponent;
      }
    }

    public int SignificandSize {
      get {
        return significandSize;
      }
    }

    public int ExponentSize {
      get {
        return exponentSize;
      }
    }

    public bool IsNegative {
      get {
        return this.isNeg;
      }
    }

    public String Value {
      get {
        return value;
      }
    }

    public static BigFloat ZERO = new BigFloat(false, BIM.Zero, BIM.Zero, 24, 8); //Does not include negative zero

    private static readonly BIM two = new BIM(2);
    private static readonly BIM one = new BIM(1);
    private static BIM two_n(int n) {
      BIM toReturn = one;
      for (int i = 0; i < n; i++)
        toReturn = toReturn * two;
      return toReturn;
    }


    ////////////////////////////////////////////////////////////////////////////
    // Constructors

    //Please note that these constructors will be called throughout boogie
    //For a complete summary of where this class has been added, simply view constructor references

    [Pure]
    public static BigFloat FromInt(int v) {
      return new BigFloat(v.ToString(), 24, 8);
    }

    public static BigFloat FromInt(int v, int significandSize, int exponentSize)
    {
      return new BigFloat(v.ToString(), significandSize, exponentSize);
    }

    public static BigFloat FromBigInt(BIM v) {
      return new BigFloat(v.ToString(), 24, 8);
    }

    public static BigFloat FromBigInt(BIM v, int significandSize, int exponentSize)
    {
      return new BigFloat(v.ToString(), significandSize, exponentSize);
    }

    public static BigFloat FromBigDec(BigDec v)
    {
      return new BigFloat(v.ToDecimalString(), 24, 8);
    }

    public static BigFloat FromBigDec(BigDec v, int significandSize, int exponentSize)
    {
      return new BigFloat(v.ToDecimalString(), significandSize, exponentSize);
    }

    [Pure]
    public static BigFloat FromString(String s) {
      /*
       * String must be either of the format *e*f*e*
       * or of the special value formats: 0NaN*e* 0nan*e* 0+oo*e* 0-oo*e*
       * Where * indicates an integer value (digit)
       */
      BIM sig, exp;
      int sigSize, expSize;
      bool isNeg;

      if (s.IndexOf('f') == -1) {
        String val = s;
        sigSize = int.Parse(s.Substring(4, s.IndexOf('e')-4));
        expSize = int.Parse(s.Substring(s.IndexOf('e') + 1));
        if (sigSize <= 0 || expSize <= 0)
          throw new FormatException("Significand and Exponent sizes must be greater than 0");
        return new BigFloat(val, sigSize, expSize);
      }

      sig = BIM.Parse(s.Substring(0, s.IndexOf('e')));
      exp = BIM.Parse(s.Substring(s.IndexOf('e') + 1, s.IndexOf('f') - s.IndexOf('e') - 1));
      sigSize = int.Parse(s.Substring(s.IndexOf('f') + 1, s.IndexOf('e', s.IndexOf('e') + 1) - s.IndexOf('f') - 1));
      expSize = int.Parse(s.Substring(s.IndexOf('e', s.IndexOf('e') + 1) + 1));
      isNeg = s[0] == '-'; //We do this so that -0 is parsed correctly
      
      if (sigSize <= 0 || expSize <= 0)
        throw new FormatException("Significand and Exponent sizes must be greater than 0");

      sigSize = sigSize - 1; //Get rid of sign bit
      sig = BIM.Abs(sig); //sig must be positive
      //Uncomment if you want to shift the exponent for the user (i.e. 0e-1f24e8 --> 0e126f24e8)
      //exp = exp + BIM.Pow(new BIM(2), expSize-1) - BIM.One;

      if (exp < 0 || exp >= BIM.Pow(new BIM(2), expSize))
        throw new FormatException("The given exponent " + exp + " cannot fit in the bit size " + expSize);

      if (sig >= BIM.Pow(new BIM(2), sigSize))
        throw new FormatException("The given significand " + sig + " cannot fit in the bit size " + (sigSize+1));

      return new BigFloat(isNeg, sig, exp, sigSize, expSize);
    }

    public BigFloat(bool isNeg, BIM significand, BIM exponent, int significandSize, int exponentSize) {
      this.exponentSize = exponentSize;
      this.exponent = exponent;
      this.significand = significand;
      this.significandSize = significandSize+1;
      this.isNeg = isNeg;
      this.value = "";
    }

    public BigFloat(String value, int significandSize, int exponentSize) {
      this.exponentSize = exponentSize;
      this.significandSize = significandSize;
      this.exponent = BIM.Zero;
      this.significand = BIM.Zero;
      this.value = value;
      if (value.Equals("nan"))
        this.value = "NaN";
      this.isNeg = value[0] == '-';
    }

    private BIM maxsignificand()
    {
      BIM result = one;
      for (int i = 0; i < significandSize; i++)
        result = result * two;
      return result - one;
    }
    private int maxExponent() { return (int)Math.Pow(2, exponentSize) - 1; }



    ////////////////////////////////////////////////////////////////////////////
    // Basic object operations

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is BigFloat))
        return false;

      return (this == (BigFloat)obj);
    }

    [Pure]
    public override int GetHashCode() {
      return significand.GetHashCode() * 13 + Exponent.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return value=="" ? String.Format("{0}x2^{1}", significand.ToString(), Exponent.ToString()) : value;
    }


    ////////////////////////////////////////////////////////////////////////////
    // Conversion operations

    /// <summary>
    /// NOTE: THIS METHOD MAY NOT WORK AS EXPECTED!!!
    /// Converts the given decimal value (provided as a string) to the nearest floating point approximation
    /// the returned fp assumes the given significand and exponent size
    /// </summary>
    /// <param name="value"></param>
    /// <param name="significandSize"></param>
    /// <param name="exponentSize"></param>
    /// <returns></returns>
    public static BigFloat Round(String value, int exponentSize, int significandSize)
    {
      int i = value.IndexOf('.');
      if (i == -1)
        return Round(BIM.Parse(value), BIM.Zero, exponentSize, significandSize);
      return Round(i == 0 ? BIM.Zero : BIM.Parse(value.Substring(0, i)), BIM.Parse(value.Substring(i + 1, value.Length - i - 1)), exponentSize, significandSize);
    }

    /// <summary>
    /// NOTE:  THIS METHOD MAY NOT WORK AS EXPECTED!!!!
    /// Converts value.dec_value to a the closest float approximation with the given significandSize, exponentSize
    /// Returns the result of this calculation
    /// </summary>
    /// <param name="value"></param>
    /// <param name="power"></param>
    /// <param name="significandSize"></param>
    /// <param name="exponentSize"></param>
    /// <returns></returns>
    public static BigFloat Round(BIM value, BIM dec_value, int exponentSize, int significandSize)
    {
      int exp = 0;
      BIM one = new BIM(1);
      BIM ten = new BIM(10);
      BIM dec_max = new BIM(0); //represents the order of magnitude of dec_value for carrying during calculations

      //First, determine the exponent
      while (value > one) { //Divide by two, increment exponent by 1
        if (!(value % two).IsZero) { //Add "1.0" to the decimal
          dec_max = new BIM(10);
          while (dec_max < dec_value)
            dec_max = dec_max * ten;
          dec_value = dec_value + dec_max;
        }
        value = value / two;
        if (!(dec_value % ten).IsZero)
          dec_value = dec_value * ten; //Creates excess zeroes to avoid losing data during division
        dec_value = dec_value / two;
        exp++;
      }
      if (value.IsZero && !dec_value.IsZero) {
        dec_max = new BIM(10);
        while (dec_max < dec_value)
          dec_max = dec_max * ten;
        while (value.IsZero) {//Multiply by two, decrement exponent by 1
          dec_value = dec_value * two;
          if (dec_value >= dec_max) {
            dec_value = dec_value - dec_max;
            value = value + one;
          }
          exp--;
        }
      }

      //Second, calculate the significand
      value = new BIM(0); //remove implicit bit
      dec_max = new BIM(10);
      while (dec_max < dec_value)
        dec_max = dec_max * ten;
      for (int i = significandSize; i > 0 && !dec_value.IsZero; i--) { //Multiply by two until the significand is fully calculated
        dec_value = dec_value * two;
        if (dec_value >= dec_max) {
          dec_value = dec_value - dec_max;
          value = value + two_n(i); //Note that i is decrementing so that the most significant bit is left-most in the representation
        }
      }

      return new BigFloat(false, BIM.Zero, BIM.Parse(value.ToString()), exponentSize, significandSize); //Sign not actually checked...
    }

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// NOTE:  This may give wrong results, it hasn't been tested extensively
    /// If you're getting weird bugs, you may want to check this function out...
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// </summary>
    /// <param name="floor">The Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BIM floor, out BIM ceiling)
    {
      BIM two = new BIM(2);

      BIM sig = Significand + BIM.Pow(two, SignificandSize); //Add hidden bit
      BIM exp = Exponent - BIM.Pow(two, ExponentSize-1) + 1;

      while (exp > BIM.Zero) {
        exp--;
        sig = sig << 1;
      }

      sig = sig >> SignificandSize;

      if (isNeg) {
        ceiling = -sig + 1;
        floor = -sig;
      }
      else {
        ceiling = sig + 1;
        floor = sig;
      }
    }

    [Pure]
    public String ToDecimalString(int maxDigits) {
      //TODO: fix for fp functionality 
      {
        throw new NotImplementedException();
      }
    }

    public String ToBVString(){
      if (this.IsSpecialType) {
        return "_ " + this.value + " " + this.exponentSize + " " + this.significandSize;
      }
      else if (this.Value == "") {
        return "fp (_ bv" + (this.isNeg ? "1" : "0") + " 1) (_ bv" + this.exponent + " " + this.exponentSize + ") (_ bv" + this.significand + " " + (this.significandSize-1) + ")";
      }
      else {
        return "(_ to_fp " + this.exponentSize + " " + this.significandSize + ") (_ bv" + this.value + " " + (this.exponentSize + this.significandSize).ToString() + ")";
      }
    }

    [Pure]
    public string ToDecimalString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return value=="" ? String.Format("{0}x2^{1}", significand.ToString(), Exponent.ToString()) : value;
    }

    [Pure]
    public static string Zeros(int n) {
      //TODO: fix for fp functionality
      Contract.Requires(0 <= n);
      if (n <= 10) {
        var tenZeros = "0000000000";
        return tenZeros.Substring(0, n);
      } else {
        var d = n / 2;
        var s = Zeros(d);
        if (n % 2 == 0) {
          return s + s;
        } else {
          return s + s + "0";
        }
      }
    }


    ////////////////////////////////////////////////////////////////////////////
    // Basic arithmetic operations

    [Pure]
    public BigFloat Abs {
      get {
        return new BigFloat(true, Significand, Exponent, SignificandSize, ExponentSize);
      }
    }

    [Pure]
    public BigFloat Negate {
      get {
        if (value != "")
          return value[0] == '-' ? new BigFloat(value.Remove(0, 1), significandSize, ExponentSize) : new BigFloat("-" + value, significandSize, ExponentSize);
        return new BigFloat(!isNeg, Significand, Exponent, SignificandSize, ExponentSize);
      }
    }

    [Pure]
    public static BigFloat operator -(BigFloat x) {
      return x.Negate;
    }

    [Pure]
    public static BigFloat operator +(BigFloat x, BigFloat y) {
      //TODO: Modify for correct fp functionality
      Contract.Requires(x.ExponentSize == y.ExponentSize);
      Contract.Requires(x.SignificandSize == y.SignificandSize);
      BIM m1 = x.significand;
      BIM e1 = x.Exponent;
      BIM m2 = y.significand;
      BIM e2 = y.Exponent;
      m1 = m1 + two_n(x.significandSize + 1); //Add implicit bit
      m2 = m2 + two_n(y.significandSize + 1);
      if (e2 > e1) {
        m1 = y.significand;
        e1 = y.Exponent;
        m2 = x.significand;
        e2 = x.Exponent;
      }

      while (e2 < e1) {
        m2 = m2 / two;
        e2 = e2 + one;
      }

      return new BigFloat(false, e1, m1 + m2, x.significandSize, x.ExponentSize);
    }

    [Pure]
    public static BigFloat operator -(BigFloat x, BigFloat y) {
      return x + y.Negate;
    }

    [Pure]
    public static BigFloat operator *(BigFloat x, BigFloat y) {
      Contract.Requires(x.ExponentSize == y.ExponentSize);
      Contract.Requires(x.SignificandSize == y.SignificandSize);
      return new BigFloat(x.isNeg ^ y.isNeg, x.significand * y.significand, x.Exponent + y.Exponent, x.significandSize, x.ExponentSize);
    }


    ////////////////////////////////////////////////////////////////////////////
    // Some basic comparison operations

    public bool IsSpecialType {
      get {
        if (value == "")
          return false;
        return (value.Equals("NaN") || value.Equals("+oo") || value.Equals("-oo") || value.Equals("zero") || value.Equals("-zero"));
      }
    }

    public bool IsPositive {
      get {
        return !IsNegative;
      }
    }

    public bool IsZero {
      get {
        return significand.Equals(BigNum.ZERO) && Exponent == BIM.Zero;
      }
    }

    [Pure]
    public int CompareTo(BigFloat that) {
      if (this.exponent > that.exponent)
        return 1;
      if (this.exponent < that.exponent)
        return -1;
      if (this.significand == that.significand)
        return 0;
      return this.significand > that.significand ? 1 : -1;
    }

    [Pure]
    public static bool operator ==(BigFloat x, BigFloat y) {
      return x.CompareTo(y) == 0;
    }

    [Pure]
    public static bool operator !=(BigFloat x, BigFloat y) {
      return x.CompareTo(y) != 0;
    }

    [Pure]
    public static bool operator <(BigFloat x, BigFloat y) {
      return x.CompareTo(y) < 0;
    }

    [Pure]
    public static bool operator >(BigFloat x, BigFloat y) {
      return x.CompareTo(y) > 0;
    }

    [Pure]
    public static bool operator <=(BigFloat x, BigFloat y) {
      return x.CompareTo(y) <= 0;
    }

    [Pure]
    public static bool operator >=(BigFloat x, BigFloat y) {
      return x.CompareTo(y) >= 0;
    }
  }
}
