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
    [Rep]
    internal readonly BigNum significand; //Note that the significand arrangement matches standard fp arrangement (most significant bit is farthest left)
    [Rep]
    internal readonly int significandSize;
    [Rep]
    internal readonly BigNum exponent; //The value of the exponent is always positive as per fp representation requirements
    [Rep]
    internal readonly int exponentSize; //The bit size of the exponent
    [Rep]
    internal readonly String value; //Only used with second syntax
    [Rep]
    internal readonly bool isNeg;

    public BigNum Significand {
      get {
        return significand;
      }
    }

    public BigNum Exponent {
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

    public static BigFloat ZERO(int exponentSize, int significandSize) { return new BigFloat(false, BigNum.ZERO, BigNum.ZERO, exponentSize, significandSize); } //Does not include negative zero

    private static readonly BigNum two = new BigNum(2);
    private static readonly BigNum one = new BigNum(1);
    private static BigNum two_n(int n) {
      BigNum toReturn = one;
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
      return new BigFloat(v.ToString(), 8, 24);
    }

    public static BigFloat FromInt(int v, int exponentSize, int significandSize)
    {
      return new BigFloat(v.ToString(), exponentSize, significandSize);
    }

    public static BigFloat FromBigInt(BIM v) {
      return new BigFloat(v.ToString(), 8, 24);
    }

    public static BigFloat FromBigInt(BIM v, int exponentSize, int significandSize)
    {
      return new BigFloat(v.ToString(), exponentSize, significandSize);
    }

    public static BigFloat FromBigDec(BigDec v)
    {
      return new BigFloat(v.ToDecimalString(), 8, 24);
    }

    public static BigFloat FromBigDec(BigDec v, int exponentSize, int significandSize)
    {
      return new BigFloat(v.ToDecimalString(), exponentSize, significandSize);
    }

    [Pure]
    public static BigFloat FromString(String v, int exp, int sig) { //String must be
      return new BigFloat(v, exp, sig);
    }

    public BigFloat(bool sign, BigNum exponent, BigNum significand, int exponentSize, int significandSize) {
      this.exponentSize = exponentSize;
      this.exponent = exponent;
      this.significand = significand;
      this.significandSize = significandSize+1;
      this.isNeg = sign;
      this.value = "";
    }

    public BigFloat(String value, int exponentSize, int significandSize) {
      this.exponentSize = exponentSize;
      this.significandSize = significandSize;
      this.exponent = BigNum.ZERO;
      this.significand = BigNum.ZERO;
      this.value = value;
      this.isNeg = value[0] == '-';
    }

    private BigNum maxsignificand()
    {
      BigNum result = one;
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
        return Round(BigNum.FromString(value), BigNum.ZERO, exponentSize, significandSize);
      return Round(i == 0 ? BigNum.ZERO : BigNum.FromString(value.Substring(0, i)), BigNum.FromString(value.Substring(i + 1, value.Length - i - 1)), exponentSize, significandSize);
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
    public static BigFloat Round(BigNum value, BigNum dec_value, int exponentSize, int significandSize)
    {
      int exp = 0;
      BigNum one = new BigNum(1);
      BigNum ten = new BigNum(10);
      BigNum dec_max = new BigNum(0); //represents the order of magnitude of dec_value for carrying during calculations

      //First, determine the exponent
      while (value > one) { //Divide by two, increment exponent by 1
        if (!(value % two).IsZero) { //Add "1.0" to the decimal
          dec_max = new BigNum(10);
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
        dec_max = new BigNum(10);
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
      value = new BigNum(0); //remove implicit bit
      dec_max = new BigNum(10);
      while (dec_max < dec_value)
        dec_max = dec_max * ten;
      for (int i = significandSize; i > 0 && !dec_value.IsZero; i--) { //Multiply by two until the significand is fully calculated
        dec_value = dec_value * two;
        if (dec_value >= dec_max) {
          dec_value = dec_value - dec_max;
          value = value + two_n(i); //Note that i is decrementing so that the most significant bit is left-most in the representation
        }
      }

      return new BigFloat(false, BigNum.ZERO, BigNum.FromString(value.ToString()), exponentSize, significandSize); //Sign not actually checked...
    }

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// NOTE:  THIS PROBABLY WON'T GIVE USEFUL OUTPUT!!!
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// </summary>
    /// <param name="floor">The Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BigNum floor, out BigNum ceiling) {
      //TODO: fix for fp functionality
      BigNum n = Significand;
      BigNum e = Exponent;
      if (n.IsZero) {
        floor = ceiling = n;
      } else if (BigNum.ZERO <= e) {
        // it's an integer
        for (; BigNum.ZERO < e; e = e - one)
        {
          n = n * two;
        }
        floor = ceiling = n;
      } else {
        // it's a non-zero integer, so the ceiling is one more than the floor
        for (; BigNum.ZERO < e && !n.IsZero; e = e + one)
        {
          n = n / two;  // Division rounds towards negative infinity
        }

        if (!IsNegative) {
          floor = n;
          ceiling = n + one;
        } else {
          ceiling = n;
          floor = n - one;
        }
      }
      Debug.Assert(floor <= ceiling, "Invariant was not maintained");
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
        return new BigFloat(true, Exponent, Significand, ExponentSize, SignificandSize);
      }
    }

    [Pure]
    public BigFloat Negate {
      get {
        if (value != "")
          return value[0] == '-' ? new BigFloat(value.Remove(0, 1), ExponentSize, significandSize) : new BigFloat("-" + value, ExponentSize, significandSize);
        return new BigFloat(!isNeg, Exponent, Significand, ExponentSize, SignificandSize);
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
      Contract.Requires(x.significandSize == y.significandSize);
      BigNum m1 = x.significand;
      BigNum e1 = x.Exponent;
      BigNum m2 = y.significand;
      BigNum e2 = y.Exponent;
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
      Contract.Requires(x.significandSize == y.significandSize);
      return new BigFloat(x.isNeg ^ y.isNeg, x.Exponent + y.Exponent, x.significand * y.significand, x.significandSize, x.ExponentSize);
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
        return significand.Equals(BigNum.ZERO) && Exponent == BigNum.ZERO;
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
