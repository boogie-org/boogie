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
  /// Note that this value has a 1-bit sign, 8-bit exponent, and 24-bit mantissa
  /// </summary>
  public struct BigFloat
  {
    //Please note that this code outline is copy-pasted from BigDec.cs

    // the internal representation
    [Rep]
    internal readonly BIM mantissa; //Note that the mantissa arrangement matches standard fp arrangement (most significant bit is farthest left)
    [Rep]
    internal readonly int mantissaSize;
    [Rep]
    internal readonly int exponent; //The value of the exponent is always positive as per fp representation requirements
    [Rep]
    internal readonly int exponentSize; //The bit size of the exponent
    [Rep]
    internal readonly String dec_value;
    [Rep]
    internal readonly bool isDec;

    public BIM Mantissa {
      get {
        return mantissa;
      }
    }

    public int Exponent {
      get {
        return exponent;
      }
    }

    public int MantissaSize {
      get {
        return mantissaSize;
      }
    }

    public int ExponentSize {
      get {
        return exponentSize;
      }
    }

    public String Decimal {
      get {
        return dec_value;
      }
    }

    public bool IsDec {
      get {
        return IsDec;
      }
    }

    public static BigFloat ZERO(int mantissaSize, int exponentSize) { return new BigFloat(0, 0, mantissaSize, exponentSize); } //Does not include negative zero

    private static readonly BIM two = new BIM(2);
    private static BIM two_n(int n) {
      BIM toReturn = new BIM(1);
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
      return new BigFloat(v, 0, 24, 8);
    }

    [Pure]
    public static BigFloat FromBigInt(BIM v) {
      return new BigFloat(0, v, 8, 24);
    }

    public static BigFloat FromBigDec(BigDec v)
    {
      return new BigFloat(v.ToDecimalString(), 8, 24);
    }

    [Pure]
    public static BigFloat FromString(string v) {
      String[] vals = v.Split(' ');
      if (vals.Length == 0 || vals.Length > 4)
        throw new FormatException();
      try
      {
        switch (vals.Length) {
          case 1:
            return new BigFloat(vals[0], 8, 24); 
          case 2:
            return new BigFloat(Int32.Parse(vals[0]), BIM.Parse(vals[1]), 8, 24);
          case 3:
            return new BigFloat(vals[0], Int32.Parse(vals[1]), Int32.Parse(vals[2]));
          case 4:
            return new BigFloat(Int32.Parse(vals[0]), BIM.Parse(vals[1]), Int32.Parse(vals[2]), Int32.Parse(vals[3]));
          default:
            throw new FormatException(); //Unreachable
        }
      }
      catch (Exception) { //Catch parsing errors
        throw new FormatException();
      }
    }

    internal BigFloat(int exponent, BIM mantissa, int exponentSize, int mantissaSize) {
      this.exponentSize = exponentSize;
      this.exponent = exponent;
      this.mantissa = mantissa;
      this.mantissaSize = mantissaSize;
      this.isDec = false;
      this.dec_value = "";
    }

    internal BigFloat(String dec_value, int exponentSize, int mantissaSize) {
      this.exponentSize = exponentSize;
      this.mantissaSize = mantissaSize;
      this.exponent = 0;
      this.mantissa = 0;
      this.isDec = true;
      this.dec_value = dec_value;
    }

    private BIM maxMantissa()
    {
      BIM result = new BIM(1);
      for (int i = 0; i < mantissaSize; i++)
        result = result * two;
      return result - 1;
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
      return Mantissa.GetHashCode() * 13 + Exponent.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return isDec ? dec_value : String.Format("{0}x2^{1}", Mantissa.ToString(), Exponent.ToString());
    }


    ////////////////////////////////////////////////////////////////////////////
    // Conversion operations

    /// <summary>
    /// NOTE: THIS METHOD MAY NOT WORK AS EXPECTED!!!
    /// Converts the given decimal value (provided as a string) to the nearest floating point approximation
    /// the returned fp assumes the given mantissa and exponent size
    /// </summary>
    /// <param name="value"></param>
    /// <param name="mantissaSize"></param>
    /// <param name="exponentSize"></param>
    /// <returns></returns>
    public static BigFloat Round(String value, int exponentSize, int mantissaSize)
    {
      int i = value.IndexOf('.');
      if (i == -1)
        return Round(BIM.Parse(value), 0, exponentSize, mantissaSize);
      return Round(i == 0 ? 0 : BIM.Parse(value.Substring(0, i)), BIM.Parse(value.Substring(i + 1, value.Length - i - 1)), exponentSize, mantissaSize);
    }

    /// <summary>
    /// NOTE:  THIS METHOD MAY NOT WORK AS EXPECTED!!!!
    /// Converts value.dec_value to a the closest float approximation with the given mantissaSize, exponentSize
    /// Returns the result of this calculation
    /// </summary>
    /// <param name="value"></param>
    /// <param name="power"></param>
    /// <param name="mantissaSize"></param>
    /// <param name="exponentSize"></param>
    /// <returns></returns>
    public static BigFloat Round(BIM value, BIM dec_value, int exponentSize, int mantissaSize)
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

      //Second, calculate the mantissa
      value = new BIM(0); //remove implicit bit
      dec_max = new BIM(10);
      while (dec_max < dec_value)
        dec_max = dec_max * ten;
      for (int i = mantissaSize; i > 0 && !dec_value.IsZero; i--) { //Multiply by two until the mantissa is fully calculated
        dec_value = dec_value * two;
        if (dec_value >= dec_max) {
          dec_value = dec_value - dec_max;
          value = value + two_n(i); //Note that i is decrementing so that the most significant bit is left-most in the representation
        }
      }

      return new BigFloat(exp, value, exponentSize, mantissaSize);
    }

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// NOTE:  THIS PROBABLY WON'T GIVE USEFUL OUTPUT!!!
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// </summary>
    /// <param name="floor">The Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BIM floor, out BIM ceiling) {
      //TODO: fix for fp functionality
      BIM n = Mantissa;
      int e = Exponent;
      if (n.IsZero) {
        floor = ceiling = n;
      } else if (0 <= e) {
        // it's an integer
        for (; 0 < e; e--) {
          n = n * two;
        }
        floor = ceiling = n;
      } else {
        // it's a non-zero integer, so the ceiling is one more than the floor
        for (; e < 0 && !n.IsZero; e++) {
          n = n / two;  // Division rounds towards negative infinity
        }

        if (!IsNegative) {
          floor = n;
          ceiling = n + 1;
        } else {
          ceiling = n;
          floor = n - 1;
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

    [Pure]
    public string ToDecimalString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return isDec ? dec_value : String.Format("{0}x2^{1}", Mantissa.ToString(), Exponent.ToString());
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
      //TODO: fix for fp functionality
      get {
        return new BigFloat(Exponent, BIM.Abs(Mantissa), ExponentSize, MantissaSize);
      }
    }

    [Pure]
    public BigFloat Negate {
      //TODO: Modify for correct fp functionality
      get {
        return new BigFloat(Exponent, BIM.Negate(Mantissa), ExponentSize, MantissaSize);
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
      Contract.Requires(x.MantissaSize == y.MantissaSize);
      BIM m1 = x.Mantissa;
      int e1 = x.Exponent;
      BIM m2 = y.Mantissa;
      int e2 = y.Exponent;
      m1 = m1 + two_n(x.mantissaSize + 1); //Add implicit bit
      m2 = m2 + two_n(y.mantissaSize + 1);
      if (e2 > e1) {
        m1 = y.Mantissa;
        e1 = y.Exponent;
        m2 = x.Mantissa;
        e2 = x.Exponent;
      }

      while (e2 < e1) {
        m2 = m2 / two;
        e2++;
      }

      return new BigFloat(e1, m1 + m2, x.MantissaSize, x.ExponentSize);
    }

    [Pure]
    public static BigFloat operator -(BigFloat x, BigFloat y) {
      return x + y.Negate;
    }

    [Pure]
    public static BigFloat operator *(BigFloat x, BigFloat y) {
      Contract.Requires(x.ExponentSize == y.ExponentSize);
      Contract.Requires(x.MantissaSize == y.MantissaSize);
      return new BigFloat(x.Exponent + y.Exponent, x.Mantissa * y.Mantissa, x.MantissaSize, x.ExponentSize);
    }


    ////////////////////////////////////////////////////////////////////////////
    // Some basic comparison operations

    public bool IsPositive {
      get {
        return !IsNegative;
      }
    }

    public bool IsNegative {
      get {
        return (isDec && dec_value[0] == '-') || mantissa < 0;
      }
    }

    public bool IsZero {
      get {
        return Mantissa.IsZero && Exponent == 0;
      }
    }

    [Pure]
    public int CompareTo(BigFloat that) {
      if (this.exponent > that.exponent)
        return 1;
      if (this.exponent < that.exponent)
        return -1;
      if (this.Mantissa == that.Mantissa)
        return 0;
      return this.Mantissa > that.Mantissa ? 1 : -1;
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
