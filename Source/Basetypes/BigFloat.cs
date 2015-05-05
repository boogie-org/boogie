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
  /// Note that this value has a 1-bit sign, 8-bit exponent, and 23-bit mantissa
  /// </summary>
  public struct BigFloat
  {
    //Please note that this code outline is copy-pasted from BigDec.cs

    // the internal representation
    [Rep]
    internal readonly BIM mantissa; //TODO: restrict mantissa.  Note that mantissa includes the sign
    [Rep]
    internal readonly int exponent; //TODO: restrict exponent to be 8-bits wide
    [Rep]
    internal readonly int mantissaSize; //Represents the maximum size of the mantissa
    [Rep]
    internal readonly int exponentSize; //Represents the maximum size of the exponent

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

    public int MantissaSize
    {
      get
      {
        return mantissaSize;
      }
    }

    public int ExponentSize
    {
      get
      {
        return exponentSize;
      }
    }

    public static readonly BigFloat ZERO = FromInt(0);
    private static readonly BIM two = new BIM(2);


    ////////////////////////////////////////////////////////////////////////////
    // Constructors

    //Please note that these constructors will be called throughout boogie
    //For a complete summary of where this class has been added, simply view constructor references

    [Pure]
    public static BigFloat FromInt(int v) {
      return new BigFloat(v, 0, 23, 8); //TODO: modify for correct fp representation
    }

    [Pure]
    public static BigFloat FromBigInt(BIM v) {
      return new BigFloat(v, 0, 23, 8); //TODO: modify for correct fp representation
    }

    public static BigFloat FromBigDec(BIM v)
    {
      return new BigFloat(v, 0, 23, 8); //TODO: modify for correct fp representation
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
            return Round(decimal.Parse(vals[0]), 23, 8);
          case 2:
            return new BigFloat(BIM.Parse(vals[0]), Int32.Parse(vals[1]), 23, 8);
          case 3:
            return Round(decimal.Parse(vals[0]), Int32.Parse(vals[1]), Int32.Parse(vals[2]));
          case 4:
            return new BigFloat(BIM.Parse(vals[0]), Int32.Parse(vals[1]), Int32.Parse(vals[2]), Int32.Parse(vals[3]));
          default:
            throw new FormatException(); //Unreachable
        }
      }
      catch (Exception) { //Catch parsing errors
        throw new FormatException();
      }
    }

    internal BigFloat(BIM mantissa, int exponent, int mantissaSize, int exponentSize) {
      this.mantissaSize = mantissaSize;
      this.exponentSize = mantissaSize;
      this.mantissa = mantissa;
      this.exponent = exponent;
    }

    private int maxMantissa() { return (int)Math.Pow(2, mantissaSize); }
    private int maxExponent() { return (int)Math.Pow(2, exponentSize); }



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
      return this.mantissa.GetHashCode() * 13 + this.exponent.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString() {
      //TODO: modify to reflect floating points
      Contract.Ensures(Contract.Result<string>() != null);
      return String.Format("{0}e{1}", this.mantissa.ToString(), this.exponent.ToString());
    }


    ////////////////////////////////////////////////////////////////////////////
    // Conversion operations

    public static BigFloat Round(decimal d, int mantissaSize, int exponentSize)
    { //TODO: round the given decimal to the nearest fp value
      return new BigFloat(0, 0, mantissaSize, exponentSize);
    }

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// </summary>
    /// <param name="floor">The Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BIM floor, out BIM ceiling) {
      //TODO: fix for fp functionality
      BIM n = this.mantissa;
      int e = this.exponent;
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

        if (this.mantissa >= 0) {
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
      string s = this.mantissa.ToString();
      int digits = (this.mantissa >= 0) ? s.Length : s.Length - 1;
      BIM max = BIM.Pow(10, maxDigits);
      BIM min = -max;

      if (this.exponent >= 0) {
        if (maxDigits < digits || maxDigits - digits < this.exponent) {
          return String.Format("{0}.0", (this.mantissa >= 0) ? max.ToString() : min.ToString());
        }
        else {
          return String.Format("{0}{1}.0", s, new string('0', this.exponent));
        }
      }
      else {
        int exp = -this.exponent;

        if (exp < digits) {
          int intDigits = digits - exp;
          if (maxDigits < intDigits) {
            return String.Format("{0}.0", (this.mantissa >= 0) ? max.ToString() : min.ToString());
          }
          else {
            int fracDigits = Math.Min(maxDigits, digits - intDigits);
            return String.Format("{0}.{1}", s.Substring(0, intDigits), s.Substring(intDigits, fracDigits));
          }
        }
        else {
          int fracDigits = Math.Min(maxDigits, digits);
          return String.Format("0.{0}{1}", new string('0', exp - fracDigits), s.Substring(0, fracDigits));
        }
      }
    }

    [Pure]
    public string ToDecimalString() {
      //TODO: fix for fp functionality
      string m = this.mantissa.ToString();
      var e = this.exponent;
      if (0 <= this.exponent) {
        return m + Zeros(e) + ".0";
      } else {
        e = -e;
        // compute k to be the longest suffix of m consisting of all zeros (but no longer than e, and not the entire string)
        var maxK = e < m.Length ? e : m.Length - 1;
        var last = m.Length - 1;
        var k = 0;
        while (k < maxK && m[last - k] == '0') {
          k++;
        }
        if (0 < k) {
          // chop off the suffix of k zeros from m and adjust e accordingly
          m = m.Substring(0, m.Length - k);
          e -= k;
        }
        if (e == 0) {
          return m;
        } else if (e < m.Length) {
          var n = m.Length - e;
          return m.Substring(0, n) + "." + m.Substring(n);
        } else {
          return "0." + Zeros(e - m.Length) + m;
        }
      }
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
        return new BigFloat(BIM.Abs(this.mantissa), this.exponent, this.mantissaSize, this.exponentSize);
      }
    }

    [Pure]
    public BigFloat Negate {
      //TODO: Modify for correct fp functionality
      get {
        return new BigFloat(BIM.Negate(this.mantissa), this.exponent, this.mantissaSize, this.exponentSize);
      }
    }

    [Pure]
    public static BigFloat operator -(BigFloat x) {
      return x.Negate;
    }

    [Pure]
    public static BigFloat operator +(BigFloat x, BigFloat y) {
      //TODO: Modify for correct fp functionality
      BIM m1 = x.mantissa;
      int e1 = x.exponent;
      BIM m2 = y.mantissa;
      int e2 = y.exponent;
      if (e2 < e1) {
        m1 = y.mantissa;
        e1 = y.exponent;
        m2 = x.mantissa;
        e2 = x.exponent;
      }

      while (e2 > e1) {
        m2 = m2 * two;
        e2 = e2 - 1;
      }

      return new BigFloat(m1 + m2, e1, Math.Max(x.MantissaSize, y.MantissaSize), Math.Max(x.ExponentSize, y.ExponentSize));
    }

    [Pure]
    public static BigFloat operator -(BigFloat x, BigFloat y) {
      return x + y.Negate;
    }

    [Pure]
    public static BigFloat operator *(BigFloat x, BigFloat y) {
      //TODO: modify for correct fp functionality
      return new BigFloat(x.mantissa * y.mantissa, x.exponent + y.exponent, Math.Max(x.MantissaSize, y.MantissaSize), Math.Max(x.ExponentSize, y.ExponentSize));
    }


    ////////////////////////////////////////////////////////////////////////////
    // Some basic comparison operations

    public bool IsPositive {
      get {
        return (this.mantissa > BIM.Zero);
      }
    }

    public bool IsNegative {
      get {
        return (this.mantissa < BIM.Zero);
      }
    }

    public bool IsZero {
      get {
        return this.mantissa.IsZero && this.exponent == 0;
      }
    }

    [Pure]
    public int CompareTo(BigFloat that) {
      //TODO: Modify for correct fp functionality
      if (this.mantissa == that.mantissa && this.exponent == that.exponent) {
        return 0;
      }
      else {
        BigFloat d = this - that;
        return d.IsNegative ? -1 : 1;
      }
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
