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
  public struct FP32
  {
    //Please note that this code outline is copy-pasted from BigDec.cs

    // the internal representation
    [Rep]
    internal readonly BIM mantissa; //TODO: restrict mantissa to be 23-bits wide
    [Rep]
    internal readonly int exponent; //TODO: restrict exponent to be 8-bits wide
    [Rep]
    internal readonly Boolean isNegative; //represents the sign bit

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

    public static readonly FP32 ZERO = FromInt(0);
    private static readonly BIM two = new BIM(2);
    private static readonly BIM ten = new BIM(10);


    ////////////////////////////////////////////////////////////////////////////
    // Constructors

    //Please note that these constructors will be called throughout boogie
    //For a complete summary of where this class has been added, simply view constructor references

    [Pure]
    public static FP32 FromInt(int v) {
      return new FP32(v, 0, v < 0); //TODO: modify for correct fp representation
    }

    [Pure]
    public static FP32 FromBigInt(BIM v) {
      return new FP32(v, 0, v < 0); //TODO: modify for correct fp representation
    }

    [Pure]
    public static FP32 FromString(string v) {
      //TODO: completely copied from BigDec.cs at the moment
      if (v == null) throw new FormatException();

      BIM integral = BIM.Zero;
      BIM fraction = BIM.Zero;
      int exponent = 0;

      int len = v.Length;

      int i = v.IndexOf('e');
      if (i >= 0) {
        if (i + 1 == v.Length) throw new FormatException();
        exponent = Int32.Parse(v.Substring(i + 1, len - i - 1));
        len = i;
      }

      int fractionLen = 0;
      i = v.IndexOf('.');
      if (i >= 0) {
        if (i + 1 == v.Length) throw new FormatException();
        fractionLen = len - i - 1;
        fraction = BIM.Parse(v.Substring(i + 1, fractionLen));
        len = i;
      }

      integral = BIM.Parse(v.Substring(0, len));

      if (!fraction.IsZero) {
        while (fractionLen > 0) {
          integral = integral * ten;
          exponent = exponent - 1;
          fractionLen = fractionLen - 1;
        }
      }
      return new FP32(integral - fraction, exponent, integral.Sign == -1);
    }

    internal FP32(BIM mantissa, int exponent, bool isNegative) {
      this.isNegative = isNegative;
      if (mantissa.IsZero) {
        this.mantissa = mantissa;
        this.exponent = 0;
      }
      else {
        while (mantissa % ten == BIM.Zero) { //TODO: get this to work as expected :P
          mantissa = mantissa / ten;
          exponent = exponent + 1;
        }
        this.mantissa = mantissa;
        this.exponent = exponent;
      }
    }


    ////////////////////////////////////////////////////////////////////////////
    // Basic object operations

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is FP32))
        return false;

      return (this == (FP32)obj);
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

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// Computes the floor and ceiling of this FP32. Note the choice of rounding towards negative
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
          n = n * ten;
        }
        floor = ceiling = n;
      } else {
        // it's a non-zero integer, so the ceiling is one more than the floor
        for (; e < 0 && !n.IsZero; e++) {
          n = n / ten;  // Division rounds towards negative infinity
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
    public FP32 Abs {
      //TODO: fix for fp functionality
      get {
        return new FP32(BIM.Abs(this.mantissa), this.exponent, false);
      }
    }

    [Pure]
    public FP32 Negate {
      //TODO: Modify for correct fp functionality
      get {
        return new FP32(BIM.Negate(this.mantissa), this.exponent, this.Mantissa >= 0);
      }
    }

    [Pure]
    public static FP32 operator -(FP32 x) {
      return x.Negate;
    }

    [Pure]
    public static FP32 operator +(FP32 x, FP32 y) {
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
        m2 = m2 * ten;
        e2 = e2 - 1;
      }

      return new FP32(m1 + m2, e1, true);
    }

    [Pure]
    public static FP32 operator -(FP32 x, FP32 y) {
      return x + y.Negate;
    }

    [Pure]
    public static FP32 operator *(FP32 x, FP32 y) {
      //TODO: modify for correct fp functionality
      return new FP32(x.mantissa * y.mantissa, x.exponent + y.exponent, false);
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
        return (isNegative);
      }
    }

    public bool IsZero {
      get {
        return this.mantissa.IsZero;
      }
    }

    [Pure]
    public int CompareTo(FP32 that) {
      //TODO: Modify for correct fp functionality
      if (this.mantissa == that.mantissa && this.exponent == that.exponent) {
        return 0;
      }
      else {
        FP32 d = this - that;
        return d.IsNegative ? -1 : 1;
      }
    }

    [Pure]
    public static bool operator ==(FP32 x, FP32 y) {
      return x.CompareTo(y) == 0;
    }

    [Pure]
    public static bool operator !=(FP32 x, FP32 y) {
      return x.CompareTo(y) != 0;
    }

    [Pure]
    public static bool operator <(FP32 x, FP32 y) {
      return x.CompareTo(y) < 0;
    }

    [Pure]
    public static bool operator >(FP32 x, FP32 y) {
      return x.CompareTo(y) > 0;
    }

    [Pure]
    public static bool operator <=(FP32 x, FP32 y) {
      return x.CompareTo(y) <= 0;
    }

    [Pure]
    public static bool operator >=(FP32 x, FP32 y) {
      return x.CompareTo(y) >= 0;
    }
  }
}
