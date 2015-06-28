//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Diagnostics.Contracts;
using System.Diagnostics;


namespace Microsoft.Basetypes {
  using BIM = System.Numerics.BigInteger;


  /// <summary>
  /// A representation of decimal values.
  /// </summary>
  public struct BigDec {

    // the internal representation
    [Rep]
    internal readonly BIM mantissa;
    [Rep]
    internal readonly int exponent;

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

    public static readonly BigDec ZERO = FromInt(0);
    private static readonly BIM ten = new BIM(10);


    ////////////////////////////////////////////////////////////////////////////
    // Constructors

    [Pure]
    public static BigDec FromInt(int v) {
      return new BigDec(v, 0);
    }

    [Pure]
    public static BigDec FromBigInt(BIM v) {
      return new BigDec(v, 0);
    }

    [Pure]
    public static BigDec FromString(string v) {
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

      if (integral.Sign == -1) {
        return new BigDec(integral - fraction, exponent);
      }
      else {
        return new BigDec(integral + fraction, exponent);
      }
    }

    internal BigDec(BIM mantissa, int exponent) {
      if (mantissa.IsZero) {
        this.mantissa = mantissa;
        this.exponent = 0;
      }
      else {
        while (mantissa % ten == BIM.Zero) {
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
      if (!(obj is BigDec))
        return false;

      return (this == (BigDec)obj);
    }

    [Pure]
    public override int GetHashCode() {
      return this.mantissa.GetHashCode() * 13 + this.exponent.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return String.Format("{0}e{1}", this.mantissa.ToString(), this.exponent.ToString());
    }


    ////////////////////////////////////////////////////////////////////////////
    // Conversion operations

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// Computes the floor and ceiling of this BigDec. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// </summary>
    /// <param name="floor">The Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BIM floor, out BIM ceiling) {
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
    public BigDec Abs {
      get {
        return new BigDec(BIM.Abs(this.mantissa), this.exponent);
      }
    }

    [Pure]
    public BigDec Negate {
      get {
        return new BigDec(BIM.Negate(this.mantissa), this.exponent);
      }
    }

    [Pure]
    public static BigDec operator -(BigDec x) {
      return x.Negate;
    }

    [Pure]
    public static BigDec operator +(BigDec x, BigDec y) {
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

      return new BigDec(m1 + m2, e1);
    }

    [Pure]
    public static BigDec operator -(BigDec x, BigDec y) {
      return x + y.Negate;
    }

    [Pure]
    public static BigDec operator *(BigDec x, BigDec y) {
      return new BigDec(x.mantissa * y.mantissa, x.exponent + y.exponent);
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
        return this.mantissa.IsZero;
      }
    }

    [Pure]
    public int CompareTo(BigDec that) {
      if (this.mantissa == that.mantissa && this.exponent == that.exponent) {
        return 0;
      }
      else {
        BigDec d = this - that;
        return d.IsNegative ? -1 : 1;
      }
    }

    [Pure]
    public static bool operator ==(BigDec x, BigDec y) {
      return x.CompareTo(y) == 0;
    }

    [Pure]
    public static bool operator !=(BigDec x, BigDec y) {
      return x.CompareTo(y) != 0;
    }

    [Pure]
    public static bool operator <(BigDec x, BigDec y) {
      return x.CompareTo(y) < 0;
    }

    [Pure]
    public static bool operator >(BigDec x, BigDec y) {
      return x.CompareTo(y) > 0;
    }

    [Pure]
    public static bool operator <=(BigDec x, BigDec y) {
      return x.CompareTo(y) <= 0;
    }

    [Pure]
    public static bool operator >=(BigDec x, BigDec y) {
      return x.CompareTo(y) >= 0;
    }
  }
}
