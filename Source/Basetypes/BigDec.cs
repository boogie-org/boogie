//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Diagnostics.Contracts;


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

      return new BigDec(integral + fraction, exponent);
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

    [Pure]
    public BIM Floor(BIM? minimum, BIM? maximum) {
      BIM n = this.mantissa;
      
      if (this.exponent >= 0) {
        int e = this.exponent;
        while (e > 0 && (minimum == null || minimum <= n) && (maximum == null || n <= maximum)) {
          n = n * ten;
          e = e - 1;
        }
      }
      else {
        int e = -this.exponent;
        while (e > 0 && !n.IsZero) {
          n = n / ten;
          e = e - 1;
        }
      }

      if (minimum != null && n < minimum)
        return (BIM)minimum;
      else if (maximum != null && maximum < n)
        return (BIM)maximum;
      else
        return n;
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
