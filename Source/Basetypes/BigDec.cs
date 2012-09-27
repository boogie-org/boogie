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
    internal readonly BIM mantisse;
    [Rep]
    internal readonly BIM exponent;

    private static readonly BIM ONE = BIM.One;
    private static readonly BIM TEN = new BIM(10);


    ////////////////////////////////////////////////////////////////////////////
    // Constructors

    [Pure]
    public static BigDec FromString(string v) {
      if (v == null) throw new FormatException();

      BIM integral = BIM.Zero;
      BIM fraction = BIM.Zero;
      BIM exponent = BIM.Zero;

      int len = v.Length;

      int i = v.IndexOf('e');
      if (i >= 0) {
        exponent = BIM.Parse(v.Substring(i + 1, len - i));
        len = i;
      }

      int fraction_len = 0;
      i = v.IndexOf('.');
      if (i >= 0) {
        fraction = BIM.Parse(v.Substring(i + 1, len - i));
        fraction_len = len - i;
        len = i;
      }

      integral = BIM.Parse(v.Substring(0, len));

      while (fraction_len > 0) {
        integral = integral * TEN;
        exponent = exponent - ONE;
      }

      return new BigDec(integral + fraction, exponent);
    }

    internal BigDec(BIM mantisse, BIM exponent) {
      while (mantisse % TEN == BIM.Zero) {
        mantisse = mantisse / TEN;
        exponent = exponent + ONE;
      }

      this.mantisse = mantisse;
      this.exponent = exponent;
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

      BigDec other = (BigDec)obj;
      return (this.mantisse == other.mantisse && this.exponent == other.exponent);
    }

    [Pure]
    public override int GetHashCode() {
      return this.mantisse.GetHashCode() * 13 + this.exponent.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return String.Format("%se%s", this.mantisse.ToString(), this.exponent.ToString());
    }


    ////////////////////////////////////////////////////////////////////////////
    // Basic arithmetic operations

    [Pure]
    public static BigDec operator -(BigDec x) {
      return new BigDec(BIM.Negate(x.mantisse), x.exponent);
    }

    [Pure]
    public static BigDec operator +(BigDec x, BigDec y) {
      BIM m1 = x.mantisse;
      BIM e1 = x.exponent;
      BIM m2 = y.mantisse;
      BIM e2 = y.exponent;
      if (e2 < e1) {
        m1 = y.mantisse;
        e1 = y.exponent;
        m2 = x.mantisse;
        e2 = x.exponent;
      }

      while (e2 > e1) {
        m2 = m2 * TEN;
        e2 = e2 - ONE;
      }

      return new BigDec(m1 + m2, e1);
    }

    [Pure]
    public static BigDec operator -(BigDec x, BigDec y) {
      return x + (-y);
    }

    [Pure]
    public static BigDec operator *(BigDec x, BigDec y) {
      return new BigDec(x.mantisse * y.mantisse, x.exponent + y.exponent);
    }


    ////////////////////////////////////////////////////////////////////////////
    // Some basic comparison operations

    public bool IsPositive {
      get {
        return (this.mantisse > BIM.Zero);
      }
    }

    public bool IsNegative {
      get {
        return (this.mantisse < BIM.Zero);
      }
    }

    public bool IsZero {
      get {
        return this.mantisse.IsZero;
      }
    }

    [Pure]
    public int CompareTo(BigDec that) {
      BigDec d = this - that;

      if (d.IsZero) {
        return 0;
      }
      else if (d.IsNegative) {
        return -1;
      }
      else {
        return 1;
      }
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
