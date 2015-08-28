//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Basetypes {
  /// <summary>
  /// The representation of a rational number.
  /// </summary>
  public struct Rational {
    public static readonly Rational ZERO = Rational.FromInts(0, 1);
    public static readonly Rational ONE = Rational.FromInts(1, 1);
    public static readonly Rational MINUS_ONE = Rational.FromInts(-1, 1);

    private BigNum numerator, denominator;

    //    int numerator;
    //    int denominator;


    // invariant: 0 < denominator || (numerator == 0 && denominator == 0);
    // invariant: numerator != 0 ==> gcd(abs(numerator),denominator) == 1;
    // invariant: numerator == 0 ==> denominator == 1 || denominator == 0;

    public static Rational FromInt(int x) {
      return FromBignum(BigNum.FromInt(x));
    }

    public static Rational FromBignum(BigNum n)       
    {
      return new Rational(n, BigNum.ONE);
    }

    private Rational(BigNum num, BigNum den)
    {
      Contract.Assert(den.Signum > 0);
      Contract.Assert(num == BigNum.ZERO || num.Gcd(den) == BigNum.ONE);
      numerator = num;
      denominator = den;
    }

    public static Rational FromBignums(BigNum num, BigNum den) {
      Contract.Assert(!den.IsZero);
      if (num == BigNum.ZERO)
        return ZERO;
      if (den.Signum < 0) {
        den = -den;
        num = -num;
      }
      if (den == BigNum.ONE)
        return new Rational(num, den);
      var gcd = num.Gcd(den);
      if (gcd == BigNum.ONE)
        return new Rational(num, den);
      return new Rational(num / gcd, den / gcd);
    }

    public static Rational FromInts(int num, int den) {
      return FromBignums(BigNum.FromInt(num), BigNum.FromInt(den));
    }

    /// <summary>
    /// Returns the absolute value of the rational.
    /// </summary>
    public Rational Abs() {
      Contract.Ensures(Contract.Result<Rational>().IsNonNegative);
      if (IsNonNegative) {
        return this;
      } else {
        return -this;
      }
    }

    /// <summary>
    /// Returns a rational whose numerator and denominator, resepctively, are the Gcd
    /// of the numerators and denominators of r and s.  If one of r and s is 0, the absolute
    /// value of the other is returned.  If both are 0, 1 is returned.
    /// </summary>
    public static Rational Gcd(Rational r, Rational s) {
      Contract.Ensures(Contract.Result<Rational>().IsPositive);
      if (r.IsZero) {
        if (s.IsZero) {
          return ONE;
        } else {
          return s.Abs();
        }
      } else if (s.IsZero) {
        return r.Abs();
      } else {
        return new Rational(r.Numerator.Gcd(s.Numerator),
                             r.Denominator.Gcd(s.Denominator));
      }
    }

    public BigNum Numerator { get { return numerator; } }
    public BigNum Denominator { get { return denominator == BigNum.ZERO ? BigNum.ONE : denominator; } }

    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return String.Format("{0}/{1}", Numerator, Denominator);
    }


    public static bool operator ==(Rational r, Rational s) {
      return r.Numerator == s.Numerator && r.Denominator == s.Denominator;
    }

    public static bool operator !=(Rational r, Rational s) {
      return !(r == s);
    }

    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      return obj is Rational && (Rational)obj == this;
    }

    public override int GetHashCode() {
      return this.Numerator.GetHashCode() * 13 + this.Denominator.GetHashCode();
    }

    public int Signum {
      get {
        return this.Numerator.Signum;
      }
    }

    public bool IsZero {
      get {
        return Signum == 0;
      }
    }

    public bool IsNonZero {
      get {
        return Signum != 0;
      }
    }

    public bool IsIntegral {
      get {
        return Denominator == BigNum.ONE;
      }
    }


    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public bool HasValue(int n) {
      return this == FromInt(n);
    }

    /// <summary>
    /// Returns the rational as an integer.  Requires the rational to be integral.
    /// </summary>
    public int AsInteger {
      get {
        Contract.Assert(this.IsIntegral);
        return Numerator.ToIntSafe;
      }
    }

    public BigNum AsBigNum {
      get {
        Contract.Assert(this.IsIntegral);
        return Numerator;
      }
    }

    public double AsDouble {
      [Pure]
      get {
        if (this.IsZero) {
          return 0.0;
        } else {
          return (double)Numerator.ToIntSafe / (double)Denominator.ToIntSafe;
        }
      }
    }

    public bool IsNegative {
      [Pure]
      get {
        return Signum < 0;
      }
    }

    public bool IsPositive {
      [Pure]
      get {
        return 0 < Signum;
      }
    }

    public bool IsNonNegative {
      [Pure]
      get {
        return 0 <= Signum;
      }
    }

    public static Rational operator -(Rational r)
    {
      return new Rational(-r.Numerator, r.Denominator);
    }

    public static Rational operator /(Rational r, Rational s)
    {
      return FromBignums(r.Numerator * s.Denominator, r.Denominator * s.Numerator);
    }

    public static Rational operator -(Rational r, Rational s)
    {
      return r + (-s);
    }

    public static Rational operator +(Rational r, Rational s)
    {
      return FromBignums(r.Numerator * s.Denominator + s.Numerator * r.Denominator, r.Denominator * s.Denominator);
    }

    public static Rational operator *(Rational r, Rational s)
    {
      return FromBignums(r.Numerator * s.Numerator, r.Denominator * s.Denominator);
    }

    public static bool operator <(Rational r, Rational s)
    {
      return (r - s).Signum < 0;
    }

    public static bool operator <=(Rational r, Rational s)
    {
      return !(r > s);
    }

    public static bool operator >=(Rational r, Rational s) {
      return !(r < s);
    }

    public static bool operator >(Rational r, Rational s) {
      return s < r;
    }
  }
}
