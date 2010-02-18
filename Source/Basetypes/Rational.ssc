//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using Microsoft.Contracts;

namespace Microsoft.Basetypes
{
  using BNM = Microsoft.FSharp.Math.BigRational;

  /// <summary>
  /// The representation of a rational number.
  /// </summary>
  public struct Rational 
  {
    public static readonly Rational ZERO = new Rational ((!)BNM.Zero);
    public static readonly Rational ONE  = new Rational ((!)BNM.One);
    public static readonly Rational MINUS_ONE = new Rational ((!)(-BNM.One));

    private readonly Microsoft.FSharp.Math.BigRational _val;

    private Microsoft.FSharp.Math.BigRational! val {
      get {
        if (_val == null)
          return (!)BNM.Zero;
        else
          return _val;
      }
	}


    //    int numerator;
    //    int denominator;


    // invariant: 0 < denominator || (numerator == 0 && denominator == 0);
    // invariant: numerator != 0 ==> gcd(abs(numerator),denominator) == 1;
    // invariant: numerator == 0 ==> denominator == 1 || denominator == 0;

    private Rational(int x)
    {
      this._val = BNM.FromInt(x);
    }

    public static Rational FromInt(int x) {
      return new Rational(x);
    }

    private Rational(Microsoft.FSharp.Math.BigRational! val) {
      this._val = val;
    }

    public Rational(BigNum num, BigNum den) {
      System.Diagnostics.Debug.Assert(!den.IsZero);
      
      this._val = BNM.FromBigInt(num.val) / BNM.FromBigInt(den.val);
    }

    public static Rational FromInts(int num, int den) {
      return new Rational(BigNum.FromInt(num), BigNum.FromInt(den));
    }

    /// <summary>
    /// Returns the absolute value of the rational.
    /// </summary>
    public Rational Abs()
        ensures result.IsNonNegative;
    {
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
    public static Rational Gcd(Rational r, Rational s)
        ensures result.IsPositive;
    {
        if (r.IsZero) {
            if (s.IsZero) {
                return ONE;
            } else {
                return s.Abs();
            }
        } else if (s.IsZero) {
            return r.Abs();
        } else {
            return new Rational (r.Numerator.Gcd(s.Numerator),
                                 r.Denominator.Gcd(s.Denominator));
        }
    }
    
    public BigNum Numerator
    {
      get
      {
        // Better way to obtain the numerator?
        // The FSharp library does not seem to offer any methods for this
        string! lin = (!)val.ToString();
        int i = lin.IndexOf('/');
        if (i == -1)
          return new BigNum(BNM.ToBigInt(this.val));
        else
          return BigNum.FromString(lin.Substring(0, i));
      }
    }

    public BigNum Denominator
    {
      get
      {
        // Better way to obtain the numerator?
        // The FSharp library does not seem to offer any methods for this
        string! lin = (!)val.ToString();
        int i = lin.IndexOf('/');
        if (i == -1)
          return BigNum.ONE;
        else
          return BigNum.FromString(lin.Substring(i+1));
      }
    }

    public override string! ToString()
    {
      return String.Format("{0}/{1}", Numerator, Denominator);
    }


    public static bool operator==(Rational r, Rational s)
    {
      return (r.val == s.val);
    }

    public static bool operator!=(Rational r, Rational s)
    {
      return !(r.val == s.val);
    }

    public override bool Equals(object obj)
    {
      if (obj == null) return false;
      return obj is Rational && (Rational)obj == this;
    }

    public override int GetHashCode()
    {
      return this.val.GetHashCode();
    }

    public int Signum {
      get { return this.val.Sign; }
    }

    public bool IsZero
    {
      get
      {
        return Signum == 0;
      }
    }

    public bool IsNonZero
    {
      get
      {
        return Signum != 0;
      }
    }

    public bool IsIntegral
    {
      get
      {
        // better way?
        return !((!)this.val.ToString()).Contains("/");
      }
    }
    
    
    [Pure][Reads(ReadsAttribute.Reads.Nothing)]
    public bool HasValue (int n) { return this == new Rational(n); }

    /// <summary>
    /// Returns the rational as an integer.  Requires the rational to be integral.
    /// </summary>
    public int AsInteger
    {
      get
      {
        System.Diagnostics.Debug.Assert(this.IsIntegral);
        return Numerator.ToIntSafe;
      }
    }

    public BigNum AsBigNum {
      get
      {
        System.Diagnostics.Debug.Assert(this.IsIntegral);
        return new BigNum (BNM.ToBigInt(this.val));
      }
    }

    public double AsDouble
    {
      [Pure]
      get
      {
        if (this.IsZero)
        {
          return 0.0;
        } 
        else
        {
          return (double)Numerator.ToIntSafe / (double)Denominator.ToIntSafe;
        }
      }
    }

    public bool IsNegative
    {
      [Pure]
      get
      {
        return Signum < 0;
      }
    }

    public bool IsPositive
    {
      [Pure]
      get
      {
        return 0 < Signum;
      }
    }

    public bool IsNonNegative
    {
      [Pure]
      get
      {
        return 0 <= Signum;
      }
    }


    public static Rational operator-(Rational r)
    {
      return new Rational ((!)(BNM.Zero -r.val)); // for whatever reason, the Spec# compiler refuses to accept -r.val (unary negation)
    }


    public static Rational operator+(Rational r, Rational s)
    {
      return new Rational ((!)(r.val + s.val));
    }

    public static Rational operator-(Rational r, Rational s)
    {
      return new Rational ((!)(r.val - s.val));
    }

    public static Rational operator*(Rational r, Rational s)
    {
      return new Rational ((!)(r.val * s.val));
    }

    public static Rational operator/(Rational r, Rational s)
    {
      return new Rational ((!)(r.val / s.val));
    }

    public static bool operator<=(Rational r, Rational s)
    {
      return (r.val <= s.val);
    }

    public static bool operator>=(Rational r, Rational s)
    {
      return (r.val >= s.val);
    }

    public static bool operator<(Rational r, Rational s)
    {
      return (r.val < s.val);
    }

    public static bool operator>(Rational r, Rational s)
    {
      return (r.val > s.val);
    }
  }
}
