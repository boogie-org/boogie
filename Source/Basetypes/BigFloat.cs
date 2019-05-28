//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Basetypes
{
  using BIM = System.Numerics.BigInteger;

  /// <summary>
  /// A representation of a floating-point value
  /// Note that this value has a 1-bit sign, along with an exponent and significand whose sizes must be greater than 1
  /// </summary>
  public struct BigFloat
  {
    //Please note that this code outline is copy-pasted from BigDec.cs

    // the internal representation
    internal readonly BIM significand; //Note that the significand arrangement matches standard fp arrangement (most significant bit is farthest left)
    internal readonly int significandSize; //The bit size of the significand
    internal readonly BIM exponent; //The value of the exponent is always positive as per fp representation requirements
    internal readonly int exponentSize; //The bit size of the exponent
    internal readonly String value; //Only used with second syntax
    internal readonly bool isSignBitSet; //Stores the sign bit in the fp representaiton

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

    public static BigFloat ZERO = new BigFloat(false, BIM.Zero, BIM.Zero, 24, 8); //Does not include negative zero

    ////////////////////////////////////////////////////////////////////////////
    // Constructors

    //Please note that these constructors will be called throughout boogie
    //For a complete summary of where this class has been added, simply view constructor references

    [Pure]
    public static BigFloat FromInt(int v) {
      return new BigFloat(v.ToString(), 24, 8);
    }

    public static BigFloat FromBigInt(BIM v, int significandSize, int exponentSize) {
      return new BigFloat(v.ToString(), significandSize, exponentSize);
    }

    [Pure]
    public static BigFloat FromString(String s) {
      /*
      * String must be either of the format [-]0x^.^e*f*e*
      * or of the special value formats: 0NaN*e* 0nan*e* 0+oo*e* 0-oo*e*
      * Where ^ indicates a hexadecimal value and * indicates an integer value
      */

      int posLastE = s.LastIndexOf('e');

      int expSize = int.Parse(s.Substring(posLastE + 1));
      if (expSize <= 1) {
        throw new FormatException("Exponent size must be greater than 1");
      }

      int posLastF = s.LastIndexOf('f');
      int posSig = posLastF + 1;
      if (posLastF == -1) {//NaN, +oo, -oo
        posSig = 4;
      }

      int sigSize = int.Parse(s.Substring(posSig, posLastE - posSig));
      if (sigSize <= 1) {
        throw new FormatException("Significand size must be greater than 1");
      }

      if (posLastF == -1) {//NaN, +oo, -oo
        return new BigFloat(s.Substring(1, 3), sigSize, expSize);
      }

      bool isSignBitSet = s[0] == '-';

      int posX = s.IndexOf('x');
      int posSecondLastE = s.LastIndexOf('e', posLastE - 1);

      string hexSig = s.Substring(posX + 1, posSecondLastE - (posX + 1));
      BIM oldExp = BIM.Parse(s.Substring(posSecondLastE + 1, posLastF - (posSecondLastE + 1)));

      string binSig = string.Join(string.Empty,
        hexSig.Select(
          c => (c == '.' ? "." : Convert.ToString(Convert.ToInt32(c.ToString(), 16), 2).PadLeft(4, '0'))
        )
      );

      int posDec = binSig.IndexOf('.');

      binSig = binSig.Remove(posDec, 1);

      int posFirstOne = binSig.IndexOf('1');
      int posLastOne = binSig.LastIndexOf('1');

      if (posFirstOne == -1) {
        return new BigFloat(isSignBitSet, 0, 0, sigSize, expSize);
      }

      binSig = binSig.Substring(posFirstOne, posLastOne - posFirstOne + 1);

      BIM bias = BIM.Pow(2, expSize - 1) - 1;
      BIM upperBound = 2 * bias + 1;

      BIM newExp = 4 * oldExp + bias + (posDec - posFirstOne - 1);

      if (newExp <= 0) {
        if (-newExp <= (sigSize - 1) - binSig.Length) {
          binSig = new string('0', (int) -newExp) + binSig;
          newExp = 0;
        }
      } else {
        binSig = binSig.Substring(1);
      }

      if (newExp < 0 || newExp >= upperBound) {
        throw new FormatException("The given exponent cannot fit in the bit size " + expSize);
      }

      binSig = binSig.PadRight(sigSize - 1, '0');

      if (binSig.Length > sigSize - 1) {
        throw new FormatException("The given significand cannot fit in the bit size " + (sigSize - 1));
      }

      BIM newSig = 0;
      foreach (char b in binSig) {
        if (b != '.') {
          newSig <<= 1;
          newSig += b - '0';
        }
      }

      return new BigFloat(isSignBitSet, newSig, newExp, sigSize, expSize);
    }

    public BigFloat(bool isSignBitSet, BIM significand, BIM exponent, int significandSize, int exponentSize) {
      this.exponentSize = exponentSize;
      this.exponent = exponent;
      this.significand = significand;
      this.significandSize = significandSize;
      this.isSignBitSet = isSignBitSet;
      this.value = "";
    }

    public BigFloat(String value, int significandSize, int exponentSize) {
      this.exponentSize = exponentSize;
      this.significandSize = significandSize;
      this.exponent = BIM.Zero;
      this.significand = BIM.Zero;
      this.value = value;
      if (value.Equals("nan")) {
        this.value = "NaN";
      }

      this.isSignBitSet = value[0] == '-';
    }

    ////////////////////////////////////////////////////////////////////////////
    // Basic object operations

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj) {
      if (obj == null) {
        return false;
      }

      if (!(obj is BigFloat)) {
        return false;
      }

      return (this == (BigFloat) obj);
    }

    [Pure]
    public override int GetHashCode() {
      return significand.GetHashCode() * 13 + exponent.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      if (value == "") {
        byte[] sigBytes = significand.ToByteArray();
        StringBuilder binSig = new StringBuilder();

        if (exponent == 0) {
          binSig.Append('0');
        } else {
          binSig.Append('1'); //hidden bit
        }

        for (int i = significandSize - 2; i >= 0; --i) { //little endian
          if (i / 8 < sigBytes.Length) {
            binSig.Append((char) ('0' + ((sigBytes[i / 8] >> (i % 8)) & 1)));
          } else {
            binSig.Append('0');
          }
        }

        BIM bias = BIM.Pow(2, exponentSize - 1) - 1;
        if (exponent == 0) {
          --bias;
        }

        int moveDec = ((int) ((exponent - bias) % 4) + 4) % 4;
        BIM finalExp = (exponent - bias - moveDec) / 4;

        string leftBinSig = binSig.ToString().Substring(0, moveDec + 1);
        string rightBinSig = binSig.ToString().Substring(moveDec + 1);

        leftBinSig = new string('0', 4 - leftBinSig.Length % 4) + leftBinSig;
        rightBinSig = rightBinSig + new string('0', 4 - rightBinSig.Length % 4);

        StringBuilder leftHexSig = new StringBuilder();
        StringBuilder rightHexSig = new StringBuilder();

        for (int i = 0; i < leftBinSig.Length / 4; ++i) {
          leftHexSig.AppendFormat("{0:X}", Convert.ToByte(leftBinSig.Substring(i * 4, 4), 2));
        }
        for (int i = 0; i < rightBinSig.Length / 4; ++i) {
          rightHexSig.AppendFormat("{0:X}", Convert.ToByte(rightBinSig.Substring(i * 4, 4), 2));
        }

        return String.Format("{0}0x{1}.{2}e{3}f{4}e{5}", isSignBitSet ? "-" : "", leftHexSig, rightHexSig, finalExp, significandSize, exponentSize);
      }
      return String.Format("0{0}{1}e{2}", value, significandSize, exponentSize);
    }


    ////////////////////////////////////////////////////////////////////////////
    // Conversion operations

    // ``floor`` rounds towards negative infinity (like SMT-LIBv2's to_int).
    /// <summary>
    /// Computes the floor and ceiling of this BigFloat. Note the choice of rounding towards negative
    /// infinity rather than zero for floor is because SMT-LIBv2's to_int function floors this way.
    /// </summary>
    /// <param name="floor">Floor (rounded towards negative infinity)</param>
    /// <param name="ceiling">Ceiling (rounded towards positive infinity)</param>
    public void FloorCeiling(out BIM floor, out BIM ceiling) {
      Contract.Requires(value == "");

      BIM sig = significand;
      BIM exp = exponent;

      BIM hiddenBitPow = BIM.Pow(2, significandSize - 1);

      if (exponent > 0) {
        sig += hiddenBitPow;
      } else {
        ++exp;
      }

      exp -= (BIM.Pow(2, exponentSize - 1) - 1) + (significandSize - 1);

      if (exp >= BIM.Zero) {
        while (exp >= int.MaxValue) {
          sig <<= int.MaxValue;
          exp -= int.MaxValue;
        }

        sig <<= (int) exp;
        floor = ceiling = (isSignBitSet ? -sig : sig);
      } else {
        exp = -exp;

        if (exp > significandSize) {
          if (sig == 0) {
            floor = ceiling = 0;
          } else {
            ceiling = isSignBitSet ? 0 : 1;
            floor = ceiling - 1;
          }
        } else {
          BIM frac = sig & ((BIM.One << (int) exp) - 1);
          sig >>= (int) exp; //Guaranteed to fit in a 32-bit integer

          if (frac == 0) {
            floor = ceiling = (isSignBitSet ? -sig : sig);
          } else {
            ceiling = isSignBitSet ? -sig : sig + 1;
            floor = ceiling - 1;
          }
        }
      }
    }

    public String ToBVString() {
      if (value != "") {
        return "_ " + value + " " + exponentSize + " " + significandSize;
      } else if (value == "") {
        return "fp (_ bv" + (isSignBitSet ? "1" : "0") + " 1) (_ bv" + exponent + " " + exponentSize + ") (_ bv" + significand + " " + (significandSize - 1) + ")";
      } else {
        return "(_ to_fp " + exponentSize + " " + significandSize + ") (_ bv" + value + " " + (exponentSize + significandSize).ToString() + ")";
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Basic arithmetic operations

    [Pure]
    public static BigFloat operator -(BigFloat x) {
      if (x.value != "") {
        if (x.value[0] == '-') {
          return new BigFloat("+oo", x.significandSize, x.exponentSize);
        }

        if (x.value[0] == '+') {
          return new BigFloat("-oo", x.significandSize, x.exponentSize);
        }

        return new BigFloat("NaN", x.significandSize, x.exponentSize);
      }

      return new BigFloat(!x.isSignBitSet, x.significand, x.exponent, x.significandSize, x.exponentSize);
    }

    [Pure]
    public static BigFloat operator +(BigFloat x, BigFloat y) {
      Contract.Requires(x.exponentSize == y.exponentSize);
      Contract.Requires(x.significandSize == y.significandSize);

      if (x.value != "" || y.value != "") {
        if (x.value == "NaN" || y.value == "NaN" || x.value == "+oo" && y.value == "-oo" || x.value == "-oo" && y.value == "+oo") {
          return new BigFloat("NaN", x.significandSize, x.exponentSize);
        }

        if (x.value != "") {
          return new BigFloat(x.value, x.significandSize, x.exponentSize);
        }

        return new BigFloat(y.value, y.significandSize, y.exponentSize);
      }

      if (x.exponent > y.exponent) {
        BigFloat temp = x;
        x = y;
        y = temp;
      }

      BIM xsig = x.significand, ysig = y.significand;
      BIM xexp = x.exponent, yexp = y.exponent;

      if (yexp - xexp > x.significandSize) //One of the numbers is relatively insignificant
      {
        return new BigFloat(y.isSignBitSet, y.significand, y.exponent, y.significandSize, y.exponentSize);
      }

      BIM hiddenBitPow = BIM.Pow(2, x.significandSize - 1);

      if (xexp > 0) {
        xsig += hiddenBitPow;
      } else {
        ++xexp;
      }

      if (yexp > 0) {
        ysig += hiddenBitPow;
      } else {
        ++yexp;
      }

      if (x.isSignBitSet) {
        xsig = -xsig;
      }
      if (y.isSignBitSet) {
        ysig = -ysig;
      }

      xsig >>= (int) (yexp - xexp); //Guaranteed to fit in a 32-bit integer

      ysig += xsig;

      bool isNeg = ysig < 0;

      ysig = BIM.Abs(ysig);

      if (ysig == 0) {
        return new BigFloat(x.isSignBitSet && y.isSignBitSet, 0, 0, x.significandSize, x.exponentSize);
      }

      if (ysig >= hiddenBitPow * 2) {
        ysig >>= 1;
        ++yexp;
      }

      while (ysig < hiddenBitPow && yexp > 1) {
        ysig <<= 1;
        --yexp;
      }

      if (ysig < hiddenBitPow) {
        yexp = 0;
      } else {
        ysig -= hiddenBitPow;
      }

      if (yexp >= BIM.Pow(2, x.exponentSize) - 1) {
        return new BigFloat(y.isSignBitSet ? "-oo" : "+oo", x.significandSize, x.exponentSize);
      }

      return new BigFloat(isNeg, ysig, yexp, x.significandSize, x.exponentSize);
    }

    [Pure]
    public static BigFloat operator -(BigFloat x, BigFloat y) {
      return x + -y;
    }

    [Pure]
    public static BigFloat operator *(BigFloat x, BigFloat y) {
      Contract.Requires(x.exponentSize == y.exponentSize);
      Contract.Requires(x.significandSize == y.significandSize);

      if (x.value == "NaN" || y.value == "NaN" || (x.value == "+oo" || x.value == "-oo") && y.IsZero || (y.value == "+oo" || y.value == "-oo") && x.IsZero) {
        return new BigFloat("NaN", x.significandSize, x.exponentSize);
      }

      if (x.value != "" || y.value != "") {
        bool xSignBitSet = x.value == "" ? x.isSignBitSet : x.value[0] == '-';
        bool ySignBitSet = y.value == "" ? y.isSignBitSet : y.value[0] == '-';
        return new BigFloat((xSignBitSet ^ ySignBitSet ? "-" : "+") + "oo", x.significandSize, x.exponentSize);
      }

      BIM xsig = x.significand, ysig = y.significand;
      BIM xexp = x.exponent, yexp = y.exponent;

      BIM hiddenBitPow = BIM.Pow(2, x.significandSize - 1);

      if (xexp > 0) {
        xsig += hiddenBitPow;
      } else {
        ++xexp;
      }

      if (yexp > 0) {
        ysig += hiddenBitPow;
      } else {
        ++yexp;
      }

      ysig *= xsig;
      yexp += xexp - (BIM.Pow(2, x.exponentSize - 1) - 1) - (x.significandSize - 1);

      while (ysig >= hiddenBitPow * 2 || yexp <= 0) {
        ysig >>= 1;
        ++yexp;
      }

      while (ysig < hiddenBitPow && yexp > 1) {
        ysig <<= 1;
        --yexp;
      }

      if (ysig < hiddenBitPow) {
        yexp = 0;
      } else {
        ysig -= hiddenBitPow;
      }

      if (yexp >= BIM.Pow(2, x.exponentSize) - 1) {
        return new BigFloat(x.isSignBitSet ^ y.isSignBitSet ? "-oo" : "+oo", x.significandSize, x.exponentSize);
      }

      return new BigFloat(x.isSignBitSet ^ y.isSignBitSet, ysig, yexp, x.significandSize, x.exponentSize);
    }


    ////////////////////////////////////////////////////////////////////////////
    // Some basic comparison operations

    public bool IsZero {
      get {
        return value == "" && significand.IsZero && exponent.IsZero;
      }
    }

    /// <summary>
    /// This method follows the specification for C#'s Single.CompareTo method.
    /// As a result, it handles NaNs differently than how the ==, !=, <, >, <=, and >= operators do.
    /// For example, the expression (0.0f / 0.0f).CompareTo(0.0f / 0.0f) should return 0,
    /// whereas the expression (0.0f / 0.0f) == (0.0f / 0.0f) should return false.
    /// </summary>
    [Pure]
    public int CompareTo(BigFloat that) {
      Contract.Requires(exponentSize == that.exponentSize);
      Contract.Requires(significandSize == that.significandSize);

      if (value == "" && that.value == "") {
        int cmpThis = IsZero ? 0 : isSignBitSet ? -1 : 1;
        int cmpThat = that.IsZero ? 0 : that.isSignBitSet ? -1 : 1;

        if (cmpThis == cmpThat) {
          if (exponent == that.exponent) {
            return cmpThis * significand.CompareTo(that.significand);
          }

          return cmpThis * exponent.CompareTo(that.exponent);
        }

        if (cmpThis == 0) {
          return -cmpThat;
        }

        return cmpThis;
      }

      if (value == that.value) {
        return 0;
      }

      if (value == "NaN" || that.value == "+oo" || value == "-oo" && that.value != "NaN") {
        return -1;
      }

      return 1;
    }

    [Pure]
    public static bool operator ==(BigFloat x, BigFloat y) {
      if (x.value == "NaN" || y.value == "NaN") {
        return false;
      }

      return x.CompareTo(y) == 0;
    }

    [Pure]
    public static bool operator !=(BigFloat x, BigFloat y) {
      if (x.value == "NaN" || y.value == "NaN") {
        return true;
      }

      return x.CompareTo(y) != 0;
    }

    [Pure]
    public static bool operator <(BigFloat x, BigFloat y) {
      if (x.value == "NaN" || y.value == "NaN") {
        return false;
      }

      return x.CompareTo(y) < 0;
    }

    [Pure]
    public static bool operator >(BigFloat x, BigFloat y) {
      if (x.value == "NaN" || y.value == "NaN") {
        return false;
      }

      return x.CompareTo(y) > 0;
    }

    [Pure]
    public static bool operator <=(BigFloat x, BigFloat y) {
      if (x.value == "NaN" || y.value == "NaN") {
        return false;
      }

      return x.CompareTo(y) <= 0;
    }

    [Pure]
    public static bool operator >=(BigFloat x, BigFloat y) {
      if (x.value == "NaN" || y.value == "NaN") {
        return false;
      }

      return x.CompareTo(y) >= 0;
    }
  }
}
