//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Diagnostics.Contracts;

namespace Microsoft.Basetypes
{

  /// <summary>
  /// A representation of a rounding mode
  /// </summary>
  public class RoundingMode
  {
    private string val;

    public static readonly RoundingMode RNE = new RoundingMode("RNE");
    public static readonly RoundingMode RNA = new RoundingMode("RNA");
    public static readonly RoundingMode RTP = new RoundingMode("RTP");
    public static readonly RoundingMode RTN = new RoundingMode("RTN");
    public static readonly RoundingMode RTZ = new RoundingMode("RTZ");

    private RoundingMode(string val)
    {
      this.val = val;
    }

    [Pure]
    public static RoundingMode FromString(String s)
    {
      if (s.Equals("RNE") || s.Equals("roundNearestTiesToEven")) return RNE;
      if (s.Equals("RNA") || s.Equals("roundNearestTiesToAway")) return RNA;
      if (s.Equals("RTP") || s.Equals("roundTowardPositive")) return RTP;
      if (s.Equals("RTN") || s.Equals("roundTowardNegative")) return RTN;
      if (s.Equals("RTZ") || s.Equals("roundTowardZero")) return RTZ;
      throw new FormatException(s + " is not a valid rounding mode.");
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      RoundingMode rm = obj as RoundingMode;
      return rm != null && this == rm;
    }

    [Pure]
    public override int GetHashCode()
    {
      return val.GetHashCode();
    }

    [Pure]
    public override string/*!*/ ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return val;
    }

    [Pure]
    public static bool operator ==(RoundingMode a, RoundingMode b)
    {
      return a.val.Equals(b.val);
    }

    [Pure]
    public static bool operator !=(RoundingMode a, RoundingMode b)
    {
      return !a.val.Equals(b.val);
    }
  }
}