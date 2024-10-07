using System;

namespace Microsoft.Boogie;

public class TraceLocation : IEquatable<TraceLocation>
{
  public int numBlock;
  public int numInstr;

  public TraceLocation(int numBlock, int numInstr)
  {
    this.numBlock = numBlock;
    this.numInstr = numInstr;
  }

  public override bool Equals(object obj)
  {
    TraceLocation that = obj as TraceLocation;
    if (that == null)
    {
      return false;
    }

    return (numBlock == that.numBlock && numInstr == that.numInstr);
  }

  public bool Equals(TraceLocation that)
  {
    return (numBlock == that.numBlock && numInstr == that.numInstr);
  }

  public override int GetHashCode()
  {
    return numBlock.GetHashCode() ^ 131 * numInstr.GetHashCode();
  }
}