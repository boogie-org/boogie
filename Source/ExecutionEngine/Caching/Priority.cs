namespace Microsoft.Boogie;

internal static class Priority
{
  public static readonly int LOW = 1; // the same snapshot has been verified before, but a callee has changed
  public static readonly int MEDIUM = 2; // old snapshot has been verified before
  public static readonly int HIGH = 3; // has been never verified before
  public static readonly int SKIP = int.MaxValue; // highest priority to get them done as soon as possible
}