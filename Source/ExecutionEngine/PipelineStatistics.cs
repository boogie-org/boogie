namespace Microsoft.Boogie;

public class PipelineStatistics
{
  public int ErrorCount;
  public int VerifiedCount;
  public int InconclusiveCount;
  public int TimeoutCount;
  public int OutOfResourceCount;
  public int OutOfMemoryCount;
  public int SolverExceptionCount;
  public long[] CachingActionCounts;
  public int CachedErrorCount;
  public int CachedVerifiedCount;
  public int CachedInconclusiveCount;
  public int CachedTimeoutCount;
  public int CachedOutOfResourceCount;
  public int CachedOutOfMemoryCount;
  public int CachedSolverExceptionCount;
}