#nullable enable
namespace VCGeneration;

public class RemainingAssertionsOrigin : TokenWrapper, IImplementationPartOrigin {
  public IImplementationPartOrigin Origin { get; }

  public RemainingAssertionsOrigin(IImplementationPartOrigin origin) : base(origin) {
    Origin = origin;
  }

  public string ShortName => $"{Origin.ShortName}/remainingAssertions";
}