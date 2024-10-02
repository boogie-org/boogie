using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using VCGeneration;

namespace VC;

public class ManualSplit : Split
{

  public ImplementationPartOrigin Origin { get; }
  
  public ManualSplit(VCGenOptions options, 
    Func<List<Block>> blocks, 
    VerificationConditionGenerator par, 
    ImplementationRun run, 
    ImplementationPartOrigin origin, int? randomSeed = null) 
    : base(options, blocks, par, run, randomSeed)
  {
    Origin = origin;
  }
}