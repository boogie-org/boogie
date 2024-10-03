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
    VerificationConditionGenerator parent, 
    ImplementationRun run, 
    ImplementationPartOrigin origin, int? randomSeed = null) 
    : base(options, blocks, parent, run, randomSeed)
  {
    Origin = origin;
  }
}