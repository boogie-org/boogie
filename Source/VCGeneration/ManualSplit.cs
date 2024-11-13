using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using VCGeneration;

namespace VC;

public class ManualSplit : Split
{

  public IImplementationPartOrigin Token { get; }
  
  public ManualSplit(VCGenOptions options, 
    Func<IList<Block>> blocks, 
    VerificationConditionGenerator parent, 
    ImplementationRun run, 
    IImplementationPartOrigin origin, int? randomSeed = null) 
    : base(options, blocks, parent, run, randomSeed)
  {
    Token = origin;
  }
}