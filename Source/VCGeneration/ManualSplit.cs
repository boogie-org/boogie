using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using VCGeneration;

namespace VC;

public class ManualSplit : Split
{

  public ImplementationPartToken Token { get; }
  
  public ManualSplit(VCGenOptions options, 
    Func<List<Block>> blocks, 
    Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, 
    VerificationConditionGenerator par, 
    ImplementationRun run, 
    ImplementationPartToken token, int? randomSeed = null) 
    : base(options, blocks, gotoCmdOrigins, par, run, randomSeed)
  {
    Token = token;
  }
}