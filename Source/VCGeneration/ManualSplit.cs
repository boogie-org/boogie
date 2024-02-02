using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public class ManualSplit : Split
{

  public IToken Token { get; }


  public ManualSplit(VCGenOptions options, 
    List<Block> blocks, 
    Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, 
    VerificationConditionGenerator par, 
    ImplementationRun run, 
    IToken token) : base(options, blocks, gotoCmdOrigins, par, run)
  {
    Token = token;
  }
}