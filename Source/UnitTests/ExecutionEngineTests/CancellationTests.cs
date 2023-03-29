using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class CancellationTests
  {
    public Program GetProgram(ExecutionEngine engine, string code) {
      var bplFileName = "1";
      int errorCount = Parser.Parse(code, bplFileName, out Program program,
        engine.Options.UseBaseNameForFileName);
      Assert.AreEqual(0, errorCount);

      engine.ResolveAndTypecheck(program, bplFileName, out _);
      engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.CoalesceBlocks(program);
      engine.Inline(program);
      return program;
    }
    
    [Test]
    public async Task InferAndVerifyCanBeCancelledWhileWaitingForProver() {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      using var executionEngine = ExecutionEngine.CreateWithoutSharedCache(options);
      var infiniteProgram = GetProgram(executionEngine, SuperSlow);
      var terminatingProgram = GetProgram(executionEngine, Fast);
      
      // We limit the number of checkers to 1.
      options.VcsCores = 1;

      var requestId = ExecutionEngine.FreshRequestId();
      var outcomeTask =
        executionEngine.InferAndVerify(Console.Out, infiniteProgram, new PipelineStatistics(), requestId, null, requestId);
      await Task.Delay(1000);
      ExecutionEngine.CancelRequest(requestId);
      var outcome = await outcomeTask;
      Assert.AreEqual(PipelineOutcome.Cancelled, outcome);
      var requestId2 = ExecutionEngine.FreshRequestId();
      var outcome2 = await executionEngine.InferAndVerify(Console.Out, terminatingProgram, new PipelineStatistics(), requestId2, null, requestId2);
      Assert.AreEqual(PipelineOutcome.VerificationCompleted, outcome2);
    }

    private const string Fast = @"
procedure easy() ensures 1 + 1 == 0; {
}
";

    private const string SuperSlow = @"
  type LayerType;
  function {:identity} LitInt(x: int) : int;
  axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);
  const $LZ: LayerType;
  function $LS(LayerType) : LayerType;

  function Ack($ly: LayerType, m#0: int, n#0: int) : int;
  function Ack#canCall(m#0: int, n#0: int) : bool;
  axiom (forall $ly: LayerType, m#0: int, n#0: int :: 
    { Ack($LS($ly), m#0, n#0) } 
    Ack($LS($ly), m#0, n#0)
       == Ack($ly, m#0, n#0));
  axiom (forall $ly: LayerType, m#0: int, n#0: int :: 
      { Ack($LS($ly), m#0, n#0) } 
      Ack#canCall(m#0, n#0)
           || (m#0 >= LitInt(0) && n#0 >= LitInt(0))
         ==> (m#0 != LitInt(0)
             ==> (n#0 == LitInt(0) ==> Ack#canCall(m#0 - 1, LitInt(1)))
               && (n#0 != LitInt(0)
                 ==> Ack#canCall(m#0, n#0 - 1)
                   && Ack#canCall(m#0 - 1, Ack($ly, m#0, n#0 - 1))))
           && Ack($LS($ly), m#0, n#0)
             == (if m#0 == LitInt(0)
               then n#0 + 1
               else (if n#0 == LitInt(0)
                 then Ack($ly, m#0 - 1, LitInt(1))
                 else Ack($ly, m#0 - 1, Ack($ly, m#0, n#0 - 1)))));
  axiom (forall $ly: LayerType, m#0: int, n#0: int :: 
      {:weight 3} { Ack($LS($ly), LitInt(m#0), LitInt(n#0)) } 
      Ack#canCall(LitInt(m#0), LitInt(n#0))
           || (LitInt(m#0) >= LitInt(0)
             && LitInt(n#0) >= LitInt(0))
         ==> (LitInt(m#0) != LitInt(0)
             ==> (LitInt(n#0) == LitInt(0)
                 ==> Ack#canCall(LitInt(m#0 - 1), LitInt(1)))
               && (LitInt(n#0) != LitInt(0)
                 ==> Ack#canCall(LitInt(m#0), LitInt(n#0 - 1))
                   && Ack#canCall(LitInt(m#0 - 1), 
                    LitInt(Ack($LS($ly), LitInt(m#0), LitInt(n#0 - 1))))))
           && Ack($LS($ly), LitInt(m#0), LitInt(n#0))
             == (if LitInt(m#0) == LitInt(0)
               then n#0 + 1
               else (if LitInt(n#0) == LitInt(0)
                 then Ack($LS($ly), LitInt(m#0 - 1), LitInt(1))
                 else Ack($LS($ly), 
                  LitInt(m#0 - 1), 
                  LitInt(Ack($LS($ly), LitInt(m#0), LitInt(n#0 - 1)))))));

  procedure proof()
  {
    assume Ack#canCall(LitInt(5), LitInt(5));
    assert LitInt(Ack($LS($LS($LZ)), LitInt(5), LitInt(5))) == LitInt(0);
  }
";
  }
}