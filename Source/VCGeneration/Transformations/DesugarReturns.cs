using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using VC;

namespace VCGeneration.Transformations;

public static class DesugarReturns {
  public static Block GenerateUnifiedExit(Implementation impl, out Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins)
    {
      Contract.Requires(impl != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Ensures(Contract.Result<Block>() != null);

      gotoCmdOrigins = new();
      Contract.Ensures(Contract.Result<Block>().TransferCmd is ReturnCmd);
      Block exitBlock = null;

      #region Create a unified exit block, if there's more than one

      {
        int returnBlocks = 0;
        foreach (Block b in impl.Blocks)
        {
          if (b.TransferCmd is ReturnCmd)
          {
            exitBlock = b;
            returnBlocks++;
          }
        }

        if (returnBlocks > 1)
        {
          string unifiedExitLabel = "GeneratedUnifiedExit";
          var unifiedExit = new Block(new Token(-17, -4), unifiedExitLabel, new List<Cmd>(),
            new ReturnCmd(impl.StructuredStmts != null ? impl.StructuredStmts.EndCurly : Token.NoToken));
          Contract.Assert(unifiedExit != null);
          foreach (Block b in impl.Blocks)
          {
            if (b.TransferCmd is ReturnCmd returnCmd)
            {
              List<String> labels = new List<String>();
              labels.Add(unifiedExitLabel);
              List<Block> bs = new List<Block>();
              bs.Add(unifiedExit);
              GotoCmd go = new GotoCmd(returnCmd.tok, labels, bs);
              gotoCmdOrigins[go] = returnCmd;
              b.TransferCmd = go;
              unifiedExit.Predecessors.Add(b);
            }
          }

          exitBlock = unifiedExit;
          impl.Blocks.Add(unifiedExit);
        }

        Contract.Assert(exitBlock != null);
      }
      return exitBlock;

      #endregion
    }
    
    /// <summary>
    /// Modifies an implementation by inserting all postconditions
    /// as assert statements at the end of the implementation
    /// Returns the possibly-new unified exit block of the implementation
    /// </summary>
    /// <param name="impl"></param>
    /// <param name="unifiedExitblock">The unified exit block that has
    /// already been constructed for the implementation (and so
    /// is already an element of impl.Blocks)
    /// </param>
    public static void InjectPostConditions(VCGenOptions options, ImplementationRun run, Block unifiedExitBlock,
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(unifiedExitBlock != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Requires(impl.Proc != null);
      Contract.Requires(unifiedExitBlock.TransferCmd is ReturnCmd);

      TokenTextWriter debugWriter = null;
      if (options.PrintWithUniqueASTIds)
      {
        debugWriter = new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options);
        debugWriter.WriteLine("Effective postcondition:");
      }

      var formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap(options));

      // (free and checked) ensures clauses
      foreach (Ensures ens in impl.Proc.Ensures)
      {
        Contract.Assert(ens != null);

        if (!ens.Free)
        {
          var ensuresCopy = (Ensures) cce.NonNull(ens.Clone());
          ensuresCopy.Condition = Substituter.Apply(formalProcImplSubst, ens.Condition);
          AssertEnsuresCmd assert = new AssertEnsuresCmd(ensuresCopy) {
            ErrorDataEnhanced = ensuresCopy.ErrorDataEnhanced
          };
          // Copy any {:id ...} from the postcondition to the assumption, so
          // we can track it while analyzing verification coverage.
          assert.CopyIdFrom(ens.tok, ens);
          unifiedExitBlock.Cmds.Add(assert);
          if (debugWriter != null)
          {
            assert.Emit(debugWriter, 1);
          }
        }
        else if (ens.CanAlwaysAssume())
        {
          Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
          unifiedExitBlock.Cmds.Add(new AssumeCmd(ens.tok, e));
        }
        else
        {
          // skip free ensures if it doesn't have the :always_assume attr
        }
      }

      if (debugWriter != null)
      {
        debugWriter.WriteLine();
      }
    }
}