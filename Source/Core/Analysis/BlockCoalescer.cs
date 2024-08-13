using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class BlockCoalescer : ReadOnlyVisitor
{
  public static void CoalesceBlocks(Program program)
  {
    Contract.Requires(program != null);
    BlockCoalescer blockCoalescer = new BlockCoalescer();
    blockCoalescer.Visit(program);
  }

  private static HashSet<Block /*!*/> /*!*/ ComputeMultiPredecessorBlocks(Implementation /*!*/ impl)
  {
    Contract.Requires(impl != null);
    Contract.Ensures(cce.NonNullElements(Contract.Result<HashSet<Block>>()));
    HashSet<Block /*!*/> visitedBlocks = new HashSet<Block /*!*/>();
    HashSet<Block /*!*/> multiPredBlocks = new HashSet<Block /*!*/>();
    Stack<Block /*!*/> dfsStack = new Stack<Block /*!*/>();
    dfsStack.Push(impl.Blocks[0]);
    while (dfsStack.Count > 0)
    {
      Block /*!*/
        b = dfsStack.Pop();
      Contract.Assert(b != null);
      if (visitedBlocks.Contains(b))
      {
        multiPredBlocks.Add(b);
        continue;
      }

      visitedBlocks.Add(b);
      if (b.TransferCmd == null)
      {
        continue;
      }

      if (b.TransferCmd is ReturnCmd)
      {
        continue;
      }

      Contract.Assert(b.TransferCmd is GotoCmd);
      GotoCmd gotoCmd = (GotoCmd) b.TransferCmd;
      if (gotoCmd.labelTargets == null)
      {
        continue;
      }

      foreach (Block /*!*/ succ in gotoCmd.labelTargets)
      {
        Contract.Assert(succ != null);
        dfsStack.Push(succ);
      }
    }

    return multiPredBlocks;
  }

  public override Implementation VisitImplementation(Implementation impl)
  {
    //Contract.Requires(impl != null);
    Contract.Ensures(Contract.Result<Implementation>() != null);
    //Console.WriteLine("Procedure {0}", impl.Name);
    //Console.WriteLine("Initial number of blocks = {0}", impl.Blocks.Count);

    HashSet<Block /*!*/> multiPredBlocks = ComputeMultiPredecessorBlocks(impl);
    Contract.Assert(cce.NonNullElements(multiPredBlocks));
    HashSet<Block /*!*/> visitedBlocks = new HashSet<Block /*!*/>();
    HashSet<Block /*!*/> removedBlocks = new HashSet<Block /*!*/>();
    Stack<Block /*!*/> dfsStack = new Stack<Block /*!*/>();
    dfsStack.Push(impl.Blocks[0]);
    while (dfsStack.Count > 0)
    {
      Block /*!*/
        b = dfsStack.Pop();
      Contract.Assert(b != null);
      if (visitedBlocks.Contains(b))
      {
        continue;
      }

      visitedBlocks.Add(b);
      if (b.TransferCmd == null)
      {
        continue;
      }

      if (b.TransferCmd is ReturnCmd)
      {
        continue;
      }

      Contract.Assert(b.TransferCmd is GotoCmd);
      GotoCmd gotoCmd = (GotoCmd) b.TransferCmd;
      if (gotoCmd.labelTargets == null)
      {
        continue;
      }

      if (gotoCmd.labelTargets.Count == 1)
      {
        Block /*!*/
          succ = cce.NonNull(gotoCmd.labelTargets[0]);
        if (!multiPredBlocks.Contains(succ))
        {
          foreach (Cmd /*!*/ cmd in succ.Cmds)
          {
            Contract.Assert(cmd != null);
            b.Cmds.Add(cmd);
          }

          b.TransferCmd = succ.TransferCmd;
          if (!b.tok.IsValid && succ.tok.IsValid)
          {
            b.tok = succ.tok;
            b.Label = succ.Label;
          }

          removedBlocks.Add(succ);
          dfsStack.Push(b);
          visitedBlocks.Remove(b);
          continue;
        }
      }

      foreach (Block /*!*/ succ in gotoCmd.labelTargets)
      {
        Contract.Assert(succ != null);
        dfsStack.Push(succ);
      }
    }

    List<Block /*!*/> newBlocks = new List<Block /*!*/>();
    foreach (Block /*!*/ b in impl.Blocks)
    {
      Contract.Assert(b != null);
      if (visitedBlocks.Contains(b) && !removedBlocks.Contains(b))
      {
        newBlocks.Add(b);
      }
    }

    impl.Blocks = newBlocks;
    foreach (Block b in impl.Blocks)
    {
      if (b.TransferCmd is ReturnCmd)
      {
        continue;
      }

      GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
      gotoCmd.labelNames = new List<string>();
      foreach (Block succ in gotoCmd.labelTargets)
      {
        gotoCmd.labelNames.Add(succ.Label);
      }
    }

    // Console.WriteLine("Final number of blocks = {0}", impl.Blocks.Count);
    return impl;
  }
}