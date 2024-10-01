using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration.Splits;

public class BlockRewriter {
  public static OrderedDictionary<Block, Block> UpdateBlocks(Stack<Block> blocksToVisit, 
    HashSet<Block> visitedBlocks, Func<Block, List<Cmd>> getCommands)
  {
    var oldToNewBlockMap = new OrderedDictionary<Block, Block>();
    while(blocksToVisit.Any()) {
      var oldBlock = blocksToVisit.Pop();
      if (!visitedBlocks.Add(oldBlock)) {
        continue;
      }
        
      var newBlock = new Block(oldBlock.tok)
      {
        Label = oldBlock.Label
      };
      oldToNewBlockMap.Add(oldBlock, newBlock);
      newBlock.Cmds = getCommands(oldBlock);
      foreach (var previous in oldBlock.Predecessors) {
        blocksToVisit.Push(previous);
      }
        
      if (oldBlock.TransferCmd is GotoCmd gtc)
      {
        var targets = gtc.LabelTargets.Where(oldToNewBlockMap.ContainsKey).ToList();
        newBlock.TransferCmd = new GotoCmd(gtc.tok,
          targets.Select(block => oldToNewBlockMap[block].Label).ToList(),
          targets.Select(block => oldToNewBlockMap[block]).ToList());
      }
    }

    return oldToNewBlockMap;
  }
}