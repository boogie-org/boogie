//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie
{
  using System;
  using System.Collections.Generic;
  using Microsoft.Contracts;

  /// <summary>
  /// This class provides the functionality of traversing a program to determine which
  /// blocks are blocks where the widening operator may need to be applied.  Assumes
  /// all 'currentlyTraversed' bits to be initially false, and leaves them that way in
  /// the end.  Assumes the 'widenBlock' bits are initially false, and sets them
  /// appropriately.
  /// </summary>
  public class WidenPoints 
  {
    /// <summary>
    /// Compute the widen points of a program
    /// </summary>
    public static void Compute(Program! program) 
    {
      expose (program)
      {
        foreach (Declaration m in program.TopLevelDeclarations) 
        {
          Implementation impl = m as Implementation;
          if (impl != null) 
          {
            if (impl.Blocks != null && impl.Blocks.Count > 0) 
            {
              assume impl.IsConsistent;
              expose (impl) {
                Block start = impl.Blocks[0];
                assume start != null;
                assume start.IsConsistent;
                Visit(start);
          
                // We reset the state...
                foreach(Block b in impl.Blocks) {
                  expose (b) {
                    b.TraversingStatus = Block.VisitState.ToVisit;
                  }
                }
              }
            }
          }
        }
      }
    }

    static void Visit(Block! b) 
    {
      assume b.IsExposable;
      if (b.TraversingStatus == Block.VisitState.BeingVisited) 
      {
        expose (b)
        {
          // we got here through a back-edge
          b.widenBlock = true;
        }
      } 
      else if(b.TraversingStatus == Block.VisitState.AlreadyVisited)
      {
        // do nothing... we already saw this node
      }
      else if (b.TransferCmd is GotoCmd) 
      {
        assert b.TraversingStatus == Block.VisitState.ToVisit;    
    
        GotoCmd g = (GotoCmd)b.TransferCmd;
        expose (b)
        {
          expose (g) {  //PM: required for the subsequent expose (g.labelTargets)
            b.TraversingStatus = Block.VisitState.BeingVisited;
           
            // labelTargets is made non-null by Resolve, which we assume
            // has already called in a prior pass.
            assume g.labelTargets != null;
            expose (g.labelTargets) {
              foreach (Block succ in g.labelTargets) 
//              invariant b.currentlyTraversed; 
                //PM: The following loop invariant will work once properties are axiomatized
                //&& (g.labelNames != null && g.labelTargets != null ==> g.labelNames.Length == g.labelTargets.Length);
              {
                assert succ != null;
                Visit(succ);
              }
            }

            assert b.TraversingStatus == Block.VisitState.BeingVisited;
//            System.Diagnostics.Debug.Assert(b.currentlyTraversed);

            b.TraversingStatus = Block.VisitState.AlreadyVisited;

            //PM: The folowing assumption is needed because we cannot prove that a simple field update
            //PM: leaves the value of a property unchanged.
            assume (g.labelNames != null ==> g.labelNames.Length == g.labelTargets.Length);
          }
        }
      }
      else 
      {
        assert b.TransferCmd == null || b.TransferCmd is ReturnCmd;        // It must be a returnCmd;
      }
    }

    static private Block rootBlock = null;         // The root point we have to consider

    /// <summary>
    /// Compute the blocks in the body loop. 
    /// <param name ="block"> Tt is the head of the loop. It must be a widen block </param>
    /// <return> The blocks that are in the loop from block </return>
    /// </summary>
    public static List<Block!> ComputeLoopBodyFrom(Block! block)
      requires block.widenBlock;
    {
      assert rootBlock == null;
      rootBlock = block;

      List<Block!> blocksInLoop = new List<Block!>();         // We use a list just because .net does not define a set      
      List<Block!> visitingPath = new List<Block!>();         // The order is important, as we want paths
             
      blocksInLoop.Add(block);      
              
      DoDFSVisit(block, visitingPath, blocksInLoop);
      
      visitingPath.Add(block);
      

      rootBlock = null;   // We reset the invariant

      return blocksInLoop;
    }

    /// <summary>
    /// Perform the Depth-first search of the so to find the loop
    /// <param name = "block"> The block to visit </param>
    /// <param name = "path"> The path we are visiting so far </param>
    /// </summary>
    private static void DoDFSVisit(Block! block, List<Block!>! path, List<Block!>! blocksInPath)
    {
        #region case 1. We visit the root => We are done, "path" is a path inside the loop
        if(block == rootBlock && path.Count > 1)
        {
          blocksInPath.AddRange(path);      // Add all the blocks in this path 
        }

        #endregion
        #region case 2. We visit a node that ends with a return => "path" is not inside the loop
        if(block.TransferCmd is ReturnCmd)
        {
          return;
        }
        #endregion
        #region case 3. We visit a node with successors => continue the exploration of its successors
        {
          assert block.TransferCmd is GotoCmd;
          GotoCmd! successors = (GotoCmd) block.TransferCmd;
          
          if (successors.labelTargets != null)
          foreach (Block! nextBlock in successors.labelTargets)
          {
            if(path.Contains(nextBlock))      // If the current path has already seen the block, just skip it 
              continue;
                                              // Otherwise we perform the DFS visit
            path.Add(nextBlock);
            DoDFSVisit(nextBlock, path, blocksInPath);
            
            assert nextBlock == path[path.Count-1];
            path.RemoveAt(path.Count-1);
          }

        }

        #endregion
    }      
 }   
}
