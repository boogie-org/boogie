using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

/// <summary>
/// The AST for Boogie structured commands was designed to support backward compatibility with
/// the Boogie unstructured commands.  This has made the structured commands hard to construct.
/// The StmtListBuilder class makes it easier to build structured commands.
/// </summary>
public class StmtListBuilder
{
  readonly List<BigBlock> bigBlocks = new();

  string label;
  List<Cmd> simpleCmds;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullElements(bigBlocks));
  }

  void Dump(IToken token, StructuredCmd scmd, TransferCmd tcmd)
  {
    
    
    if (label == null && simpleCmds == null && scmd == null && tcmd == null)
    {
      // nothing to do
    }
    else
    {
      if (simpleCmds == null)
      {
        simpleCmds = new List<Cmd>();
      }

      bigBlocks.Add(new BigBlock(token, label, simpleCmds, scmd, tcmd));
      label = null;
      simpleCmds = null;
    }
  }

  /// <summary>
  /// Collects the StmtList built so far and returns it.  The StmtListBuilder should no longer
  /// be used once this method has been invoked.
  /// </summary>
  public StmtList Collect(IToken endCurlyBrace)
  {
    
    
    Dump(endCurlyBrace, null, null);
    if (bigBlocks.Count == 0)
    {
      simpleCmds = new List<Cmd>(); // the StmtList constructor doesn't like an empty list of BigBlock's
      Dump(endCurlyBrace, null, null);
    }

    return new StmtList(bigBlocks, endCurlyBrace);
  }

  public void Add(Cmd cmd)
  {
    
    if (simpleCmds == null)
    {
      simpleCmds = new List<Cmd>();
    }

    simpleCmds.Add(cmd);
  }

  public void Add(StructuredCmd scmd)
  {
    
    Dump(scmd.tok, scmd, null);
  }

  public void Add(TransferCmd tcmd)
  {
    
    Dump(tcmd.tok, null, tcmd);
  }

  public void AddLabelCmd(IToken token, string label)
  {
    
    Dump(token, null, null);
    this.label = label;
  }

  public void AddLocalVariable(string name)
  {
    
    // TODO
  }
}