//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;

namespace BytecodeTranslator {
  public abstract class TraverserFactory {
    public virtual MetadataTraverser MakeMetadataTraverser(Sink sink, IContractProvider contractProvider, PdbReader/*?*/ pdbReader)
    {
      return new MetadataTraverser(sink, pdbReader);
    }
    public virtual StatementTraverser MakeStatementTraverser(Sink sink, PdbReader/*?*/ pdbReader, bool contractContext) {
      return new StatementTraverser(sink, pdbReader, contractContext);
    }
    public virtual ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext) {
      return new ExpressionTraverser(sink, statementTraverser, contractContext);
    }
  }
}