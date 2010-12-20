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
    public virtual MetadataTraverser MakeMetadataTraverser(IContractProvider contractProvider, ISourceLocationProvider/*?*/ sourceLocationProvider)
    { 
      return new MetadataTraverser(new Sink(this), contractProvider, sourceLocationProvider);
    }
    public virtual StatementTraverser MakeStatementTraverser(Sink sink, ISourceLocationProvider/*?*/ sourceLocationProvider) {
      return new StatementTraverser(sink, sourceLocationProvider);
    }
    public virtual ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser) {
      return new ExpressionTraverser(sink, statementTraverser);
    }
  }
}