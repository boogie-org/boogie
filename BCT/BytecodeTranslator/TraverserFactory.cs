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
    public virtual MetadataTraverser MakeMetadataTraverser(Sink sink,
      IDictionary<IUnit, IContractProvider> contractProviders, // TODO: remove this parameter?
      IDictionary<IUnit, PdbReader> sourceLocationProviders)
    {
      return new MetadataTraverser(sink, sourceLocationProviders);
    }
    public virtual StatementTraverser MakeStatementTraverser(Sink sink, PdbReader/*?*/ pdbReader, bool contractContext, List<Tuple<ITryCatchFinallyStatement,StatementTraverser.TryCatchFinallyContext>> nestedTryCatchFinallyStatements) {
      return new StatementTraverser(sink, pdbReader, contractContext, nestedTryCatchFinallyStatements);
    }
    public virtual ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext) {
      return new ExpressionTraverser(sink, statementTraverser, contractContext);
    }
  }
}