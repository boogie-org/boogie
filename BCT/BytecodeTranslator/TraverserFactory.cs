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

using TranslationPlugins;

using Bpl = Microsoft.Boogie;
using BytecodeTranslator.TranslationPlugins;

namespace BytecodeTranslator {
  public abstract class TraverserFactory {
    public int Priority { get; set; }

    public abstract Translator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> reader);

    public virtual BCTMetadataTraverser MakeMetadataTraverser(Sink sink,
      IDictionary<IUnit, IContractProvider> contractProviders, // TODO: remove this parameter?
      IDictionary<IUnit, PdbReader> sourceLocationProviders)
    {
      return new BCTMetadataTraverser(sink, sourceLocationProviders, this);
    }
    public virtual StatementTraverser MakeStatementTraverser(Sink sink, PdbReader/*?*/ pdbReader, bool contractContext) {
      return new StatementTraverser(sink, pdbReader, contractContext, this);
    }

    public virtual ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsOpAssignStatement = false) {
      return new ExpressionTraverser(sink, statementTraverser, contractContext, expressionIsOpAssignStatement);
    }
  }
}