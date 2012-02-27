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
using BytecodeTranslator.TranslationPlugins;

namespace BytecodeTranslator {

  public class CLRSemantics : TraverserFactory {

    public override Translator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      Translator translator = new BaseTranslator(this, sink, contractProviders, pdbReaders);
      return translator;
    }

    public override ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement) {
      return new CLRExpressionSemantics(sink, statementTraverser, contractContext, expressionIsStatement);
    }


    public class CLRExpressionSemantics : ExpressionTraverser {

      public CLRExpressionSemantics(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement)
        : base(sink, statementTraverser, contractContext, expressionIsStatement) { }
      
    }
  }
}