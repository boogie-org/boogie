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

  public class CLRSemantics : TraverserFactory {

    public override ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext) {
      return new CLRExpressionSemantics(sink, statementTraverser, contractContext);
    }


    public class CLRExpressionSemantics : ExpressionTraverser {

      public CLRExpressionSemantics(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext)
        : base(sink, statementTraverser, contractContext) { }
      
    }
  }
}