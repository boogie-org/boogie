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
    public virtual MetadataTraverser MakeMetadataTraverser(IContractProvider contractProvider) { return new MetadataTraverser(this, contractProvider); }
    public virtual StatementTraverser MakeStatementTraverser(MetadataTraverser parent, Bpl.Variable heapVariable) { return new StatementTraverser(this, parent, heapVariable); }
    public virtual ExpressionTraverser MakeExpressionTraverser(StatementTraverser parent, Bpl.Variable heapVariable) { return new ExpressionTraverser(parent, heapVariable); }
  }
}