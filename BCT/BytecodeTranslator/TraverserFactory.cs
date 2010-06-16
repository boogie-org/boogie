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
    public virtual ToplevelTraverser MakeTopLevelTraverser(IContractProvider contractProvider) { return new ToplevelTraverser(this, contractProvider); }
    public virtual ClassTraverser MakeClassTraverser(ToplevelTraverser parent, IContractProvider contractProvider) { return new ClassTraverser(this, contractProvider, parent); }
    public virtual MethodTraverser MakeMethodTraverser(ClassTraverser parent, IContractProvider contractProvider) { return new MethodTraverser(this, contractProvider, parent); }
    public virtual StatementTraverser MakeStatementTraverser(MethodTraverser parent, Bpl.Variable heapVariable) { return new StatementTraverser(this, parent, heapVariable); }
    public virtual ExpressionTraverser MakeExpressionTraverser(StatementTraverser parent, Bpl.Variable heapVariable) { return new ExpressionTraverser(parent, heapVariable); }
  }
}