//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;
using TranslationPlugins;
using BytecodeTranslator.Phone;


namespace BytecodeTranslator {

  internal class ExceptionAnalyzer : CodeTraverser {

    private Dictionary<IMethodDefinition, HashSet<ITypeReference>> exceptionsExplicitlyThrownByMethod;
    private bool resultsChanged;

    private ExceptionAnalyzer() {
      this.exceptionsExplicitlyThrownByMethod = new Dictionary<IMethodDefinition, HashSet<ITypeReference>>();
    }

    public static Predicate<IMethodDefinition> ComputeExplicitlyThrownExceptions(IEnumerable<IUnit> units) {
      var me = new ExceptionAnalyzer();
      do {
        me.resultsChanged = false;
        foreach (var u in units)
          me.Traverse(u.UnitNamespaceRoot);
      } while (me.resultsChanged);
      return m => m != null && me.exceptionsExplicitlyThrownByMethod.ContainsKey(m);
    }

    public override void TraverseChildren(IMethodDefinition method) {
      var newExceptions = MethodExceptionAnalyzer.ExplicitlyThrownExceptions(this, method);
      HashSet<ITypeReference> alreadyKnownExceptions = null;
      if (this.exceptionsExplicitlyThrownByMethod.TryGetValue(method, out alreadyKnownExceptions)) {
        if (!newExceptions.SetEquals(alreadyKnownExceptions)) {
          this.resultsChanged = true;
          this.exceptionsExplicitlyThrownByMethod[method] = newExceptions;
        }
      } else {
        if (0 < newExceptions.Count) {
          this.resultsChanged = true;
          this.exceptionsExplicitlyThrownByMethod[method] = newExceptions;
        }
      }

    }

    private class MethodExceptionAnalyzer : CodeTraverser {

      private ExceptionAnalyzer parent;
      private HashSet<ITypeReference> exceptionsThrown;

      /// <summary>
      /// Used to track the type thrown by rethrow statements.
      /// </summary>
      private ITypeReference/*?*/ currentCatchClauseExceptionType;

      private MethodExceptionAnalyzer(ExceptionAnalyzer parent) {
        this.parent = parent;
        this.exceptionsThrown = new HashSet<ITypeReference>();
      }

      public static HashSet<ITypeReference> ExplicitlyThrownExceptions(ExceptionAnalyzer parent, IMethodDefinition methodDefinition) {
        var me = new MethodExceptionAnalyzer(parent);
        me.Traverse(methodDefinition);
        return me.exceptionsThrown;
      }

      public override void TraverseChildren(ICatchClause catchClause) {
        this.exceptionsThrown.RemoveWhere(t => TypeHelper.Type1DerivesFromOrIsTheSameAsType2(t.ResolvedType, catchClause.ExceptionType, true));

        // no need to save the current value: catch clauses cannot be nested.
        this.currentCatchClauseExceptionType = catchClause.ExceptionType;
        base.TraverseChildren(catchClause);
        this.currentCatchClauseExceptionType = null;
      }

      public override void TraverseChildren(IMethodCall methodCall) {
        var calledMethod = MemberHelper.UninstantiateAndUnspecialize(methodCall.MethodToCall.ResolvedMethod).ResolvedMethod;
        HashSet<ITypeReference> calledMethodExceptionSet;
        if (this.parent.exceptionsExplicitlyThrownByMethod.TryGetValue(calledMethod, out calledMethodExceptionSet))
          this.exceptionsThrown.UnionWith(calledMethodExceptionSet);
        base.TraverseChildren(methodCall);
      }

      public override void TraverseChildren(IRethrowStatement rethrowStatement) {
        this.exceptionsThrown.Add(this.currentCatchClauseExceptionType);
      }

      public override void TraverseChildren(IThrowStatement throwStatement) {
        this.exceptionsThrown.Add(throwStatement.Exception.Type);
      }

      public override void TraverseChildren(ITryCatchFinallyStatement tryCatchFilterFinallyStatement) {
        var savedExceptions = this.exceptionsThrown;
        this.exceptionsThrown = new HashSet<ITypeReference>();

        base.TraverseChildren(tryCatchFilterFinallyStatement);

        savedExceptions.UnionWith(this.exceptionsThrown);
        this.exceptionsThrown = savedExceptions;
      }
    }

  }

}