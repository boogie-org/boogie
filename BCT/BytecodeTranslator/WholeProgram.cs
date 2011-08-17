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
using System.Diagnostics.Contracts;

namespace BytecodeTranslator {
  class WholeProgram : TraverserFactory {

    public override TranslationPlugins.Translator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      BaseTranslator translator = new BaseTranslator(this, sink, contractProviders, pdbReaders);
      return translator;
    }

    /// <summary>
    /// Table to be filled by the metadata traverser before visiting any assemblies.
    /// 
    /// The table lists the direct supertypes of all type definitions that it encounters during the
    /// traversal. (But the table is organized so that subTypes[T] is the list of type definitions
    /// that are direct subtypes of T.)
    /// </summary>
    readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes = new Dictionary<ITypeReference, List<ITypeReference>>();

    public override MetadataTraverser MakeMetadataTraverser(Sink sink,
      IDictionary<IUnit, IContractProvider> contractProviders, // TODO: remove this parameter?
      IDictionary<IUnit, PdbReader> pdbReaders) {
      return new WholeProgramMetadataSemantics(this, sink, pdbReaders, this);
    }

    public class WholeProgramMetadataSemantics : MetadataTraverser {

      readonly WholeProgram parent;
      readonly Sink sink;

      readonly Dictionary<IUnit, bool> codeUnderAnalysis = new Dictionary<IUnit, bool>();

      public WholeProgramMetadataSemantics(WholeProgram parent, Sink sink, IDictionary<IUnit, PdbReader> pdbReaders, TraverserFactory factory)
        : base(sink, pdbReaders, factory) {
        this.parent = parent;
        this.sink = sink;
      }

      public override void TranslateAssemblies(IEnumerable<IUnit> assemblies) {
        #region traverse all of the units gathering type information
        var typeRecorder = new RecordSubtypes(this.parent.subTypes);
        foreach (var a in assemblies) {
          this.codeUnderAnalysis.Add(a, true);
          typeRecorder.Visit(a);
        }
        #endregion
        base.TranslateAssemblies(assemblies);
      }
      
      class RecordSubtypes : BaseMetadataTraverser {

        Dictionary<ITypeReference, List<ITypeReference>> subTypes;

        public RecordSubtypes(Dictionary<ITypeReference, List<ITypeReference>> subTypes) {
          this.subTypes = subTypes;
        }

        public override void Visit(ITypeDefinition typeDefinition) {
          foreach (var baseClass in typeDefinition.BaseClasses) {
            if (!this.subTypes.ContainsKey(baseClass)) {
              this.subTypes[baseClass] = new List<ITypeReference>();
            }
            this.subTypes[baseClass].Add(typeDefinition);
          }
          base.Visit(typeDefinition);
        }
      }

    }

    public override ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext) {
      return new WholeProgramExpressionSemantics(this, sink, statementTraverser, contractContext);
    }

    /// <summary>
    /// implement virtual method calls to methods defined in the CUA (code under analysis, i.e.,
    /// the set of assemblies being translated) by a "switch statement" that dispatches to the
    /// most derived type's method. I.e., make explicit the dynamic dispatch mechanism.
    /// </summary>
    public class WholeProgramExpressionSemantics : CLRSemantics.CLRExpressionSemantics {

      readonly WholeProgram parent;
      readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes;

      public WholeProgramExpressionSemantics(WholeProgram parent, Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext)
        : base(sink, statementTraverser, contractContext) {
        this.parent = parent;
        this.subTypes = parent.subTypes;
      }

      public override void Visit(IMethodCall methodCall) {

        if (!methodCall.IsVirtualCall) {
          base.Visit(methodCall);
          return;
        }
        var containingType = methodCall.MethodToCall.ContainingType;
        List<ITypeReference> subTypesOfContainingType;
        if (!this.subTypes.TryGetValue(containingType, out subTypesOfContainingType)) {
          base.Visit(methodCall);
          return;
        }
        Contract.Assert(0 < subTypesOfContainingType.Count);
        Contract.Assert(!methodCall.IsStaticCall);
        var resolvedMethod = methodCall.MethodToCall.ResolvedMethod;
        Contract.Assert(!resolvedMethod.IsConstructor);
        var overrides = FindOverrides(containingType, resolvedMethod);
        if (0 == overrides.Count) {
          base.Visit(methodCall);
          return;
        }

        Bpl.IToken token = methodCall.Token();

        List<Bpl.Expr> inexpr;
        List<Bpl.IdentifierExpr> outvars;
        Bpl.IdentifierExpr thisExpr;
        Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed;
        var proc = TranslateArgumentsAndReturnProcedure(token, methodCall.MethodToCall, resolvedMethod, methodCall.IsStaticCall ? null : methodCall.ThisArgument, methodCall.Arguments, out inexpr, out outvars, out thisExpr, out toBoxed);


        Bpl.QKeyValue attrib = null;
        foreach (var a in resolvedMethod.Attributes) {
          if (TypeHelper.GetTypeName(a.Type).EndsWith("AsyncAttribute")) {
            attrib = new Bpl.QKeyValue(token, "async", new List<object>(), null);
            break;
          }
        }

        var elseBranch = new Bpl.StmtListBuilder();

        var methodname = proc.Name;

        Bpl.CallCmd call;
        if (attrib != null)
          call = new Bpl.CallCmd(token, methodname, inexpr, outvars, attrib);
        else
          call = new Bpl.CallCmd(token, methodname, inexpr, outvars);
        elseBranch.Add(call);

        Bpl.IfCmd ifcmd = null;

        Contract.Assume(1 <= overrides.Count);
        foreach (var typeMethodPair in overrides) {
          var t = typeMethodPair.Item1;
          var m = typeMethodPair.Item2;
          var thenBranch = new Bpl.StmtListBuilder();
          methodname = TranslationHelper.CreateUniqueMethodName(m); // REVIEW: Shouldn't this be call to FindOrCreateProcedure?
          if (attrib != null)
            call = new Bpl.CallCmd(token, methodname, inexpr, outvars, attrib);
          else
            call = new Bpl.CallCmd(token, methodname, inexpr, outvars);
          thenBranch.Add(call);
          ifcmd = new Bpl.IfCmd(token,
            Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
            this.sink.Heap.DynamicType(inexpr[0]),
            this.sink.FindOrCreateType(t)
            ),
            thenBranch.Collect(token),
            null,
            elseBranch.Collect(token)
            );
          elseBranch = new Bpl.StmtListBuilder();
          elseBranch.Add(ifcmd);
        }

        this.StmtTraverser.StmtBuilder.Add(ifcmd);

        return;
      }

      /// <summary>
      /// Modifies <paramref name="overrides"/> as side-effect.
      /// </summary>
      private List<Tuple<ITypeReference, IMethodReference>> FindOverrides(ITypeReference type, IMethodDefinition resolvedMethod) {
        Contract.Requires(type != null);
        Contract.Requires(resolvedMethod != null);
        var overrides = new List<Tuple<ITypeReference, IMethodReference>>();
        foreach (var subType in this.subTypes[type]) {
          var overriddenMethod = MemberHelper.GetImplicitlyOverridingDerivedClassMethod(resolvedMethod, subType.ResolvedType);
          if (overriddenMethod != Dummy.Method) {
            resolvedMethod = overriddenMethod;
          }
          overrides.Add(Tuple.Create<ITypeReference, IMethodReference>(subType, resolvedMethod));
          if (this.subTypes.ContainsKey(subType)) {
            overrides.AddRange(FindOverrides(subType, resolvedMethod));
          }
        }
        return overrides;
      }

    }

  }
}
