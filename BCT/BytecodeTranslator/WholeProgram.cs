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

    /// <summary>
    /// Table to be filled by the metadata traverser when it first gets to an assembly.
    /// [TODO: It should be full set of assemblies that are being translated (CUA).]
    /// 
    /// The table lists the direct supertypes of all type definitions that it encounters during the
    /// traversal. (But the table is organized so that subTypes[T] is the list of type definitions
    /// that are direct subtypes of T.)
    /// </summary>
    readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes = new Dictionary<ITypeReference, List<ITypeReference>>();

    public override MetadataTraverser MakeMetadataTraverser(IContractProvider contractProvider, PdbReader pdbReader, HeapFactory heapFactory) {
      return new WholeProgramMetadataSemantics(this, new Sink(this, heapFactory, contractProvider), pdbReader);
    }

    public class WholeProgramMetadataSemantics : MetadataTraverser {

      readonly WholeProgram parent;
      readonly Sink sink;

      /// <summary>
      /// TODO: Need to have this populated before any of the assemblies in the CUA are traversed.
      /// </summary>
      readonly Dictionary<IAssembly, bool> codeUnderAnalysis = new Dictionary<IAssembly, bool>();

      public WholeProgramMetadataSemantics(WholeProgram parent, Sink sink, PdbReader/*?*/ pdbReader)
        : base(sink, pdbReader) {
        this.parent = parent;
        this.sink = sink;
      }

      public override void Visit(IAssembly assembly) {

        #region When doing whole-program analysis, traverse the assembly gathering type information
        this.codeUnderAnalysis.Add(assembly, true);
        var typeRecorder = new RecordSubtypes(this.parent.subTypes);
        typeRecorder.Visit(assembly);
        #endregion

        base.Visit(assembly);

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

    public override ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser) {
      return new WholeProgramExpressionSemantics(this, sink, statementTraverser);
    }

    /// <summary>
    /// implement virtual method calls to methods defined in the CUA (code under analysis, i.e.,
    /// the set of assemblies being translated) by a "switch statement" that dispatches to the
    /// most derived type's method. I.e., make explicit the dynamic dispatch mechanism.
    /// </summary>
    public class WholeProgramExpressionSemantics : CLRSemantics.CLRExpressionSemantics {

      readonly WholeProgram parent;
      readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes;

      public WholeProgramExpressionSemantics(WholeProgram parent, Sink sink, StatementTraverser/*?*/ statementTraverser)
        : base(sink, statementTraverser) {
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

        #region Translate In Parameters

        var inexpr = new List<Bpl.Expr>();
        #region Create the 'this' argument for the function call
        this.Visit(methodCall.ThisArgument);
        inexpr.Add(this.TranslatedExpressions.Pop());
        #endregion

        Dictionary<IParameterDefinition, Bpl.Expr> p2eMap = new Dictionary<IParameterDefinition, Bpl.Expr>();
        IEnumerator<IParameterDefinition> penum = resolvedMethod.Parameters.GetEnumerator();
        penum.MoveNext();
        foreach (IExpression exp in methodCall.Arguments) {
          if (penum.Current == null) {
            throw new TranslationException("More Arguments than Parameters in functioncall");
          }
          this.Visit(exp);
          Bpl.Expr e = this.TranslatedExpressions.Pop();

          p2eMap.Add(penum.Current, e);
          if (!penum.Current.IsOut) {
            inexpr.Add(e);
          }

          penum.MoveNext();
        }
        #endregion

        Bpl.IToken token = methodCall.Token();

        // TODO: if there is no stmttraverser we are visiting a contract and should use a boogie function instead of procedure!

        #region Translate Out vars
        var outvars = new List<Bpl.IdentifierExpr>();

        foreach (KeyValuePair<IParameterDefinition, Bpl.Expr> kvp in p2eMap) {
          if (kvp.Key.IsOut || kvp.Key.IsByReference) {
            Bpl.IdentifierExpr iexp = kvp.Value as Bpl.IdentifierExpr;
            if (iexp == null) {
              throw new TranslationException("Trying to pass complex expression as out in functioncall");
            }
            outvars.Add(iexp);
          }
        }
        #endregion

        if (methodCall.Type.ResolvedType.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Variable v = this.sink.CreateFreshLocal(methodCall.Type.ResolvedType);
          outvars.Add(new Bpl.IdentifierExpr(token, v));
          TranslatedExpressions.Push(new Bpl.IdentifierExpr(token, v));
        }

        Bpl.QKeyValue attrib = null;
        foreach (var a in resolvedMethod.Attributes) {
          if (TypeHelper.GetTypeName(a.Type).EndsWith("AsyncAttribute")) {
            attrib = new Bpl.QKeyValue(token, "async", new List<object>(), null);
            break;
          }
        }

        var elseBranch = new Bpl.StmtListBuilder();

        var proc = this.sink.FindOrCreateProcedure(resolvedMethod, resolvedMethod.IsStatic);
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
            Bpl.Expr.Ident(this.sink.FindOrCreateType(t))
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
