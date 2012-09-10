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

    public override BCTMetadataTraverser MakeMetadataTraverser(Sink sink,
      IDictionary<IUnit, IContractProvider> contractProviders, // TODO: remove this parameter?
      IDictionary<IUnit, PdbReader> pdbReaders) {
      return new WholeProgramMetadataSemantics(this, sink, pdbReaders, this);
    }

    public class WholeProgramMetadataSemantics : BCTMetadataTraverser {

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
          typeRecorder.Traverse((IAssembly)a);
        }
        #endregion
        #region Possibly gather exception information
        if (sink.Options.modelExceptions == 1) {
          this.sink.MethodThrowsExceptions = ExceptionAnalyzer.ComputeExplicitlyThrownExceptions(assemblies);
        }
          
        #endregion

        base.TranslateAssemblies(assemblies);
      }
      
      class RecordSubtypes : MetadataTraverser {

        Dictionary<ITypeReference, List<ITypeReference>> subTypes;

        public RecordSubtypes(Dictionary<ITypeReference, List<ITypeReference>> subTypes) {
          this.subTypes = subTypes;
        }

        public override void TraverseChildren(ITypeDefinition typeDefinition) {
          foreach (var baseClass in typeDefinition.BaseClasses) {
            if (!this.subTypes.ContainsKey(baseClass)) {
              this.subTypes[baseClass] = new List<ITypeReference>();
            }
            this.subTypes[baseClass].Add(typeDefinition);
          }

          foreach (var iface in typeDefinition.Interfaces) {
            if (!this.subTypes.ContainsKey(iface)) {
              this.subTypes[iface] = new List<ITypeReference>();
            }
            this.subTypes[iface].Add(typeDefinition);
          }
          base.TraverseChildren(typeDefinition);
        }
      }

    }

    public override ExpressionTraverser MakeExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement) {
      return new WholeProgramExpressionSemantics(this, sink, statementTraverser, contractContext, expressionIsStatement);
    }

    /// <summary>
    /// implement virtual method calls to methods defined in the CUA (code under analysis, i.e.,
    /// the set of assemblies being translated) by a "switch statement" that dispatches to the
    /// most derived type's method. I.e., make explicit the dynamic dispatch mechanism.
    /// </summary>
    public class WholeProgramExpressionSemantics : CLRSemantics.CLRExpressionSemantics {

      readonly WholeProgram parent;
      readonly public Dictionary<ITypeReference, List<ITypeReference>> subTypes;

      public WholeProgramExpressionSemantics(WholeProgram parent, Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement)
        : base(sink, statementTraverser, contractContext, expressionIsStatement) {
        this.parent = parent;
        this.subTypes = parent.subTypes;
      }

      public override void TraverseChildren(IMethodCall methodCall) {
        var resolvedMethod = Sink.Unspecialize(methodCall.MethodToCall).ResolvedMethod;

        var methodName = Microsoft.Cci.MemberHelper.GetMethodSignature(resolvedMethod);
        if (methodName.Equals("System.Object.GetHashCode") || methodName.Equals("System.Object.ToString")) {
          base.TraverseChildren(methodCall);
          return;
        }

        bool isEventAdd = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("add_");
        bool isEventRemove = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("remove_");
        if (isEventAdd || isEventRemove) {
          base.TraverseChildren(methodCall);
          return;
        }

        if (!methodCall.IsVirtualCall) {
          base.TraverseChildren(methodCall);
          return;
        }
        var containingType = methodCall.MethodToCall.ContainingType;
        List<ITypeReference> subTypesOfContainingType;
        if (!this.subTypes.TryGetValue(containingType, out subTypesOfContainingType)) {
          base.TraverseChildren(methodCall);
          return;
        }
        Contract.Assert(0 < subTypesOfContainingType.Count);
        Contract.Assert(!methodCall.IsStaticCall);
        Contract.Assert(!resolvedMethod.IsConstructor);
        var overrides = FindOverrides(containingType, resolvedMethod);
        bool same = true;
        foreach (var o in overrides) {
          IMethodDefinition resolvedOverride = Sink.Unspecialize(o.Item2).ResolvedMethod;
          if (resolvedOverride != resolvedMethod)
            same = false;
        }
        if (!(containingType.ResolvedType.IsInterface) && (0 == overrides.Count || same)) {
          base.TraverseChildren(methodCall);
          return;
        }

        Contract.Assume(1 <= overrides.Count);

        var getType = new Microsoft.Cci.MethodReference(
          this.sink.host,
          this.sink.host.PlatformType.SystemObject,
          CallingConvention.HasThis,
          this.sink.host.PlatformType.SystemType,
          this.sink.host.NameTable.GetNameFor("GetType"), 0);
        var op_Type_Equality = new Microsoft.Cci.MethodReference(
          this.sink.host,
          this.sink.host.PlatformType.SystemType,
          CallingConvention.Default,
          this.sink.host.PlatformType.SystemBoolean,
          this.sink.host.NameTable.GetNameFor("op_Equality"),
          0,
          this.sink.host.PlatformType.SystemType,
          this.sink.host.PlatformType.SystemType);

        // Depending on whether the method is a void method or not
        // Turn into expression:
        //   (o.GetType() == typeof(T1)) ? ((T1)o).M(...) : ( (o.GetType() == typeof(T2)) ? ((T2)o).M(...) : ...
        // Or turn into statements:
        //   if (o.GetType() == typeof(T1)) ((T1)o).M(...) else if ...
        var turnIntoStatements = resolvedMethod.Type.TypeCode == PrimitiveTypeCode.Void;
        IStatement elseStatement = null;

        IExpression elseValue = new MethodCall() {
          Arguments = new List<IExpression>(methodCall.Arguments),
          IsStaticCall = false,
          IsVirtualCall = false,
          MethodToCall = methodCall.MethodToCall,
          ThisArgument = methodCall.ThisArgument,
          Type = methodCall.Type,
        };
        if (turnIntoStatements)
          elseStatement = new ExpressionStatement() { Expression = elseValue, };

        Conditional ifConditional = null;
        ConditionalStatement ifStatement = null;

        foreach (var typeMethodPair in overrides) {
          var t = typeMethodPair.Item1;
          var m = typeMethodPair.Item2;

          if (m.IsGeneric) {
            var baseMethod = m.ResolvedMethod;
            m = new GenericMethodInstanceReference() {
              CallingConvention = baseMethod.CallingConvention,
              ContainingType = baseMethod.ContainingTypeDefinition,
              GenericArguments = new List<ITypeReference>(IteratorHelper.GetConversionEnumerable<IGenericMethodParameter, ITypeReference>(baseMethod.GenericParameters)),
              GenericMethod = baseMethod,
              InternFactory = this.sink.host.InternFactory,
              Name = baseMethod.Name,
              Parameters = baseMethod.ParameterCount == 0 ? null : new List<IParameterTypeInformation>(baseMethod.Parameters),
              Type = baseMethod.Type,
            };
          }

          var cond = new MethodCall() {
            Arguments = new List<IExpression>(){
                new MethodCall() {
                  Arguments = new List<IExpression>(),
                  IsStaticCall = false,
                  IsVirtualCall = false,
                  MethodToCall = getType,
                  ThisArgument = methodCall.ThisArgument,
                },
                new TypeOf() {
                  TypeToGet = t,
                },
              },
            IsStaticCall = true,
            IsVirtualCall = false,
            MethodToCall = op_Type_Equality,
            Type = this.sink.host.PlatformType.SystemBoolean,
          };
          var thenValue = new MethodCall() {
            Arguments = new List<IExpression>(methodCall.Arguments),
            IsStaticCall = false,
            IsVirtualCall = false,
            MethodToCall = m,
            ThisArgument = methodCall.ThisArgument,
            Type = t,
          };
          if (turnIntoStatements) {
            ifStatement = new ConditionalStatement() {
              Condition = cond,
              FalseBranch = elseStatement,
              TrueBranch = new ExpressionStatement() { Expression = thenValue, },
            };
            elseStatement = ifStatement;
          } else {
            ifConditional = new Conditional() {
              Condition = cond,
              ResultIfFalse = elseValue,
              ResultIfTrue = thenValue,
            };
            elseValue = ifConditional;
          }
        }
        if (turnIntoStatements) {
          Contract.Assume(ifStatement != null);
          this.StmtTraverser.Traverse(ifStatement);
        } else {
          Contract.Assume(ifConditional != null);
          base.Traverse(ifConditional);
        }

        return;
      }

      /// <summary>
      /// Modifies <paramref name="overrides"/> as side-effect.
      /// </summary>
      private List<Tuple<ITypeReference, IMethodReference>> FindOverrides(ITypeReference type, IMethodDefinition resolvedMethod) {
        Contract.Requires(type != null);
        Contract.Requires(resolvedMethod != null);
        var overrides = new List<Tuple<ITypeReference, IMethodReference>>();
        if (type.ResolvedType.IsInterface) {
          foreach (var subType in this.subTypes[type]) {
            var def = subType.ResolvedType;
            var foundSome = false; // prefer explicit, since if both are there, only the implicit get called through the iface pointer.
            foreach (var implementingMethod in GetExplicitlyImplementedMethods(def, resolvedMethod)) {
              overrides.Add(Tuple.Create<ITypeReference, IMethodReference>(subType, implementingMethod));
              foundSome = true;
            }
            if (!foundSome) { // look for implicit
              var mems = def.GetMatchingMembersNamed(resolvedMethod.Name, true,
                tdm => {
                  var m = tdm as IMethodDefinition;
                  if (m == null) return false;
                  return TypeHelper.ParameterListsAreEquivalentAssumingGenericMethodParametersAreEquivalentIfTheirIndicesMatch(
                    m.Parameters, resolvedMethod.Parameters);
                });
              foreach (var mem in mems) {
                var methodDef = mem as IMethodDefinition;
                if (methodDef == null) continue;
                overrides.Add(Tuple.Create<ITypeReference, IMethodReference>(subType, methodDef));

              }
            }
          }
        } else {
          foreach (var subType in this.subTypes[type]) {
            var overridingMethod = MemberHelper.GetImplicitlyOverridingDerivedClassMethod(resolvedMethod, subType.ResolvedType);
            if (overridingMethod != Dummy.Method) {
              resolvedMethod = overridingMethod;
            }
            overrides.Add(Tuple.Create<ITypeReference, IMethodReference>(subType, resolvedMethod));
            if (this.subTypes.ContainsKey(subType)) {
              overrides.AddRange(FindOverrides(subType, resolvedMethod));
            }
          }
        }
        return overrides;
      }

      /// <summary>
      /// Returns zero or more explicit implementations of an interface method that are defined in the given type definition.
      /// </summary>
      /// <remarks>
      /// IMethodReferences are returned (as opposed to IMethodDefinitions) because the references are directly available:
      /// no resolving is needed to find them.
      /// </remarks>
      public static IEnumerable<IMethodReference> GetExplicitlyImplementedMethods(ITypeDefinition typeDefinition, IMethodDefinition ifaceMethod) {
        Contract.Requires(ifaceMethod != null);
        Contract.Ensures(Contract.Result<IEnumerable<IMethodReference>>() != null);
        Contract.Ensures(Contract.ForAll(Contract.Result<IEnumerable<IMethodReference>>(), x => x != null));

        foreach (IMethodImplementation methodImplementation in typeDefinition.ExplicitImplementationOverrides) {
          if (ifaceMethod.InternedKey == methodImplementation.ImplementedMethod.InternedKey)
            yield return methodImplementation.ImplementingMethod;
        }
        var mems = TypeHelper.GetMethod(typeDefinition, ifaceMethod.Name, ifaceMethod.Parameters.Select(p => p.Type).ToArray());
      }


    }

  }
}
