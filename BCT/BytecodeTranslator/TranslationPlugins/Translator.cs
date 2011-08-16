using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace BytecodeTranslator.TranslationPlugins {
  public abstract class Translator {
    public abstract void initialize();
    public abstract bool isOneShot();
    public abstract int getPriority();

    public virtual void TranslateAssemblies(IEnumerable<IUnit> assemblies) { }

    // Each plugged translator may choose to implement some action on each metadata / AST element
    public virtual void onMetadataElement(IArrayTypeReference arrayTypeReference) { }
    public virtual void onMetadataElement(IAssembly assembly) { }
    public virtual void onMetadataElement(IAssemblyReference assemblyReference) { }
    public virtual void onMetadataElement(ICustomAttribute customAttribute) { }
    public virtual void onMetadataElement(ICustomModifier customModifier) { }
    public virtual void onMetadataElement(IEventDefinition eventDefinition) { }
    public virtual void onMetadataElement(IFieldDefinition fieldDefinition) { }
    public virtual void onMetadataElement(IFieldReference fieldReference) { }
    public virtual void onMetadataElement(IFileReference fileReference) { }
    public virtual void onMetadataElement(IFunctionPointerTypeReference functionPointerTypeReference) { }
    public virtual void onMetadataElement(IGenericMethodInstanceReference genericMethodInstanceReference) { }
    public virtual void onMetadataElement(IGenericMethodParameter genericMethodParameter) { }
    public virtual void onMetadataElement(IGenericMethodParameterReference genericMethodParameterReference) { }
    public virtual void onMetadataElement(IGlobalFieldDefinition globalFieldDefinition) { }
    public virtual void onMetadataElement(IGlobalMethodDefinition globalMethodDefinition) { }
    public virtual void onMetadataElement(IGenericTypeInstanceReference genericTypeInstanceReference) { }
    public virtual void onMetadataElement(IGenericTypeParameter genericTypeParameter) { }
    public virtual void onMetadataElement(IGenericTypeParameterReference genericTypeParameterReference) { }
    public virtual void onMetadataElement(ILocalDefinition localDefinition) { }
    public virtual void onMetadataElement(IManagedPointerTypeReference managedPointerTypeReference) { }
    public virtual void onMetadataElement(IMarshallingInformation marshallingInformation) { }
    public virtual void onMetadataElement(IMetadataConstant constant) { }
    public virtual void onMetadataElement(IMetadataCreateArray createArray) { }
    public virtual void onMetadataElement(IMetadataExpression expression) { }
    public virtual void onMetadataElement(IMetadataNamedArgument namedArgument) { }
    public virtual void onMetadataElement(IMetadataTypeOf typeOf) { }
    public virtual void onMetadataElement(IMethodBody methodBody) { }
    public virtual void onMetadataElement(IMethodDefinition method) { }
    public virtual void onMetadataElement(IMethodImplementation methodImplementation) { }
    public virtual void onMetadataElement(IMethodReference methodReference) { }
    public virtual void onMetadataElement(IModifiedTypeReference modifiedTypeReference) { }
    public virtual void onMetadataElement(IModule module) { }
    public virtual void onMetadataElement(IModuleReference moduleReference) { }
    public virtual void onMetadataElement(INamespaceAliasForType namespaceAliasForType) { }
    public virtual void onMetadataElement(INamespaceTypeDefinition namespaceTypeDefinition) { }
    public virtual void onMetadataElement(INamespaceTypeReference namespaceTypeReference) { }
    public virtual void onMetadataElement(INestedAliasForType nestedAliasForType) { }
    public virtual void onMetadataElement(INestedTypeDefinition nestedTypeDefinition) { }
    public virtual void onMetadataElement(INestedTypeReference nestedTypeReference) { }
    public virtual void onMetadataElement(INestedUnitNamespace nestedUnitNamespace) { }
    public virtual void onMetadataElement(INestedUnitNamespaceReference nestedUnitNamespaceReference) { }
    public virtual void onMetadataElement(INestedUnitSetNamespace nestedUnitSetNamespace) { }
    public virtual void onMetadataElement(IOperation operation) { }
    public virtual void onMetadataElement(IOperationExceptionInformation operationExceptionInformation) { }
    public virtual void onMetadataElement(IParameterDefinition parameterDefinition) { }
    public virtual void onMetadataElement(IParameterTypeInformation parameterTypeInformation) { }
    public virtual void onMetadataElement(IPESection peSection) { }
    public virtual void onMetadataElement(IPlatformInvokeInformation platformInvokeInformation) { }
    public virtual void onMetadataElement(IPointerTypeReference pointerTypeReference) { }
    public virtual void onMetadataElement(IPropertyDefinition propertyDefinition) { }
    public virtual void onMetadataElement(IResourceReference resourceReference) { }
    public virtual void onMetadataElement(IRootUnitNamespace rootUnitNamespace) { }
    public virtual void onMetadataElement(IRootUnitNamespaceReference rootUnitNamespaceReference) { }
    public virtual void onMetadataElement(IRootUnitSetNamespace rootUnitSetNamespace) { }
    public virtual void onMetadataElement(ISecurityAttribute securityAttribute) { }
    public virtual void onMetadataElement(ISpecializedEventDefinition specializedEventDefinition) { }
    public virtual void onMetadataElement(ISpecializedFieldDefinition specializedFieldDefinition) { }
    public virtual void onMetadataElement(ISpecializedFieldReference specializedFieldReference) { }
    public virtual void onMetadataElement(ISpecializedMethodDefinition specializedMethodDefinition) { }
    public virtual void onMetadataElement(ISpecializedMethodReference specializedMethodReference) { }
    public virtual void onMetadataElement(ISpecializedPropertyDefinition specializedPropertyDefinition) { }
    public virtual void onMetadataElement(ISpecializedNestedTypeDefinition specializedNestedTypeDefinition) { }
    public virtual void onMetadataElement(ISpecializedNestedTypeReference specializedNestedTypeReference) { }
    public virtual void onMetadataElement(IUnitSet unitSet) { }
    public virtual void onMetadataElement(IWin32Resource win32Resource) { }

    public virtual void onASTElement(IAddition addition) { }
    public virtual void onASTElement(IAddressableExpression addressableExpression) { }
    public virtual void onASTElement(IAddressDereference addressDereference) { }
    public virtual void onASTElement(IAddressOf addressOf) { }
    public virtual void onASTElement(IAnonymousDelegate anonymousDelegate) { }
    public virtual void onASTElement(IArrayIndexer arrayIndexer) { }
    public virtual void onASTElement(IAssertStatement assertStatement) { }
    public virtual void onASTElement(IAssignment assignment) { }
    public virtual void onASTElement(IAssumeStatement assumeStatement) { }
    public virtual void onASTElement(IBitwiseAnd bitwiseAnd) { }
    public virtual void onASTElement(IBitwiseOr bitwiseOr) { }
    public virtual void onASTElement(IBlockExpression blockExpression) { }
    public virtual void onASTElement(IBlockStatement block) { }
    public virtual void onASTElement(IBreakStatement breakStatement) { }
    public virtual void onASTElement(IBoundExpression boundExpression) { }
    public virtual void onASTElement(ICastIfPossible castIfPossible) { }
    public virtual void onASTElement(ICatchClause catchClause) { }
    public virtual void onASTElement(ICheckIfInstance checkIfInstance) { }
    public virtual void onASTElement(ICompileTimeConstant constant) { }
    public virtual void onASTElement(IConversion conversion) { }
    public virtual void onASTElement(IConditional conditional) { }
    public virtual void onASTElement(IConditionalStatement conditionalStatement) { }
    public virtual void onASTElement(IContinueStatement continueStatement) { }
    public virtual void onASTElement(ICreateArray createArray) { }
    public virtual void onASTElement(ICreateDelegateInstance createDelegateInstance) { }
    public virtual void onASTElement(ICreateObjectInstance createObjectInstance) { }
    public virtual void onASTElement(IDebuggerBreakStatement debuggerBreakStatement) { }
    public virtual void onASTElement(IDefaultValue defaultValue) { }
    public virtual void onASTElement(IDivision division) { }
    public virtual void onASTElement(IDoUntilStatement doUntilStatement) { }
    public virtual void onASTElement(IDupValue dupValue) { }
    public virtual void onASTElement(IEmptyStatement emptyStatement) { }
    public virtual void onASTElement(IEquality equality) { }
    public virtual void onASTElement(IExclusiveOr exclusiveOr) { }
    public virtual void onASTElement(IExpressionStatement expressionStatement) { }
    public virtual void onASTElement(IForEachStatement forEachStatement) { }
    public virtual void onASTElement(IForStatement forStatement) { }
    public virtual void onASTElement(IGotoStatement gotoStatement) { }
    public virtual void onASTElement(IGotoSwitchCaseStatement gotoSwitchCaseStatement) { }
    public virtual void onASTElement(IGetTypeOfTypedReference getTypeOfTypedReference) { }
    public virtual void onASTElement(IGetValueOfTypedReference getValueOfTypedReference) { }
    public virtual void onASTElement(IGreaterThan greaterThan) { }
    public virtual void onASTElement(IGreaterThanOrEqual greaterThanOrEqual) { }
    public virtual void onASTElement(ILabeledStatement labeledStatement) { }
    public virtual void onASTElement(ILeftShift leftShift) { }
    public virtual void onASTElement(ILessThan lessThan) { }
    public virtual void onASTElement(ILessThanOrEqual lessThanOrEqual) { }
    public virtual void onASTElement(ILocalDeclarationStatement localDeclarationStatement) { }
    public virtual void onASTElement(ILockStatement lockStatement) { }
    public virtual void onASTElement(ILogicalNot logicalNot) { }
    public virtual void onASTElement(IMakeTypedReference makeTypedReference) { }
    public virtual void onASTElement(IMethodCall methodCall) { }
    public virtual void onASTElement(IModulus modulus) { }
    public virtual void onASTElement(IMultiplication multiplication) { }
    public virtual void onASTElement(INamedArgument namedArgument) { }
    public virtual void onASTElement(INotEquality notEquality) { }
    public virtual void onASTElement(IOldValue oldValue) { }
    public virtual void onASTElement(IOnesComplement onesComplement) { }
    public virtual void onASTElement(IOutArgument outArgument) { }
    public virtual void onASTElement(IPointerCall pointerCall) { }
    public virtual void onASTElement(IPopValue popValue) { }
    public virtual void onASTElement(IPushStatement pushStatement) { }
    public virtual void onASTElement(IRefArgument refArgument) { }
    public virtual void onASTElement(IResourceUseStatement resourceUseStatement) { }
    public virtual void onASTElement(IReturnValue returnValue) { }
    public virtual void onASTElement(IRethrowStatement rethrowStatement) { }
    public virtual void onASTElement(IReturnStatement returnStatement) { }
    public virtual void onASTElement(IRightShift rightShift) { }
    public virtual void onASTElement(IRuntimeArgumentHandleExpression runtimeArgumentHandleExpression) { }
    public virtual void onASTElement(ISizeOf sizeOf) { }
    public virtual void onASTElement(IStackArrayCreate stackArrayCreate) { }
    public virtual void onASTElement(ISubtraction subtraction) { }
    public virtual void onASTElement(ISwitchCase switchCase) { }
    public virtual void onASTElement(ISwitchStatement switchStatement) { }
    public virtual void onASTElement(ITargetExpression targetExpression) { }
    public virtual void onASTElement(IThisReference thisReference) { }
    public virtual void onASTElement(IThrowStatement throwStatement) { }
    public virtual void onASTElement(ITryCatchFinallyStatement tryCatchFilterFinallyStatement) { }
    public virtual void onASTElement(ITokenOf tokenOf) { }
    public virtual void onASTElement(ITypeOf typeOf) { }
    public virtual void onASTElement(IUnaryNegation unaryNegation) { }
    public virtual void onASTElement(IUnaryPlus unaryPlus) { }
    public virtual void onASTElement(IVectorLength vectorLength) { }
    public virtual void onASTElement(IWhileDoStatement whileDoStatement) { }
    public virtual void onASTElement(IYieldBreakStatement yieldBreakStatement) { }
    public virtual void onASTElement(IYieldReturnStatement yieldReturnStatement) { }
  }
}
