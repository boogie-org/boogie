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
using System.Diagnostics.Contracts;

using Bpl = Microsoft.Boogie;


namespace BytecodeTranslator {

  public class Sink {

    public TraverserFactory Factory {
      get { return this.factory; }
    }
    readonly TraverserFactory factory;
    public readonly IContractProvider ContractProvider;

    public Sink(TraverserFactory factory, HeapFactory heapFactory, IContractProvider contractProvider) {
      this.factory = factory;
      var b = heapFactory.MakeHeap(this, out this.heap, out this.TranslatedProgram); // TODO: what if it returns false?
      this.ContractProvider = contractProvider;
      if (this.TranslatedProgram == null)
        this.TranslatedProgram = new Bpl.Program();
    }

    public Heap Heap {
      get { return this.heap; }
    }
    readonly Heap heap;

    public Bpl.Variable ArrayContentsVariable
    {
        get { return this.arrayContentsVariable; }
    }
    readonly Bpl.Variable arrayContentsVariable = TranslationHelper.TempArrayContentsVar();

    public Bpl.Variable ArrayLengthVariable
    {
        get { return this.arrayLengthVariable; }
    }
    readonly Bpl.Variable arrayLengthVariable = TranslationHelper.TempArrayLengthVar();

    public Bpl.Variable ThisVariable = TranslationHelper.TempThisVar();
    public Bpl.Variable RetVariable;

    public readonly string AllocationMethodName = "Alloc";
    public readonly string StaticFieldFunction = "ClassRepr";
    public readonly string ReferenceTypeName = "Ref";

    public readonly string DelegateAddHelperName = "DelegateAddHelper";
    public readonly string DelegateAddName = "DelegateAdd";
    public readonly string DelegateRemoveName = "DelegateRemove";

    public Bpl.Expr ReadHead(Bpl.Expr delegateReference)
    {
      return Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.DelegateHead), delegateReference);
    }

    public Bpl.Expr ReadNext(Bpl.Expr delegateReference, Bpl.Expr listNodeReference)
    {
      return Bpl.Expr.Select(Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.DelegateNext), delegateReference), listNodeReference);
    }

    public Bpl.Expr ReadMethod(Bpl.Expr delegateReference, Bpl.Expr listNodeReference)
    {
      return Bpl.Expr.Select(Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.DelegateMethod), delegateReference), listNodeReference);
    }

    public Bpl.Expr ReadReceiver(Bpl.Expr delegateReference, Bpl.Expr listNodeReference)
    {
      return Bpl.Expr.Select(Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.DelegateReceiver), delegateReference), listNodeReference);
    }
    
    public readonly Bpl.Program TranslatedProgram;

    /// <summary>
    /// Creates a fresh local var of the given Type and adds it to the
    /// Bpl Implementation
    /// </summary>
    /// <param name="typeReference"> The type of the new variable </param>
    /// <returns> A fresh Variable with automatic generated name and location </returns>
    public Bpl.Variable CreateFreshLocal(ITypeReference typeReference) {
      Bpl.IToken loc = Bpl.Token.NoToken; // Helper Variables do not have a location
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(typeReference);
      Bpl.LocalVariable v = new Bpl.LocalVariable(loc, new Bpl.TypedIdent(loc, TranslationHelper.GenerateTempVarName(), t));
      ILocalDefinition dummy = new LocalDefinition(); // Creates a dummy entry for the Dict, since only locals in the dict are translated to boogie
      localVarMap.Add(dummy, v);
      return v;
    }

    private Dictionary<ILocalDefinition, Bpl.LocalVariable> localVarMap = null;
    public Dictionary<ILocalDefinition, Bpl.LocalVariable> LocalVarMap {
      get { return this.localVarMap; }
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="local"></param>
    /// <returns></returns>
    public Bpl.Variable FindOrCreateLocalVariable(ILocalDefinition local) {
      Bpl.LocalVariable v;
      Bpl.IToken tok = local.Token();
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(local.Type.ResolvedType);
      if (!localVarMap.TryGetValue(local, out v)) {
        v = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, local.Name.Value, t));
        localVarMap.Add(local, v);
      }
      return v;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="param"></param>
    /// <remarks>STUB</remarks>
    /// <returns></returns>
    public Bpl.Variable FindParameterVariable(IParameterDefinition param) {
      MethodParameter mp;
      ProcedureInfo procAndFormalMap;
      this.declaredMethods.TryGetValue(param.ContainingSignature, out procAndFormalMap);
      var formalMap = procAndFormalMap.FormalMap;
      formalMap.TryGetValue(param, out mp);
      return mp.outParameterCopy;
    }

    public Bpl.Variable FindOrCreateFieldVariable(IFieldReference field) {
      // The Heap has to decide how to represent the field (i.e., its type),
      // all the Sink cares about is adding a declaration for it.
      Bpl.Variable v;
      var key = field.InternedKey;
      if (!this.declaredFields.TryGetValue(key, out v)) {
        v = this.Heap.CreateFieldVariable(field);
        this.declaredFields.Add(key, v);
        this.TranslatedProgram.TopLevelDeclarations.Add(v);
      }
      return v;
    }
    /// <summary>
    /// The keys to the table are the interned key of the field.
    /// </summary>
    private Dictionary<uint, Bpl.Variable> declaredFields = new Dictionary<uint, Bpl.Variable>();

    public Bpl.Variable FindOrCreateEventVariable(IEventDefinition e)
    {
      Bpl.Variable v;
      if (!this.declaredEvents.TryGetValue(e, out v))
      {
        v = this.Heap.CreateEventVariable(e);
        this.declaredEvents.Add(e, v);
        this.TranslatedProgram.TopLevelDeclarations.Add(v);
      }
      return v;
    }

    private Dictionary<IEventDefinition, Bpl.Variable> declaredEvents = new Dictionary<IEventDefinition, Bpl.Variable>();

    public Bpl.Variable FindOrCreatePropertyVariable(IPropertyDefinition p)
    {
      return null;
    }

    public Bpl.Constant FindOrCreateConstant(string str) {
      Bpl.Constant c;
      if (!this.declaredStringConstants.TryGetValue(str, out c)) {
        var tok = Bpl.Token.NoToken;
        var t = Bpl.Type.Int;
        var name = "$string_literal_" + TranslationHelper.TurnStringIntoValidIdentifier(str);
        var tident = new Bpl.TypedIdent(tok, name, t);
        c = new Bpl.Constant(tok, tident, true);
        this.declaredStringConstants.Add(str, c);
        this.TranslatedProgram.TopLevelDeclarations.Add(c);
      }
      return c;
    }
    private Dictionary<string, Bpl.Constant> declaredStringConstants = new Dictionary<string, Bpl.Constant>();

    private Dictionary<IPropertyDefinition, Bpl.Variable> declaredProperties = new Dictionary<IPropertyDefinition, Bpl.Variable>();

    public struct ProcedureInfo {
      private Bpl.Procedure proc;
      private Dictionary<IParameterDefinition, MethodParameter> formalMap;
      private Bpl.Variable returnVariable;

      public ProcedureInfo(Bpl.Procedure proc, Dictionary<IParameterDefinition, MethodParameter> formalMap, Bpl.Variable returnVariable) {
        this.proc = proc;
        this.formalMap = formalMap;
        this.returnVariable = returnVariable;
      }

      public Bpl.Procedure Procedure { get { return proc; } }
      public Dictionary<IParameterDefinition, MethodParameter> FormalMap { get { return formalMap; } }
      public Bpl.Variable ReturnVariable { get { return returnVariable; } }
    }

    public Bpl.Procedure FindOrCreateProcedure(IMethodReference method, bool isStatic) {
      ProcedureInfo procAndFormalMap;

      var key = method; //.InternedKey;
      if (!this.declaredMethods.TryGetValue(key, out procAndFormalMap)) {
        #region Create in- and out-parameters

        int in_count = 0;
        int out_count = 0;
        MethodParameter mp;
        var formalMap = new Dictionary<IParameterDefinition, MethodParameter>();
        foreach (IParameterDefinition formal in method.Parameters) {

          mp = new MethodParameter(formal);
          if (mp.inParameterCopy != null) in_count++;
          if (mp.outParameterCopy != null && (formal.IsByReference || formal.IsOut))
            out_count++;
          formalMap.Add(formal, mp);
        }

        #region Look for Returnvalue

        if (method.Type.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Type rettype = TranslationHelper.CciTypeToBoogie(method.Type);
          out_count++;
          this.RetVariable = new Bpl.Formal(method.Token(),
              new Bpl.TypedIdent(method.Type.Token(),
                  "$result", rettype), false);
        } else {
          this.RetVariable = null;
        }

        #endregion

        Bpl.Formal/*?*/ self = null;
        #region Create 'this' parameter
        if (!isStatic) {
          in_count++;
          Bpl.Type selftype = Bpl.Type.Int;
          self = new Bpl.Formal(method.Token(),
              new Bpl.TypedIdent(method.Type.Token(),
                  "this", selftype), true);
        }
        #endregion

        Bpl.Variable[] invars = new Bpl.Formal[in_count];
        Bpl.Variable[] outvars = new Bpl.Formal[out_count];

        int i = 0;
        int j = 0;

        #region Add 'this' parameter as first in parameter
        if (!isStatic)
          invars[i++] = self;
        #endregion

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            invars[i++] = mparam.inParameterCopy;
          }
          if (mparam.outParameterCopy != null) {
            if (mparam.underlyingParameter.IsByReference || mparam.underlyingParameter.IsOut)
              outvars[j++] = mparam.outParameterCopy;
          }
        }

        #region add the returnvalue to out if there is one
        if (this.RetVariable != null) outvars[j] = this.RetVariable;
        #endregion

        #endregion

        #region Check The Method Contracts
        Bpl.RequiresSeq boogiePrecondition = new Bpl.RequiresSeq();
        Bpl.EnsuresSeq boogiePostcondition = new Bpl.EnsuresSeq();
        Bpl.IdentifierExprSeq boogieModifies = new Bpl.IdentifierExprSeq();

        var possiblyUnspecializedMethod = Unspecialize(method);
        IMethodContract contract = ContractProvider.GetMethodContractFor(possiblyUnspecializedMethod);

        if (contract != null) {
          try {
            foreach (IPrecondition pre in contract.Preconditions) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this, null);
              exptravers.Visit(pre.Condition); // TODO
              // Todo: Deal with Descriptions


              Bpl.Requires req
                  = new Bpl.Requires(pre.Token(),
                      false, exptravers.TranslatedExpressions.Pop(), "");
              boogiePrecondition.Add(req);
            }

            foreach (IPostcondition post in contract.Postconditions) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this, null);

              exptravers.Visit(post.Condition);
              // Todo: Deal with Descriptions

              Bpl.Ensures ens =
                  new Bpl.Ensures(post.Token(),
                      false, exptravers.TranslatedExpressions.Pop(), "");
              boogiePostcondition.Add(ens);
            }

            foreach (IAddressableExpression mod in contract.ModifiedVariables) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this, null);
              exptravers.Visit(mod);

              Bpl.IdentifierExpr idexp = exptravers.TranslatedExpressions.Pop() as Bpl.IdentifierExpr;

              if (idexp == null) {
                throw new TranslationException(String.Format("Cannot create IdentifierExpr for Modifyed Variable {0}", mod.ToString()));
              }
              boogieModifies.Add(idexp);
            }
          } catch (TranslationException te) {
            throw new NotImplementedException("Cannot Handle Errors in Method Contract: " + te.ToString());
          } catch {
            throw;
          }
        }

        #endregion

        string MethodName = TranslationHelper.CreateUniqueMethodName(method);

        var proc = new Bpl.Procedure(method.Token(),
            MethodName,
            new Bpl.TypeVariableSeq(),
            new Bpl.VariableSeq(invars), // in
            new Bpl.VariableSeq(outvars), // out
            boogiePrecondition,
            boogieModifies,
            boogiePostcondition);


        this.TranslatedProgram.TopLevelDeclarations.Add(proc);
        procAndFormalMap = new ProcedureInfo(proc, formalMap, this.RetVariable);
        this.declaredMethods.Add(key, procAndFormalMap);
      }
      return procAndFormalMap.Procedure;
    }
    public ProcedureInfo FindOrCreateProcedureAndReturnProcAndFormalMap(IMethodDefinition method, bool isStatic) {
      this.FindOrCreateProcedure(method, isStatic);
      return this.declaredMethods[method];
    }
    private static IMethodReference Unspecialize(IMethodReference method) {
      IMethodReference result = method;
      var gmir = result as IGenericMethodInstanceReference;
      if (gmir != null) {
        result = gmir.GenericMethod;
      }
      var smr = result as ISpecializedMethodReference;
      if (smr != null) {
        result = smr.UnspecializedVersion;
      }
      // Temporary hack until ISpecializedMethodDefinition implements ISpecializedMethodReference
      var smd = result as ISpecializedMethodDefinition;
      if (smd != null) {
        result = smd.UnspecializedVersion;
      }
      return result;
    }



    /// <summary>
    /// Creates a fresh variable that represents the type of
    /// <paramref name="type"/> in the Bpl program. I.e., its
    /// value represents the expression "typeof(type)".
    /// </summary>
    public Bpl.Variable FindOrCreateType(ITypeReference type) {
      // The Heap has to decide how to represent the field (i.e., its type),
      // all the Sink cares about is adding a declaration for it.
      Bpl.Variable t;
      var key = type.InternedKey;
      if (!this.declaredTypes.TryGetValue(key, out t)) {
        t = this.Heap.CreateTypeVariable(type);
        this.declaredTypes.Add(key, t);
        this.TranslatedProgram.TopLevelDeclarations.Add(t);
      }
      return t;
    }
    /// <summary>
    /// The keys to the table are the interned key of the type.
    /// </summary>
    private Dictionary<uint, Bpl.Variable> declaredTypes = new Dictionary<uint, Bpl.Variable>();

    /// <summary>
    /// The keys to the table are the signatures of the methods.
    /// The values are pairs: first element is the procedure,
    /// second element is the formal map for the procedure
    /// </summary>
    private Dictionary<ISignature, ProcedureInfo> declaredMethods = new Dictionary<ISignature, ProcedureInfo>();

    public void BeginMethod() {
      this.localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();
    }

    public Dictionary<ITypeDefinition, HashSet<IMethodDefinition>> delegateTypeToDelegates = new Dictionary<ITypeDefinition, HashSet<IMethodDefinition>>();

    public void AddDelegate(ITypeDefinition type, IMethodDefinition defn)
    {
      if (!delegateTypeToDelegates.ContainsKey(type))
        delegateTypeToDelegates[type] = new HashSet<IMethodDefinition>();
      delegateTypeToDelegates[type].Add(defn);
    }

    public void AddDelegateType(ITypeDefinition type) {
      if (!delegateTypeToDelegates.ContainsKey(type))
        delegateTypeToDelegates[type] = new HashSet<IMethodDefinition>();
    }

    private Dictionary<IMethodDefinition, Bpl.Constant> delegateMethods = new Dictionary<IMethodDefinition, Bpl.Constant>();

    public Bpl.Constant FindOrAddDelegateMethodConstant(IMethodDefinition defn)
    {
      if (delegateMethods.ContainsKey(defn))
        return delegateMethods[defn];
      string methodName = TranslationHelper.CreateUniqueMethodName(defn);
      var typedIdent = new Bpl.TypedIdent(Bpl.Token.NoToken, methodName, Bpl.Type.Int);
      var constant = new Bpl.Constant(Bpl.Token.NoToken, typedIdent, true);
      this.TranslatedProgram.TopLevelDeclarations.Add(constant);
      delegateMethods[defn] = constant;
      return constant;
    }
  }

}