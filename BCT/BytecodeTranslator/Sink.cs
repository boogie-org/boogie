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

    public IHeap Heap {
      get { return this.heap; }
    }
    readonly IHeap heap;

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
      this.FormalMap.TryGetValue(param, out mp);
      return mp.outParameterCopy;
    }
    public Dictionary<IParameterDefinition, MethodParameter> FormalMap = null;

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

    public Bpl.Procedure FindOrCreateProcedure(IMethodReference method, bool isStatic) {
      Bpl.Procedure proc;
      var key = method.InternedKey;
      if (!this.declaredMethods.TryGetValue(key, out proc)) {
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
        this.FormalMap = formalMap;

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

        IMethodContract contract = ContractProvider.GetMethodContractFor(method);

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

        proc = new Bpl.Procedure(method.Token(),
            MethodName,
            new Bpl.TypeVariableSeq(),
            new Bpl.VariableSeq(invars), // in
            new Bpl.VariableSeq(outvars), // out
            boogiePrecondition,
            boogieModifies,
            boogiePostcondition);


        this.TranslatedProgram.TopLevelDeclarations.Add(proc);
        this.declaredMethods.Add(key, proc);
      }
      return proc;
    }
    /// <summary>
    /// The keys to the table are the interned key of the field.
    /// </summary>
    private Dictionary<uint, Bpl.Procedure> declaredMethods = new Dictionary<uint, Bpl.Procedure>();

    public void BeginMethod() {
      this.localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();
      this.FormalMap = new Dictionary<IParameterDefinition, MethodParameter>();
    }

    public Dictionary<ITypeDefinition, HashSet<Bpl.Constant>> delegateTypeToDelegates =
      new Dictionary<ITypeDefinition, HashSet<Bpl.Constant>>();

    public void AddDelegate(ITypeDefinition type, Bpl.Constant constant)
    {
      if (!delegateTypeToDelegates.ContainsKey(type))
        delegateTypeToDelegates[type] = new HashSet<Bpl.Constant>();
      delegateTypeToDelegates[type].Add(constant);
    }

    public void AddDelegateType(ITypeDefinition type) {
      if (!delegateTypeToDelegates.ContainsKey(type))
        delegateTypeToDelegates[type] = new HashSet<Bpl.Constant>();
    }
  }

}