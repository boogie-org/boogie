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

    public Sink(TraverserFactory factory, HeapFactory heapFactory) {
      this.factory = factory;
      var b = heapFactory.MakeHeap(this, out this.heap, out this.TranslatedProgram); // TODO: what if it returns false?
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
    /// The keys to the table are tuples of the containing type (its interned key) and the name of the field. That
    /// should uniquely identify each field.
    /// </summary>
    private Dictionary<uint, Bpl.Variable> declaredFields = new Dictionary<uint, Bpl.Variable>();

    public void BeginMethod() {
      this.localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();
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