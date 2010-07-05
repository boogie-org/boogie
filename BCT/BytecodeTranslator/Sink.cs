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

    public Sink(TraverserFactory factory) {
      this.factory = factory;
    }

    public Bpl.Variable HeapVariable {
      get { return this.heapVariable; }
    }
    readonly Bpl.Variable heapVariable = TranslationHelper.TempHeapVar();

    public Bpl.Variable ThisVariable = TranslationHelper.TempThisVar();
    public Bpl.Variable RetVariable;
    public readonly Bpl.Program TranslatedProgram = new Bpl.Program();
    internal List<MethodParameter> OutVars = new List<MethodParameter>();

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
      Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(local.Locations);
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
      return mp.localParameter;
    }
    public Dictionary<IParameterDefinition, MethodParameter> FormalMap = null;

    private Dictionary<IFieldDefinition, Bpl.GlobalVariable> fieldVarMap = new Dictionary<IFieldDefinition,Bpl.GlobalVariable>();

    public Bpl.Variable FindOrCreateFieldVariable(IFieldDefinition field) {
      Bpl.GlobalVariable v;
      if (!fieldVarMap.TryGetValue(field, out v)) {
        string fieldname = field.ContainingTypeDefinition.ToString() + "." + field.Name.Value;
        Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(field.Locations);
        Bpl.Type t = TranslationHelper.CciTypeToBoogie(field.Type.ResolvedType);
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);

        v = new Bpl.GlobalVariable(tok, tident);
        fieldVarMap.Add(field, v);
        this.TranslatedProgram.TopLevelDeclarations.Add(new Bpl.Constant(tok, tident, true));
      }
      return v;
    }

    public void BeginMethod() {
      this.localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();
    }

  }

}