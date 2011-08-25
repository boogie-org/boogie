//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;
using System.Diagnostics.Contracts;

using Bpl = Microsoft.Boogie;
using BytecodeTranslator.TranslationPlugins;


namespace BytecodeTranslator {

  public class Sink {

    public IEnumerable<Translator> TranslationPlugins {
      get { return this.translationPlugins; }
      set { this.translationPlugins= value; }
    }
    private IEnumerable<Translator> translationPlugins;
    private readonly Options options;
    readonly bool whiteList;
    readonly List<Regex> exemptionList;


    public Sink(IContractAwareHost host, HeapFactory heapFactory, Options options, List<Regex> exemptionList, bool whiteList) {
      Contract.Requires(host != null);
      Contract.Requires(heapFactory != null);
      this.host = host;
      var b = heapFactory.MakeHeap(this, out this.heap, out this.TranslatedProgram); // TODO: what if it returns false?
      this.options = options;
      this.exemptionList = exemptionList;
      this.whiteList = whiteList;
      if (this.TranslatedProgram == null) {
        this.TranslatedProgram = new Bpl.Program();
      }
      else {
        foreach (var d in this.TranslatedProgram.TopLevelDeclarations) {
          var p = d as Bpl.Procedure;
          if (p != null) {
            if (Bpl.QKeyValue.FindBoolAttribute(p.Attributes, "extern")) continue;
            this.initiallyDeclaredProcedures.Add(p.Name, new ProcedureInfo(p));
          }
        }
      }
    }

    public Options Options { get { return this.options; } }

    public Heap Heap {
      get { return this.heap; }
    }
    readonly Heap heap;

    public Bpl.Formal ThisVariable {
      get {
        ProcedureInfo info = FindOrCreateProcedure(this.methodBeingTranslated);
        return info.ThisVariable;
      }
    }
    public Bpl.Formal ReturnVariable {
      get {
        ProcedureInfo info = FindOrCreateProcedure(this.methodBeingTranslated);
        return info.ReturnVariable;
      }
    }
    public Bpl.LocalVariable LocalExcVariable {
      get {
        ProcedureInfo info = FindOrCreateProcedure(this.methodBeingTranslated);
        return info.LocalExcVariable;
      }
    }
    public Bpl.LocalVariable LabelVariable {
      get {
        ProcedureInfo info = FindOrCreateProcedure(this.methodBeingTranslated);
        return info.LabelVariable;
      }
    }

    public readonly string AllocationMethodName = "Alloc";
    public readonly string StaticFieldFunction = "ClassRepr";
    public readonly string ReferenceTypeName = "Ref";

    public readonly string DelegateAddHelperName = "DelegateAddHelper";
    public readonly string DelegateAddName = "DelegateAdd";
    public readonly string DelegateRemoveName = "DelegateRemove";

    public Bpl.Expr ReadHead(Bpl.Expr delegateReference) {
      return Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.DelegateHead), delegateReference);
    }

    public Bpl.Expr ReadNext(Bpl.Expr delegateReference, Bpl.Expr listNodeReference) {
      return Bpl.Expr.Select(Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.DelegateNext), delegateReference), listNodeReference);
    }

    public Bpl.Expr ReadDelegate(Bpl.Expr delegateReference, Bpl.Expr listNodeReference) {
      return Bpl.Expr.Select(Bpl.Expr.Select(new Bpl.IdentifierExpr(delegateReference.tok, this.heap.Delegate), delegateReference), listNodeReference);
    }

    public Bpl.Expr ReadMethod(Bpl.Expr delegateExpr) {
      return new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.heap.DelegateMethod), new Bpl.ExprSeq(delegateExpr));
    }

    public Bpl.Expr ReadReceiver(Bpl.Expr delegateExpr) {
      return new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.heap.DelegateReceiver), new Bpl.ExprSeq(delegateExpr));
    }

    public Bpl.Expr ReadTypeParameters(Bpl.Expr delegateExpr) {
      return new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.heap.DelegateTypeParameters), new Bpl.ExprSeq(delegateExpr));
    }

    public Bpl.Expr CreateDelegate(Bpl.Expr methodExpr, Bpl.Expr instanceExpr, Bpl.Expr typeParameterExpr) {
      return new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.heap.DelegateCons), 
                              new Bpl.ExprSeq(methodExpr, instanceExpr, typeParameterExpr));
    }

    public readonly Bpl.Program TranslatedProgram;

    public Bpl.Type CciTypeToBoogie(ITypeReference type) {
      if (TypeHelper.TypesAreEquivalent(type, type.PlatformType.SystemBoolean))
        return Bpl.Type.Bool;
      else if (type.TypeCode == PrimitiveTypeCode.UIntPtr || type.TypeCode == PrimitiveTypeCode.IntPtr)
        return Bpl.Type.Int;
      else if (TypeHelper.IsPrimitiveInteger(type))
        return Bpl.Type.Int;
      else if (type.TypeCode == PrimitiveTypeCode.Float32 || type.TypeCode == PrimitiveTypeCode.Float64)
        return heap.RealType;
      else if (type.ResolvedType.IsStruct)
        return heap.RefType; // structs are kept on the heap with special rules about assignment
      else if (type.IsEnum)
        return Bpl.Type.Int; // The underlying type of an enum is always some kind of integer
      else if (type is IGenericTypeParameter || type is IGenericMethodParameter)
        return heap.BoxType;
      else
        return heap.RefType;
    }

    /// <summary>
    /// Creates a fresh local var of the given Type and adds it to the
    /// Bpl Implementation
    /// </summary>
    /// <param name="typeReference"> The type of the new variable </param>
    /// <returns> A fresh Variable with automatic generated name and location </returns>
    public Bpl.Variable CreateFreshLocal(ITypeReference typeReference) {
      Bpl.IToken loc = Bpl.Token.NoToken; // Helper Variables do not have a location
      Bpl.Type t = CciTypeToBoogie(typeReference);
      Bpl.LocalVariable v = new Bpl.LocalVariable(loc, new Bpl.TypedIdent(loc, TranslationHelper.GenerateTempVarName(), t));
      ILocalDefinition dummy = new LocalDefinition(); // Creates a dummy entry for the Dict, since only locals in the dict are translated to boogie
      localVarMap.Add(dummy, v);
      return v;
    }

    public Bpl.Variable CreateFreshLocal(Bpl.Type t) {
      Bpl.IToken loc = Bpl.Token.NoToken; // Helper Variables do not have a location
      Bpl.LocalVariable v = new Bpl.LocalVariable(loc, new Bpl.TypedIdent(loc, TranslationHelper.GenerateTempVarName(), t));
      ILocalDefinition dummy = new LocalDefinition(); // Creates a dummy entry for the Dict, since only locals in the dict are translated to boogie
      localVarMap.Add(dummy, v);
      return v;
    }

    /// <summary>
    /// There are no global variables in code, but it may be useful to have global Boogie vars in the translation
    /// 
    /// This should be just the same as the encoding for a static field, but I'm being
    /// IL-unaware here...not sure if this is 100% right
    /// </summary>
    private IDictionary<string, Bpl.Variable> globalVariables = new Dictionary<string, Bpl.Variable>();
    public Bpl.Variable FindOrCreateGlobalVariable(string globalVarName, Bpl.Type type) {
      Bpl.Variable globalVar;
      // assuming globalVarName is a valid identifier. Possible name clashing issues too
      if (!globalVariables.TryGetValue(globalVarName, out globalVar)) {
        globalVar = new Bpl.GlobalVariable(null, new Bpl.TypedIdent(null, globalVarName, type));
      }

      return globalVar;
    }


    /// <summary>
    /// State that gets re-initialized per method
    /// </summary>
    private Dictionary<ILocalDefinition, Bpl.LocalVariable> localVarMap = null;
    public Dictionary<ILocalDefinition, Bpl.LocalVariable> LocalVarMap {
      get { return this.localVarMap; }
    }
    private int localCounter;
    public int LocalCounter { get { return this.localCounter++; } }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="local"></param>
    /// <returns></returns>
    public Bpl.Variable FindOrCreateLocalVariable(ILocalDefinition local) {
      Bpl.LocalVariable v;
      Bpl.IToken tok = local.Token();
      Bpl.Type t = CciTypeToBoogie(local.Type.ResolvedType);
      if (!localVarMap.TryGetValue(local, out v)) {
        var name = local.Name.Value;
        name = TranslationHelper.TurnStringIntoValidIdentifier(name);
        v = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name, t));
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
    public Bpl.Variable FindParameterVariable(IParameterDefinition param, bool contractContext) {
      MethodParameter mp;
      ProcedureInfo procAndFormalMap;
      var sig = param.ContainingSignature;
      // BUGBUG: If param's signature is not a method reference, then it doesn't have an interned
      // key. The declaredMethods table needs to use ISignature for its keys.
      var key = ((IMethodReference)sig).InternedKey;
      this.declaredMethods.TryGetValue(key, out procAndFormalMap);
      var formalMap = procAndFormalMap.FormalMap;
      formalMap.TryGetValue(param, out mp);
      return contractContext ? mp.inParameterCopy : mp.outParameterCopy;
    }

    public Bpl.Variable FindOrCreateFieldVariable(IFieldReference field) {
      // The Heap has to decide how to represent the field (i.e., its type),
      // all the Sink cares about is adding a declaration for it.
      Bpl.Variable v;
      var specializedField = field as ISpecializedFieldReference;
      if (specializedField != null)
        field = specializedField.UnspecializedVersion;
      var key = field.InternedKey;
      if (!this.declaredFields.TryGetValue(key, out v)) {
        v = this.Heap.CreateFieldVariable(field);

        var isExtern = this.assemblyBeingTranslated != null &&
                !TypeHelper.GetDefiningUnitReference(field.ContainingType).UnitIdentity.Equals(this.assemblyBeingTranslated.UnitIdentity);
        if (isExtern) {
          var attrib = new Bpl.QKeyValue(Bpl.Token.NoToken, "extern", new List<object>(1), null);
          v.Attributes = attrib;
        }

        this.declaredFields.Add(key, v);
        this.TranslatedProgram.TopLevelDeclarations.Add(v);
      }
      return v;
    }

    /// <summary>
    /// The keys to the table are the interned key of the field.
    /// </summary>
    private Dictionary<uint, Bpl.Variable> declaredFields = new Dictionary<uint, Bpl.Variable>();

    public Bpl.Variable FindOrCreateEventVariable(IEventDefinition e) {
      Bpl.Variable v;
      if (!this.declaredEvents.TryGetValue(e, out v)) {
        v = null;

        // First, see if the compiler generated a field (which happens when the event did not explicitly
        // define an adder and remover. If so, then just use the variable that corresponds to that field.
        foreach (var f in e.ContainingTypeDefinition.Fields) {
          if (e.Name == f.Name) {
            v = this.FindOrCreateFieldVariable(f);
            break;
          }
        }

        if (v == null) {
          v = this.Heap.CreateEventVariable(e);

          var isExtern = this.assemblyBeingTranslated != null &&
            !TypeHelper.GetDefiningUnitReference(e.ContainingType).UnitIdentity.Equals(this.assemblyBeingTranslated.UnitIdentity);
          if (isExtern) {
            var attrib = new Bpl.QKeyValue(Bpl.Token.NoToken, "extern", new List<object>(1), null);
            v.Attributes = attrib;
          }

          this.TranslatedProgram.TopLevelDeclarations.Add(v);
        }
        this.declaredEvents.Add(e, v);
      }
      return v;
    }

    private Dictionary<IEventDefinition, Bpl.Variable> declaredEvents = new Dictionary<IEventDefinition, Bpl.Variable>();

    public Bpl.Variable FindOrCreatePropertyVariable(IPropertyDefinition p) {
      return null;
    }

    public Bpl.Constant FindOrCreateConstant(string str) {
      Bpl.Constant c;
      if (!this.declaredStringConstants.TryGetValue(str, out c)) {
        var tok = Bpl.Token.NoToken;
        var t = Heap.RefType;
        var name = "$string_literal_" + TranslationHelper.TurnStringIntoValidIdentifier(str) + "_" + declaredStringConstants.Count;
        var tident = new Bpl.TypedIdent(tok, name, t);
        c = new Bpl.Constant(tok, tident, true);
        this.declaredStringConstants.Add(str, c);
        this.TranslatedProgram.TopLevelDeclarations.Add(c);
      }
      return c;
    }
    private Dictionary<string, Bpl.Constant> declaredStringConstants = new Dictionary<string, Bpl.Constant>();

    public Bpl.Constant FindOrCreateConstant(double d) {
      Bpl.Constant c;
      var str = d.ToString();
      if (!this.declaredRealConstants.TryGetValue(str, out c)) {
        var tok = Bpl.Token.NoToken;
        var t = Heap.RealType;
        var name = "$real_literal_" + TranslationHelper.TurnStringIntoValidIdentifier(str) + "_" + declaredStringConstants.Count;
        var tident = new Bpl.TypedIdent(tok, name, t);
        c = new Bpl.Constant(tok, tident, true);
        this.declaredRealConstants.Add(str, c);
        this.TranslatedProgram.TopLevelDeclarations.Add(c);
      }
      return c;
    }
    public Bpl.Constant FindOrCreateConstant(float f) {
      Bpl.Constant c;
      var str = f.ToString();
      if (!this.declaredRealConstants.TryGetValue(str, out c)) {
        var tok = Bpl.Token.NoToken;
        var t = Heap.RealType;
        var name = "$real_literal_" + TranslationHelper.TurnStringIntoValidIdentifier(str) + "_" + declaredStringConstants.Count;
        var tident = new Bpl.TypedIdent(tok, name, t);
        c = new Bpl.Constant(tok, tident, true);
        this.declaredRealConstants.Add(str, c);
        this.TranslatedProgram.TopLevelDeclarations.Add(c);
      }
      return c;
    }
    private Dictionary<string, Bpl.Constant> declaredRealConstants = new Dictionary<string, Bpl.Constant>();

    private Dictionary<IPropertyDefinition, Bpl.Variable> declaredProperties = new Dictionary<IPropertyDefinition, Bpl.Variable>();

    private List<Bpl.Function> projectionFunctions = new List<Bpl.Function>();
    private Dictionary<int, Bpl.Function> arityToNaryIntFunctions = new Dictionary<int, Bpl.Function>();
    public Bpl.Function FindOrCreateNaryIntFunction(int arity) {
      Bpl.Function f;
      if (!this.arityToNaryIntFunctions.TryGetValue(arity, out f)) {
        Bpl.VariableSeq vseq = new Bpl.VariableSeq();
        for (int i = 0; i < arity; i++) {
          vseq.Add(new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "arg" + i, Bpl.Type.Int), true));
        }
        f = new Bpl.Function(Bpl.Token.NoToken, "Int" + arity, vseq, new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "result", Bpl.Type.Int), false));
        this.arityToNaryIntFunctions.Add(arity, f);
        TranslatedProgram.TopLevelDeclarations.Add(f);
        if (arity > projectionFunctions.Count) {
          for (int i = projectionFunctions.Count; i < arity; i++) {
            Bpl.Variable input = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "in", Bpl.Type.Int), true);
            Bpl.Variable output = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "out", Bpl.Type.Int), false);
            Bpl.Function g = new Bpl.Function(Bpl.Token.NoToken, "Proj" + i, new Bpl.VariableSeq(input), output);
            TranslatedProgram.TopLevelDeclarations.Add(g);
            projectionFunctions.Add(g);
          }
        }
        Bpl.VariableSeq qvars = new Bpl.VariableSeq();
        Bpl.ExprSeq exprs = new Bpl.ExprSeq();
        for (int i = 0; i < arity; i++) {
          Bpl.Variable v = new Bpl.Constant(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "arg" + i, Bpl.Type.Int));
          qvars.Add(v);
          exprs.Add(Bpl.Expr.Ident(v));
        }
        Bpl.Expr e = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(f), exprs);
        for (int i = 0; i < arity; i++) {
          Bpl.Expr appl = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(projectionFunctions[i]), new Bpl.ExprSeq(e));
          Bpl.Trigger trigger = new Bpl.Trigger(Bpl.Token.NoToken, true, new Bpl.ExprSeq(e));
          Bpl.Expr qexpr = new Bpl.ForallExpr(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), qvars, null, trigger, Bpl.Expr.Eq(appl, Bpl.Expr.Ident(qvars[i])));
          TranslatedProgram.TopLevelDeclarations.Add(new Bpl.Axiom(Bpl.Token.NoToken, qexpr));
        }
      }
      return f;
    }

    private List<Bpl.Function> typeParameterFunctions = new List<Bpl.Function>();
    private Dictionary<int, Bpl.Function> arityToNaryTypeFunctions = new Dictionary<int, Bpl.Function>();
    public Bpl.Function FindOrCreateNaryTypeFunction(int arity) {
      Bpl.Function f;
      if (!this.arityToNaryTypeFunctions.TryGetValue(arity, out f)) {
        Bpl.VariableSeq vseq = new Bpl.VariableSeq();
        for (int i = 0; i < arity; i++) {
          vseq.Add(new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "arg" + i, this.Heap.TypeType), true));
        }
        f = new Bpl.Function(Bpl.Token.NoToken, "Type" + arity, vseq, new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "result", this.Heap.TypeType), false));
        this.arityToNaryTypeFunctions.Add(arity, f);
        TranslatedProgram.TopLevelDeclarations.Add(f);
        if (arity > typeParameterFunctions.Count) {
          for (int i = typeParameterFunctions.Count; i < arity; i++) {
            Bpl.Variable input = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "in", this.Heap.TypeType), true);
            Bpl.Variable output = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "out", this.Heap.TypeType), false);
            Bpl.Function g = new Bpl.Function(Bpl.Token.NoToken, "TypeProj" + i, new Bpl.VariableSeq(input), output);
            TranslatedProgram.TopLevelDeclarations.Add(g);
            typeParameterFunctions.Add(g);
          }
        }
        Bpl.VariableSeq qvars = new Bpl.VariableSeq();
        Bpl.ExprSeq exprs = new Bpl.ExprSeq();
        for (int i = 0; i < arity; i++) {
          Bpl.Variable v = new Bpl.Constant(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "arg" + i, this.Heap.TypeType));
          qvars.Add(v);
          exprs.Add(Bpl.Expr.Ident(v));
        }
        Bpl.Expr e = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(f), exprs);
        for (int i = 0; i < arity; i++) {
          Bpl.Expr appl = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(typeParameterFunctions[i]), new Bpl.ExprSeq(e));
          Bpl.Trigger trigger = new Bpl.Trigger(Bpl.Token.NoToken, true, new Bpl.ExprSeq(e));
          Bpl.Expr qexpr = new Bpl.ForallExpr(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), qvars, null, trigger, Bpl.Expr.Eq(appl, Bpl.Expr.Ident(qvars[i])));
          TranslatedProgram.TopLevelDeclarations.Add(new Bpl.Axiom(Bpl.Token.NoToken, qexpr));
        }
      }
      return f;
    }
    public Bpl.Function FindOrCreateTypeParameterFunction(int id) {
      FindOrCreateNaryTypeFunction(id + 1);
      return typeParameterFunctions[id];
    }

    public struct ProcedureInfo {
      private Bpl.DeclWithFormals decl;
      private Dictionary<IParameterDefinition, MethodParameter> formalMap;
      private Bpl.Formal thisVariable;
      private Bpl.Formal returnVariable;
      private Bpl.LocalVariable localExcVariable;
      private Bpl.LocalVariable labelVariable;
      private List<Bpl.Formal> typeParameters;
      private List<Bpl.Formal> methodParameters;

      public ProcedureInfo(Bpl.DeclWithFormals decl) {
        this.decl = decl;
        this.formalMap = null;
        this.returnVariable = null;
        this.thisVariable = null;
        this.localExcVariable = null;
        this.labelVariable = null;
        this.typeParameters = null;
        this.methodParameters = null;
      }
      public ProcedureInfo(
        Bpl.DeclWithFormals decl,
        Dictionary<IParameterDefinition, MethodParameter> formalMap)
        : this(decl) {
        this.formalMap = formalMap;
      }
      public ProcedureInfo(
        Bpl.DeclWithFormals decl,
        Dictionary<IParameterDefinition, MethodParameter> formalMap,
        Bpl.Formal returnVariable)
        : this(decl, formalMap) {
        this.returnVariable = returnVariable;
      }
      public ProcedureInfo(
        Bpl.DeclWithFormals decl,
        Dictionary<IParameterDefinition, MethodParameter> formalMap,
        Bpl.Formal returnVariable,
        Bpl.Formal thisVariable,
        Bpl.LocalVariable localExcVariable,
        Bpl.LocalVariable labelVariable,
        List<Bpl.Formal> typeParameters,
        List<Bpl.Formal> methodParameters)
        : this(decl, formalMap, returnVariable) {
        this.thisVariable = thisVariable;
        this.localExcVariable = localExcVariable;
        this.labelVariable = labelVariable;
        this.typeParameters = typeParameters;
        this.methodParameters = methodParameters;
      }

      public Bpl.DeclWithFormals Decl { get { return decl; } }
      public Dictionary<IParameterDefinition, MethodParameter> FormalMap { get { return formalMap; } }
      public Bpl.Formal ThisVariable { get { return thisVariable; } }
      public Bpl.Formal ReturnVariable { get { return returnVariable; } }
      public Bpl.LocalVariable LocalExcVariable { get { return localExcVariable; } }
      public Bpl.LocalVariable LabelVariable { get { return labelVariable; } }
      public Bpl.Formal TypeParameter(int index) { return typeParameters[index]; }
      public Bpl.Formal MethodParameter(int index) { return methodParameters[index]; }
    }

    public ProcedureInfo FindOrCreateProcedure(IMethodDefinition method) {
      ProcedureInfo procInfo;
      var key = method.InternedKey;

      if (!this.declaredMethods.TryGetValue(key, out procInfo)) {
        string MethodName = TranslationHelper.CreateUniqueMethodName(method);

        if (this.initiallyDeclaredProcedures.TryGetValue(MethodName, out procInfo)) return procInfo;

        Bpl.Formal thisVariable = null;
        Bpl.Formal retVariable = null;
        Bpl.LocalVariable localExcVariable = new Bpl.LocalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "$localExc", this.Heap.RefType));
        Bpl.LocalVariable labelVariable = new Bpl.LocalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "$label", Bpl.Type.Int));

        int in_count = 0;
        int out_count = 0;
        MethodParameter mp;
        var formalMap = new Dictionary<IParameterDefinition, MethodParameter>();
        foreach (IParameterDefinition formal in method.Parameters) {
          mp = new MethodParameter(formal, this.CciTypeToBoogie(formal.Type));
          if (mp.inParameterCopy != null) in_count++;
          if (mp.outParameterCopy != null && formal.IsByReference)
            out_count++;
          formalMap.Add(formal, mp);
        }

        if (method.Type.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Type rettype = CciTypeToBoogie(method.Type);
          out_count++;
          retVariable = new Bpl.Formal(method.Token(), new Bpl.TypedIdent(method.Type.Token(), "$result", rettype), false);
        }

        if (!method.IsStatic) {
          var selfType = CciTypeToBoogie(method.ContainingType);
          in_count++;
          thisVariable = new Bpl.Formal(method.Token(), new Bpl.TypedIdent(method.Type.Token(), "$this", selfType), true);
        }

        List<Bpl.Formal> typeParameters = new List<Bpl.Formal>();
        ITypeDefinition containingType = method.ContainingType.ResolvedType;
        while (true) {
          int paramIndex = 0;
          foreach (IGenericTypeParameter gtp in containingType.GenericParameters) {
            Bpl.Formal f = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, gtp.Name.Value, this.Heap.TypeType), true);
            typeParameters.Insert(paramIndex, f);
            if (method.IsStatic) in_count++;
            paramIndex++;
          }
          INestedTypeDefinition ntd = containingType as INestedTypeDefinition;
          if (ntd == null) break;
          containingType = ntd.ContainingType.ResolvedType;
        }

        List<Bpl.Formal> methodParameters = new List<Bpl.Formal>();
        foreach (IGenericMethodParameter gmp in method.GenericParameters) {
          Bpl.Formal f = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, gmp.Name.Value, this.Heap.TypeType), true);
          methodParameters.Add(f);
          in_count++;
        }

        Bpl.Variable[] invars = new Bpl.Formal[in_count];
        Bpl.Variable[] outvars = new Bpl.Formal[out_count];

        int i = 0;
        int j = 0;

        if (thisVariable != null)
          invars[i++] = thisVariable;

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            invars[i++] = mparam.inParameterCopy;
          }
          if (mparam.outParameterCopy != null) {
            if (mparam.underlyingParameter.IsByReference)
              outvars[j++] = mparam.outParameterCopy;
          }
        }

        if (method.IsStatic) {
          foreach (Bpl.Formal f in typeParameters) {
            invars[i++] = f;
          }
        }
        foreach (Bpl.Formal f in methodParameters) {
          invars[i++] = f;
        }

        if (retVariable != null) outvars[j++] = retVariable;

        var tok = method.Token();
        Bpl.RequiresSeq boogiePrecondition = new Bpl.RequiresSeq();
        Bpl.EnsuresSeq boogiePostcondition = new Bpl.EnsuresSeq();
        Bpl.IdentifierExprSeq boogieModifies = new Bpl.IdentifierExprSeq();

        Bpl.DeclWithFormals decl;
        if (IsPure(method)) {
          var func = new Bpl.Function(tok,
            MethodName,
            new Bpl.VariableSeq(invars),
            retVariable);
          decl = func;
        }
        else {
          var proc = new Bpl.Procedure(tok,
              MethodName,
              new Bpl.TypeVariableSeq(),
              new Bpl.VariableSeq(invars),
              new Bpl.VariableSeq(outvars),
              boogiePrecondition,
              boogieModifies,
              boogiePostcondition);
          decl = proc;
        }
        if (this.assemblyBeingTranslated != null && !TypeHelper.GetDefiningUnitReference(method.ContainingType).UnitIdentity.Equals(this.assemblyBeingTranslated.UnitIdentity)) {
          var attrib = new Bpl.QKeyValue(tok, "extern", new List<object>(1), null);
          decl.Attributes = attrib;
        }

        string newName = null;
        if (IsStubMethod(method, out newName)) {
          if (newName != null) {
            decl.Name = newName;
          }
        }
        else {
          this.TranslatedProgram.TopLevelDeclarations.Add(decl);
        }
        procInfo = new ProcedureInfo(decl, formalMap, retVariable, thisVariable, localExcVariable, labelVariable, typeParameters, methodParameters);
        this.declaredMethods.Add(key, procInfo);

        // Can't visit the method's contracts until the formalMap and procedure are added to the
        // table because information in them might be needed (e.g., if a parameter is mentioned
        // in a contract.
        #region Translate the method's contracts

        var possiblyUnspecializedMethod = Unspecialize(method);

        var contract = Microsoft.Cci.MutableContracts.ContractHelper.GetMethodContractFor(this.host, possiblyUnspecializedMethod.ResolvedMethod);

        if (contract != null) {
          try {
            foreach (Translator translatorPlugin in translationPlugins) {
              ContractAwareTranslator translator = translatorPlugin as ContractAwareTranslator;
              if (translator != null) {
                IEnumerable<Bpl.Requires> preConds = translator.getPreconditionTranslation(contract);
                foreach (Bpl.Requires preExpr in preConds) {
                  boogiePrecondition.Add(preExpr);
                }

                IEnumerable<Bpl.Ensures> ensures = translator.getPostconditionTranslation(contract);
                foreach (Bpl.Ensures ensuring in ensures) {
                  boogiePostcondition.Add(ensuring);
                }

                IEnumerable<Bpl.IdentifierExpr> modifiedExpr = translator.getModifiedIdentifiers(contract);
                foreach (Bpl.IdentifierExpr ident in modifiedExpr) {
                  boogieModifies.Add(ident);
                }
              }
            }
          }
          catch (TranslationException te) {
            throw new NotImplementedException("Cannot Handle Errors in Method Contract: " + te.ToString());
          }
          catch {
            throw;
          }
        }

        #endregion

        #region Add disjointness contracts for any struct values passed by value
        var paramList = new List<IParameterDefinition>(method.Parameters);
        for (int p1index = 0; p1index < method.ParameterCount; p1index++) {
          var p1 = paramList[p1index];
          if (p1.IsByReference) continue;
          if (!TranslationHelper.IsStruct(p1.Type)) continue;
          for (int p2index = p1index + 1; p2index < method.ParameterCount; p2index++) {
            var p2 = paramList[p2index];
            if (p2.IsByReference) continue;
            if (!TranslationHelper.IsStruct(p2.Type)) continue;
            if (!TypeHelper.TypesAreEquivalent(p1.Type, p2.Type)) continue;
            var req = new Bpl.Requires(true, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq,
              Bpl.Expr.Ident(formalMap[p1].inParameterCopy), Bpl.Expr.Ident(formalMap[p2].inParameterCopy)));
            boogiePrecondition.Add(req);
          }
        }
        #endregion
      }
      return procInfo;
    }

    private Dictionary<uint, ProcedureInfo> declaredStructDefaultCtors = new Dictionary<uint, ProcedureInfo>();
    /// <summary>
    /// Struct "creation" (source code that looks like "new S()" for a struct type S) is modeled
    /// by a call to the nullary "ctor" that initializes all of the structs fields to zero-
    /// equivalent values. Note that the generated procedure has no contract. So if the struct
    /// is defined in an assembly that is not being translated, then its behavior is unspecified.
    /// </summary>
    /// <param name="structType">A type reference to the value type for which the ctor should be returned.</param>
    /// <returns>A unary procedure (i.e., it takes the struct value as its parameter) that initializes
    /// its parameter of type <paramref name="structType"/>.
    /// </returns>
    public Bpl.DeclWithFormals FindOrCreateProcedureForDefaultStructCtor(ITypeReference structType) {
      Contract.Requires(structType.IsValueType);

      ProcedureInfo procAndFormalMap;
      var key = structType.InternedKey;
      if (!this.declaredStructDefaultCtors.TryGetValue(key, out procAndFormalMap)) {
        var typename = TranslationHelper.TurnStringIntoValidIdentifier(TypeHelper.GetTypeName(structType));
        // The type can be generic and then there can be name clashes. So append the key to make it unique.
        typename += key.ToString();
        var tok = structType.Token();
        var selfType = this.CciTypeToBoogie(structType); //new Bpl.MapType(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Heap.FieldType), Heap.BoxType);
        var selfIn = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "this", selfType), true);
        var invars = new Bpl.Formal[] { selfIn };
        var proc = new Bpl.Procedure(Bpl.Token.NoToken, typename + ".#default_ctor",
          new Bpl.TypeVariableSeq(),
          new Bpl.VariableSeq(invars),
          new Bpl.VariableSeq(), // out
          new Bpl.RequiresSeq(),
          new Bpl.IdentifierExprSeq(), // modifies
          new Bpl.EnsuresSeq()
          );
        this.TranslatedProgram.TopLevelDeclarations.Add(proc);
        procAndFormalMap = new ProcedureInfo(proc, new Dictionary<IParameterDefinition, MethodParameter>());
        this.declaredStructDefaultCtors.Add(key, procAndFormalMap);
      }
      return procAndFormalMap.Decl;
    }

    private Dictionary<uint, ProcedureInfo> declaredStructCopyCtors = new Dictionary<uint, ProcedureInfo>();
    private Dictionary<uint, ProcedureInfo> declaredStructEqualityOperators = new Dictionary<uint, ProcedureInfo>();
    /// <summary>
    /// The assignment of one struct value to another is modeled by a method that makes a field-by-field
    /// copy of the source of the assignment.
    /// Note that the generated procedure has no contract. So if the struct
    /// is defined in an assembly that is not being translated, then its behavior is unspecified.
    /// </summary>
    /// <param name="structType">A type reference to the value type for which the procedure should be returned.</param>
    /// <returns>A binary procedure (i.e., it takes the two struct values as its parameters).
    /// </returns>
    public Bpl.DeclWithFormals FindOrCreateProcedureForStructCopy(ITypeReference structType) {
      Contract.Requires(structType.IsValueType);

      ProcedureInfo procAndFormalMap;
      var key = structType.InternedKey;
      if (!this.declaredStructCopyCtors.TryGetValue(key, out procAndFormalMap)) {
        var typename = TranslationHelper.TurnStringIntoValidIdentifier(TypeHelper.GetTypeName(structType));
        var tok = structType.Token();
        var selfType = this.CciTypeToBoogie(structType); //new Bpl.MapType(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Heap.FieldType), Heap.BoxType);
        var selfIn = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "this", selfType), true);
        var otherIn = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "other", selfType), true);
        var invars = new Bpl.Formal[] { selfIn, otherIn, };
        var outvars = new Bpl.Formal[0];
        var selfInExpr = Bpl.Expr.Ident(selfIn);
        var otherInExpr = Bpl.Expr.Ident(otherIn);
        var req = new Bpl.Requires(true, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, selfInExpr, otherInExpr));
        var ens = new Bpl.Ensures(true, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, selfInExpr, otherInExpr));

        var proc = new Bpl.Procedure(Bpl.Token.NoToken, typename + ".#copy_ctor",
          new Bpl.TypeVariableSeq(),
          new Bpl.VariableSeq(invars),
          new Bpl.VariableSeq(outvars),
          new Bpl.RequiresSeq(req),
          new Bpl.IdentifierExprSeq(), // modifies
          new Bpl.EnsuresSeq(ens)
          );
        this.TranslatedProgram.TopLevelDeclarations.Add(proc);
        procAndFormalMap = new ProcedureInfo(proc, new Dictionary<IParameterDefinition, MethodParameter>());
        this.declaredStructCopyCtors.Add(key, procAndFormalMap);
      }
      return procAndFormalMap.Decl;
    }

    // TODO: Fix test to return true iff method is marked with the "real" [Pure] attribute
    // also, should it return true for properties and all of the other things the tools
    // consider pure?
    private bool IsPure(IMethodDefinition method) {
      // TODO:
      // This needs to wait until we get function bodies sorted out.
      //bool isPropertyGetter = method.IsSpecialName && method.Name.Value.StartsWith("get_");
      //if (isPropertyGetter) return true;

      foreach (var a in method.Attributes) {
        if (TypeHelper.GetTypeName(a.Type).EndsWith("PureAttribute")) {
          return true;
        }
      }
      return false;
    }

    // TODO: check method's containing type in case the entire type is a stub type.
    // TODO: do a type test, not a string test for the attribute
    private bool IsStubMethod(IMethodReference method, out string/*?*/ newName) {
      newName = null;
      var methodDefinition = method.ResolvedMethod;
      foreach (var a in methodDefinition.Attributes) {
        if (TypeHelper.GetTypeName(a.Type).EndsWith("StubAttribute")) {
          foreach (var c in a.Arguments) {
            var mdc = c as IMetadataConstant;
            if (mdc != null && mdc.Type.TypeCode == PrimitiveTypeCode.String) {
              newName = (string)(mdc.Value);
              break;
            }
          }
          return true;
        }
      }
      return false;
    }

    public static IMethodReference Unspecialize(IMethodReference method) {
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

    private static int NumGenericParameters(ITypeReference typeReference) {
      ITypeDefinition typeDefinition = typeReference.ResolvedType;
      int numParameters = typeDefinition.GenericParameterCount;
      INestedTypeDefinition ntd = typeDefinition as INestedTypeDefinition;
      while (ntd != null) {
        ITypeDefinition containingType = ntd.ContainingType.ResolvedType;
        numParameters += containingType.GenericParameterCount;
        ntd = containingType as INestedTypeDefinition;
      }
      return numParameters;
    }

    public static ITypeReference GetUninstantiatedGenericType(ITypeReference typeReference) {
      IGenericTypeInstanceReference/*?*/ genericTypeInstanceReference = typeReference as IGenericTypeInstanceReference;
      if (genericTypeInstanceReference != null) return GetUninstantiatedGenericType(genericTypeInstanceReference.GenericType);
      INestedTypeReference/*?*/ nestedTypeReference = typeReference as INestedTypeReference;
      if (nestedTypeReference != null) {
        ISpecializedNestedTypeReference/*?*/ specializedNestedType = nestedTypeReference as ISpecializedNestedTypeReference;
        if (specializedNestedType != null) return specializedNestedType.UnspecializedVersion;
        return nestedTypeReference;
      }
      return typeReference;
    }

    public static void GetConsolidatedTypeArguments(List<ITypeReference> consolidatedTypeArguments, ITypeReference typeReference) {
      IGenericTypeInstanceReference/*?*/ genTypeInstance = typeReference as IGenericTypeInstanceReference;
      if (genTypeInstance != null) {
        GetConsolidatedTypeArguments(consolidatedTypeArguments, genTypeInstance.GenericType);
        consolidatedTypeArguments.AddRange(genTypeInstance.GenericArguments);
        return;
      }
      INestedTypeReference/*?*/ nestedTypeReference = typeReference as INestedTypeReference;
      if (nestedTypeReference != null) GetConsolidatedTypeArguments(consolidatedTypeArguments, nestedTypeReference.ContainingType);
    }

    public static int GetNumberTypeParameters(IMethodDefinition method) {
      int count = 0;
      if (method.IsStatic) {
        List<ITypeReference> consolidatedTypeArguments = new List<ITypeReference>();
        Sink.GetConsolidatedTypeArguments(consolidatedTypeArguments, method.ContainingType);
        count += consolidatedTypeArguments.Count;
      }
      count += method.GenericParameterCount;
      return count;
    }

    /// <summary>
    /// Creates a fresh variable that represents the type of
    /// <paramref name="type"/> in the Bpl program. I.e., its
    /// value represents the expression "typeof(type)".
    /// </summary>
    public Bpl.Expr FindOrCreateType(ITypeReference type) {
      // The Heap has to decide how to represent the field (i.e., its type),
      // all the Sink cares about is adding a declaration for it.

      IGenericTypeParameter gtp = type as IGenericTypeParameter;
      if (gtp != null) {
        int index = gtp.Index;
        var nestedType = gtp.DefiningType as INestedTypeDefinition;
        while (nestedType != null) {
          // calculate the consolidated index: the parameter knows only its index
          // in the type that declares it, not including any outer containing types
          var containingType = nestedType.ContainingTypeDefinition;
          index += containingType.GenericParameterCount;
          nestedType = containingType as INestedTypeDefinition;
        }

        ProcedureInfo info = FindOrCreateProcedure(methodBeingTranslated);
        if (methodBeingTranslated.IsStatic) {
          return Bpl.Expr.Ident(info.TypeParameter(index));
        }
        else {
          Bpl.Expr thisExpr = Bpl.Expr.Ident(this.ThisVariable);
          return new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(childFunctions[index]), new Bpl.ExprSeq(this.Heap.DynamicType(thisExpr)));
        }
      }

      IGenericMethodParameter gmp = type as IGenericMethodParameter;
      if (gmp != null) {
        ProcedureInfo info = FindOrCreateProcedure(methodBeingTranslated);
        return Bpl.Expr.Ident(info.MethodParameter(gmp.Index));
      }

      ITypeReference uninstantiatedGenericType = GetUninstantiatedGenericType(type);
      List<ITypeReference> consolidatedTypeArguments = new List<ITypeReference>();
      GetConsolidatedTypeArguments(consolidatedTypeArguments, type);

      if (consolidatedTypeArguments.Count > 0) {
        this.FindOrCreateType(uninstantiatedGenericType);
        var key = uninstantiatedGenericType.InternedKey;
        Bpl.Function f = this.declaredTypeFunctions[key];
        Bpl.ExprSeq args = new Bpl.ExprSeq();
        foreach (ITypeReference p in consolidatedTypeArguments) {
          args.Add(FindOrCreateType(p));
        }
        Bpl.Expr naryExpr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(f), args);
        return naryExpr;
      }

      int numParameters = NumGenericParameters(type);
      bool isExtern = this.assemblyBeingTranslated != null &&
                      !TypeHelper.GetDefiningUnitReference(type).UnitIdentity.Equals(this.assemblyBeingTranslated.UnitIdentity);

      if (numParameters > 0) {
        Bpl.Function f;
        var key = type.InternedKey;
        if (!this.declaredTypeFunctions.TryGetValue(key, out f)) {
          Bpl.VariableSeq vseq = new Bpl.VariableSeq();
          for (int i = 0; i < numParameters; i++) {
            vseq.Add(new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "arg" + i, this.Heap.TypeType), true));
          }
          f = this.Heap.CreateTypeFunction(type, numParameters);
          this.declaredTypeFunctions.Add(key, f);
          this.TranslatedProgram.TopLevelDeclarations.Add(f);
          if (numParameters > childFunctions.Count) {
            for (int i = childFunctions.Count; i < numParameters; i++) {
              Bpl.Variable input = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "in", this.Heap.TypeType), true);
              Bpl.Variable output = new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "out", this.Heap.TypeType), false);
              Bpl.Function g = new Bpl.Function(Bpl.Token.NoToken, "Child" + i, new Bpl.VariableSeq(input), output);
              TranslatedProgram.TopLevelDeclarations.Add(g);
              childFunctions.Add(g);
            }
          }
          if (isExtern) {
            var attrib = new Bpl.QKeyValue(Bpl.Token.NoToken, "extern", new List<object>(1), null);
            f.Attributes = attrib;
          }
          else {
            Bpl.VariableSeq qvars = new Bpl.VariableSeq();
            Bpl.ExprSeq exprs = new Bpl.ExprSeq();
            for (int i = 0; i < numParameters; i++) {
              Bpl.Variable v = new Bpl.Constant(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "arg" + i, this.Heap.TypeType));
              qvars.Add(v);
              exprs.Add(Bpl.Expr.Ident(v));
            }
            Bpl.Expr e = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(f), exprs);
            for (int i = 0; i < numParameters; i++) {
              Bpl.Expr appl = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(childFunctions[i]), new Bpl.ExprSeq(e));
              Bpl.Trigger trigger = new Bpl.Trigger(Bpl.Token.NoToken, true, new Bpl.ExprSeq(e));
              Bpl.Expr qexpr = new Bpl.ForallExpr(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), qvars, null, trigger, Bpl.Expr.Eq(appl, Bpl.Expr.Ident(qvars[i])));
              TranslatedProgram.TopLevelDeclarations.Add(new Bpl.Axiom(Bpl.Token.NoToken, qexpr));
            }
          }
        }
        return null;
      }
      else {
        Bpl.Variable t;
        var key = type.InternedKey;
        if (!this.declaredTypeConstants.TryGetValue(key, out t)) {
          //List<ITypeReference> structuralParents;
          //var parents = GetParents(type.ResolvedType, out structuralParents);
          //t = this.Heap.CreateTypeVariable(type, parents);
          t = this.Heap.CreateTypeVariable(type, null);
          this.declaredTypeConstants.Add(key, t);
          //foreach (var p in structuralParents) {
          //  var p_prime = FindOrCreateType(p);
          //  //var e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Subtype, Bpl.Expr.Ident(t), p_prime);
          //  var e = new Bpl.NAryExpr(
          //    Bpl.Token.NoToken,
          //    new Bpl.FunctionCall(this.Heap.Subtype),
          //    new Bpl.ExprSeq(Bpl.Expr.Ident(t), p_prime)
          //    );
          //  var a = new Bpl.Axiom(Bpl.Token.NoToken, e);
          //  this.TranslatedProgram.TopLevelDeclarations.Add(a);
          //}
          this.TranslatedProgram.TopLevelDeclarations.Add(t);
          DeclareParents(type.ResolvedType, t);
          if (isExtern) {
            var attrib = new Bpl.QKeyValue(Bpl.Token.NoToken, "extern", new List<object>(1), null);
            t.Attributes = attrib;
          }
        }
        return Bpl.Expr.Ident(t);
      }
    }

    private void DeclareSuperType(Bpl.Variable typeDefinitionAsBplConstant, ITypeReference superType) {
      var superType_prime = FindOrCreateType(superType);
      var e = new Bpl.NAryExpr(
        Bpl.Token.NoToken,
        new Bpl.FunctionCall(this.Heap.Subtype),
        new Bpl.ExprSeq(Bpl.Expr.Ident(typeDefinitionAsBplConstant), superType_prime)
        );
      var a = new Bpl.Axiom(Bpl.Token.NoToken, e);
      this.TranslatedProgram.TopLevelDeclarations.Add(a);
      if (!superType.ResolvedType.IsInterface) {
        var e2 = new Bpl.NAryExpr(
          Bpl.Token.NoToken,
          new Bpl.FunctionCall(this.Heap.DisjointSubtree),
          new Bpl.ExprSeq(Bpl.Expr.Ident(typeDefinitionAsBplConstant), superType_prime)
          );
        var a2 = new Bpl.Axiom(Bpl.Token.NoToken, e2);
        this.TranslatedProgram.TopLevelDeclarations.Add(a2);
      }
    }
    private void DeclareParents(ITypeDefinition typeDefinition, Bpl.Variable typeDefinitionAsBplConstant) {
      foreach (var p in typeDefinition.BaseClasses) {
        DeclareSuperType(typeDefinitionAsBplConstant, p);
      }
      foreach (var j in typeDefinition.Interfaces) {
        DeclareSuperType(typeDefinitionAsBplConstant, j);
      }
      return;
    }

    private List<Bpl.ConstantParent> GetParents(ITypeDefinition typeDefinition, out List<ITypeReference> structuralParents) {
      var parents = new List<Bpl.ConstantParent>();
      structuralParents = new List<ITypeReference>();
      foreach (var p in typeDefinition.BaseClasses) {
        if (p is IGenericTypeInstanceReference) {
          structuralParents.Add(p);
        }
        else {
          var v = (Bpl.IdentifierExpr)FindOrCreateType(p);
          parents.Add(new Bpl.ConstantParent(v, true));
        }
      }
      foreach (var j in typeDefinition.Interfaces) {
        if (j is IGenericTypeInstanceReference) {
          structuralParents.Add(j);
        }
        else {
          var v = (Bpl.IdentifierExpr)FindOrCreateType(j);
          parents.Add(new Bpl.ConstantParent(v, false));
        }
      }
      return parents;
    }

    /// <summary>
    /// The keys to the table are the interned key of the type.
    /// </summary>
    private Dictionary<uint, Bpl.Variable> declaredTypeConstants = new Dictionary<uint, Bpl.Variable>();
    private Dictionary<uint, Bpl.Function> declaredTypeFunctions = new Dictionary<uint, Bpl.Function>();
    private List<Bpl.Function> childFunctions = new List<Bpl.Function>();

    /// <summary>
    /// The keys to the table are the interned keys of the methods.
    /// The values are pairs: first element is the procedure,
    /// second element is the formal map for the procedure
    /// </summary>
    private Dictionary<uint, ProcedureInfo> declaredMethods = new Dictionary<uint, ProcedureInfo>();
    /// <summary>
    /// The values in this table are the procedures
    /// defined in the program created by the heap in the Sink's ctor.
    /// </summary>
    public Dictionary<string, ProcedureInfo> initiallyDeclaredProcedures = new Dictionary<string, ProcedureInfo>();

    public void BeginMethod(ITypeReference containingType) {
      this.localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();
      this.localCounter = 0;
      this.methodBeingTranslated = null;
    }

    public Dictionary<IName, int> cciLabels;
    public int FindOrCreateCciLabelIdentifier(IName label) {
      int v;
      if (!cciLabels.TryGetValue(label, out v)) {
        v = cciLabels.Count;
        cciLabels[label] = v;
      }
      return v;
    }
    public Dictionary<ITryCatchFinallyStatement, int> tryCatchFinallyIdentifiers;
    public string FindOrCreateCatchLabel(ITryCatchFinallyStatement stmt) {
      int id;
      if (!tryCatchFinallyIdentifiers.TryGetValue(stmt, out id)) {
        id = tryCatchFinallyIdentifiers.Count;
        tryCatchFinallyIdentifiers[stmt] = id;
      }
      return "catch" + id;
    }
    public string FindOrCreateFinallyLabel(ITryCatchFinallyStatement stmt) {
      int id;
      if (!tryCatchFinallyIdentifiers.TryGetValue(stmt, out id)) {
        id = tryCatchFinallyIdentifiers.Count;
        tryCatchFinallyIdentifiers[stmt] = id;
      }
      return "finally" + id;
    }
    public string FindOrCreateContinuationLabel(ITryCatchFinallyStatement stmt) {
      int id;
      if (!tryCatchFinallyIdentifiers.TryGetValue(stmt, out id)) {
        id = tryCatchFinallyIdentifiers.Count;
        tryCatchFinallyIdentifiers[stmt] = id;
      }
      return "continuation" + id;
    }
    MostNestedTryStatementTraverser mostNestedTryStatementTraverser;
    public ITryCatchFinallyStatement MostNestedTryStatement(IName label) {
      return mostNestedTryStatementTraverser.MostNestedTryStatement(label);
    }
    Dictionary<ITryCatchFinallyStatement, List<string>> escapingGotoEdges;
    public void AddEscapingEdge(ITryCatchFinallyStatement tryCatchFinallyStatement, out int labelId, out string label) {
      List<string> edges = null;
      if (!escapingGotoEdges.ContainsKey(tryCatchFinallyStatement)) {
        escapingGotoEdges[tryCatchFinallyStatement] = new List<string>();
      }
      edges = escapingGotoEdges[tryCatchFinallyStatement];
      label = this.FindOrCreateFinallyLabel(tryCatchFinallyStatement) + "_" + edges.Count;
      labelId = edges.Count;
      edges.Add(label);
    }
    public List<string> EscapingEdges(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      if (!escapingGotoEdges.ContainsKey(tryCatchFinallyStatement)) {
        escapingGotoEdges[tryCatchFinallyStatement] = new List<string>();
      }
      return escapingGotoEdges[tryCatchFinallyStatement];
    }
    public enum TryCatchFinallyContext { InTry, InCatch, InFinally };
    public List<Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext>> nestedTryCatchFinallyStatements;

    IMethodDefinition methodBeingTranslated;

    public IMethodDefinition getMethodBeingTranslated() {
      return methodBeingTranslated;
    }

    public void BeginMethod(IMethodDefinition method) {
      this.BeginMethod(method.ContainingType);
      this.methodBeingTranslated = method;
      this.cciLabels = new Dictionary<IName, int>();
      this.tryCatchFinallyIdentifiers = new Dictionary<ITryCatchFinallyStatement, int>();
      mostNestedTryStatementTraverser = new MostNestedTryStatementTraverser();
      escapingGotoEdges = new Dictionary<ITryCatchFinallyStatement, List<string>>();
      nestedTryCatchFinallyStatements = new List<Tuple<ITryCatchFinallyStatement, TryCatchFinallyContext>>();
      mostNestedTryStatementTraverser.Visit(method.Body);
    }

    public void BeginAssembly(IAssembly assembly) {
      this.assemblyBeingTranslated = assembly;
    }

    public void EndAssembly(IAssembly assembly) {
      this.assemblyBeingTranslated = null;
    }
    private IAssembly/*?*/ assemblyBeingTranslated;

    public Dictionary<uint, Tuple<ITypeDefinition, HashSet<IMethodDefinition>>> delegateTypeToDelegates =
      new Dictionary<uint, Tuple<ITypeDefinition, HashSet<IMethodDefinition>>>();

    public void AddDelegate(ITypeDefinition type, IMethodDefinition defn) {
      if (type == Dummy.Type) {
      }
      uint key = type.InternedKey;
      if (!delegateTypeToDelegates.ContainsKey(key))
        delegateTypeToDelegates[key] = new Tuple<ITypeDefinition, HashSet<IMethodDefinition>>(type, new HashSet<IMethodDefinition>());
      FindOrCreateProcedure(defn);
      delegateTypeToDelegates[key].Item2.Add(defn);
    }

    public void AddDelegateType(ITypeDefinition type) {
      if (type == Dummy.Type) {
      }
      uint key = type.InternedKey;
      if (!delegateTypeToDelegates.ContainsKey(key))
        delegateTypeToDelegates[key] = new Tuple<ITypeDefinition, HashSet<IMethodDefinition>>(type, new HashSet<IMethodDefinition>());
    }

    private Dictionary<IMethodDefinition, Bpl.Constant> delegateMethods = new Dictionary<IMethodDefinition, Bpl.Constant>();
    internal IContractAwareHost host;

    public Bpl.Constant FindOrCreateDelegateMethodConstant(IMethodDefinition defn) {
      if (delegateMethods.ContainsKey(defn))
        return delegateMethods[defn];
      string methodName = TranslationHelper.CreateUniqueMethodName(defn);
      var typedIdent = new Bpl.TypedIdent(Bpl.Token.NoToken, methodName, Bpl.Type.Int);
      var constant = new Bpl.Constant(Bpl.Token.NoToken, typedIdent, true);
      this.TranslatedProgram.TopLevelDeclarations.Add(constant);
      delegateMethods[defn] = constant;
      return constant;
    }

    public bool TranslateType(ITypeReference t) {
      if (this.exemptionList == null)
        return !this.whiteList;
      var fullName = TypeHelper.GetTypeName(t);
      var fullerName = "[" + TypeHelper.GetDefiningUnitReference(t).Name.Value + "]" + fullName;
      foreach (Regex r in this.exemptionList) {
        Match m = r.Match(fullName);
        if (m.Success)
          return this.whiteList;
        m = r.Match(fullerName);
        if (m.Success)
          return this.whiteList;
      }
      return !this.whiteList;
    }

    // TODO: get full namespace name from a namespace definition
    //public bool TranslateNamespace(INamespaceDefinition nameSpace) {
    //  if (this.exemptionList == null)
    //    return !this.whiteList;
    //  var fullName = TypeHelper.GetNamespaceName(nameSpace, NameFormattingOptions.None);
    //  foreach (Regex r in this.exemptionList) {
    //    Match m = r.Match(fullName);
    //    if (m.Success)
    //      return this.whiteList;
    //  }
    //  return !this.whiteList;
    //}

  }
}