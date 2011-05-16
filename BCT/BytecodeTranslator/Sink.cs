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

    public Sink(IContractAwareHost host, TraverserFactory factory, HeapFactory heapFactory) {
      Contract.Requires(host != null);
      Contract.Requires(factory != null);
      Contract.Requires(heapFactory != null);

      this.host = host;
      this.factory = factory;
      var b = heapFactory.MakeHeap(this, out this.heap, out this.TranslatedProgram); // TODO: what if it returns false?
      if (this.TranslatedProgram == null) {
        this.TranslatedProgram = new Bpl.Program();
      } else {
        foreach (var d in this.TranslatedProgram.TopLevelDeclarations) {
          var p = d as Bpl.Procedure;
          if (p != null) {
            this.initiallyDeclaredProcedures.Add(p.Name, p);
          }
        }
      }
    }

    public Heap Heap {
      get { return this.heap; }
    }
    readonly Heap heap;

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

    public Bpl.Expr DefaultValue(ITypeReference type) {
      var bplType = CciTypeToBoogie(type);
      if (bplType == Bpl.Type.Int) {
        var lit = Bpl.Expr.Literal(0);
        lit.Type = Bpl.Type.Int;
        return lit;
      } else if (bplType == Bpl.Type.Bool) {
        var lit = Bpl.Expr.False;
        lit.Type = Bpl.Type.Bool;
        return lit;
      } else if (type.ResolvedType.IsStruct) {
        return Bpl.Expr.Ident(this.Heap.DefaultStruct);
      } else if (bplType == this.Heap.RefType) {
        return Bpl.Expr.Ident(this.Heap.NullRef);
      }
      else if (bplType == this.Heap.BoxType) {
        return Bpl.Expr.Ident(this.Heap.DefaultBox);
      } else {
        throw new NotImplementedException(String.Format("Don't know how to translate type: '{0}'", TypeHelper.GetTypeName(type)));
      }
    }

    public Bpl.Type CciTypeToBoogie(ITypeReference type) {
      if (TypeHelper.TypesAreEquivalent(type, type.PlatformType.SystemBoolean))
        return Bpl.Type.Bool;
      else if (TypeHelper.IsPrimitiveInteger(type))
        return Bpl.Type.Int;
      else if (type.TypeCode == PrimitiveTypeCode.Float32 || type.TypeCode == PrimitiveTypeCode.Float64)
        return heap.RealType;
      else if (type.ResolvedType.IsStruct)
        return heap.StructType;
      else if (type.IsEnum)
        return Bpl.Type.Int; // The underlying type of an enum is always some kind of integer
      else if (type is IGenericTypeParameter)
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
          this.TranslatedProgram.TopLevelDeclarations.Add(v);
        }
        this.declaredEvents.Add(e, v);
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
          Bpl.Expr qexpr = new Bpl.ForallExpr(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), qvars, null, null, Bpl.Expr.Eq(appl, Bpl.Expr.Ident(qvars[i])));
          TranslatedProgram.TopLevelDeclarations.Add(new Bpl.Axiom(Bpl.Token.NoToken, qexpr));
        }

      }
      return f;
    }

    public struct ProcedureInfo {
      private Bpl.DeclWithFormals decl;
      private Dictionary<IParameterDefinition, MethodParameter> formalMap;
      private Bpl.Variable returnVariable;

      public ProcedureInfo(Bpl.DeclWithFormals decl, Dictionary<IParameterDefinition, MethodParameter> formalMap, Bpl.Variable returnVariable) {
        this.decl = decl;
        this.formalMap = formalMap;
        this.returnVariable = returnVariable;
      }

      public Bpl.DeclWithFormals Decl { get { return decl; } }
      public Dictionary<IParameterDefinition, MethodParameter> FormalMap { get { return formalMap; } }
      public Bpl.Variable ReturnVariable { get { return returnVariable; } }
    }

    public Bpl.DeclWithFormals FindOrCreateProcedure(IMethodDefinition method) {
      ProcedureInfo procAndFormalMap;

      var key = method.InternedKey;

      if (!this.declaredMethods.TryGetValue(key, out procAndFormalMap)) {

        string MethodName = TranslationHelper.CreateUniqueMethodName(method);

        Bpl.Procedure p;
        if (this.initiallyDeclaredProcedures.TryGetValue(MethodName, out p)) return p;

        #region Create in- and out-parameters

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

        #region Look for Returnvalue

        Bpl.Variable savedRetVariable = this.RetVariable;

        if (method.Type.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Type rettype = CciTypeToBoogie(method.Type);
          out_count++;
          this.RetVariable = new Bpl.Formal(method.Token(),
              new Bpl.TypedIdent(method.Type.Token(),
                  "$result", rettype), false);
        } else {
          this.RetVariable = null;
        }

        #endregion

        Bpl.Formal/*?*/ self = null;
        Bpl.Formal selfOut = null;
        #region Create 'this' parameter
        if (!method.IsStatic) {
          var selfType = CciTypeToBoogie(method.ContainingType);
          if (method.ContainingType.ResolvedType.IsStruct) {
            //selfType = Heap.StructType;
            in_count++;
            self = new Bpl.Formal(method.Token(), new Bpl.TypedIdent(method.Type.Token(), "thisIn", selfType), true);
            out_count++;
            selfOut = new Bpl.Formal(method.Token(), new Bpl.TypedIdent(method.Type.Token(), "this", selfType), false);
          }
          else {
            in_count++;
            //selfType = Heap.RefType;
            self = new Bpl.Formal(method.Token(), new Bpl.TypedIdent(method.Type.Token(), "this", selfType), true);
          }
        }
        #endregion

        Bpl.Variable[] invars = new Bpl.Formal[in_count];
        Bpl.Variable[] outvars = new Bpl.Formal[out_count];

        int i = 0;
        int j = 0;

        #region Add 'this' parameter as first in parameter and 'thisOut' parameter as first out parameter
        if (self != null)
          invars[i++] = self;
        if (selfOut != null)
          outvars[j++] = selfOut;
        #endregion

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            invars[i++] = mparam.inParameterCopy;
          }
          if (mparam.outParameterCopy != null) {
            if (mparam.underlyingParameter.IsByReference)
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

        var contract = Microsoft.Cci.MutableContracts.ContractHelper.GetMethodContractFor(this.host, possiblyUnspecializedMethod.ResolvedMethod);

        if (contract != null) {
          try {

            foreach (IPrecondition pre in contract.Preconditions) {
              var stmtTraverser = this.factory.MakeStatementTraverser(this, null, true);
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this, stmtTraverser, true);
              exptravers.Visit(pre.Condition); // TODO
              // Todo: Deal with Descriptions
              var req = new Bpl.Requires(pre.Token(), false, exptravers.TranslatedExpressions.Pop(), "");
              boogiePrecondition.Add(req);
            }

            foreach (IPostcondition post in contract.Postconditions) {
              var stmtTraverser = this.factory.MakeStatementTraverser(this, null, true);
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this, stmtTraverser, true);
              exptravers.Visit(post.Condition);
              // Todo: Deal with Descriptions
              var ens = new Bpl.Ensures(post.Token(), false, exptravers.TranslatedExpressions.Pop(), "");
              boogiePostcondition.Add(ens);
            }

            foreach (IAddressableExpression mod in contract.ModifiedVariables) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this, null, true);
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

        var tok = method.Token();
        Bpl.DeclWithFormals decl;
        if (IsPure(method)) {
          var func = new Bpl.Function(tok,
            MethodName,
            new Bpl.VariableSeq(invars),
            this.RetVariable);
          decl = func;
        } else {
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
        if (!TypeHelper.GetDefiningUnitReference(method.ContainingType).UnitIdentity.Equals(this.assemblyBeingTranslated.UnitIdentity)) {
          var attrib = new Bpl.QKeyValue(tok, "extern", new List<object>(1), null);
          decl.Attributes = attrib;
        }

        string newName = null;
        if (IsStubMethod(method, out newName)) {
          if (newName != null) {
            decl.Name = newName;
          }
        } else {
          this.TranslatedProgram.TopLevelDeclarations.Add(decl);
        }
        procAndFormalMap = new ProcedureInfo(decl, formalMap, this.RetVariable);
        this.declaredMethods.Add(key, procAndFormalMap);
        this.RetVariable = savedRetVariable;
      }
      return procAndFormalMap.Decl;
    }

    /// <summary>
    /// Struct "creation" (source code that looks like "new S()" for a struct type S) is modeled
    /// by a call to the nullary "ctor" that initializes all of the structs fields to zero-
    /// equivalent values. Note that the generated procedure has no contract. So if the struct
    /// is defined in an assembly that is not being translated, then its behavior is unspecified.
    /// </summary>
    /// <param name="structType">A type reference to the value type for which the ctor should be returned.</param>
    /// <returns>A nullary procedure that returns an initialized value of type <paramref name="structType"/>.</returns>
    public Bpl.DeclWithFormals FindOrCreateProcedureForDefaultStructCtor(ITypeReference structType) {
      Contract.Requires(structType.IsValueType);
     
      ProcedureInfo procAndFormalMap;
      var key = structType.InternedKey;
      if (!this.declaredMethods.TryGetValue(key, out procAndFormalMap)) {
        var typename = TranslationHelper.TurnStringIntoValidIdentifier(TypeHelper.GetTypeName(structType));
        var tok = structType.Token();
        var selfType = new Bpl.MapType(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(Heap.FieldType), Heap.BoxType);
        var selfOut = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "this", selfType), false);
        var outvars = new Bpl.Formal[]{ selfOut };
        var proc = new Bpl.Procedure(Bpl.Token.NoToken, typename + ".#default_ctor",
          new Bpl.TypeVariableSeq(),
          new Bpl.VariableSeq(), // in
          new Bpl.VariableSeq(outvars),
          new Bpl.RequiresSeq(),
          new Bpl.IdentifierExprSeq(), // modifies
          new Bpl.EnsuresSeq()
          );
        this.TranslatedProgram.TopLevelDeclarations.Add(proc);
        procAndFormalMap = new ProcedureInfo(proc, new Dictionary<IParameterDefinition, MethodParameter>(), this.RetVariable);
        this.declaredMethods.Add(key, procAndFormalMap);
      }
      return procAndFormalMap.Decl;
    }

    // TODO: Fix test to return true iff method is marked with the "real" [Pure] attribute
    // also, should it return true for properties and all of the other things the tools
    // consider pure?
    private bool IsPure(IMethodDefinition method) {
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
              newName = (string) (mdc.Value);
              break;
            }
          }
          return true;
        }
      }
      return false;
    }

    public ProcedureInfo FindOrCreateProcedureAndReturnProcAndFormalMap(IMethodDefinition method) {
      this.FindOrCreateProcedure(method);
      var key = method.InternedKey;
      return this.declaredMethods[key];
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
    /// The keys to the table are the interned keys of the methods.
    /// The values are pairs: first element is the procedure,
    /// second element is the formal map for the procedure
    /// </summary>
    private Dictionary<uint, ProcedureInfo> declaredMethods = new Dictionary<uint, ProcedureInfo>();
    /// <summary>
    /// The values in this table are the procedures
    /// defined in the program created by the heap in the Sink's ctor.
    /// </summary>
    private Dictionary<string, Bpl.Procedure> initiallyDeclaredProcedures = new Dictionary<string, Bpl.Procedure>();

    public void BeginMethod() {
      this.localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();
      this.localCounter = 0;
    }

    public void BeginAssembly(IAssembly assembly) {
      this.assemblyBeingTranslated = assembly;
    }

    public void EndAssembly(IAssembly assembly) {
      this.assemblyBeingTranslated = null;
    }
    private IAssembly assemblyBeingTranslated;

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
    internal IContractAwareHost host;

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