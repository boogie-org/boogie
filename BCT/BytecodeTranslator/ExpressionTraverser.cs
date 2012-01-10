//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;
using TranslationPlugins;
using BytecodeTranslator.Phone;


namespace BytecodeTranslator
{
  public class ExpressionTraverser : CodeTraverser
  {
    public readonly Stack<Bpl.Expr> TranslatedExpressions;

    protected readonly Sink sink;

    protected readonly StatementTraverser StmtTraverser;

    private bool contractContext;

    private Bpl.Expr FindOrCreateTypeReferenceInCodeContext(ITypeReference typeReference) {
      return this.sink.FindOrCreateTypeReference(typeReference, true);

      IGenericTypeParameter gtp = typeReference as IGenericTypeParameter;
      if (gtp != null) {
        var selectorName = gtp.Name.Value;
        selectorName = TranslationHelper.TurnStringIntoValidIdentifier(selectorName);
        var typeName = TypeHelper.GetTypeName(gtp.DefiningType, NameFormattingOptions.DocumentationId);
        typeName = TranslationHelper.TurnStringIntoValidIdentifier(typeName);
        var funcName = String.Format("{0}#{1}", selectorName, typeName);
        Bpl.IToken tok = Bpl.Token.NoToken;
        var identExpr = Bpl.Expr.Ident(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, funcName, this.sink.Heap.TypeType)));
        var funcCall = new Bpl.FunctionCall(identExpr);
        var thisArg = new Bpl.IdentifierExpr(tok, this.sink.ThisVariable);
        var dynType = this.sink.Heap.DynamicType(thisArg);
        var nary = new Bpl.NAryExpr(Bpl.Token.NoToken, funcCall, new Bpl.ExprSeq(dynType));
        return nary;
      }
      return this.sink.FindOrCreateTypeReference(typeReference);
    }

    private static IMethodDefinition ResolveUnspecializedMethodOrThrow(IMethodReference methodReference) {
      var resolvedMethod = Sink.Unspecialize(methodReference).ResolvedMethod;
      if (resolvedMethod == Dummy.Method) { // avoid downstream errors, fail early
        throw new TranslationException(ExceptionType.UnresolvedMethod, MemberHelper.GetMethodSignature(methodReference, NameFormattingOptions.None));
      }
      return resolvedMethod;
    }


    #region Constructors

    ///// <summary>
    ///// Use this constructor for translating expressions that do *not* occur
    ///// within the context of the statements in a method body.
    ///// </summary>
    //public ExpressionTraverser(Sink sink)
    //  : this(sink, null)
    //{ }

    /// <summary>
    /// Use this constructor for translating expressions that do occur within
    /// the context of the statements in a method body.
    /// </summary>
    public ExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext)
    {
      this.sink = sink;
      this.StmtTraverser = statementTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();

      this.contractContext = contractContext;
    }

    #endregion

    #region Translate Variable Access

    /// <summary>
    /// 
    /// </summary>
    /// <param name="addressableExpression"></param>
    /// <remarks>still a stub</remarks>
    public override void TraverseChildren(IAddressableExpression addressableExpression)
    {
      ILocalDefinition/*?*/ local = addressableExpression.Definition as ILocalDefinition;
      if (local != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      IParameterDefinition/*?*/ param = addressableExpression.Definition as IParameterDefinition;
      if (param != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param, this.contractContext)));
        return;
      }
      IFieldReference/*?*/ field = addressableExpression.Definition as IFieldReference;
      if (field != null) {
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field.ResolvedField));
        var instance = addressableExpression.Instance;
        if (instance == null) {
          TranslatedExpressions.Push(f);
        } else {
          this.Traverse(instance);
          Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
          Bpl.IdentifierExpr temp = Bpl.Expr.Ident(this.sink.CreateFreshLocal(field.ResolvedField.Type));
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(temp, this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, temp.Type)));
          TranslatedExpressions.Push(temp);
        } 
        return;
      }
      IArrayIndexer/*?*/ arrayIndexer = addressableExpression.Definition as IArrayIndexer;
      if (arrayIndexer != null)
      {
        this.Traverse(arrayIndexer);
        return;
      }
      IAddressDereference/*?*/ addressDereference = addressableExpression.Definition as IAddressDereference;
      if (addressDereference != null)
      {
        this.Traverse(addressDereference);
        return;
      }
      IBlockExpression block = addressableExpression.Definition as IBlockExpression;
      if (block != null) {
        this.Traverse(block);
        return;
      }
      IMethodReference/*?*/ method = addressableExpression.Definition as IMethodReference;
      if (method != null)
      {
        Console.WriteLine(MemberHelper.GetMethodSignature(method, NameFormattingOptions.Signature));
        //TODO
        throw new NotImplementedException();
      }
      Contract.Assert(addressableExpression.Definition is IThisReference);
    }

    public override void TraverseChildren(IAddressDereference addressDereference)
    {
      IBoundExpression be = addressDereference.Address as IBoundExpression;
      if (be != null)
      {
        IParameterDefinition pd = be.Definition as IParameterDefinition;
        if (pd != null)
        {
          var pv = this.sink.FindParameterVariable(pd, this.contractContext);
          TranslatedExpressions.Push(Bpl.Expr.Ident(pv));
          return;
        }
      }
      this.Traverse(addressDereference.Address);
      return;
    }

    public override void TraverseChildren(IArrayIndexer arrayIndexer) {

      if (!IsAtomicInstance(arrayIndexer.IndexedObject)) {
        // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
        var se = ExpressionSimplifier.Simplify(this.sink, arrayIndexer);
        this.Traverse(se);
        return;
      }

      this.Traverse(arrayIndexer.IndexedObject);
      Bpl.Expr arrayExpr = TranslatedExpressions.Pop();
      this.Traverse(arrayIndexer.Indices);
      int count = arrayIndexer.Indices.Count();
      Bpl.Expr[] indexExprs = new Bpl.Expr[count];
      for (int i = count; i > 0; i--) {
        indexExprs[i - 1] = TranslatedExpressions.Pop();
      }
      Bpl.Expr indexExpr;
      if (indexExprs.Length == 1) {
        indexExpr = indexExprs[0];
      }
      else {
        Bpl.Function f = this.sink.FindOrCreateNaryIntFunction(indexExprs.Length);
        indexExpr = new Bpl.NAryExpr(arrayIndexer.Token(), new Bpl.FunctionCall(f), new Bpl.ExprSeq(indexExprs));
      }

      this.TranslatedExpressions.Push(this.sink.Heap.ReadHeap(arrayExpr, indexExpr, AccessType.Array, this.sink.CciTypeToBoogie(arrayIndexer.Type)));
    }

    public override void TraverseChildren(ITargetExpression targetExpression)
    {
      Contract.Assume(false, "The expression containing this as a subexpression should never allow a call to this routine.");
    }

    public override void TraverseChildren(IThisReference thisReference)
    {
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(thisReference.Token(),
        this.sink.ThisVariable));
    }

    public override void TraverseChildren(IBoundExpression boundExpression)
    {

      if (boundExpression.Instance != null && !IsAtomicInstance(boundExpression.Instance)) {
        // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
        var se = ExpressionSimplifier.Simplify(this.sink, boundExpression);
        this.Traverse(se);
        return;
      }

      #region Local
      ILocalDefinition local = boundExpression.Definition as ILocalDefinition;
      if (local != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      #endregion

      #region Parameter
      IParameterDefinition param = boundExpression.Definition as IParameterDefinition;
      if (param != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param, this.contractContext)));
        return;
      }
      #endregion

      #region Field
      IFieldReference field = boundExpression.Definition as IFieldReference;
      if (field != null) {
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field.ResolvedField));
        var instance = boundExpression.Instance;
        if (instance == null) {
          TranslatedExpressions.Push(f);
        } else {
          this.Traverse(instance);
          Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
          var bplType = this.sink.CciTypeToBoogie(field.Type);
          var e = this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, bplType);
          this.TranslatedExpressions.Push(e);
        }
        return;
      }
      #endregion

      #region ArrayIndexer
      IArrayIndexer/*?*/ indexer = boundExpression.Definition as IArrayIndexer;
      if (indexer != null)
      {
        this.Traverse(indexer);
        return;
      }
      #endregion

      #region AddressDereference
      IAddressDereference/*?*/ deref = boundExpression.Definition as IAddressDereference;
      if (deref != null)
      {
        IAddressOf/*?*/ addressOf = deref.Address as IAddressOf;
        if (addressOf != null)
        {
          this.Traverse(addressOf.Expression);
          return;
        }
        if (boundExpression.Instance != null)
        {
          // TODO
          this.Traverse(boundExpression.Instance);
          Console.Write("->");
        }
        else if (deref.Address.Type is IPointerTypeReference)
          Console.Write("*");
        this.Traverse(deref.Address);
        return;
      }
      else
      {
        if (boundExpression.Instance != null)
        {
          throw new NotImplementedException("Addr DeRef without instance.");
        }
      }
      #endregion
    }

    internal static bool IsAtomicInstance(IExpression expression) {
      var thisInst = expression as IThisReference;
      if (thisInst != null) return true;
      // Since we're treating structs as being kept in the heap,
      // the expression "&s" is atomic if s is atomic.
      var addressOf = expression as IAddressOf;
      if (addressOf != null) {
        var ae = addressOf.Expression;
        return ae.Instance == null || IsAtomicInstance(ae.Instance);
      }
      var be = expression as IBoundExpression;
      if (be == null) return false;
      return be.Instance == null;
    }

    public override void TraverseChildren(IPopValue popValue) {
      var locExpr = this.StmtTraverser.operandStack.Pop();
      this.Traverse(locExpr);
      this.TranslatedExpressions.Push(this.TranslatedExpressions.Pop());
    }

    /// <summary>
    /// If the expression's type is a generic parameter (either method or type),
    /// then this returns a "unboxed" expression, i.e., the value as a ref.
    /// Otherwise it just translates the underlying expression and boxes it.
    /// </summary>
    public override void TraverseChildren(IAddressOf addressOf)
    {
      var t = addressOf.Expression.Type;
      var boogieT = this.sink.CciTypeToBoogie(t);

      if (t is IGenericParameterReference) {
        if (boogieT == this.sink.Heap.BoxType) {
          // then the expression will be represented by something of type Box
          // but the address of it must be a ref, so do the conversion
          this.Traverse(addressOf.Expression);
          var e = this.TranslatedExpressions.Pop();
          this.TranslatedExpressions.Push(this.sink.Heap.Unbox(addressOf.Token(), this.sink.Heap.RefType, e));
        } else {
          this.Traverse(addressOf.Expression);
        }
      } else {
        this.Traverse(addressOf.Expression);
        return;
        // TODO: Sometimes the value must still be boxed: for anythign that is not going to be represented as a Ref in Boogie!
        //this.Traverse(addressOf.Expression);
        //var e = this.TranslatedExpressions.Pop();

        //Bpl.Variable a = this.sink.CreateFreshLocal(addressOf.Type);
        //this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(Bpl.Token.NoToken, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
        //this.StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(Bpl.Token.NoToken, Bpl.Expr.Ident(a), Bpl.Expr.Ident(this.sink.Heap.BoxField), e, AccessType.Heap, boogieT));
        //this.TranslatedExpressions.Push(Bpl.Expr.Ident(a));

      }
    }
    #endregion

    #region Translate Constant Access

    public override void TraverseChildren(ICompileTimeConstant constant) {
      if (constant.Value == null) {
        var bplType = sink.CciTypeToBoogie(constant.Type);
        if (bplType == Bpl.Type.Int) {
          var lit = Bpl.Expr.Literal(0);
          lit.Type = Bpl.Type.Int;
          TranslatedExpressions.Push(lit);
        } else if (bplType == Bpl.Type.Bool) {
          TranslatedExpressions.Push(Bpl.Expr.False);
        } else if (bplType == this.sink.Heap.RefType) {
          TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.Heap.NullRef));
        } else {
          throw new NotImplementedException(String.Format("Don't know how to translate type: '{0}'", TypeHelper.GetTypeName(constant.Type)));
        }
        return;
      }
      if (constant.Value is string) {
        var c = this.sink.FindOrCreateConstant((string)(constant.Value));
        TranslatedExpressions.Push(Bpl.Expr.Ident(c));
        return;
      }
      if (constant.Type.IsEnum) {
        var lit = Bpl.Expr.Literal((int)constant.Value);
        lit.Type = Bpl.Type.Int;
        TranslatedExpressions.Push(lit);
        return;
      }
      switch (constant.Type.TypeCode) {
        case PrimitiveTypeCode.Boolean:
          // Decompiler might not have converted the constant back to a boolean? Not sure why,
          // but that's what I'm seeing here.
          if (constant.Value is bool) {
            TranslatedExpressions.Push(((bool)constant.Value) ? Bpl.Expr.True : Bpl.Expr.False);
          } else {
            TranslatedExpressions.Push(((int)constant.Value) != 0 ? Bpl.Expr.True : Bpl.Expr.False);
          }
          break;
        case PrimitiveTypeCode.Char: {
            var lit = Bpl.Expr.Literal((int)(char)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.Int8: {
            var lit = Bpl.Expr.Literal((int)(sbyte)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.Int16: {
            var lit = Bpl.Expr.Literal((int)(short)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.Int32: {
            var lit = Bpl.Expr.Literal((int)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.Int64: {
            var lit = Bpl.Expr.Literal(Microsoft.Basetypes.BigNum.FromLong((long)constant.Value));
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.UInt8: {
            var lit = Bpl.Expr.Literal((int)(byte)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.UInt16: {
            var lit = Bpl.Expr.Literal((int)(ushort)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.UInt32: {
            var lit = Bpl.Expr.Literal((int)(uint)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.UInt64: {
            var lit = Bpl.Expr.Literal(Microsoft.Basetypes.BigNum.FromULong((ulong)constant.Value));
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            break;
          }
        case PrimitiveTypeCode.Float32: {
            var c = this.sink.FindOrCreateConstant((float)(constant.Value));
            TranslatedExpressions.Push(Bpl.Expr.Ident(c));
            break;
          }
        case PrimitiveTypeCode.Float64: {
            var c = this.sink.FindOrCreateConstant((double)(constant.Value));
            TranslatedExpressions.Push(Bpl.Expr.Ident(c));
            break;
          }
        default:
          throw new NotImplementedException(String.Format("Can't translate compile-time constant of type '{0}'",
            TypeHelper.GetTypeName(constant.Type)));
      }
      return;
    }

    public override void TraverseChildren(IDefaultValue defaultValue) {
      var typ = defaultValue.Type;

      if (TranslationHelper.IsStruct(typ)) {
        translateStructDefaultValue(defaultValue, typ);
        return;
      }

      Bpl.Expr e;
      var bplType = this.sink.CciTypeToBoogie(typ);
      if (bplType == Bpl.Type.Int) {
        var lit = Bpl.Expr.Literal(0);
        lit.Type = Bpl.Type.Int;
        e = lit;
      } else if (bplType == Bpl.Type.Bool) {
        var lit = Bpl.Expr.False;
        lit.Type = Bpl.Type.Bool;
        e = lit;
      } else if (bplType == this.sink.Heap.RefType) {
        e = Bpl.Expr.Ident(this.sink.Heap.NullRef);
      } else if (bplType == this.sink.Heap.BoxType) {
        e = Bpl.Expr.Ident(this.sink.Heap.DefaultBox);
      } else if (bplType == this.sink.Heap.RealType) {
        e = Bpl.Expr.Ident(this.sink.Heap.DefaultReal);
      } else {
        throw new NotImplementedException(String.Format("Don't know how to translate type: '{0}'", TypeHelper.GetTypeName(typ)));
      }

      TranslatedExpressions.Push(e);
      return;
    }

    private void translateStructDefaultValue(IDefaultValue defaultValue, ITypeReference typ) {
      // then it is a struct and gets special treatment
      // translate it as if it were a call to the nullary ctor for the struct type
      // (which doesn't actually exist, but gets generated for each struct type
      // encountered during translation)

      var tok = defaultValue.Token();

      var loc = this.sink.CreateFreshLocal(typ);
      var locExpr = Bpl.Expr.Ident(loc);

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(tok, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(locExpr)));

      // Second, generate the call to the appropriate ctor
      var proc = this.sink.FindOrCreateProcedureForDefaultStructCtor(typ);
      var invars = new List<Bpl.Expr>();
      invars.Add(locExpr);
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(tok, proc.Name, invars, new List<Bpl.IdentifierExpr>()));

      // Generate an assumption about the dynamic type of the just allocated object
      this.StmtTraverser.StmtBuilder.Add(
          new Bpl.AssumeCmd(tok,
            Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
            this.sink.Heap.DynamicType(locExpr),
            this.FindOrCreateTypeReferenceInCodeContext(typ)
            )
            )
          );

      this.TranslatedExpressions.Push(locExpr);
    }

    #endregion

    #region Translate Method Calls
    /// <summary>
    /// 
    /// </summary>
    /// <param name="methodCall"></param>
    /// <remarks>Stub, This one really needs comments!</remarks>
    public override void TraverseChildren(IMethodCall methodCall) {
      var resolvedMethod = ResolveUnspecializedMethodOrThrow(methodCall.MethodToCall);

      Bpl.IToken methodCallToken = methodCall.Token();

      if (this.sink.Options.getMeHere) {
        // TODO: Get a method reference so this isn't a string comparison?
        var methodName = MemberHelper.GetMethodSignature(methodCall.MethodToCall, NameFormattingOptions.None);
        if (methodName.Equals("GetMeHere.GetMeHere.Assert")) {
          // for now, just translate it as "assert e"
          this.Traverse(methodCall.Arguments.First());
          Bpl.Expr e = this.TranslatedExpressions.Pop();
          this.StmtTraverser.StmtBuilder.Add(new Bpl.AssertCmd(methodCallToken, e));
          return;
        }
      }

      List<Bpl.Expr> inexpr;
      List<Bpl.IdentifierExpr> outvars;
      Bpl.IdentifierExpr thisExpr;
      Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed;
      var proc = TranslateArgumentsAndReturnProcedure(methodCallToken, methodCall.MethodToCall, resolvedMethod, methodCall.IsStaticCall ? null : methodCall.ThisArgument, methodCall.Arguments, out inexpr, out outvars, out thisExpr, out toBoxed);
      string methodname = proc.Name;
      var translateAsFunctionCall = proc is Bpl.Function;
      Bpl.QKeyValue attrib = null;

      // this code structure is quite chaotic, and some code needs to be evaluated regardless, hence the try-finally
      try {
        if (!translateAsFunctionCall) {
          foreach (var a in resolvedMethod.Attributes) {
            if (TypeHelper.GetTypeName(a.Type).EndsWith("AsyncAttribute")) {
              attrib = new Bpl.QKeyValue(methodCallToken, "async", new List<object>(), null);
            }
          }
        }

        var deferringCtorCall = resolvedMethod.IsConstructor && methodCall.ThisArgument is IThisReference;
        // REVIEW!! Ask Herman: is the above test enough? The following test is used in FindCtorCall.IsDeferringCtor,
        // but it doesn't work when the type is a struct S because then "this" has a type of "&S".
          //&& TypeHelper.TypesAreEquivalent(resolvedMethod.ContainingType, methodCall.ThisArgument.Type);

        if (resolvedMethod.IsConstructor && resolvedMethod.ContainingTypeDefinition.IsStruct && !deferringCtorCall) {
          handleStructConstructorCall(methodCall, methodCallToken, inexpr, outvars, thisExpr, proc);
          return;
        }

        Bpl.CallCmd call;
        bool isEventAdd = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("add_");
        bool isEventRemove = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("remove_");
        if (isEventAdd || isEventRemove) {
          call = translateAddRemoveCall(methodCall, resolvedMethod, methodCallToken, inexpr, outvars, thisExpr, isEventAdd);
        } else {
          if (translateAsFunctionCall) {
            var func = proc as Bpl.Function;
            var exprSeq = new Bpl.ExprSeq();
            foreach (var e in inexpr) {
              exprSeq.Add(e);
            }
            var callFunction = new Bpl.NAryExpr(methodCallToken, new Bpl.FunctionCall(func), exprSeq);
            this.TranslatedExpressions.Push(callFunction);
            return;
          } else {
            if (attrib != null)
              call = new Bpl.CallCmd(methodCallToken, methodname, inexpr, outvars, attrib);
            else
              call = new Bpl.CallCmd(methodCallToken, methodname, inexpr, outvars);
            this.StmtTraverser.StmtBuilder.Add(call);
          }
        }

        foreach (KeyValuePair<Bpl.IdentifierExpr, Bpl.IdentifierExpr> kv in toBoxed) {
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(kv.Key, this.sink.Heap.Unbox(Bpl.Token.NoToken, kv.Key.Type, kv.Value)));
        }

        Bpl.Expr expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef));
        this.StmtTraverser.RaiseException(expr);
      } finally {
        // TODO move away phone related code from the translation, it would be better to have 2 or more translation phases
        if (PhoneCodeHelper.instance().PhonePlugin != null) {
          if (PhoneCodeHelper.instance().PhoneNavigationToggled) {
            if (PhoneCodeHelper.instance().isNavigationCall(methodCall)) {
              Bpl.AssignCmd assignCmd = PhoneCodeHelper.instance().createBoogieNavigationUpdateCmd(sink);
              this.StmtTraverser.StmtBuilder.Add(assignCmd);
            }
          }

          if (PhoneCodeHelper.instance().PhoneFeedbackToggled) {
            if (PhoneCodeHelper.instance().isMethodKnownUIChanger(methodCall)) {
              Bpl.AssumeCmd assumeFalse = new Bpl.AssumeCmd(Bpl.Token.NoToken, Bpl.LiteralExpr.False);
              this.StmtTraverser.StmtBuilder.Add(assumeFalse);
            }
          }
        }
      }
    }

    private Bpl.CallCmd translateAddRemoveCall(IMethodCall methodCall, IMethodDefinition resolvedMethod, Bpl.IToken methodCallToken, List<Bpl.Expr> inexpr, List<Bpl.IdentifierExpr> outvars, Bpl.IdentifierExpr thisExpr, bool isEventAdd) {
      Bpl.CallCmd call;
      var mName = resolvedMethod.Name.Value;
      var eventName = mName.Substring(mName.IndexOf('_') + 1);
      var eventDef = TypeHelper.GetEvent(resolvedMethod.ContainingTypeDefinition, this.sink.host.NameTable.GetNameFor(eventName));
      Contract.Assert(eventDef != Dummy.Event);
      Bpl.Variable eventVar = this.sink.FindOrCreateEventVariable(eventDef);
      Bpl.Variable local = this.sink.CreateFreshLocal(eventDef.Type);

      if (methodCall.IsStaticCall) {
        this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(local), Bpl.Expr.Ident(eventVar)));
        inexpr.Insert(0, Bpl.Expr.Ident(local));
      } else {
        this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(local), this.sink.Heap.ReadHeap(thisExpr, Bpl.Expr.Ident(eventVar), resolvedMethod.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, local.TypedIdent.Type)));
        inexpr[0] = Bpl.Expr.Ident(local);
      }

      System.Diagnostics.Debug.Assert(outvars.Count == 0);
      outvars.Insert(0, Bpl.Expr.Ident(local));
      string methodName = isEventAdd ? this.sink.DelegateAddName : this.sink.DelegateRemoveName;
      call = new Bpl.CallCmd(methodCallToken, methodName, inexpr, outvars);
      this.StmtTraverser.StmtBuilder.Add(call);
      if (methodCall.IsStaticCall) {
        this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(eventVar), Bpl.Expr.Ident(local)));
      } else {
        this.StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(methodCallToken, thisExpr, Bpl.Expr.Ident(eventVar), Bpl.Expr.Ident(local), resolvedMethod.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, local.TypedIdent.Type));
      }
      return call;
    }

    private void handleStructConstructorCall(IMethodCall methodCall, Bpl.IToken methodCallToken, List<Bpl.Expr> inexpr, List<Bpl.IdentifierExpr> outvars, Bpl.IdentifierExpr thisExpr, Bpl.DeclWithFormals proc) {
      // then the method call looks like "&s.S.ctor(...)" for some variable s of struct type S
      // treat it as if it was "s := new S(...)"
      // So this code is the same as Visit(ICreateObjectInstance)
      // TODO: factor the code into a single method?

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(methodCallToken, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(thisExpr)));

      // Second, generate the call to the appropriate ctor
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(methodCallToken, proc.Name, inexpr, outvars));

      // Generate an assumption about the dynamic type of the just allocated object
      this.StmtTraverser.StmtBuilder.Add(
          new Bpl.AssumeCmd(methodCallToken,
            Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
            this.sink.Heap.DynamicType(thisExpr),
            this.FindOrCreateTypeReferenceInCodeContext(methodCall.MethodToCall.ResolvedMethod.ContainingTypeDefinition)
            )
            )
          );
    }

    // REVIEW: Does "thisExpr" really need to come back as an identifier? Can't it be a general expression?
    protected Bpl.DeclWithFormals TranslateArgumentsAndReturnProcedure(Bpl.IToken token, IMethodReference methodToCall, IMethodDefinition resolvedMethod, IExpression/*?*/ thisArg, IEnumerable<IExpression> arguments, out List<Bpl.Expr> inexpr, out List<Bpl.IdentifierExpr> outvars, out Bpl.IdentifierExpr thisExpr, out Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed) {
      inexpr = new List<Bpl.Expr>();
      outvars = new List<Bpl.IdentifierExpr>();

      #region Create the 'this' argument for the function call
      thisExpr = null;
      if (thisArg != null) {

        // Special case! thisArg is going to be an AddressOf expression if the receiver is a value-type
        // But if the method's containing type is something that doesn't get translated as a Ref, then
        // the AddressOf node should be ignored.
        var addrOf = thisArg as IAddressOf;
        var boogieType = this.sink.CciTypeToBoogie(methodToCall.ContainingType);
        if (addrOf != null && boogieType != this.sink.Heap.RefType) {
          thisArg = addrOf.Expression;
        }

        this.Traverse(thisArg);

        var e = this.TranslatedExpressions.Pop();
        var identifierExpr = e as Bpl.IdentifierExpr;
        if (identifierExpr == null) {
          var newLocal = Bpl.Expr.Ident(this.sink.CreateFreshLocal(methodToCall.ContainingType));
          var cmd = Bpl.Cmd.SimpleAssign(token, newLocal, e);
          this.StmtTraverser.StmtBuilder.Add(cmd);
          e = newLocal;
        } else {

        }
        inexpr.Add(e);
        thisExpr = (Bpl.IdentifierExpr) e;
      }
      #endregion

      toBoxed = new Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr>();
      IEnumerator<IParameterDefinition> penum = resolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More arguments than parameters in method call");
        }

        var expressionToTraverse = exp;
        Bpl.Type boogieTypeOfExpression;

        // Special case! exp can be an AddressOf expression if it is a value type being passed by reference.
        // But since we pass reference parameters by in-out value passing, need to short-circuit the
        // AddressOf node if the underlying type is not a Ref.
        var addrOf = exp as IAddressOf;
        if (addrOf != null) {
          boogieTypeOfExpression = this.sink.CciTypeToBoogie(addrOf.Expression.Type);
          if (boogieTypeOfExpression != this.sink.Heap.RefType) {
            expressionToTraverse = addrOf.Expression;
          }
        }

        boogieTypeOfExpression = this.sink.CciTypeToBoogie(expressionToTraverse.Type);
        this.Traverse(expressionToTraverse);

        Bpl.Expr e = this.TranslatedExpressions.Pop();
        var currentType = penum.Current.Type;
        if (currentType is IGenericParameterReference && this.sink.CciTypeToBoogie(currentType) == this.sink.Heap.BoxType)
          inexpr.Add(sink.Heap.Box(token, this.sink.CciTypeToBoogie(expressionToTraverse.Type), e));
        else {
          // Need to check if a struct value is being passed as an argument. If so, don't pass the struct,
          // but pass a copy of it.
          if (TranslationHelper.IsStruct(currentType)) {
            var proc = this.sink.FindOrCreateProcedureForStructCopy(currentType);
            var bplLocal = Bpl.Expr.Ident(this.sink.CreateFreshLocal(e.Type));
            var cmd = new Bpl.CallCmd(token, proc.Name, new List<Bpl.Expr> { e, }, new List<Bpl.IdentifierExpr>{ bplLocal, });
            this.StmtTraverser.StmtBuilder.Add(cmd);
            e = bplLocal;
          }
          inexpr.Add(e);
        }
        if (penum.Current.IsByReference) {
          Bpl.IdentifierExpr unboxed = e as Bpl.IdentifierExpr;
          if (unboxed == null) {
            throw new TranslationException("Trying to pass a complex expression for an out or ref parameter");
          }
          if (penum.Current.Type is IGenericParameterReference) {
            var boogieType = this.sink.CciTypeToBoogie(penum.Current.Type);
            if (boogieType == this.sink.Heap.BoxType) {
              Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(sink.CreateFreshLocal(this.sink.Heap.BoxType));
              toBoxed[unboxed] = boxed;
              outvars.Add(boxed);
            } else {
              outvars.Add(unboxed);
            }
          } else {
            outvars.Add(unboxed);
          }
        }
        penum.MoveNext();
      }

      if (resolvedMethod.IsStatic) {
        List<ITypeReference> consolidatedTypeArguments = new List<ITypeReference>();
        Sink.GetConsolidatedTypeArguments(consolidatedTypeArguments, methodToCall.ContainingType);
        foreach (ITypeReference typeReference in consolidatedTypeArguments) {
          inexpr.Add(this.FindOrCreateTypeReferenceInCodeContext(typeReference));
        }
      }
      IGenericMethodInstanceReference methodInstanceReference = methodToCall as IGenericMethodInstanceReference;
      if (methodInstanceReference != null) {
        foreach (ITypeReference typeReference in methodInstanceReference.GenericArguments) {
          inexpr.Add(this.FindOrCreateTypeReferenceInCodeContext(typeReference));
        }
      }

      var procInfo = this.sink.FindOrCreateProcedure(resolvedMethod);
      var translateAsFunctionCall = procInfo.Decl is Bpl.Function;
      if (!translateAsFunctionCall) {
        if (resolvedMethod.Type.ResolvedType.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Variable v = this.sink.CreateFreshLocal(methodToCall.ResolvedMethod.Type.ResolvedType);
          Bpl.IdentifierExpr unboxed = new Bpl.IdentifierExpr(token, v);
          if (resolvedMethod.Type is IGenericParameterReference) {
            var boogieType = this.sink.CciTypeToBoogie(resolvedMethod.Type);
            if (boogieType == this.sink.Heap.BoxType) {
              Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(this.sink.CreateFreshLocal(this.sink.Heap.BoxType));
              toBoxed[unboxed] = boxed;
              outvars.Add(boxed);
            } else {
              outvars.Add(unboxed);
            }
          } else {
            outvars.Add(unboxed);
          }
          TranslatedExpressions.Push(unboxed);
        }
      }

      return procInfo.Decl;
    }

    #endregion

    #region Translate Assignments

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub </remarks>
    /// <param name="assignment"></param>
    public override void TraverseChildren(IAssignment assignment) {
      Contract.Assert(TranslatedExpressions.Count == 0);
      var tok = assignment.Token();

      bool translationIntercepted= false;
      ICompileTimeConstant constant= assignment.Source as ICompileTimeConstant;
      // TODO move away phone related code from the translation, it would be better to have 2 or more translation phases
      // NAVIGATION TODO maybe this will go away if I can handle it with stubs
      if (PhoneCodeHelper.instance().PhonePlugin != null && PhoneCodeHelper.instance().PhoneNavigationToggled) {
        IFieldReference target = assignment.Target.Definition as IFieldReference;
        if (target != null && target.Name.Value == PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE) {
          if (constant != null && constant.Type == sink.host.PlatformType.SystemString && constant.Value != null &&
              constant.Value.Equals(PhoneCodeHelper.BOOGIE_DO_HAVOC_CURRENTURI)) {
            TranslateHavocCurrentURI();
            translationIntercepted = true;
          }
          StmtTraverser.StmtBuilder.Add(PhoneCodeHelper.instance().getAddNavigationCheck(sink));
        }
      }

      if (!translationIntercepted)
        TranslateAssignment(tok, assignment.Target.Definition, assignment.Target.Instance, assignment.Source);
    }

    /// <summary>
    /// Patch, to account for URIs that cannot be tracked because of current dataflow restrictions
    /// </summary>
    private void TranslateHavocCurrentURI() {
      // TODO move away phone related code from the translation, it would be better to have 2 or more translation phases
      IMethodReference havocMethod= PhoneCodeHelper.instance().getUriHavocerMethod(sink);
      Sink.ProcedureInfo procInfo= sink.FindOrCreateProcedure(havocMethod.ResolvedMethod);
      Bpl.CallCmd havocCall = new Bpl.CallCmd(Bpl.Token.NoToken, procInfo.Decl.Name, new List<Bpl.Expr>(), new List<Bpl.IdentifierExpr>());
      StmtTraverser.StmtBuilder.Add(havocCall);
    }

    /// <summary>
    /// Handles "instance.container := source".
    /// Note that instance can be null in which case the container better be
    /// a local, parameter, static field, or address dereference.
    /// </summary>
    private void TranslateAssignment(Bpl.IToken tok, object container, IExpression/*?*/ instance, IExpression source) {
      Contract.Assert(TranslatedExpressions.Count == 0);

      var typ = source.Type;
      var structCopy = TranslationHelper.IsStruct(typ) && !(source is IDefaultValue);
      // then a struct value of type S is being assigned: "lhs := s"
      // model this as the statement "call lhs := S..#copy_ctor(s)" that does the bit-wise copying
      Bpl.DeclWithFormals proc = null;
      if (structCopy) {
        proc = this.sink.FindOrCreateProcedureForStructCopy(typ);
      }
      Bpl.Cmd cmd;

      var/*?*/ local = container as ILocalDefinition;
      if (local != null) {
        Contract.Assume(instance == null);
        this.Traverse(source);
        var e = this.TranslatedExpressions.Pop();
        var bplLocal = Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local));
        if (structCopy) {
          cmd = new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr>{ e, }, new List<Bpl.IdentifierExpr>{ bplLocal, });
        } else {
          cmd = Bpl.Cmd.SimpleAssign(tok, bplLocal, e);
        }
        StmtTraverser.StmtBuilder.Add(cmd);
        return;
      }

      var/*?*/ parameter = container as IParameterDefinition;
      if (parameter != null) {
        Contract.Assume(instance == null);
        this.Traverse(source);
        var e = this.TranslatedExpressions.Pop();
        var bplParam = Bpl.Expr.Ident(this.sink.FindParameterVariable(parameter, this.contractContext));
        if (structCopy) {
          cmd = new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { e, bplParam, }, new List<Bpl.IdentifierExpr>());
        } else {
          cmd = Bpl.Cmd.SimpleAssign(tok, bplParam, e);
        }
        StmtTraverser.StmtBuilder.Add(cmd);
        return;
      }

      var/*?*/ field = container as IFieldReference;
      if (field != null) {
        this.Traverse(source);
        var e = this.TranslatedExpressions.Pop();
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field));
        if (instance == null) {
          // static fields are not kept in the heap
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, f, e));
        }
        else {
          this.Traverse(instance);
          var x = this.TranslatedExpressions.Pop();
          var boogieType = sink.CciTypeToBoogie(field.Type);
          StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(tok, x, f, e,
            field.ResolvedField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap,
            boogieType));
        }
        return;
      }

      var/*?*/ arrayIndexer = container as IArrayIndexer;
      if (arrayIndexer != null) {
        this.Traverse(instance);
        var x = this.TranslatedExpressions.Pop();
        this.Traverse(arrayIndexer.Indices);
        var indices_prime = this.TranslatedExpressions.Pop();
        this.Traverse(source);
        var e = this.TranslatedExpressions.Pop();
        StmtTraverser.StmtBuilder.Add(sink.Heap.WriteHeap(Bpl.Token.NoToken, x, indices_prime, e, AccessType.Array, sink.CciTypeToBoogie(arrayIndexer.Type)));
        return;
      }

      var/*?*/ addressDereference = container as IAddressDereference;
      if (addressDereference != null) {
        var addressOf = addressDereference.Address as IAddressOf;
        if (addressOf != null) {
          var ae = addressOf.Expression;
          TranslateAssignment(tok, ae.Definition, ae.Instance, source);
          return;
        }
        var pop = addressDereference.Address as IPopValue;
        if (pop != null) {
          var popValue = this.StmtTraverser.operandStack.Pop();
          var be = popValue as IBoundExpression;
          if (be != null) {
            TranslateAssignment(tok, be.Definition, be.Instance, source);
            return;
          }
          var ao = popValue as IAddressOf;
          if (ao != null) {
            TranslateAssignment(tok, ao.Expression.Definition, ao.Expression.Instance, source);
            return;
          }
        }
        var be2 = addressDereference.Address as IBoundExpression;
        if (be2 != null) {
          TranslateAssignment(tok, be2.Definition, be2.Instance, source);
          return;
        }
        var thisExp = addressDereference.Address as IThisReference;
        if (thisExp != null) {
          // I believe this happens only when a struct calls the default
          // ctor (probably only ever done in a different ctor for the
          // struct). The assignment actually looks like "*this := DefaultValue(S)"
          Contract.Assume(instance == null);
          this.Traverse(source);
          var e = this.TranslatedExpressions.Pop();
          var bplLocal = Bpl.Expr.Ident(this.sink.ThisVariable);
          cmd = Bpl.Cmd.SimpleAssign(tok, bplLocal, e);
          StmtTraverser.StmtBuilder.Add(cmd);
          return;
        }
      }

      Contract.Assume(false);
    }
    
    #endregion

    #region Translate Object Creation

    /// <summary>
    /// For "new A(...)" generate "{ A a = Alloc(); A..ctor(a); return a; }" where
    /// "a" is a fresh local.
    /// </summary>
    public override void TraverseChildren(ICreateObjectInstance createObjectInstance)
    {
      var ctor = createObjectInstance.MethodToCall;
      var resolvedMethod = ResolveUnspecializedMethodOrThrow(ctor);

      Bpl.IToken token = createObjectInstance.Token();

      var a = this.sink.CreateFreshLocal(createObjectInstance.Type);

      if (createObjectInstance.Type.TypeCode == PrimitiveTypeCode.IntPtr ||
          createObjectInstance.Type.TypeCode == PrimitiveTypeCode.UIntPtr) {
        List<Bpl.Expr> args = new List<Bpl.Expr>();
        foreach (IExpression e in createObjectInstance.Arguments) {
          this.Traverse(e);
          args.Add(TranslatedExpressions.Pop());
        }
        System.Diagnostics.Debug.Assert(args.Count == 1);
        this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(a), args[0]));
      }
      else {
        // First generate an Alloc() call
        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));

        // Second, generate the call to the appropriate ctor

        List<Bpl.Expr> inexpr;
        List<Bpl.IdentifierExpr> outvars;
        Bpl.IdentifierExpr thisExpr;
        Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed;
        var proc = TranslateArgumentsAndReturnProcedure(token, ctor, resolvedMethod, null, createObjectInstance.Arguments, out inexpr, out outvars, out thisExpr, out toBoxed);
        inexpr.Insert(0, Bpl.Expr.Ident(a));
        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, proc.Name, inexpr, outvars));

        // Generate an assumption about the dynamic type of the just allocated object
        this.StmtTraverser.StmtBuilder.Add(
            new Bpl.AssumeCmd(token,
              Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
              this.sink.Heap.DynamicType(Bpl.Expr.Ident(a)),
              this.FindOrCreateTypeReferenceInCodeContext(createObjectInstance.Type)
              )
              )
            );
      }
      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }

    public override void TraverseChildren(ICreateArray createArrayInstance)
    {
      Bpl.IToken cloc = createArrayInstance.Token();
      var a = this.sink.CreateFreshLocal(createArrayInstance.Type);

      Debug.Assert(createArrayInstance.Rank > 0); 
      Bpl.Expr lengthExpr = Bpl.Expr.Literal(1);
      foreach (IExpression expr in createArrayInstance.Sizes) {
        this.Traverse(expr);
        lengthExpr = Bpl.Expr.Mul(lengthExpr, TranslatedExpressions.Pop());
      }
      
      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
      Bpl.Expr assumeExpr = Bpl.Expr.Eq(new Bpl.NAryExpr(cloc, new Bpl.FunctionCall(this.sink.Heap.ArrayLengthFunction), new Bpl.ExprSeq(Bpl.Expr.Ident(a))), lengthExpr);
      this.StmtTraverser.StmtBuilder.Add(new Bpl.AssumeCmd(cloc, assumeExpr));
      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }

    public override void TraverseChildren(ICreateDelegateInstance createDelegateInstance)
    {
      if (createDelegateInstance.Instance == null) {
        TranslatedExpressions.Push(Bpl.Expr.Literal(0));
      }
      else {
        this.Traverse(createDelegateInstance.Instance);
      }

      TranslateDelegateCreation(createDelegateInstance.MethodToCallViaDelegate, createDelegateInstance.Type, createDelegateInstance);
    }

    private void TranslateDelegateCreation(IMethodReference methodToCall, ITypeReference type, IExpression creationAST)
    {
      Bpl.IToken cloc = creationAST.Token();
      var a = this.sink.CreateFreshLocal(creationAST.Type);

      ITypeDefinition unspecializedType = Microsoft.Cci.MutableContracts.ContractHelper.Unspecialized(type.ResolvedType).ResolvedType;
      IMethodDefinition unspecializedMethod = ResolveUnspecializedMethodOrThrow(methodToCall);
      sink.AddDelegate(unspecializedType, unspecializedMethod);
      Bpl.Constant constant = sink.FindOrCreateDelegateMethodConstant(unspecializedMethod);
      Bpl.Expr methodExpr = Bpl.Expr.Ident(constant);
      Bpl.Expr instanceExpr = TranslatedExpressions.Pop();

      Bpl.ExprSeq typeParameterExprs = new Bpl.ExprSeq();

      if (unspecializedMethod.IsStatic) {
        List<ITypeReference> consolidatedTypeArguments = new List<ITypeReference>();
        Sink.GetConsolidatedTypeArguments(consolidatedTypeArguments, methodToCall.ContainingType);
        foreach (ITypeReference typeReference in consolidatedTypeArguments) {
          typeParameterExprs.Add(this.FindOrCreateTypeReferenceInCodeContext(typeReference));
        }
      }
      IGenericMethodInstanceReference methodInstanceReference = methodToCall as IGenericMethodInstanceReference;
      if (methodInstanceReference != null) {
        foreach (ITypeReference typeReference in methodInstanceReference.GenericArguments) {
          typeParameterExprs.Add(this.FindOrCreateTypeReferenceInCodeContext(typeReference));
        }
      }
      Bpl.Expr typeParameterExpr =
        new Bpl.NAryExpr(Bpl.Token.NoToken,
                         new Bpl.FunctionCall(this.sink.FindOrCreateNaryTypeFunction(typeParameterExprs.Length)),
                         typeParameterExprs);
      this.StmtTraverser.StmtBuilder.Add(
        new Bpl.CallCmd(cloc, this.sink.DelegateCreateName,
                        new Bpl.ExprSeq(this.sink.CreateDelegate(methodExpr, instanceExpr, typeParameterExpr)), 
                        new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }
    
    #endregion

    #region Translate Binary Operators

    public override void TraverseChildren(IAddition addition)
    {
      base.TraverseChildren(addition);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      switch (addition.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            addition.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealPlus),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Add, lexp, rexp);
          break;
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IBitwiseAnd bitwiseAnd) {
      base.TraverseChildren(bitwiseAnd);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      if (bitwiseAnd.Type.TypeCode == PrimitiveTypeCode.Boolean) {
        e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, lexp, rexp);
      }
      else {
        e = new Bpl.NAryExpr(
          bitwiseAnd.Token(),
          new Bpl.FunctionCall(this.sink.Heap.BitwiseAnd),
          new Bpl.ExprSeq(lexp, rexp)
          );
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IBitwiseOr bitwiseOr) {
      base.TraverseChildren(bitwiseOr);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      if (bitwiseOr.Type.TypeCode == PrimitiveTypeCode.Boolean) {
        e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Or, lexp, rexp);
      }
      else {
        e = new Bpl.NAryExpr(
          bitwiseOr.Token(),
          new Bpl.FunctionCall(this.sink.Heap.BitwiseOr),
          new Bpl.ExprSeq(lexp, rexp)
          );
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IModulus modulus) {
      base.TraverseChildren(modulus);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      switch (modulus.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            modulus.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealModulus),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Mod, lexp, rexp);
          break;
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IDivision division)
    {
      base.TraverseChildren(division);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      switch (division.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            division.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealDivide),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Div, lexp, rexp);
          break;
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IExclusiveOr exclusiveOr) {
      base.TraverseChildren(exclusiveOr);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      var e = new Bpl.NAryExpr(
        exclusiveOr.Token(),
        new Bpl.FunctionCall(this.sink.Heap.BitwiseExclusiveOr),
        new Bpl.ExprSeq(lexp, rexp)
        );
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(ISubtraction subtraction)
    {
      base.TraverseChildren(subtraction);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      switch (subtraction.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            subtraction.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealMinus),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, lexp, rexp);
          break;
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IMultiplication multiplication)
    {
      base.TraverseChildren(multiplication);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e;
      switch (multiplication.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            multiplication.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealTimes),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Mul, lexp, rexp);
          break;
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IGreaterThan greaterThan)
    {
      base.TraverseChildren(greaterThan);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();

      Bpl.Expr e;
      switch (greaterThan.LeftOperand.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            greaterThan.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealGreaterThan),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Gt, lexp, rexp);
          break;
      }

      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IGreaterThanOrEqual greaterEqual)
    {
      base.TraverseChildren(greaterEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();

      Bpl.Expr e;
      switch (greaterEqual.LeftOperand.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            greaterEqual.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealGreaterThanOrEqual),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Ge, lexp, rexp);
          break;
      } 
      
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(ILessThan lessThan)
    {
      base.TraverseChildren(lessThan);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();

      Bpl.Expr e;
      switch (lessThan.LeftOperand.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            lessThan.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealLessThan),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Lt, lexp, rexp);
          break;
      }

      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(ILessThanOrEqual lessEqual)
    {
      base.TraverseChildren(lessEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();

      Bpl.Expr e;
      switch (lessEqual.LeftOperand.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            lessEqual.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealLessThanOrEqual),
            new Bpl.ExprSeq(lexp, rexp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Le, lexp, rexp);
          break;
      }

      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IEquality equal)
    {
      base.TraverseChildren(equal);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, lexp, rexp));
    }

    public override void TraverseChildren(INotEquality nonEqual)
    {
      base.TraverseChildren(nonEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, lexp, rexp));
    }

    public override void TraverseChildren(IRightShift rightShift) {
      base.TraverseChildren(rightShift);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e = new Bpl.NAryExpr(
            rightShift.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RightShift),
            new Bpl.ExprSeq(lexp, rexp)
            );
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(ILeftShift leftShift) {
      base.TraverseChildren(leftShift);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      Bpl.Expr e = new Bpl.NAryExpr(
            leftShift.Token(),
            new Bpl.FunctionCall(this.sink.Heap.LeftShift),
            new Bpl.ExprSeq(lexp, rexp)
            );
      TranslatedExpressions.Push(e);
    }
    /// <summary>
    /// There aren't any logical-and expressions or logical-or expressions in CCI.
    /// Instead they are encoded as "x ? y : 0" for "x && y" and "x ? 1 : y"
    /// for "x || y".
    /// TODO:
    /// If it isn't either of these short forms then emit the proper expression!
    /// </summary>
    public override void TraverseChildren(IConditional conditional) {
      /*
      #region Try and reconstruct And, Or, Not expressions
      if (conditional.Type.TypeCode == PrimitiveTypeCode.Boolean) {
        CompileTimeConstant ctc = conditional.ResultIfFalse as CompileTimeConstant;
        if (ctc != null) {
          var v = BooleanValueOfCompileTimeConstant(ctc);
          if (!v) { // x ? y : "false or 0" == x && y
            Visit(conditional.Condition);
            Bpl.Expr x = TranslatedExpressions.Pop();
            x = PossiblyCoerceRefToBool(x);
            Visit(conditional.ResultIfTrue);
            Bpl.Expr y = TranslatedExpressions.Pop();
            y = PossiblyCoerceRefToBool(y);
            TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, x, y));
            return;
          } else { // x ? y : "true or 1" == !x || y
            Visit(conditional.Condition);
            Bpl.Expr x = TranslatedExpressions.Pop();
            x = PossiblyCoerceRefToBool(x);
            Visit(conditional.ResultIfTrue);
            Bpl.Expr y = TranslatedExpressions.Pop();
            y = PossiblyCoerceRefToBool(y);
            var notX = Bpl.Expr.Unary(conditional.Token(), Bpl.UnaryOperator.Opcode.Not, x);
            TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Or, notX, y));
            return;
          }
        }
        ctc = conditional.ResultIfTrue as CompileTimeConstant;
        if (ctc != null && ctc.Type == BCT.Host.PlatformType.SystemInt32) {
          var v = BooleanValueOfCompileTimeConstant(ctc);
          if (v) { // x ? "true or 1" : y == x || y
            Visit(conditional.Condition);
            Bpl.Expr x = TranslatedExpressions.Pop();
            x = PossiblyCoerceRefToBool(x);
            Visit(conditional.ResultIfFalse);
            Bpl.Expr y = TranslatedExpressions.Pop();
            y = PossiblyCoerceRefToBool(y);
            TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Or, x, y));
            return;
          } else { // x ? "false or 0" : y == !x && y
            Visit(conditional.Condition);
            Bpl.Expr x = TranslatedExpressions.Pop();
            x = PossiblyCoerceRefToBool(x);
            Visit(conditional.ResultIfFalse);
            Bpl.Expr y = TranslatedExpressions.Pop();
            y = PossiblyCoerceRefToBool(y);
            var notX = Bpl.Expr.Unary(conditional.Token(), Bpl.UnaryOperator.Opcode.Not, x);
            TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, notX, y));
            return;
          }
        }
      }
      #endregion

      #region Just translate it as an if-then-else expression
      base.Visit(conditional);
      var ifFalse = TranslatedExpressions.Pop();
      var ifTrue = TranslatedExpressions.Pop();
      var c = TranslatedExpressions.Pop();
      var tok = conditional.Token();
      TranslatedExpressions.Push(
        new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok), new Bpl.ExprSeq(c, ifTrue, ifFalse))
          );
      return;
      #endregion
      */


      // TODO is this code actually needed at all? It seems that all this is already being done in the Statement traverser for the conditional
      StatementTraverser thenStmtTraverser = this.StmtTraverser.factory.MakeStatementTraverser(this.sink, this.StmtTraverser.PdbReader, this.contractContext);
      StatementTraverser elseStmtTraverser = this.StmtTraverser.factory.MakeStatementTraverser(this.sink, this.StmtTraverser.PdbReader, this.contractContext);
      ExpressionTraverser thenExprTraverser = this.StmtTraverser.factory.MakeExpressionTraverser(this.sink, thenStmtTraverser, this.contractContext);
      ExpressionTraverser elseExprTraverser = this.StmtTraverser.factory.MakeExpressionTraverser(this.sink, elseStmtTraverser, this.contractContext);
      thenExprTraverser.Traverse(conditional.ResultIfTrue);
      elseExprTraverser.Traverse(conditional.ResultIfFalse);

      this.Traverse(conditional.Condition);
      Bpl.Expr conditionExpr = this.TranslatedExpressions.Pop();

      Bpl.IfCmd ifcmd = new Bpl.IfCmd(conditional.Token(),
          conditionExpr,
          thenStmtTraverser.StmtBuilder.Collect(conditional.ResultIfTrue.Token()),
          null,
          elseStmtTraverser.StmtBuilder.Collect(conditional.ResultIfFalse.Token())
          );

      this.StmtTraverser.StmtBuilder.Add(ifcmd);

      var ifFalse = elseExprTraverser.TranslatedExpressions.Pop();
      var ifTrue = thenExprTraverser.TranslatedExpressions.Pop();
      TranslatedExpressions.Push(new Bpl.NAryExpr(conditional.Token(), new Bpl.IfThenElse(conditional.Token()), new Bpl.ExprSeq(conditionExpr, ifTrue, ifFalse)));
    }

    private bool BooleanValueOfCompileTimeConstant(CompileTimeConstant ctc) {
      if (ctc.Type.TypeCode == PrimitiveTypeCode.Int32)
        return ((int)ctc.Value) != 0;
      if (ctc.Type.TypeCode == PrimitiveTypeCode.Boolean)
        return (bool)ctc.Value;
      throw new NotImplementedException("BooleanValueOfCompileTimeConstant: Unknown type of compile-time constant");
    }

    /// <summary>
    /// Sometimes the decompiler doesn't recreate the expression "o != null" when the
    /// IL tests an object for being null by just branching on the object instead of
    /// doing a ceq operation on the constant null.
    /// </summary>
    /// <returns>
    /// If o is not of type Ref, then it just returns o, otherwise it returns
    /// the expression "o != null".
    /// </returns>
    private Bpl.Expr PossiblyCoerceRefToBool(Bpl.Expr o) {
      if (o.Type != this.sink.Heap.RefType) return o;
      return Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, o, Bpl.Expr.Ident(this.sink.Heap.NullRef));
    }

    #endregion

    #region Translate Unary Operators

    public override void TraverseChildren(ICastIfPossible castIfPossible) {
      base.Traverse(castIfPossible.ValueToCast);
      var exp = TranslatedExpressions.Pop();
      var e = this.FindOrCreateTypeReferenceInCodeContext(castIfPossible.TargetType);
      var callAs = new Bpl.NAryExpr(
        castIfPossible.Token(),
        new Bpl.FunctionCall(this.sink.Heap.AsFunction),
        new Bpl.ExprSeq(exp, e)
        );
      TranslatedExpressions.Push(callAs);
      return;
    }
    public override void TraverseChildren(ICheckIfInstance checkIfInstance) {
      var e = this.FindOrCreateTypeReferenceInCodeContext(checkIfInstance.TypeToCheck);
      //var callTypeOf = new Bpl.NAryExpr(
      //  checkIfInstance.Token(),
      //  new Bpl.FunctionCall(this.sink.Heap.TypeOfFunction),
      //  new Bpl.ExprSeq(new Bpl.IdentifierExpr(checkIfInstance.Token(), v))
      //  );
      base.Traverse(checkIfInstance.Operand);
      var exp = TranslatedExpressions.Pop();
      var dynTypeOfOperand = this.sink.Heap.DynamicType(exp);
      //var subtype = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Subtype, dynTypeOfOperand, e);
      var subtype = new Bpl.NAryExpr(
        Bpl.Token.NoToken,
        new Bpl.FunctionCall(this.sink.Heap.Subtype),
        new Bpl.ExprSeq(dynTypeOfOperand, e)
        );
      var notnull = Bpl.Expr.Neq(exp, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      var and = Bpl.Expr.And(notnull, subtype);
      TranslatedExpressions.Push(and);
      return;
    }

    public override void TraverseChildren(IConversion conversion) {
      var tok = conversion.ValueToConvert.Token();
      this.Traverse(conversion.ValueToConvert);
      var boogieTypeOfValue = this.sink.CciTypeToBoogie(conversion.ValueToConvert.Type);
      var boogieTypeToBeConvertedTo = this.sink.CciTypeToBoogie(conversion.TypeAfterConversion);
      if (boogieTypeOfValue == boogieTypeToBeConvertedTo) {
        // then this conversion is a nop, just ignore it
        return;
      }
      var nameOfTypeToConvert = TypeHelper.GetTypeName(conversion.ValueToConvert.Type);
      var nameOfTypeToBeConvertedTo = TypeHelper.GetTypeName(conversion.TypeAfterConversion);
      var msg = String.Format("Can't convert '{0}' to '{1}'", nameOfTypeToConvert, nameOfTypeToBeConvertedTo);

      var exp = TranslatedExpressions.Pop();

      if (boogieTypeToBeConvertedTo == Bpl.Type.Bool) {
        Bpl.Expr expr;
        if (boogieTypeOfValue == Bpl.Type.Int) {
          expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, exp, Bpl.Expr.Literal(0));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RefType) {
          expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, exp, Bpl.Expr.Ident(this.sink.Heap.NullRef));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RealType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Real2Int), new Bpl.ExprSeq(exp));
          expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, expr, Bpl.Expr.Literal(0));
        }
        else if (boogieTypeOfValue == this.sink.Heap.BoxType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Box2Bool), new Bpl.ExprSeq(exp));
        }
        else {
          throw new NotImplementedException(msg);
        }
        TranslatedExpressions.Push(expr);
        return;
      }

      if (boogieTypeToBeConvertedTo == Bpl.Type.Int) {
        Bpl.Expr expr;
        if (boogieTypeOfValue == Bpl.Type.Bool) {
          expr = new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok), new Bpl.ExprSeq(exp, Bpl.Expr.Literal(1), Bpl.Expr.Literal(0)));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RefType) {
          expr = this.sink.Heap.ReadHeap(exp, Bpl.Expr.Ident(this.sink.Heap.BoxField), AccessType.Heap, Bpl.Type.Int);
        }
        else if (boogieTypeOfValue == this.sink.Heap.RealType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Real2Int), new Bpl.ExprSeq(exp));
        }
        else if (boogieTypeOfValue == this.sink.Heap.BoxType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Box2Int), new Bpl.ExprSeq(exp));
        }
        else {
          throw new NotImplementedException(msg);
        }
        TranslatedExpressions.Push(expr);
        return;
      }

      if (boogieTypeToBeConvertedTo == this.sink.Heap.RefType) {
        Bpl.Variable a = this.sink.CreateFreshLocal(conversion.TypeAfterConversion);
        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(Bpl.Token.NoToken, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
        this.StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(Bpl.Token.NoToken, Bpl.Expr.Ident(a), Bpl.Expr.Ident(this.sink.Heap.BoxField), exp, AccessType.Heap, boogieTypeOfValue));
        TranslatedExpressions.Push(Bpl.Expr.Ident(a));
        return;
      }

      if (boogieTypeToBeConvertedTo == this.sink.Heap.RealType) {
        Bpl.Expr expr;
        if (boogieTypeOfValue == Bpl.Type.Bool) {
          expr = new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok), new Bpl.ExprSeq(exp, Bpl.Expr.Literal(1), Bpl.Expr.Literal(0)));
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Int2Real), new Bpl.ExprSeq(expr));
        }
        else if (boogieTypeOfValue == Bpl.Type.Int) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Int2Real), new Bpl.ExprSeq(exp));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RefType) {
          expr = this.sink.Heap.ReadHeap(exp, Bpl.Expr.Ident(this.sink.Heap.BoxField), AccessType.Heap, this.sink.Heap.RealType);
        }
        else if (boogieTypeOfValue == this.sink.Heap.BoxType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Box2Real), new Bpl.ExprSeq(exp));
        }
        else {
          throw new NotImplementedException(msg);
        }
        TranslatedExpressions.Push(expr);
        return;
      }
      
      if (boogieTypeToBeConvertedTo == this.sink.Heap.BoxType) {
        Bpl.Function func;
        if (boogieTypeOfValue == Bpl.Type.Bool) {
          func = this.sink.Heap.Bool2Box;
        }
        else if (boogieTypeOfValue == Bpl.Type.Int) {
          func = this.sink.Heap.Int2Box;
        }
        else if (boogieTypeOfValue == this.sink.Heap.RefType) {
          func = this.sink.Heap.Ref2Box;
        }
        else if (boogieTypeOfValue == this.sink.Heap.RealType) {
          func = this.sink.Heap.Real2Box;
        }
        else {
          throw new NotImplementedException(msg);
        }
        var boxExpr = new Bpl.NAryExpr(conversion.Token(), new Bpl.FunctionCall(func), new Bpl.ExprSeq(exp));
        TranslatedExpressions.Push(boxExpr);
        return;
      }
    }

    public override void TraverseChildren(IOnesComplement onesComplement) {
      base.TraverseChildren(onesComplement);
      var exp = TranslatedExpressions.Pop();
      var e = new Bpl.NAryExpr(
        onesComplement.Token(),
        new Bpl.FunctionCall(this.sink.Heap.BitwiseNegation),
        new Bpl.ExprSeq(exp)
        );
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(IUnaryNegation unaryNegation)
    {
      base.TraverseChildren(unaryNegation);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      Bpl.Expr e, zero, realZero;
      zero = Bpl.Expr.Literal(0);
      realZero = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Int2Real), new Bpl.ExprSeq(zero));
      switch (unaryNegation.Type.TypeCode) {
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          e = new Bpl.NAryExpr(
            unaryNegation.Token(),
            new Bpl.FunctionCall(this.sink.Heap.RealMinus),
            new Bpl.ExprSeq(realZero, exp)
            );
          break;
        default:
          e = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, Bpl.Expr.Literal(0), exp);
          break;
      }
      TranslatedExpressions.Push(e);
    }

    public override void TraverseChildren(ILogicalNot logicalNot)
    {
      base.Traverse(logicalNot.Operand);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      Bpl.Type operandType = this.sink.CciTypeToBoogie(logicalNot.Operand.Type);
      if (operandType == this.sink.Heap.RefType) {
        exp = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, exp, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (operandType == Bpl.Type.Int) {
        exp = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, exp, Bpl.Expr.Literal(0));
      }
      else {
        //System.Diagnostics.Debug.Assert(operandType == Bpl.Type.Bool);
      }
      TranslatedExpressions.Push(Bpl.Expr.Unary(
          logicalNot.Token(),
          Bpl.UnaryOperator.Opcode.Not, exp));
    }

    public override void TraverseChildren(ITypeOf typeOf) {
      var e = this.FindOrCreateTypeReferenceInCodeContext(typeOf.TypeToGet);
      var callTypeOf = new Bpl.NAryExpr(
        typeOf.Token(),
        new Bpl.FunctionCall(this.sink.Heap.TypeOfFunction),
        new Bpl.ExprSeq(e)
        );
      TranslatedExpressions.Push(callTypeOf);
    }

    public override void TraverseChildren(IVectorLength vectorLength) {
      base.Traverse(vectorLength.Vector);
      var e = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(new Bpl.NAryExpr(vectorLength.Token(), new Bpl.FunctionCall(this.sink.Heap.ArrayLengthFunction), new Bpl.ExprSeq(e)));
    }

    #endregion

    #region CodeContract Expressions
    public override void TraverseChildren(IOldValue oldValue)
    {
      base.TraverseChildren(oldValue);
      TranslatedExpressions.Push(new Bpl.OldExpr(oldValue.Token(),
        TranslatedExpressions.Pop()));
    }

    public override void TraverseChildren(IReturnValue returnValue)
    {
      if (this.sink.ReturnVariable == null)
      {
        throw new TranslationException(String.Format("Don't know what to do with return value {0}", returnValue.ToString()));
      }
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(returnValue.Token(),
        this.sink.ReturnVariable));

    }
    #endregion

    public override void TraverseChildren(IBlockExpression blockExpression) {
      this.StmtTraverser.Traverse(blockExpression.BlockStatement);
      this.Traverse(blockExpression.Expression);
    }

    /// <summary>
    /// This is a rewriter so it must be used on a mutable Code Model!!!
    /// </summary>
    private class ExpressionSimplifier : CodeRewriter {

      Sink sink;

      private ExpressionSimplifier(Sink sink)
        : base(sink.host) {
        this.sink = sink;
      }

      public static IExpression Simplify(Sink sink, IExpression expression) {
        var a = new ExpressionSimplifier(sink);
        return a.Rewrite(expression);
      }

      public override IExpression Rewrite(IBoundExpression boundExpression) {

        if (boundExpression.Instance == null || ExpressionTraverser.IsAtomicInstance(boundExpression.Instance)) return boundExpression;

        // boundExpression == BE(inst, def), i.e., inst.def
        // return { loc := e; [assert loc != null;] | BE(BE(null,loc), def) }, i.e., "loc := e; loc.def"
        //   where e is the rewritten inst

        var e = base.Rewrite(boundExpression.Instance);

        var loc = new LocalDefinition() {
          Name = this.host.NameTable.GetNameFor("_loc" + this.sink.LocalCounter.ToString()),
          Type = e.Type,
        };
        var locDecl = new LocalDeclarationStatement() {
          InitialValue = e,
          LocalVariable = loc,
        };
        return new BlockExpression() {
          BlockStatement = new BlockStatement() {
            Statements = new List<IStatement> { locDecl },
          },
          Expression = new BoundExpression() {
            Definition = boundExpression.Definition,
            Instance = new BoundExpression() {
              Definition = loc,
              Instance = null,
              Type = loc.Type,
            },
            Type = boundExpression.Type,
          },
        };

      }

      public override IExpression Rewrite(IArrayIndexer arrayIndexer) {
        if (ExpressionTraverser.IsAtomicInstance(arrayIndexer.IndexedObject)) return arrayIndexer;

        // arrayIndexer == AI(inst, [index]), i.e., inst[index0, index1,...]
        // return { loc := e; [assert loc != null;] | AI(BE(null,loc), [index]) }
        //   where e is the rewritten array instance

        var e = base.Rewrite(arrayIndexer.IndexedObject);

        var loc = new LocalDefinition() {
          Name = this.host.NameTable.GetNameFor("_loc" + this.sink.LocalCounter.ToString()),
          Type = e.Type
        };
        var locDecl = new LocalDeclarationStatement() {
          InitialValue = e,
          LocalVariable = loc,
        };
        return new BlockExpression() {
          BlockStatement = new BlockStatement() {
            Statements = new List<IStatement> { locDecl },
          },
          Expression = new ArrayIndexer() {
            IndexedObject = new BoundExpression() {
              Definition = loc,
              Instance = null,
              Type = loc.Type,
            },
            Indices = new List<IExpression>(arrayIndexer.Indices),
            Type = arrayIndexer.Type,
          },
        };
      }

      public override ITargetExpression Rewrite(ITargetExpression targetExpression) {
        Contract.Assume(false, "The expression containing this as a subexpression should never allow a call to this routine.");
        return null;
      }

    }
  }

}
