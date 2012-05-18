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

    /// <summary>
    /// True when the binary expression currently being processed is the top level expression of an ExpressionStatement and it has
    /// a target expression as its left operand (i.e. it is an assignment statement of the form tgt op= src).
    /// Be sure to clear this flag before any sub expresions are processed.
    /// </summary>
    bool currentExpressionIsOpAssignStatement;


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
    public ExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser, bool contractContext, bool expressionIsStatement)
    {
      this.sink = sink;
      this.StmtTraverser = statementTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();

      this.contractContext = contractContext;
      this.currentExpressionIsOpAssignStatement = expressionIsStatement;
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
      Contract.Assume(false, "The expression containing this as a subexpression should never allow a call to this routine.");
    }

    private void LoadAddressOf(object container, IExpression/*?*/ instance) {

      ILocalDefinition/*?*/ local = container as ILocalDefinition;
      if (local != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      IParameterDefinition/*?*/ param = container as IParameterDefinition;
      if (param != null)
      {
        this.LoadParameter(param);
        return;
      }
      IFieldReference/*?*/ field = container as IFieldReference;
      if (field != null) {
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field.ResolvedField));
        if (instance == null) {
          TranslatedExpressions.Push(f);
        } else {
          this.Traverse(instance);
          Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
          Bpl.IdentifierExpr temp = Bpl.Expr.Ident(this.sink.CreateFreshLocal(field.ResolvedField.Type));
          AssertOrAssumeNonNull(Bpl.Token.NoToken, instanceExpr);
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(temp, this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, temp.Type)));
          TranslatedExpressions.Push(temp);
        } 
        return;
      }
      IArrayIndexer/*?*/ arrayIndexer = container as IArrayIndexer;
      if (arrayIndexer != null)
      {
        this.Traverse(arrayIndexer);
        return;
      }
      IAddressDereference/*?*/ addressDereference = container as IAddressDereference;
      if (addressDereference != null)
      {
        this.Traverse(addressDereference);
        return;
      }
      IBlockExpression block = container as IBlockExpression;
      if (block != null) {
        this.Traverse(block);
        return;
      }
      IMethodReference/*?*/ method = container as IMethodReference;
      if (method != null)
      {
        Console.WriteLine(MemberHelper.GetMethodSignature(method, NameFormattingOptions.Signature));
        //TODO
        throw new NotImplementedException();
      }
      IExpression/*?*/ expression = container as IExpression;
      if (expression != null) {
        
        this.Traverse(expression);
        var e = this.TranslatedExpressions.Pop();

        var newLocal = Bpl.Expr.Ident(this.sink.CreateFreshLocal(expression.Type));
        var cmd = Bpl.Cmd.SimpleAssign(Bpl.Token.NoToken, newLocal, e);
        this.StmtTraverser.StmtBuilder.Add(cmd);

        this.TranslatedExpressions.Push(newLocal);

        return;
      }

      Contract.Assume(false);
    }

    public override void TraverseChildren(IAddressDereference addressDereference)
    {
      IBoundExpression be = addressDereference.Address as IBoundExpression;
      if (be != null)
      {
        IParameterDefinition pd = be.Definition as IParameterDefinition;
        if (pd != null)
        {
          this.LoadParameter(pd);
          return;
        }
      }
      this.Traverse(addressDereference.Address);
      return;
    }

    public override void TraverseChildren(IArrayIndexer arrayIndexer) {

      //if (!IsAtomicInstance(arrayIndexer.IndexedObject)) {
      //  // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
      //  var se = ExpressionSimplifier.Simplify(this.sink, arrayIndexer);
      //  this.Traverse(se);
      //  return;
      //}

      this.Traverse(arrayIndexer.IndexedObject);
      Bpl.Expr arrayExpr = TranslatedExpressions.Pop();

      var be = arrayIndexer.IndexedObject as IBoundExpression;
      if (be != null && be.Instance != null) {
        var l = this.sink.CreateFreshLocal(be.Type);
        var lhs = Bpl.Expr.Ident(l);
        var cmd = Bpl.Cmd.SimpleAssign(arrayIndexer.Token(), lhs, arrayExpr);
        this.StmtTraverser.StmtBuilder.Add(cmd);
        arrayExpr = lhs;
      }

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

      AssertOrAssumeNonNull(arrayIndexer.Token(), arrayExpr);
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

      //if (boundExpression.Instance != null && !IsAtomicInstance(boundExpression.Instance)) {
      //  // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
      //  var se = ExpressionSimplifier.Simplify(this.sink, boundExpression);
      //  this.Traverse(se);
      //  return;
      //}

      if (boundExpression.Instance != null) {
        this.Traverse(boundExpression.Instance);
        var nestedBE = boundExpression.Instance as IBoundExpression;
        if (nestedBE != null) {
          var l = this.sink.CreateFreshLocal(nestedBE.Type);
          var e = this.TranslatedExpressions.Pop();
          var lhs = Bpl.Expr.Ident(l);
          var cmd = Bpl.Cmd.SimpleAssign(boundExpression.Token(), lhs, e);
          this.StmtTraverser.StmtBuilder.Add(cmd);
          this.TranslatedExpressions.Push(lhs);
        }
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
        this.LoadParameter(param);
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
//          this.Traverse(instance);
          Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
          var bplType = this.sink.CciTypeToBoogie(field.Type);
          var e = this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, bplType);

          AssertOrAssumeNonNull(boundExpression.Token(), instanceExpr);

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

    private void AssertOrAssumeNonNull(Bpl.IToken token, Bpl.Expr instance) {
      if (this.sink.Options.dereference != Options.Dereference.None) {
        Bpl.Cmd c;
        var n = Bpl.Expr.Ident(this.sink.Heap.NullRef);
        var neq = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, instance, n);
        if (this.sink.Options.dereference == Options.Dereference.Assume) {
          c = new Bpl.AssumeCmd(token, neq);
        } else {
          c = new Bpl.AssertCmd(token, neq);
        }
        this.StmtTraverser.StmtBuilder.Add(c);
      }
    }

    internal static bool IsAtomicInstance(IExpression expression) {
      var thisInst = expression as IThisReference;
      if (thisInst != null) return true;
      if (expression is IDupValue) return true;
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

    public override void TraverseChildren(IDupValue dupValue) {
      var e = this.StmtTraverser.operandStack.Peek();
      this.TranslatedExpressions.Push(e);
    }
    public override void TraverseChildren(IPopValue popValue) {
      var locExpr = this.StmtTraverser.operandStack.Pop();
      this.TranslatedExpressions.Push(locExpr);
    }

    private void LoadParameter(IParameterDefinition parameter) {
      TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(parameter, this.contractContext)));
      return;
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

      if (t is IGenericParameterReference && boogieT == this.sink.Heap.UnionType) {
        // then the expression will be represented by something of type Box
        // but the address of it must be a ref, so do the conversion
        this.Traverse(addressOf.Expression);
        var e = this.TranslatedExpressions.Pop();
        this.TranslatedExpressions.Push(this.sink.Heap.FromUnion(addressOf.Token(), this.sink.Heap.RefType, e));
      } else {
        object container = addressOf.Expression.Definition;
        IExpression/*?*/ instance = addressOf.Expression.Instance;
        this.LoadAddressOf(container, instance);
        return;
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
      } else if (bplType == this.sink.Heap.UnionType) {
        e = Bpl.Expr.Ident(this.sink.Heap.DefaultHeapValue);
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
      Dictionary<Bpl.IdentifierExpr, Tuple<Bpl.IdentifierExpr,bool>> toBoxed;
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
            EmitLineDirective(methodCallToken);
            if (attrib != null)
              call = new Bpl.CallCmd(methodCallToken, methodname, inexpr, outvars, attrib);
            else
              call = new Bpl.CallCmd(methodCallToken, methodname, inexpr, outvars);
            this.StmtTraverser.StmtBuilder.Add(call);
          }
        }

        foreach (KeyValuePair<Bpl.IdentifierExpr, Tuple<Bpl.IdentifierExpr,bool>> kv in toBoxed) {
          var lhs = kv.Key;
          var tuple = kv.Value;
          var rhs = tuple.Item1;
          Bpl.Expr fromUnion;
          if (tuple.Item2) {
            // Since both structs and objects are represented by "Ref", need to make a distinction here.
            // Review: Introduce an explicit type "Struct"?
            fromUnion = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Union2Struct), new Bpl.ExprSeq(rhs));
          } else {
            fromUnion = this.sink.Heap.FromUnion(Bpl.Token.NoToken, lhs.Type, rhs);
            //this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(lhs, this.sink.Heap.FromUnion(Bpl.Token.NoToken, lhs.Type, rhs)));
          }
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(lhs, fromUnion));
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

    private void EmitLineDirective(Bpl.IToken methodCallToken) {
      var sloc = this.StmtTraverser.lastSourceLocation;
      if (sloc != null) {
        var fileName = sloc.Document.Location;
        var lineNumber = sloc.StartLine;
        var attrib = new Bpl.QKeyValue(methodCallToken, "sourceLine", new List<object> { Bpl.Expr.Literal((int)lineNumber) }, null);
        attrib = new Bpl.QKeyValue(methodCallToken, "sourceFile", new List<object> { fileName }, attrib);
        this.StmtTraverser.StmtBuilder.Add(new Bpl.AssertCmd(methodCallToken, Bpl.Expr.True, attrib));
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
        AssertOrAssumeNonNull(methodCallToken, thisExpr);
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
      EmitLineDirective(methodCallToken);
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
    protected Bpl.DeclWithFormals TranslateArgumentsAndReturnProcedure(Bpl.IToken token, IMethodReference methodToCall, IMethodDefinition resolvedMethod, IExpression/*?*/ thisArg, IEnumerable<IExpression> arguments, out List<Bpl.Expr> inexpr, out List<Bpl.IdentifierExpr> outvars, out Bpl.IdentifierExpr thisExpr, out Dictionary<Bpl.IdentifierExpr, Tuple<Bpl.IdentifierExpr,bool>> toUnioned) {
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
        if (false && addrOf != null && boogieType != this.sink.Heap.RefType) {
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

      toUnioned = new Dictionary<Bpl.IdentifierExpr, Tuple<Bpl.IdentifierExpr,bool>>();
      IEnumerator<IParameterDefinition> penum = resolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More arguments than parameters in method call");
        }

        var expressionToTraverse = exp;
        //Bpl.Type boogieTypeOfExpression;

        //// Special case! exp can be an AddressOf expression if it is a value type being passed by reference.
        //// But since we pass reference parameters by in-out value passing, need to short-circuit the
        //// AddressOf node if the underlying type is not a Ref.
        //var addrOf = exp as IAddressOf;
        //if (addrOf != null) {
        //  boogieTypeOfExpression = this.sink.CciTypeToBoogie(addrOf.Expression.Type);
        //  if (boogieTypeOfExpression != this.sink.Heap.RefType) {
        //    expressionToTraverse = addrOf.Expression;
        //  }
        //}

        //boogieTypeOfExpression = this.sink.CciTypeToBoogie(expressionToTraverse.Type);
        this.Traverse(expressionToTraverse);

        Bpl.Expr e = this.TranslatedExpressions.Pop();
        var currentType = penum.Current.Type;

        // If the argument is a struct, then make a copy of it to pass to the procedure.
        if (TranslationHelper.IsStruct(exp.Type)) {
          var proc = this.sink.FindOrCreateProcedureForStructCopy(exp.Type);
          var bplLocal = Bpl.Expr.Ident(this.sink.CreateFreshLocal(exp.Type));
          var cmd = new Bpl.CallCmd(token, proc.Name, new List<Bpl.Expr> { e, }, new List<Bpl.IdentifierExpr> { bplLocal, });
          this.StmtTraverser.StmtBuilder.Add(cmd);
          e = bplLocal;
        }

        if (currentType is IGenericParameterReference && this.sink.CciTypeToBoogie(currentType) == this.sink.Heap.UnionType) {
          if (TranslationHelper.IsStruct(expressionToTraverse.Type)) {
            // Since both structs and objects are represented by "Ref", need to make a distinction here.
            // Review: Introduce an explicit type "Struct"?
            var toUnion = new Bpl.NAryExpr(token, new Bpl.FunctionCall(this.sink.Heap.Struct2Union), new Bpl.ExprSeq(e));
            inexpr.Add(toUnion);
          } else {
            inexpr.Add(sink.Heap.ToUnion(token, this.sink.CciTypeToBoogie(expressionToTraverse.Type), e));
          }
        } else {
          inexpr.Add(e);
        }
        if (penum.Current.IsByReference) {
          Bpl.IdentifierExpr unboxed = e as Bpl.IdentifierExpr;
          if (unboxed == null) {
            throw new TranslationException("Trying to pass a complex expression for an out or ref parameter");
          }
          if (penum.Current.Type is IGenericParameterReference) {
            var boogieType = this.sink.CciTypeToBoogie(penum.Current.Type);
            if (boogieType == this.sink.Heap.UnionType) {
              Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(sink.CreateFreshLocal(this.sink.Heap.UnionType));
              toUnioned[unboxed] = Tuple.Create(boxed,false);
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
          Bpl.IdentifierExpr unUnioned = new Bpl.IdentifierExpr(token, v);
          if (resolvedMethod.Type is IGenericParameterReference) {
            var boogieType = this.sink.CciTypeToBoogie(resolvedMethod.Type);
            if (boogieType == this.sink.Heap.UnionType) {
              Bpl.IdentifierExpr unioned = Bpl.Expr.Ident(this.sink.CreateFreshLocal(this.sink.Heap.UnionType));
              toUnioned[unUnioned] = Tuple.Create(unioned, TranslationHelper.IsStruct(methodToCall.ResolvedMethod.Type.ResolvedType));
              outvars.Add(unioned);
            } else {
              outvars.Add(unUnioned);
            }
          } else {
            outvars.Add(unUnioned);
          }
          TranslatedExpressions.Push(unUnioned);
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

      EmitLineDirective(tok);

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

    internal delegate void SourceTraverser(IExpression source);

    private void VisitAssignment(ITargetExpression target, IExpression source, SourceTraverser sourceTraverser,
      bool treatAsStatement, bool pushTargetRValue, bool resultIsInitialTargetRValue) {
      Contract.Requires(target != null);
      Contract.Requires(source != null);
      Contract.Requires(sourceTraverser != null);
      Contract.Requires(!resultIsInitialTargetRValue || pushTargetRValue);
      Contract.Requires(!pushTargetRValue || source is IBinaryOperation);

      var tok = source.Token();
      var typ = source.Type;
      var structCopy = TranslationHelper.IsStruct(typ) && !(source is IDefaultValue);
      // then a struct value of type S is being assigned: "lhs := s"
      // model this as the statement "call lhs := S..#copy_ctor(s)" that does the bit-wise copying
      Bpl.DeclWithFormals proc = null;
      if (structCopy) {
        proc = this.sink.FindOrCreateProcedureForStructCopy(typ);
      }

      object container = target.Definition;

      Top:

      ILocalDefinition/*?*/ local = container as ILocalDefinition;
      if (local != null) {
        if (source is IDefaultValue && !local.Type.ResolvedType.IsReferenceType) {
        //  this.LoadAddressOf(local, null);
        //  this.generator.Emit(OperationCode.Initobj, local.Type);
        //  if (!treatAsStatement) this.LoadLocal(local);
        } else {
          Bpl.IdentifierExpr temp = null;
          var bplLocal = Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local));
          if (pushTargetRValue) {
            this.TranslatedExpressions.Push(bplLocal);
            if (!treatAsStatement && resultIsInitialTargetRValue) {
              var loc = this.sink.CreateFreshLocal(source.Type);
              temp = Bpl.Expr.Ident(loc);
              var e3 = this.TranslatedExpressions.Pop();
              var cmd3 = Bpl.Cmd.SimpleAssign(tok, temp, e3);
              this.StmtTraverser.StmtBuilder.Add(cmd3);
              this.TranslatedExpressions.Push(temp);
            }
          }
          sourceTraverser(source);
          var e = this.TranslatedExpressions.Pop();
          if (temp != null) this.TranslatedExpressions.Push(temp);

          Bpl.Cmd cmd;
          if (structCopy) {
            cmd = new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { e, }, new List<Bpl.IdentifierExpr> { bplLocal, });
          } else {
            cmd = Bpl.Cmd.SimpleAssign(tok, bplLocal, e);
          }
          StmtTraverser.StmtBuilder.Add(cmd);

          if (!treatAsStatement && !resultIsInitialTargetRValue) {
            this.TranslatedExpressions.Push(bplLocal);
          }
        }
        return;
      }
      IParameterDefinition/*?*/ parameter = container as IParameterDefinition;
      if (parameter != null) {
        if (source is IDefaultValue && !parameter.Type.ResolvedType.IsReferenceType) {
          //this.LoadAddressOf(parameter, null);
          //this.generator.Emit(OperationCode.Initobj, parameter.Type);
          //if (!treatAsStatement) this.LoadParameter(parameter);
        } else {
          Bpl.IdentifierExpr temp = null;
          if (pushTargetRValue) {
            this.LoadParameter(parameter);
            if (!treatAsStatement && resultIsInitialTargetRValue) {
              var loc = this.sink.CreateFreshLocal(source.Type);
              temp = Bpl.Expr.Ident(loc);
              var e3 = this.TranslatedExpressions.Pop();
              var cmd3 = Bpl.Cmd.SimpleAssign(tok, temp, e3);
              this.StmtTraverser.StmtBuilder.Add(cmd3);
              this.TranslatedExpressions.Push(temp);
            }
          }
          sourceTraverser(source);
          var e = this.TranslatedExpressions.Pop();
          if (temp != null) this.TranslatedExpressions.Push(temp);
          var bplParam = Bpl.Expr.Ident(this.sink.FindParameterVariable(parameter, this.contractContext));

          Bpl.Cmd cmd;
          if (structCopy) {
            cmd = new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { e, bplParam, }, new List<Bpl.IdentifierExpr>());
          } else {
            cmd = Bpl.Cmd.SimpleAssign(tok, bplParam, e);
          }
          StmtTraverser.StmtBuilder.Add(cmd);

          if (!treatAsStatement && !resultIsInitialTargetRValue) {
            this.LoadParameter(parameter);
          }
        }
        return;
      }
      IFieldReference/*?*/ field = container as IFieldReference;
      if (field != null) {

        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field));
        var boogieTypeOfField = sink.CciTypeToBoogie(field.Type);

        if (source is IDefaultValue && !field.Type.ResolvedType.IsReferenceType) {
          //this.LoadAddressOf(field, target.Instance);
          //if (!treatAsStatement) {
          //  this.generator.Emit(OperationCode.Dup);
          //  this.StackSize++;
          //}
          //this.generator.Emit(OperationCode.Initobj, field.Type);
          //if (!treatAsStatement)
          //  this.generator.Emit(OperationCode.Ldobj, field.Type);
          //else
          //  this.StackSize--;
        } else {
          Bpl.Expr x = null;
          Bpl.IdentifierExpr temp = null;
          if (target.Instance != null) {
            this.Traverse(target.Instance);
            x = this.TranslatedExpressions.Pop();
            if (pushTargetRValue) {
              AssertOrAssumeNonNull(tok, x);
              var e2 = this.sink.Heap.ReadHeap(x, f, TranslationHelper.IsStruct(field.ContainingType) ? AccessType.Struct : AccessType.Heap, boogieTypeOfField);
              this.TranslatedExpressions.Push(e2);

              if (!treatAsStatement && resultIsInitialTargetRValue) {
                var loc = this.sink.CreateFreshLocal(source.Type);
                temp = Bpl.Expr.Ident(loc);
                var e3 = this.TranslatedExpressions.Pop();
                var cmd = Bpl.Cmd.SimpleAssign(tok, temp, e3);
                this.StmtTraverser.StmtBuilder.Add(cmd);
                this.TranslatedExpressions.Push(temp);
              }
            }
          }
          sourceTraverser(source);
          if (!treatAsStatement && !resultIsInitialTargetRValue) {
            var loc = this.sink.CreateFreshLocal(source.Type);
            temp = Bpl.Expr.Ident(loc);
            var e3 = this.TranslatedExpressions.Pop();
            var cmd = Bpl.Cmd.SimpleAssign(tok, temp, e3);
            this.StmtTraverser.StmtBuilder.Add(cmd);
            this.TranslatedExpressions.Push(temp);
          }

          var e = this.TranslatedExpressions.Pop();
          if (temp != null) this.TranslatedExpressions.Push(temp);

          if (target.Instance == null) {
            // static fields are not kept in the heap
            StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, f, e));
          } else {
            StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(tok, x, f, e,
              field.ResolvedField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap,
              boogieTypeOfField));
          }

        }
        return;
      }

      VisitArrayIndexer:

      IArrayIndexer/*?*/ arrayIndexer = container as IArrayIndexer;
      if (arrayIndexer != null) {
        Contract.Assume(arrayIndexer.Indices.Count() == 1); // BUG: deal with multi-dimensional arrays
        if (source is IDefaultValue && !arrayIndexer.Type.ResolvedType.IsReferenceType) {
        //  this.LoadAddressOf(arrayIndexer, target.Instance);
        //  if (!treatAsStatement) {
        //    this.generator.Emit(OperationCode.Dup);
        //    this.StackSize++;
        //  }
        //  this.generator.Emit(OperationCode.Initobj, arrayIndexer.Type);
        //  if (!treatAsStatement)
        //    this.generator.Emit(OperationCode.Ldobj, arrayIndexer.Type);
        //  else
        //    this.StackSize--;
        } else {
          Bpl.IdentifierExpr/*?*/ temp = null;
          this.Traverse(arrayIndexer.IndexedObject);
          var arrayExpr = this.TranslatedExpressions.Peek();
          this.Traverse(arrayIndexer.Indices);
          var indexExpr = this.TranslatedExpressions.Peek();
          if (pushTargetRValue) {
            AssertOrAssumeNonNull(tok, arrayExpr);
            var e2 = this.sink.Heap.ReadHeap(arrayExpr, indexExpr, AccessType.Array, this.sink.CciTypeToBoogie(arrayIndexer.Type));
            this.TranslatedExpressions.Push(e2);

            if (!treatAsStatement && resultIsInitialTargetRValue) {
                var loc = this.sink.CreateFreshLocal(source.Type);
                temp = Bpl.Expr.Ident(loc);
                var e3 = this.TranslatedExpressions.Pop();
                var cmd = Bpl.Cmd.SimpleAssign(tok, temp, e3);
                this.StmtTraverser.StmtBuilder.Add(cmd);
                this.TranslatedExpressions.Push(temp);
            }
          }
          sourceTraverser(source);

          var e = this.TranslatedExpressions.Pop();
          var indices_prime = this.TranslatedExpressions.Pop();
          var x = this.TranslatedExpressions.Pop();
          StmtTraverser.StmtBuilder.Add(sink.Heap.WriteHeap(Bpl.Token.NoToken, x, indices_prime, e, AccessType.Array, sink.CciTypeToBoogie(arrayIndexer.Type)));

          if (!treatAsStatement && !resultIsInitialTargetRValue) {
            AssertOrAssumeNonNull(tok, arrayExpr);
            var e2 = this.sink.Heap.ReadHeap(arrayExpr, indexExpr, AccessType.Array, this.sink.CciTypeToBoogie(arrayIndexer.Type));
            this.TranslatedExpressions.Push(e2);
          } else {
            if (temp != null) this.TranslatedExpressions.Push(temp);
          }
        }
        return;
      }
      IAddressDereference/*?*/ addressDereference = container as IAddressDereference;
      if (addressDereference != null) {
        var addrOf = addressDereference.Address as IAddressOf;
        if (addrOf != null) {
          var arrayIndexer2 = addrOf.Expression.Definition as IArrayIndexer;
          if (arrayIndexer2 != null) {
            container = arrayIndexer2;
            goto VisitArrayIndexer;
          }
        }
        var be = addressDereference.Address as IBoundExpression;
        if (be != null) {
          container = be.Definition;
          goto Top;
        }
        this.Traverse(addressDereference.Address);
        if (source is IDefaultValue && !addressDereference.Type.ResolvedType.IsReferenceType) {
          //if (!treatAsStatement) {
          //  this.generator.Emit(OperationCode.Dup);
          //  this.StackSize++;
          //}
          //this.generator.Emit(OperationCode.Initobj, addressDereference.Type);
          //if (!treatAsStatement)
          //  this.generator.Emit(OperationCode.Ldobj, addressDereference.Type);
          //else
          //  this.StackSize--;
        } else if (source is IAddressDereference) {
          //if (!treatAsStatement) {
          //  this.generator.Emit(OperationCode.Dup);
          //  this.StackSize++;
          //}
          //this.Traverse(((IAddressDereference)source).Address);
          //this.generator.Emit(OperationCode.Cpobj, addressDereference.Type);
          //this.StackSize -= 2;
          //if (!treatAsStatement)
          //  this.generator.Emit(OperationCode.Ldobj, addressDereference.Type);
        } else {
          Bpl.IdentifierExpr/*?*/ temp = null;
          if (pushTargetRValue) {
            this.TranslatedExpressions.Push(this.TranslatedExpressions.Peek());
            if (!treatAsStatement && resultIsInitialTargetRValue) {
              this.TranslatedExpressions.Push(this.TranslatedExpressions.Peek());
              var loc = this.sink.CreateFreshLocal(source.Type);
              temp = Bpl.Expr.Ident(loc);
              var e3 = this.TranslatedExpressions.Pop();
              var cmd = Bpl.Cmd.SimpleAssign(tok, temp, e3);
              this.StmtTraverser.StmtBuilder.Add(cmd);
              this.TranslatedExpressions.Push(temp);
            }
          }
          sourceTraverser(source);
          if (!treatAsStatement && !resultIsInitialTargetRValue) {
            this.TranslatedExpressions.Push(this.TranslatedExpressions.Peek());
            var loc = this.sink.CreateFreshLocal(source.Type);
            temp = Bpl.Expr.Ident(loc);
            var e3 = this.TranslatedExpressions.Pop();
            var cmd = Bpl.Cmd.SimpleAssign(tok, temp, e3);
            this.StmtTraverser.StmtBuilder.Add(cmd);
            this.TranslatedExpressions.Push(temp);
          }
          //this.VisitAssignmentTo(addressDereference);
          if (temp != null) this.TranslatedExpressions.Push(temp);
        }
        return;
      }
      IPropertyDefinition/*?*/ propertyDefinition = container as IPropertyDefinition;
      if (propertyDefinition != null) {
        Contract.Assume(propertyDefinition.Getter != null && propertyDefinition.Setter != null);
        if (!propertyDefinition.IsStatic) {
          this.Traverse(target.Instance);
        }
        Bpl.IdentifierExpr temp = null;
        var token = Bpl.Token.NoToken;
        if (pushTargetRValue) {

          List<Bpl.Expr> inexpr;
          List<Bpl.IdentifierExpr> outvars;
          Bpl.IdentifierExpr thisExpr;
          Dictionary<Bpl.IdentifierExpr, Tuple<Bpl.IdentifierExpr, bool>> toBoxed;
          var proc2 = TranslateArgumentsAndReturnProcedure(token, propertyDefinition.Getter, propertyDefinition.Getter.ResolvedMethod, target.Instance, Enumerable<IExpression>.Empty, out inexpr, out outvars, out thisExpr, out toBoxed);

          EmitLineDirective(token);

          this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, proc2.Name, inexpr, outvars));

          if (!treatAsStatement && resultIsInitialTargetRValue) {
            //var 
            //this.generator.Emit(OperationCode.Dup);
            //this.StackSize++;
            //temp = new TemporaryVariable(source.Type, this.method);
            //this.VisitAssignmentTo(temp);
          }
        }
        sourceTraverser(source);
        if (!treatAsStatement && !resultIsInitialTargetRValue) {
          var e3 = this.TranslatedExpressions.Pop();
          var loc = this.sink.CreateFreshLocal(source.Type);
          temp = Bpl.Expr.Ident(loc);
          var cmd = Bpl.Cmd.SimpleAssign(tok, temp, e3);
          this.StmtTraverser.StmtBuilder.Add(cmd);
          this.TranslatedExpressions.Push(temp);
        }

        var setterArgs = new List<Bpl.Expr>();
        var setterArg = this.TranslatedExpressions.Pop();
        if (!propertyDefinition.IsStatic)
          setterArgs.Add(this.TranslatedExpressions.Pop());
        setterArgs.Add(setterArg);

        var setterProc = this.sink.FindOrCreateProcedure(propertyDefinition.Setter.ResolvedMethod);
        EmitLineDirective(token);
        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, setterProc.Decl.Name, setterArgs, new List<Bpl.IdentifierExpr>()));

        if (temp != null) this.TranslatedExpressions.Push(temp);
        return;
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
        Dictionary<Bpl.IdentifierExpr, Tuple<Bpl.IdentifierExpr,bool>> toBoxed;
        var proc = TranslateArgumentsAndReturnProcedure(token, ctor, resolvedMethod, null, createObjectInstance.Arguments, out inexpr, out outvars, out thisExpr, out toBoxed);
        inexpr.Insert(0, Bpl.Expr.Ident(a));

        EmitLineDirective(token);

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
      var targetExpression = addition.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x += e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, addition, (IExpression e) => this.TraverseAdditionRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: addition.ResultIsUnmodifiedLeftOperand);
      } else { // x + e
        this.Traverse(addition.LeftOperand);
        this.TraverseAdditionRightOperandAndDoOperation(addition);
      }
    }
    private void TraverseAdditionRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IAddition);
      var addition = (IAddition)expression;
      this.Traverse(addition.RightOperand);

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
      var targetExpression = bitwiseAnd.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x &= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, bitwiseAnd, (IExpression e) => this.TraverseBitwiseAndRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: bitwiseAnd.ResultIsUnmodifiedLeftOperand);
      } else { // x & e
        this.Traverse(bitwiseAnd.LeftOperand);
        this.TraverseBitwiseAndRightOperandAndDoOperation(bitwiseAnd);
      }
    }
    private void TraverseBitwiseAndRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IBitwiseAnd);
      var bitwiseAnd = (IBitwiseAnd)expression;

      this.Traverse(bitwiseAnd.RightOperand);

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
      var targetExpression = bitwiseOr.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x |= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, bitwiseOr, (IExpression e) => this.TraverseBitwiseOrRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: bitwiseOr.ResultIsUnmodifiedLeftOperand);
      } else { // x | e
        this.Traverse(bitwiseOr.LeftOperand);
        this.TraverseBitwiseOrRightOperandAndDoOperation(bitwiseOr);
      }
    }

    private void TraverseBitwiseOrRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IBitwiseOr);
      var bitwiseOr = (IBitwiseOr)expression;
      this.Traverse(bitwiseOr.RightOperand);

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
      var targetExpression = modulus.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x %= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, modulus, (IExpression e) => this.TraverseModulusRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: modulus.ResultIsUnmodifiedLeftOperand);
      } else { // x % e
        this.Traverse(modulus.LeftOperand);
        this.TraverseModulusRightOperandAndDoOperation(modulus);
      }
    }

    private void TraverseModulusRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IModulus);
      var modulus = (IModulus)expression;
      this.Traverse(modulus.RightOperand);

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
      var targetExpression = division.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x /= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, division, (IExpression e) => this.TraverseDivisionRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: division.ResultIsUnmodifiedLeftOperand);
      } else { // x / e
        this.Traverse(division.LeftOperand);
        this.TraverseDivisionRightOperandAndDoOperation(division);
      }
    }

    private void TraverseDivisionRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IDivision);
      var division = (IDivision)expression;
      this.Traverse(division.RightOperand);

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
      var targetExpression = exclusiveOr.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x ^= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, exclusiveOr, (IExpression e) => this.TraverseExclusiveOrRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: exclusiveOr.ResultIsUnmodifiedLeftOperand);
      } else { // x ^ e
        this.Traverse(exclusiveOr.LeftOperand);
        this.TraverseExclusiveOrRightOperandAndDoOperation(exclusiveOr);
      }
    }

    private void TraverseExclusiveOrRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IExclusiveOr);
      var exclusiveOr = (IExclusiveOr)expression;
      this.Traverse(exclusiveOr.RightOperand);

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
      var targetExpression = subtraction.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x -= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, subtraction, (IExpression e) => this.TraverseSubtractionRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: subtraction.ResultIsUnmodifiedLeftOperand);
      } else { // x - e
        this.Traverse(subtraction.LeftOperand);
        this.TraverseSubtractionRightOperandAndDoOperation(subtraction);
      }
    }
    private void TraverseSubtractionRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is ISubtraction);
      var subtraction = (ISubtraction)expression;

      this.Traverse(subtraction.RightOperand);
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
      var targetExpression = multiplication.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x *= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, multiplication, (IExpression e) => this.TraverseMultiplicationRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: multiplication.ResultIsUnmodifiedLeftOperand);
      } else { // x * e
        this.Traverse(multiplication.LeftOperand);
        this.TraverseMultiplicationRightOperandAndDoOperation(multiplication);
      }
    }

    private void TraverseMultiplicationRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IMultiplication);
      var multiplication = (IMultiplication)expression;
      this.Traverse(multiplication.RightOperand);

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
      if ((equal.LeftOperand.Type.TypeCode != PrimitiveTypeCode.NotPrimitive || equal.LeftOperand.Type.TypeCode != PrimitiveTypeCode.NotPrimitive)
        && !TypeHelper.TypesAreEquivalent(equal.LeftOperand.Type, equal.RightOperand.Type)) {
        throw new TranslationException(
          String.Format("Decompiler messed up: equality's left operand is of type '{0}' but right operand is of type '{1}'.",
          TypeHelper.GetTypeName(equal.LeftOperand.Type),
          TypeHelper.GetTypeName(equal.RightOperand.Type)
          ));
      }

      base.TraverseChildren(equal);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, lexp, rexp));
    }

    public override void TraverseChildren(INotEquality nonEqual)
    {

      if ((nonEqual.LeftOperand.Type.TypeCode != PrimitiveTypeCode.NotPrimitive || nonEqual.LeftOperand.Type.TypeCode != PrimitiveTypeCode.NotPrimitive)
        &&
        !TypeHelper.TypesAreEquivalent(nonEqual.LeftOperand.Type, nonEqual.RightOperand.Type)) {
        throw new TranslationException(
          String.Format("Decompiler messed up: inequality's left operand is of type '{0}' but right operand is of type '{1}'.",
          TypeHelper.GetTypeName(nonEqual.LeftOperand.Type),
          TypeHelper.GetTypeName(nonEqual.RightOperand.Type)
          ));
      }

      base.TraverseChildren(nonEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, lexp, rexp));
    }

    public override void TraverseChildren(IRightShift rightShift) {
      var targetExpression = rightShift.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x >>= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, rightShift, (IExpression e) => this.TraverseRightShiftRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: rightShift.ResultIsUnmodifiedLeftOperand);
      } else { // x >> e
        this.Traverse(rightShift.LeftOperand);
        this.TraverseRightShiftRightOperandAndDoOperation(rightShift);
      }
    }

    private void TraverseRightShiftRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is IRightShift);
      var rightShift = (IRightShift)expression;
      this.Traverse(rightShift.RightOperand);

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
      var targetExpression = leftShift.LeftOperand as ITargetExpression;
      if (targetExpression != null) { // x <<= e
        bool statement = this.currentExpressionIsOpAssignStatement;
        this.currentExpressionIsOpAssignStatement = false;
        this.VisitAssignment(targetExpression, leftShift, (IExpression e) => this.TraverseLeftShiftRightOperandAndDoOperation(e),
          treatAsStatement: statement, pushTargetRValue: true, resultIsInitialTargetRValue: leftShift.ResultIsUnmodifiedLeftOperand);
      } else { // x << e
        this.Traverse(leftShift.LeftOperand);
        this.TraverseLeftShiftRightOperandAndDoOperation(leftShift);
      }
    }

    private void TraverseLeftShiftRightOperandAndDoOperation(IExpression expression) {
      Contract.Assume(expression is ILeftShift);
      var leftShift = (ILeftShift)expression;
      this.Traverse(leftShift.RightOperand);

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
      if (boogieTypeOfValue == boogieTypeToBeConvertedTo && !TranslationHelper.IsStruct(conversion.ValueToConvert.Type)
        && !TranslationHelper.IsStruct(conversion.TypeAfterConversion)) {
        // then this conversion is a nop, just ignore it
        return;
      }
      var nameOfTypeToConvert = TypeHelper.GetTypeName(conversion.ValueToConvert.Type);
      var nameOfTypeToBeConvertedTo = TypeHelper.GetTypeName(conversion.TypeAfterConversion);
      var msg = String.Format("Can't convert '{0}' to '{1}'", nameOfTypeToConvert, nameOfTypeToBeConvertedTo);

      var exp = TranslatedExpressions.Pop();

      if (boogieTypeOfValue == this.sink.Heap.UnionType && boogieTypeToBeConvertedTo != this.sink.Heap.RefType) {
        var e = this.sink.Heap.FromUnion(tok, boogieTypeToBeConvertedTo, exp);
        TranslatedExpressions.Push(e);
        return;
      }
      if (boogieTypeToBeConvertedTo == this.sink.Heap.UnionType) {
        Bpl.Expr e;
        if (boogieTypeOfValue == this.sink.Heap.RefType)
          e = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Unbox2Union), new Bpl.ExprSeq(exp));
        else
          e = this.sink.Heap.ToUnion(tok, boogieTypeOfValue, exp);
        TranslatedExpressions.Push(e);
        return;
      }

      if (boogieTypeToBeConvertedTo == this.sink.Heap.RefType &&
        TranslationHelper.IsStruct(conversion.TypeAfterConversion) &&
        boogieTypeOfValue == this.sink.Heap.RefType) {
        // REVIEW: This also applies to conversions from one struct type to another!
        var e = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Unbox2Struct), new Bpl.ExprSeq(exp));
        TranslatedExpressions.Push(e);
        return;
      }

      if (boogieTypeToBeConvertedTo == Bpl.Type.Bool) {
        Bpl.Expr expr;
        if (boogieTypeOfValue == Bpl.Type.Int) {
          expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, exp, Bpl.Expr.Literal(0));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RefType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Unbox2Bool), new Bpl.ExprSeq(exp));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RealType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Real2Int), new Bpl.ExprSeq(exp));
          expr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, expr, Bpl.Expr.Literal(0));
        }
        else if (boogieTypeOfValue == this.sink.Heap.UnionType) {
          expr = this.sink.Heap.FromUnion(tok, Bpl.Type.Bool, exp);
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
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Unbox2Int), new Bpl.ExprSeq(exp));
        }
        else if (boogieTypeOfValue == this.sink.Heap.RealType) {
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Real2Int), new Bpl.ExprSeq(exp));
        }
        else if (boogieTypeOfValue == this.sink.Heap.UnionType) {
          expr = this.sink.Heap.FromUnion(Bpl.Token.NoToken, Bpl.Type.Int, exp);
        }
        else {
          throw new NotImplementedException(msg);
        }
        TranslatedExpressions.Push(expr);
        return;
      }

      if (boogieTypeToBeConvertedTo == this.sink.Heap.RefType) {
        // var a = BoxFromXXX(exp);
        Bpl.Variable a = this.sink.CreateFreshLocal(conversion.TypeAfterConversion);
        Bpl.Procedure boxOperator;
        if (boogieTypeOfValue == Bpl.Type.Bool)
          boxOperator = this.sink.Heap.BoxFromBool;
        else if (boogieTypeOfValue == Bpl.Type.Int)
          boxOperator = this.sink.Heap.BoxFromInt;
        else if (boogieTypeOfValue == this.sink.Heap.RealType)
          boxOperator = this.sink.Heap.BoxFromReal;
        else if (TranslationHelper.IsStruct(conversion.ValueToConvert.Type)) {
          // Boxing a struct implicitly makes a copy of the struct
          var typeOfValue = conversion.ValueToConvert.Type;
          var proc = this.sink.FindOrCreateProcedureForStructCopy(typeOfValue);
          var bplLocal = Bpl.Expr.Ident(this.sink.CreateFreshLocal(typeOfValue));
          var cmd = new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { exp, }, new List<Bpl.IdentifierExpr> { bplLocal, });
          this.StmtTraverser.StmtBuilder.Add(cmd);
          exp = bplLocal;
          boxOperator = this.sink.Heap.BoxFromStruct;
        }  else {
          if (boogieTypeOfValue != this.sink.Heap.UnionType)
            throw new NotImplementedException(msg);
          boxOperator = this.sink.Heap.BoxFromUnion;
        }
        var name = boxOperator.Name;

        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(Bpl.Token.NoToken, name, new Bpl.ExprSeq(exp), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
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
          expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Unbox2Real), new Bpl.ExprSeq(exp));
        }
        else if (boogieTypeOfValue == this.sink.Heap.UnionType) {
          expr = this.sink.Heap.FromUnion(tok, this.sink.Heap.RealType, exp);
        }
        else {
          throw new NotImplementedException(msg);
        }
        TranslatedExpressions.Push(expr);
        return;
      }
      
      //if (boogieTypeToBeConvertedTo == this.sink.Heap.UnionType) {
      //  Bpl.Function func;
      //  if (boogieTypeOfValue == Bpl.Type.Bool) {
      //    func = this.sink.Heap.Bool2Union;
      //  }
      //  else if (boogieTypeOfValue == Bpl.Type.Int) {
      //    func = this.sink.Heap.Int2Union;
      //  }
      //  else if (boogieTypeOfValue == this.sink.Heap.RefType) {
      //    func = this.sink.Heap.Ref2Union;
      //  }
      //  else if (boogieTypeOfValue == this.sink.Heap.RealType) {
      //    func = this.sink.Heap.Real2Union;
      //  }
      //  else {
      //    throw new NotImplementedException(msg);
      //  }
      //  var boxExpr = new Bpl.NAryExpr(conversion.Token(), new Bpl.FunctionCall(func), new Bpl.ExprSeq(exp));
      //  TranslatedExpressions.Push(boxExpr);
      //  return;
      //}
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
