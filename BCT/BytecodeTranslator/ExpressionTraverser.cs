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
  public class ExpressionTraverser : BaseCodeTraverser
  {
    public readonly Stack<Bpl.Expr> TranslatedExpressions;

    protected readonly Sink sink;

    protected readonly StatementTraverser StmtTraverser;

    private bool contractContext;

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
    public override void Visit(IAddressableExpression addressableExpression)
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
          this.Visit(instance);
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
        this.Visit(arrayIndexer);
        return;
      }
      IAddressDereference/*?*/ addressDereference = addressableExpression.Definition as IAddressDereference;
      if (addressDereference != null)
      {
        this.Visit(addressDereference);
        return;
      }
      IBlockExpression block = addressableExpression.Definition as IBlockExpression;
      if (block != null) {
        this.Visit(block);
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

    public override void Visit(IAddressDereference addressDereference)
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
      this.Visit(addressDereference.Address);
      return;
    }

    public override void Visit(IArrayIndexer arrayIndexer) {

      if (!IsAtomicInstance(arrayIndexer.IndexedObject)) {
        // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
        var se = ExpressionSimplifier.Simplify(this.sink, arrayIndexer);
        this.Visit(se);
        return;
      }

      this.Visit(arrayIndexer.IndexedObject);
      Bpl.Expr arrayExpr = TranslatedExpressions.Pop();
      this.Visit(arrayIndexer.Indices);
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

    public override void Visit(ITargetExpression targetExpression)
    {
      Contract.Assume(false, "The expression containing this as a subexpression should never allow a call to this routine.");
    }

    public override void Visit(IThisReference thisReference)
    {
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(thisReference.Token(),
        this.sink.ThisVariable));
    }

    public override void Visit(IBoundExpression boundExpression)
    {

      if (boundExpression.Instance != null && !IsAtomicInstance(boundExpression.Instance)) {
        // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
        var se = ExpressionSimplifier.Simplify(this.sink, boundExpression);
        this.Visit(se);
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
          this.Visit(instance);
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
        Visit(indexer);
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
          this.Visit(addressOf.Expression);
          return;
        }
        if (boundExpression.Instance != null)
        {
          // TODO
          this.Visit(boundExpression.Instance);
          Console.Write("->");
        }
        else if (deref.Address.Type is IPointerTypeReference)
          Console.Write("*");
        this.Visit(deref.Address);
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

    public override void Visit(IPopValue popValue) {
      var locExpr = this.StmtTraverser.operandStack.Pop();
      this.Visit(locExpr);
      this.TranslatedExpressions.Push(this.TranslatedExpressions.Pop());
    }

    /// <summary>
    /// If the expression is a struct, then this returns a "boxed" struct.
    /// Otherwise it just translates the expression and skips the address-of
    /// operation.
    /// </summary>
    public override void Visit(IAddressOf addressOf)
    {
      Visit(addressOf.Expression);
    }
    #endregion

    #region Translate Constant Access

    public override void Visit(ICompileTimeConstant constant) {
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
        case PrimitiveTypeCode.Char: // chars are represented as ints
        case PrimitiveTypeCode.Int8:
        case PrimitiveTypeCode.Int16:
          var lit = Bpl.Expr.Literal((short)constant.Value);
          lit.Type = Bpl.Type.Int;
          TranslatedExpressions.Push(lit);
          break;
        case PrimitiveTypeCode.Int32:
        case PrimitiveTypeCode.Int64:
          var lit2 = Bpl.Expr.Literal((int)constant.Value);
          lit2.Type = Bpl.Type.Int;
          TranslatedExpressions.Push(lit2);
          break;
        case PrimitiveTypeCode.UInt16:
        case PrimitiveTypeCode.UInt32:
        case PrimitiveTypeCode.UInt64:
        case PrimitiveTypeCode.UInt8:
          lit = Bpl.Expr.Literal((int)(uint)constant.Value);
          lit.Type = Bpl.Type.Int;
          TranslatedExpressions.Push(lit);
          break;
        case PrimitiveTypeCode.Float32: {
            var c = this.sink.FindOrCreateConstant((float)(constant.Value));
            TranslatedExpressions.Push(Bpl.Expr.Ident(c));
            return;
          }
        case PrimitiveTypeCode.Float64: {
            var c = this.sink.FindOrCreateConstant((double)(constant.Value));
            TranslatedExpressions.Push(Bpl.Expr.Ident(c));
            return;
          }
        case PrimitiveTypeCode.NotPrimitive:
          if (constant.Type.IsEnum) {
            lit = Bpl.Expr.Literal((int)constant.Value);
            lit.Type = Bpl.Type.Int;
            TranslatedExpressions.Push(lit);
            return;
          }
          throw new NotImplementedException(String.Format("Can't translate compile-time constant of type '{0}'",
            TypeHelper.GetTypeName(constant.Type)));
        default:
          throw new NotImplementedException();
      }
      return;
    }

    public override void Visit(IDefaultValue defaultValue) {

      var typ = defaultValue.Type;

      #region Struct
      if (TranslationHelper.IsStruct(typ)) {
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
              this.sink.FindOrCreateType(typ)
              )
              )
            );

        this.TranslatedExpressions.Push(locExpr);
        return;
      }
      #endregion

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

    #endregion

    #region Translate Method Calls
    /// <summary>
    /// 
    /// </summary>
    /// <param name="methodCall"></param>
    /// <remarks>Stub, This one really needs comments!</remarks>
    public override void Visit(IMethodCall methodCall) {
      var resolvedMethod = Sink.Unspecialize(methodCall.MethodToCall).ResolvedMethod;
      if (resolvedMethod == Dummy.Method) {
        throw new TranslationException(
          ExceptionType.UnresolvedMethod,
          MemberHelper.GetMethodSignature(methodCall.MethodToCall, NameFormattingOptions.None));
      }

      Bpl.IToken methodCallToken = methodCall.Token();
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

        if (resolvedMethod.IsConstructor && resolvedMethod.ContainingTypeDefinition.IsStruct) {
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
        if (PhoneCodeHelper.PhonePlugin != null) {
          if (PhoneCodeHelper.isNavigationCall(methodCall, sink.host)) {
            // the block is a potential page changer
            List<Bpl.AssignLhs> lhs = new List<Bpl.AssignLhs>();
            List<Bpl.Expr> rhs = new List<Bpl.Expr>();
            Bpl.Expr value = new Bpl.LiteralExpr(Bpl.Token.NoToken, false);
            rhs.Add(value);
            Bpl.SimpleAssignLhs assignee=
              new Bpl.SimpleAssignLhs(Bpl.Token.NoToken,
                                      new Bpl.IdentifierExpr(Bpl.Token.NoToken,
                                                             sink.FindOrCreateGlobalVariable(PhoneCodeHelper.BOOGIE_CONTINUE_ON_PAGE_VARIABLE, Bpl.Type.Bool)));
            lhs.Add(assignee);
            Bpl.AssignCmd assignCmd = new Bpl.AssignCmd(Bpl.Token.NoToken, lhs, rhs);
            this.StmtTraverser.StmtBuilder.Add(assignCmd);
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
            this.sink.FindOrCreateType(methodCall.MethodToCall.ResolvedMethod.ContainingTypeDefinition)
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
        this.Visit(thisArg);

        var e = this.TranslatedExpressions.Pop();
        var identifierExpr = e as Bpl.IdentifierExpr;
        if (identifierExpr == null) {
          var newLocal = Bpl.Expr.Ident(this.sink.CreateFreshLocal(thisArg.Type));
          var cmd = Bpl.Cmd.SimpleAssign(token, newLocal, e);
          this.StmtTraverser.StmtBuilder.Add(cmd);
          e = newLocal;
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
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();
        if (penum.Current.Type is IGenericTypeParameter || penum.Current.Type is IGenericMethodParameter)
          inexpr.Add(sink.Heap.Box(token, this.sink.CciTypeToBoogie(exp.Type), e));
        else
          inexpr.Add(e);
        if (penum.Current.IsByReference) {
          Bpl.IdentifierExpr unboxed = e as Bpl.IdentifierExpr;
          if (unboxed == null) {
            throw new TranslationException("Trying to pass a complex expression for an out or ref parameter");
          }
          if (penum.Current.Type is IGenericTypeParameter || penum.Current.Type is IGenericMethodParameter) {
            Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(sink.CreateFreshLocal(this.sink.Heap.BoxType));
            toBoxed[unboxed] = boxed;
            outvars.Add(boxed);
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
          inexpr.Add(sink.FindOrCreateType(typeReference));
        }
      }
      IGenericMethodInstanceReference methodInstanceReference = methodToCall as IGenericMethodInstanceReference;
      if (methodInstanceReference != null) {
        foreach (ITypeReference typeReference in methodInstanceReference.GenericArguments) {
          inexpr.Add(sink.FindOrCreateType(typeReference));
        }
      }

      var procInfo = this.sink.FindOrCreateProcedure(resolvedMethod);
      var translateAsFunctionCall = procInfo.Decl is Bpl.Function;
      if (!translateAsFunctionCall) {
        if (resolvedMethod.Type.ResolvedType.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Variable v = this.sink.CreateFreshLocal(methodToCall.ResolvedMethod.Type.ResolvedType);
          Bpl.IdentifierExpr unboxed = new Bpl.IdentifierExpr(token, v);
          if (resolvedMethod.Type is IGenericTypeParameter || resolvedMethod.Type is IGenericMethodParameter) {
            Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(this.sink.CreateFreshLocal(this.sink.Heap.BoxType));
            toBoxed[unboxed] = boxed;
            outvars.Add(boxed);
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
    public override void Visit(IAssignment assignment) {
      Contract.Assert(TranslatedExpressions.Count == 0);
      var tok = assignment.Token();

      ICompileTimeConstant constant= assignment.Source as ICompileTimeConstant;
      if (PhoneCodeHelper.PhonePlugin != null && constant != null && constant.Value.Equals(PhoneCodeHelper.BOOGIE_DO_HAVOC_CURRENTURI)) {
        TranslateHavocCurrentURI();
      } else {
        TranslateAssignment(tok, assignment.Target.Definition, assignment.Target.Instance, assignment.Source);
      }
    }

    /// <summary>
    /// Patch, to account for URIs that cannot be tracked because of current dataflow restrictions
    /// </summary>
    private void TranslateHavocCurrentURI() {
      Bpl.CallCmd havocCall = new Bpl.CallCmd(Bpl.Token.NoToken, PhoneCodeHelper.BOOGIE_DO_HAVOC_CURRENTURI, new List<Bpl.Expr>(), new List<Bpl.IdentifierExpr>());
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
        this.Visit(source);
        var e = this.TranslatedExpressions.Pop();
        var bplLocal = Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local));
        if (structCopy) {
          cmd = new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr>{ e, bplLocal, }, new List<Bpl.IdentifierExpr>());
        } else {
          cmd = Bpl.Cmd.SimpleAssign(tok, bplLocal, e);
        }
        StmtTraverser.StmtBuilder.Add(cmd);
        return;
      }

      var/*?*/ parameter = container as IParameterDefinition;
      if (parameter != null) {
        Contract.Assume(instance == null);
        this.Visit(source);
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
        this.Visit(source);
        var e = this.TranslatedExpressions.Pop();
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field));
        if (instance == null) {
          // static fields are not kept in the heap
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, f, e));
        }
        else {
          this.Visit(instance);
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
        this.Visit(instance);
        var x = this.TranslatedExpressions.Pop();
        this.Visit(arrayIndexer.Indices);
        var indices_prime = this.TranslatedExpressions.Pop();
        this.Visit(source);
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
          this.Visit(source);
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
    public override void Visit(ICreateObjectInstance createObjectInstance)
    {
      var ctor = createObjectInstance.MethodToCall;
      var resolvedMethod = Sink.Unspecialize(ctor).ResolvedMethod;
      Bpl.IToken token = createObjectInstance.Token();

      var a = this.sink.CreateFreshLocal(createObjectInstance.Type);

      if (createObjectInstance.Type.TypeCode == PrimitiveTypeCode.IntPtr ||
          createObjectInstance.Type.TypeCode == PrimitiveTypeCode.UIntPtr) {
        List<Bpl.Expr> args = new List<Bpl.Expr>();
        foreach (IExpression e in createObjectInstance.Arguments) {
          this.Visit(e);
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
              this.sink.FindOrCreateType(createObjectInstance.Type)
              )
              )
            );
      }
      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }

    public override void Visit(ICreateArray createArrayInstance)
    {
      Bpl.IToken cloc = createArrayInstance.Token();
      var a = this.sink.CreateFreshLocal(createArrayInstance.Type);

      Debug.Assert(createArrayInstance.Rank > 0); 
      Bpl.Expr lengthExpr = Bpl.Expr.Literal(1);
      foreach (IExpression expr in createArrayInstance.Sizes) {
        this.Visit(expr);
        lengthExpr = Bpl.Expr.Mul(lengthExpr, TranslatedExpressions.Pop());
      }
      
      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
      Bpl.Expr assumeExpr = Bpl.Expr.Eq(new Bpl.NAryExpr(cloc, new Bpl.FunctionCall(this.sink.Heap.ArrayLengthFunction), new Bpl.ExprSeq(Bpl.Expr.Ident(a))), lengthExpr);
      this.StmtTraverser.StmtBuilder.Add(new Bpl.AssumeCmd(cloc, assumeExpr));
      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }
    
    public override void Visit(ICreateDelegateInstance createDelegateInstance)
    {
      if (createDelegateInstance.Instance == null) {
        TranslatedExpressions.Push(Bpl.Expr.Literal(0));
      }
      else {
        this.Visit(createDelegateInstance.Instance);
      }

      TranslateDelegateCreation(createDelegateInstance.MethodToCallViaDelegate, createDelegateInstance.Type, createDelegateInstance);
    }

    private void TranslateDelegateCreation(IMethodReference methodToCall, ITypeReference type, IExpression creationAST)
    {
      Bpl.IToken cloc = creationAST.Token();
      var a = this.sink.CreateFreshLocal(creationAST.Type);

      sink.AddDelegate(type.ResolvedType, methodToCall.ResolvedMethod);
      Bpl.Constant constant = sink.FindOrAddDelegateMethodConstant(methodToCall.ResolvedMethod);
      Bpl.Expr methodExpr = Bpl.Expr.Ident(constant);
      Bpl.Expr instanceExpr = TranslatedExpressions.Pop();

      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, this.sink.DelegateAddHelperName,
                                                         new Bpl.ExprSeq(Bpl.Expr.Ident(this.sink.Heap.NullRef), Bpl.Expr.Ident(constant), instanceExpr), 
                                                         new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));
      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }
    
    #endregion

    #region Translate Binary Operators

    public override void Visit(IAddition addition)
    {
      base.Visit(addition);
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

    public override void Visit(IBitwiseAnd bitwiseAnd) {
      base.Visit(bitwiseAnd);
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

    public override void Visit(IBitwiseOr bitwiseOr) {
      base.Visit(bitwiseOr);
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

    public override void Visit(IDivision division)
    {
      base.Visit(division);
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

    public override void Visit(IExclusiveOr exclusiveOr) {
      base.Visit(exclusiveOr);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      var e = new Bpl.NAryExpr(
        exclusiveOr.Token(),
        new Bpl.FunctionCall(this.sink.Heap.BitwiseExclusiveOr),
        new Bpl.ExprSeq(lexp, rexp)
        );
      TranslatedExpressions.Push(e);
    }

    public override void Visit(ISubtraction subtraction)
    {
      base.Visit(subtraction);
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

    public override void Visit(IMultiplication multiplication)
    {
      base.Visit(multiplication);
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

    public override void Visit(IModulus modulus)
    {
      base.Visit(modulus);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Mod, lexp, rexp));
    }

    public override void Visit(IGreaterThan greaterThan)
    {
      base.Visit(greaterThan);
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

    public override void Visit(IGreaterThanOrEqual greaterEqual)
    {
      base.Visit(greaterEqual);
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

    public override void Visit(ILessThan lessThan)
    {
      base.Visit(lessThan);
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

    public override void Visit(ILessThanOrEqual lessEqual)
    {
      base.Visit(lessEqual);
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

    public override void Visit(IEquality equal)
    {
      base.Visit(equal);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, lexp, rexp));
    }

    public override void Visit(INotEquality nonEqual)
    {
      base.Visit(nonEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, lexp, rexp));
    }

    /// <summary>
    /// There aren't any logical-and expressions or logical-or expressions in CCI.
    /// Instead they are encoded as "x ? y : 0" for "x && y" and "x ? 1 : y"
    /// for "x || y".
    /// TODO:
    /// If it isn't either of these short forms then emit the proper expression!
    /// </summary>
    public override void Visit(IConditional conditional) {
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

      StatementTraverser thenStmtTraverser = this.StmtTraverser.factory.MakeStatementTraverser(this.sink, this.StmtTraverser.PdbReader, this.contractContext);
      StatementTraverser elseStmtTraverser = this.StmtTraverser.factory.MakeStatementTraverser(this.sink, this.StmtTraverser.PdbReader, this.contractContext);
      ExpressionTraverser thenExprTraverser = this.StmtTraverser.factory.MakeExpressionTraverser(this.sink, thenStmtTraverser, this.contractContext);
      ExpressionTraverser elseExprTraverser = this.StmtTraverser.factory.MakeExpressionTraverser(this.sink, elseStmtTraverser, this.contractContext);
      thenExprTraverser.Visit(conditional.ResultIfTrue);
      elseExprTraverser.Visit(conditional.ResultIfFalse);

      this.Visit(conditional.Condition);
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

    public override void Visit(ICastIfPossible castIfPossible) {
      base.Visit(castIfPossible.ValueToCast);
      var exp = TranslatedExpressions.Pop();
      var e = this.sink.FindOrCreateType(castIfPossible.TargetType);
      var callAs = new Bpl.NAryExpr(
        castIfPossible.Token(),
        new Bpl.FunctionCall(this.sink.Heap.AsFunction),
        new Bpl.ExprSeq(exp, e)
        );
      TranslatedExpressions.Push(callAs);
      return;
    }
    public override void Visit(ICheckIfInstance checkIfInstance) {
      var e = this.sink.FindOrCreateType(checkIfInstance.TypeToCheck);
      //var callTypeOf = new Bpl.NAryExpr(
      //  checkIfInstance.Token(),
      //  new Bpl.FunctionCall(this.sink.Heap.TypeOfFunction),
      //  new Bpl.ExprSeq(new Bpl.IdentifierExpr(checkIfInstance.Token(), v))
      //  );
      base.Visit(checkIfInstance.Operand);
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

    public override void Visit(IConversion conversion) {
      var tok = conversion.ValueToConvert.Token();
      Visit(conversion.ValueToConvert);
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

    public override void Visit(IOnesComplement onesComplement) {
      base.Visit(onesComplement);
      var exp = TranslatedExpressions.Pop();
      var e = new Bpl.NAryExpr(
        onesComplement.Token(),
        new Bpl.FunctionCall(this.sink.Heap.BitwiseNegation),
        new Bpl.ExprSeq(exp)
        );
      TranslatedExpressions.Push(e);
    }

    public override void Visit(IUnaryNegation unaryNegation)
    {
      base.Visit(unaryNegation);
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

    public override void Visit(ILogicalNot logicalNot)
    {
      base.Visit(logicalNot.Operand);
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

    public override void Visit(ITypeOf typeOf) {
      var e = this.sink.FindOrCreateType(typeOf.TypeToGet);
      var callTypeOf = new Bpl.NAryExpr(
        typeOf.Token(),
        new Bpl.FunctionCall(this.sink.Heap.TypeOfFunction),
        new Bpl.ExprSeq(e)
        );
      TranslatedExpressions.Push(callTypeOf);
    }

    public override void Visit(IVectorLength vectorLength) {
      base.Visit(vectorLength.Vector);
      var e = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(new Bpl.NAryExpr(vectorLength.Token(), new Bpl.FunctionCall(this.sink.Heap.ArrayLengthFunction), new Bpl.ExprSeq(e)));
    }

    #endregion

    #region CodeContract Expressions
    public override void Visit(IOldValue oldValue)
    {
      base.Visit(oldValue);
      TranslatedExpressions.Push(new Bpl.OldExpr(oldValue.Token(),
        TranslatedExpressions.Pop()));
    }

    public override void Visit(IReturnValue returnValue)
    {
      if (this.sink.ReturnVariable == null)
      {
        throw new TranslationException(String.Format("Don't know what to do with return value {0}", returnValue.ToString()));
      }
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(returnValue.Token(),
        this.sink.ReturnVariable));

    }
    #endregion

    public override void Visit(IBlockExpression blockExpression) {
      this.StmtTraverser.Visit(blockExpression.BlockStatement);
      this.Visit(blockExpression.Expression);
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
