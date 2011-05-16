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
        }
        else {
          this.Visit(instance);
          if (this.collectStructFields) {
            this.structFields.Add(field.ResolvedField);
          }
          else {
            Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
            Bpl.IdentifierExpr temp = Bpl.Expr.Ident(this.sink.CreateFreshLocal(field.ResolvedField.Type));
            this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(temp, this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, temp.Type)));
            TranslatedExpressions.Push(temp);
          }
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

#if EXPERIMENTAL
      if (!IsAtomicInstance(arrayIndexer.IndexedObject)) {
        // Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
        var se = ExpressionSimplifier.Simplify(this.sink, arrayIndexer);
        this.Visit(se);
        return;
      }
#endif

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

#if EXPERIMENTAL
      this.TranslatedExpressions.Push(arrayExpr);
#else
      Bpl.IdentifierExpr temp = Bpl.Expr.Ident(this.sink.CreateFreshLocal(arrayIndexer.Type));
      Bpl.Expr selectExpr = sink.Heap.ReadHeap(arrayExpr, indexExpr, AccessType.Array, temp.Type);
      this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(temp, selectExpr));
      TranslatedExpressions.Push(temp);

      this.arrayExpr = arrayExpr;
      this.indexExpr = indexExpr;
#endif
    }

    public override void Visit(ITargetExpression targetExpression)
    {
#if EXPERIMENTAL
      Contract.Assume(false, "The expression containing this as a subexpression should never allow a call to this routine.");

      if (targetExpression.Instance != null && !IsAtomicInstance(targetExpression.Instance)) {
        //// Simplify the BE so that all nested dereferences and method calls are broken up into separate assignments to locals.
        var se = ExpressionSimplifier.Simplify(this.sink, targetExpression);
        this.Visit(se);
        return;
      }
#endif

      #region ArrayIndexer
      IArrayIndexer/*?*/ indexer = targetExpression.Definition as IArrayIndexer;
      if (indexer != null)
      {
        Visit(indexer);
        return;
      }
      #endregion

      #region AddressDereference
      IAddressDereference/*?*/ deref = targetExpression.Definition as IAddressDereference;
      if (deref != null)
      {
        IAddressOf/*?*/ addressOf = deref.Address as IAddressOf;
        if (addressOf != null)
        {
          this.Visit(addressOf.Expression);
          return;
        }
        IConversion/*?*/ conversion = deref.Address as IConversion;
        if (conversion != null)
        {
          IBoundExpression be = conversion.ValueToConvert as IBoundExpression;
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
        }
        if (targetExpression.Instance != null)
        {
          // TODO
          throw new NotImplementedException("targetExpr->AddrDeRef->InstanceNull");
        }
        else if (deref.Address.Type is IPointerTypeReference)
          throw new NotImplementedException("targetExpr->AddrDeRef->Pointertype");
        this.Visit(deref.Address);
        return;
      }
      #endregion

      #region Local
      ILocalDefinition/*?*/ local = targetExpression.Definition as ILocalDefinition;
      if (local != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      #endregion

      #region Parameter
      IParameterDefinition param = targetExpression.Definition as IParameterDefinition;
      if (param != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param, this.contractContext)));
        return;
      }
      #endregion

      #region Field
      IFieldReference field = targetExpression.Definition as IFieldReference;
      if (field != null)
      {
        var instance = targetExpression.Instance;
        if (instance != null) {
          this.Visit(instance);
        }
        return;
      }
      #endregion

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
        }
        else {
          this.Visit(instance);
          if (this.collectStructFields) {
            this.structFields.Add(field.ResolvedField);
          }
          else {
            Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
            var bplType = this.sink.CciTypeToBoogie(field.Type);
            var e = this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, bplType);
            this.TranslatedExpressions.Push(e);
          }
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
      var be = expression as IBoundExpression;
      if (be == null) return false;
      return be.Instance == null;
    }

    public override void Visit(IPopValue popValue) {
      var locExpr = this.StmtTraverser.operandStack.Pop();
      this.TranslatedExpressions.Push(locExpr);
    }

    /// <summary>
    /// If the expression is a struct, then this returns a "boxed" struct.
    /// Otherwise it just translates the expression and skips the address-of
    /// operation.
    /// </summary>
    public override void Visit(IAddressOf addressOf)
    {
      Visit(addressOf.Expression);
      //if (addressOf.Expression.Type.IsValueType)
      //{
      //  var e = this.TranslatedExpressions.Pop();
      //  var callBox = new Bpl.NAryExpr(
      //    addressOf.Token(),
      //  new Bpl.FunctionCall(this.sink.Heap.Struct2Ref),
      //  new Bpl.ExprSeq(e)
      //  );
      //  TranslatedExpressions.Push(callBox);
      //}
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
          TranslatedExpressions.Push(((bool)constant.Value) ? Bpl.Expr.True : Bpl.Expr.False);
          break;
        case PrimitiveTypeCode.Char: // chars are represented as ints
        case PrimitiveTypeCode.Int16:
        case PrimitiveTypeCode.Int32:
        case PrimitiveTypeCode.Int64:
        case PrimitiveTypeCode.Int8:
          var lit = Bpl.Expr.Literal((int)constant.Value);
          lit.Type = Bpl.Type.Int;
          TranslatedExpressions.Push(lit);
          break;
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          var c = this.sink.FindOrCreateConstant((double)(constant.Value));
          TranslatedExpressions.Push(Bpl.Expr.Ident(c));
          return;
        default:
          throw new NotImplementedException();
      }
      return;
    }

    public override void Visit(IDefaultValue defaultValue) {
      TranslatedExpressions.Push(this.sink.DefaultValue(defaultValue.Type));
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

      #region Translate In and Out Parameters
      var inexpr = new List<Bpl.Expr>();
      var outvars = new List<Bpl.IdentifierExpr>();

      #region Create the 'this' argument for the function call
      Bpl.IdentifierExpr thisExpr = null;
      List<Bpl.Variable> locals = null;
      List<IFieldDefinition> args = null;
      Bpl.Expr arrayExpr = null;
      Bpl.Expr indexExpr = null;
      if (!methodCall.IsStaticCall) {
        this.collectStructFields = true;
        this.structFields = new List<IFieldDefinition>();
        this.arrayExpr = null;
        this.indexExpr = null;
        this.Visit(methodCall.ThisArgument);
        this.collectStructFields = false;
        args = this.structFields;
        arrayExpr = this.arrayExpr;
        indexExpr = this.indexExpr;

        var e = this.TranslatedExpressions.Pop();
        inexpr.Add(e);
        if (e is Bpl.NAryExpr) {
          e = ((Bpl.NAryExpr)e).Args[0];
        }
        thisExpr = e as Bpl.IdentifierExpr;
        locals = new List<Bpl.Variable>();
        Bpl.Variable x = thisExpr.Decl;
        locals.Add(x);
        for (int i = 0; i < args.Count; i++) {
          Bpl.IdentifierExpr g = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(args[i]));
          Bpl.Variable y = this.sink.CreateFreshLocal(args[i].Type);
          StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(y), this.sink.Heap.ReadHeap(Bpl.Expr.Ident(x), g, args[i].ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, y.TypedIdent.Type)));
          x = y;
          locals.Add(y);
        }
      }
      if (!methodCall.IsStaticCall && methodCall.MethodToCall.ContainingType.ResolvedType.IsStruct) {
        outvars.Add(thisExpr);
      }
      #endregion

      Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed = new Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr>();
      Dictionary<IParameterDefinition, Bpl.IdentifierExpr> p2eMap = new Dictionary<IParameterDefinition, Bpl.IdentifierExpr>();
      IEnumerator<IParameterDefinition> penum = resolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in methodCall.Arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More arguments than parameters in method call");
        }
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();
        if (penum.Current.Type is IGenericTypeParameter)
          inexpr.Add(sink.Heap.Box(methodCall.Token(), this.sink.CciTypeToBoogie(exp.Type), e));
        else
          inexpr.Add(e);
        if (penum.Current.IsByReference) {
          Bpl.IdentifierExpr unboxed = e as Bpl.IdentifierExpr;
          if (unboxed == null) {
            throw new TranslationException("Trying to pass a complex expression for an out or ref parameter");
          }
          if (penum.Current.Type is IGenericTypeParameter) {
            Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(sink.CreateFreshLocal(this.sink.Heap.BoxType));
            toBoxed[unboxed] = boxed;
            outvars.Add(boxed);
          }
          else {
            outvars.Add(unboxed);
          }
        }
        penum.MoveNext();
      }
      #endregion

      Bpl.IToken cloc = methodCall.Token();
      if (resolvedMethod.Type.ResolvedType.TypeCode != PrimitiveTypeCode.Void) {
        Bpl.Variable v = this.sink.CreateFreshLocal(methodCall.Type.ResolvedType);
        Bpl.IdentifierExpr unboxed = new Bpl.IdentifierExpr(cloc, v);
        if (resolvedMethod.Type is IGenericTypeParameter) {
          Bpl.IdentifierExpr boxed = Bpl.Expr.Ident(this.sink.CreateFreshLocal(this.sink.Heap.BoxType));
          toBoxed[unboxed] = boxed;
          outvars.Add(boxed);
        }
        else {
          outvars.Add(unboxed);
        }
        TranslatedExpressions.Push(unboxed);
      }
      var proc = this.sink.FindOrCreateProcedure(resolvedMethod);
      string methodname = proc.Name;

      Bpl.QKeyValue attrib = null;
      foreach (var a in resolvedMethod.Attributes) {
        if (TypeHelper.GetTypeName(a.Type).EndsWith("AsyncAttribute")) {
          attrib = new Bpl.QKeyValue(cloc, "async", new List<object>(), null);
        }
      }

      Bpl.CallCmd call;
      bool isEventAdd = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("add_");
      bool isEventRemove = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("remove_");
      if (isEventAdd || isEventRemove) {
        var mName = resolvedMethod.Name.Value;
        var eventName = mName.Substring(mName.IndexOf('_') + 1);
        var eventDef = TypeHelper.GetEvent(resolvedMethod.ContainingTypeDefinition, this.sink.host.NameTable.GetNameFor(eventName));
        Contract.Assert(eventDef != Dummy.Event);
        Bpl.Variable eventVar = this.sink.FindOrCreateEventVariable(eventDef);
        Bpl.Variable local = this.sink.CreateFreshLocal(eventDef.Type);

        if (methodCall.IsStaticCall) {
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(local), Bpl.Expr.Ident(eventVar)));
          inexpr.Insert(0, Bpl.Expr.Ident(local));
        }
        else {
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(local), this.sink.Heap.ReadHeap(thisExpr, Bpl.Expr.Ident(eventVar), resolvedMethod.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, local.TypedIdent.Type)));
          inexpr[0] = Bpl.Expr.Ident(local);
        }

        System.Diagnostics.Debug.Assert(outvars.Count == 0);
        outvars.Add(Bpl.Expr.Ident(local));
        string methodName = isEventAdd ? this.sink.DelegateAddName : this.sink.DelegateRemoveName;
        call = new Bpl.CallCmd(methodCall.Token(), methodName, inexpr, outvars);
        this.StmtTraverser.StmtBuilder.Add(call);
        if (methodCall.IsStaticCall) {
          this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(eventVar), Bpl.Expr.Ident(local)));
        }
        else {
          this.StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(methodCall.Token(), thisExpr, Bpl.Expr.Ident(eventVar), Bpl.Expr.Ident(local), resolvedMethod.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, local.TypedIdent.Type));
        }
      }
      else {
        if (attrib != null)
          call = new Bpl.CallCmd(cloc, methodname, inexpr, outvars, attrib);
        else
          call = new Bpl.CallCmd(cloc, methodname, inexpr, outvars);
        this.StmtTraverser.StmtBuilder.Add(call);
      }

      foreach (KeyValuePair<Bpl.IdentifierExpr, Bpl.IdentifierExpr> kv in toBoxed) {
        this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(kv.Key, this.sink.Heap.Unbox(Bpl.Token.NoToken, kv.Key.Type, kv.Value)));
      }

      if (!methodCall.IsStaticCall) {
        Debug.Assert(args != null && locals != null);
        int count = args.Count;
        Bpl.Variable x = locals[count];
        count--;
        while (0 <= count) {
          IFieldDefinition currField = args[count];
          Bpl.IdentifierExpr g = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(currField));
          Bpl.Variable y = locals[count];
          StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(methodCall.Token(), Bpl.Expr.Ident(y), g, Bpl.Expr.Ident(x), currField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, x.TypedIdent.Type));
          x = y;
          count--;
        }
        if (indexExpr != null) {
          Debug.Assert(arrayExpr != null);
          StmtTraverser.StmtBuilder.Add(sink.Heap.WriteHeap(Bpl.Token.NoToken, arrayExpr, indexExpr, Bpl.Expr.Ident(x), AccessType.Array, x.TypedIdent.Type));
        }
      }
    }

    #endregion

    #region Translate Assignments
    private List<IFieldDefinition> structFields = null;
    private bool collectStructFields = false;
    private Bpl.Expr arrayExpr = null;
    private Bpl.Expr indexExpr = null;

#if EXPERIMENTAL
    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub </remarks>
    /// <param name="assignment"></param>
    public override void Visit(IAssignment assignment) {
      Contract.Assert(TranslatedExpressions.Count == 0);

      var tok = assignment.Token();

      object container = assignment.Target.Definition;

      var/*?*/ local = container as ILocalDefinition;
      if (local != null) {
        Contract.Assume(assignment.Target.Instance == null);
        this.Visit(assignment.Source);
        var e = this.TranslatedExpressions.Pop();
        var bplLocal = Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local));
        StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, bplLocal, e));
        return;
      }

      var/*?*/ parameter = container as IParameterDefinition;
      if (parameter != null) {
        Contract.Assume(assignment.Target.Instance == null);
        this.Visit(assignment.Source);
        var e = this.TranslatedExpressions.Pop();
        var bplParam = Bpl.Expr.Ident(this.sink.FindParameterVariable(parameter, this.contractContext));
        StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, bplParam, e));
        return;
      }

      var/*?*/ field = container as IFieldReference;
      if (field != null) {
        this.Visit(assignment.Source);
        var e = this.TranslatedExpressions.Pop();
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field));
        if (assignment.Target.Instance == null) {
          // static fields are not kept in the heap
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, f, e));
        } else {
          if (field.ContainingType.ResolvedType.IsStruct) {
            //var s_prime = this.sink.CreateFreshLocal(this.sink.Heap.StructType);
            //var s_prime_expr = Bpl.Expr.Ident(s_prime);
            //var boogieType = sink.CciTypeToBoogie(field.Type);
            //StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(tok, s_prime_expr, f, e,
            //  field.ResolvedField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap,
            //  boogieType));
            UpdateStruct(tok, assignment.Target.Instance, field, e);
          } else {
            this.Visit(assignment.Target.Instance);
            var x = this.TranslatedExpressions.Pop();
            var boogieType = sink.CciTypeToBoogie(field.Type);
            StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(tok, x, f, e,
              field.ResolvedField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap,
              boogieType));
          }
        }
        return;
      }

      var/*?*/ arrayIndexer = container as IArrayIndexer;
      if (arrayIndexer != null) {
        this.Visit(assignment.Target.Instance);
        var x = this.TranslatedExpressions.Pop();
        this.Visit(arrayIndexer.Indices);
        var indices_prime = this.TranslatedExpressions.Pop();
        this.Visit(assignment.Source);
        var e = this.TranslatedExpressions.Pop();
        StmtTraverser.StmtBuilder.Add(sink.Heap.WriteHeap(Bpl.Token.NoToken, x, indices_prime, e, AccessType.Array, sink.CciTypeToBoogie(arrayIndexer.Type)));
        return;
      }

      Contract.Assume(false);
    }

    private void UpdateStruct(Bpl.IToken tok, IExpression iExpression, IFieldReference field, Bpl.Expr e) {
      var addrOf = iExpression as IAddressOf;
      if (addrOf == null) return;
      var addressableExpression = addrOf.Expression as IAddressableExpression;
      if (addressableExpression == null) return;

      var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field));

      if (addressableExpression.Instance == null) {
        var boogieType = sink.CciTypeToBoogie(field.Type);
        this.Visit(addressableExpression);
        var def = this.TranslatedExpressions.Pop();
        StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(tok, def, f, e,
          AccessType.Struct,
          boogieType));
      } else {
        var s_prime = this.sink.CreateFreshLocal(this.sink.Heap.StructType);
        var s_prime_expr = Bpl.Expr.Ident(s_prime);
        var boogieType = sink.CciTypeToBoogie(field.Type);
        StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(tok, s_prime_expr, f, e,
          AccessType.Struct,
          boogieType));
        UpdateStruct(tok, addressableExpression.Instance, addressableExpression.Definition as IFieldReference, s_prime_expr);
      }
    }

#else

    public override void Visit(IAssignment assignment) {
      Contract.Assert(TranslatedExpressions.Count == 0);

      #region Transform Right Hand Side ...
      this.Visit(assignment.Source);
      var sourceexp = this.TranslatedExpressions.Pop();
      #endregion

      // Simplify the LHS so that all nested dereferences and method calls are broken
      // up into separate assignments to locals.
      var blockExpression = ExpressionSimplifier.Simplify(this.sink, assignment.Target) as IBlockExpression;
      foreach (var s in blockExpression.BlockStatement.Statements) {
        this.StmtTraverser.Visit(s);
      }
      var target = blockExpression.Expression as ITargetExpression;

      List<IFieldDefinition> args = null;
      Bpl.Expr arrayExpr = null;
      Bpl.Expr indexExpr = null;
      this.collectStructFields = true;
      this.structFields = new List<IFieldDefinition>();
      this.arrayExpr = null;
      this.indexExpr = null;
      this.Visit(target);
      this.collectStructFields = false;
      args = this.structFields;
      arrayExpr = this.arrayExpr;
      indexExpr = this.indexExpr;

      var fieldReference = target.Definition as IFieldReference;
      if (fieldReference != null) {
        Bpl.IdentifierExpr f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(fieldReference.ResolvedField));
        if (target.Instance == null) {
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(assignment.Token(), f, sourceexp));
        } else {
          Debug.Assert(args != null);
          List<Bpl.Variable> locals = new List<Bpl.Variable>();
          Bpl.IdentifierExpr instanceExpr = TranslatedExpressions.Pop() as Bpl.IdentifierExpr;
          Bpl.Variable x = instanceExpr.Decl;
          locals.Add(x);
          for (int i = 0; i < args.Count; i++) {
            Bpl.IdentifierExpr g = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(args[i]));
            Bpl.Variable y = this.sink.CreateFreshLocal(args[i].Type);
            StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(y), this.sink.Heap.ReadHeap(Bpl.Expr.Ident(x), g, args[i].ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, y.TypedIdent.Type)));
            x = y;
            locals.Add(y);
          }
          var boogieType = sink.CciTypeToBoogie(fieldReference.Type);
          StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(assignment.Token(), Bpl.Expr.Ident(x), f, sourceexp, fieldReference.ResolvedField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, boogieType));

          int count = args.Count;
          x = locals[count];
          count--;
          while (0 <= count) {
            IFieldDefinition currField = args[count];
            Bpl.IdentifierExpr g = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(currField));
            Bpl.Variable y = locals[count];
            StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(assignment.Token(), Bpl.Expr.Ident(y), g, Bpl.Expr.Ident(x), currField.ContainingType.ResolvedType.IsStruct ? AccessType.Struct : AccessType.Heap, x.TypedIdent.Type));
            x = y;
            count--;
          }
          if (indexExpr != null) {
            Debug.Assert(arrayExpr != null);
            StmtTraverser.StmtBuilder.Add(sink.Heap.WriteHeap(Bpl.Token.NoToken, arrayExpr, indexExpr, Bpl.Expr.Ident(x), AccessType.Array, x.TypedIdent.Type));
          }
        }
        return;
      }

      // this is the case when it is just an array indexer expression
      if (indexExpr != null) {
        Debug.Assert(arrayExpr != null);
        StmtTraverser.StmtBuilder.Add(sink.Heap.WriteHeap(Bpl.Token.NoToken, arrayExpr, indexExpr, sourceexp, AccessType.Array, sink.CciTypeToBoogie(target.Type)));
        return;
      }

      var parameterDefinition = target.Definition as IParameterDefinition;
      if (parameterDefinition != null) {
        Bpl.IdentifierExpr idexp = this.TranslatedExpressions.Pop() as Bpl.IdentifierExpr;
        if (idexp != null) {
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(assignment.Token(), idexp, sourceexp));
        } else {
          throw new TranslationException("Trying to create a SimpleAssign with complex/illegal lefthand side");
        }
        return;
      }

      // Not sure what else can appear as a target, but whatever it is, if it didn't translate as an
      // identifier expression, then it is an error because we don't know what to do with it.
      // TODO: Create an exhaustive test of what the target expression can be.
      if (target.Instance != null) {
        throw new TranslationException("Unknown target expression in assignment.");
      }
      {
        Bpl.IdentifierExpr idexp = this.TranslatedExpressions.Pop() as Bpl.IdentifierExpr;
        if (idexp != null) {
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(assignment.Token(), idexp, sourceexp));
        } else {
          throw new TranslationException("Trying to create a SimpleAssign with complex/illegal lefthand side");
        }
      }

      return;
    }

#endif

    #endregion

    #region Translate Object Creation

    /// <summary>
    /// For "new A(...)" generate "{ A a = Alloc(); A..ctor(a); return a; }" where
    /// "a" is a fresh local.
    /// </summary>
    public override void Visit(ICreateObjectInstance createObjectInstance)
    {
      TranslateObjectCreation(createObjectInstance.MethodToCall, createObjectInstance.Arguments, createObjectInstance);
    }

    public override void Visit(ICreateArray createArrayInstance)
    {
      TranslateArrayCreation(createArrayInstance);
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

    private void TranslateArrayCreation(IExpression creationAST)
    {
      Bpl.IToken cloc = creationAST.Token();

      var a = this.sink.CreateFreshLocal(creationAST.Type);

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));

      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
    }

    private void TranslateObjectCreation(IMethodReference ctor, IEnumerable<IExpression> arguments, IExpression creationAST)
    {
      var resolvedMethod = Sink.Unspecialize(ctor).ResolvedMethod;
      Bpl.IToken token = creationAST.Token();
      
      var a = this.sink.CreateFreshLocal(creationAST.Type);

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));

      // Second, generate the call to the appropriate ctor
      var proc = this.sink.FindOrCreateProcedure(resolvedMethod);
      Bpl.ExprSeq inexpr = new Bpl.ExprSeq();
      inexpr.Add(Bpl.Expr.Ident(a));
      IEnumerator<IParameterDefinition> penum = resolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More Arguments than Parameters in functioncall");
        }
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();
        if (penum.Current.Type is IGenericTypeParameter)
          inexpr.Add(sink.Heap.Box(ctor.Token(), this.sink.CciTypeToBoogie(exp.Type), e));
        else
          inexpr.Add(e);
        penum.MoveNext();
      }

      Bpl.IdentifierExprSeq outvars = new Bpl.IdentifierExprSeq();

      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, proc.Name, inexpr, outvars));

      // Generate assumption about the dynamic type of the just allocated object
      this.StmtTraverser.StmtBuilder.Add(
        new Bpl.AssumeCmd(token, 
          Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
          this.sink.Heap.DynamicType(inexpr[0]),
          Bpl.Expr.Ident(this.sink.FindOrCreateType(creationAST.Type))
          )
          )
        );

      TranslatedExpressions.Push(Bpl.Expr.Ident(a));
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
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Add, lexp, rexp));
    }

    public override void Visit(IDivision division)
    {
      base.Visit(division);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Div, lexp, rexp));
    }

    public override void Visit(ISubtraction subtraction)
    {
      base.Visit(subtraction);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, lexp, rexp));
    }

    public override void Visit(IMultiplication multiplication)
    {
      base.Visit(multiplication);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Mul, lexp, rexp));
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
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Gt, lexp, rexp));
    }

    public override void Visit(IGreaterThanOrEqual greaterEqual)
    {
      base.Visit(greaterEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Ge, lexp, rexp));
    }

    public override void Visit(ILessThan lessThan)
    {
      base.Visit(lessThan);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Lt, lexp, rexp));
    }

    public override void Visit(ILessThanOrEqual lessEqual)
    {
      base.Visit(lessEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Le, lexp, rexp));
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
      #region Try and reconstruct And, Or, Not expressions
      CompileTimeConstant ctc = conditional.ResultIfFalse as CompileTimeConstant;
      if (ctc != null && ctc.Type == BCT.Host.PlatformType.SystemInt32)
      {
        int v = (int)ctc.Value;
        if (v == 0) { // x ? y : 0 == x && y
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfTrue);
          Bpl.Expr y = TranslatedExpressions.Pop();
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, x, y));
          return;
        }
        if (v == 1) { // x ? y : 1 == !x || y
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfTrue);
          Bpl.Expr y = TranslatedExpressions.Pop();
          var notX = Bpl.Expr.Unary(conditional.Token(), Bpl.UnaryOperator.Opcode.Not, x);
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Or, notX, y));
          return;
        }
      }
      ctc = conditional.ResultIfTrue as CompileTimeConstant;
      if (ctc != null && ctc.Type == BCT.Host.PlatformType.SystemInt32)
      {
        int v = (int)ctc.Value;
        if (v == 1) { // x ? 1 : y == x || y
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfFalse);
          Bpl.Expr y = TranslatedExpressions.Pop();
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Or, x, y));
          return;
        }
        if (v == 0) { // x ? 0 : y == !x && y
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfFalse);
          Bpl.Expr y = TranslatedExpressions.Pop();
          var notX = Bpl.Expr.Unary(conditional.Token(), Bpl.UnaryOperator.Opcode.Not, x);
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, notX, y));
          return;
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

    }

    #endregion

    #region Translate Unary Operators

    public override void Visit(ICastIfPossible castIfPossible) {
      base.Visit(castIfPossible.ValueToCast);
      var exp = TranslatedExpressions.Pop();
      var v = this.sink.FindOrCreateType(castIfPossible.TargetType);
      var callAs = new Bpl.NAryExpr(
        castIfPossible.Token(),
        new Bpl.FunctionCall(this.sink.Heap.AsFunction),
        new Bpl.ExprSeq(exp, new Bpl.IdentifierExpr(castIfPossible.Token(), v))
        );
      TranslatedExpressions.Push(callAs);
      return;
    }
    public override void Visit(ICheckIfInstance checkIfInstance) {
      var v = this.sink.FindOrCreateType(checkIfInstance.TypeToCheck);
      //var callTypeOf = new Bpl.NAryExpr(
      //  checkIfInstance.Token(),
      //  new Bpl.FunctionCall(this.sink.Heap.TypeOfFunction),
      //  new Bpl.ExprSeq(new Bpl.IdentifierExpr(checkIfInstance.Token(), v))
      //  );
      base.Visit(checkIfInstance.Operand);
      var exp = TranslatedExpressions.Pop();
      var dynTypeOfOperand = this.sink.Heap.DynamicType(exp);
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, dynTypeOfOperand, new Bpl.IdentifierExpr(checkIfInstance.Token(), v)));
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
      var exp = TranslatedExpressions.Pop();
      switch (conversion.TypeAfterConversion.TypeCode) {
        case PrimitiveTypeCode.Int16:
        case PrimitiveTypeCode.Int32:
        case PrimitiveTypeCode.Int64:
        case PrimitiveTypeCode.Int8:
        case PrimitiveTypeCode.UInt16:
        case PrimitiveTypeCode.UInt32:
        case PrimitiveTypeCode.UInt64:
        case PrimitiveTypeCode.UInt8:
          switch (conversion.ValueToConvert.Type.TypeCode) {
            case PrimitiveTypeCode.Boolean:
              TranslatedExpressions.Push(
                new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok), new Bpl.ExprSeq(exp, Bpl.Expr.Literal(1), Bpl.Expr.Literal(0)))
                );
              return;
            case PrimitiveTypeCode.IntPtr:
              // just ignore the conversion. REVIEW: is that the right thing to do?
              this.TranslatedExpressions.Push(exp);
              return;
            case PrimitiveTypeCode.Float32:
            case PrimitiveTypeCode.Float64: {
                var convExpr = new Bpl.NAryExpr(
                conversion.Token(),
                new Bpl.FunctionCall(this.sink.Heap.Real2Int),
                new Bpl.ExprSeq(exp,
                  new Bpl.IdentifierExpr(tok, this.sink.FindOrCreateType(conversion.ValueToConvert.Type)),
                  new Bpl.IdentifierExpr(tok, this.sink.FindOrCreateType(conversion.TypeAfterConversion))
                  )
                );
                TranslatedExpressions.Push(convExpr);
                return;
              }

            default:
              throw new NotImplementedException();
          }
        case PrimitiveTypeCode.Boolean:
          if (TypeHelper.IsPrimitiveInteger(conversion.ValueToConvert.Type)) {
              TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, exp, Bpl.Expr.Literal(0)));
              return;
          } else {
            throw new NotImplementedException();
          }
        case PrimitiveTypeCode.NotPrimitive:
          Bpl.Function func;
          if (conversion.ValueToConvert.Type.TypeCode == PrimitiveTypeCode.Boolean){
              func = this.sink.Heap.Bool2Ref;
          }else if (TypeHelper.IsPrimitiveInteger(conversion.ValueToConvert.Type)) {
              func = this.sink.Heap.Int2Ref;
          } else if (conversion.ValueToConvert.Type.TypeCode == PrimitiveTypeCode.NotPrimitive) {
            // REVIEW: Do we need to check to make sure that conversion.ValueToConvert.Type.IsValueType?
            func = this.sink.Heap.Struct2Ref;
          } else {
            throw new NotImplementedException();
          }
          var boxExpr = new Bpl.NAryExpr(
            conversion.Token(),
            new Bpl.FunctionCall(func),
            new Bpl.ExprSeq(exp)
            );
            TranslatedExpressions.Push(boxExpr);
            return;
        case PrimitiveTypeCode.Float32:
        case PrimitiveTypeCode.Float64:
          if (TypeHelper.IsPrimitiveInteger(conversion.ValueToConvert.Type)) {
            var convExpr = new Bpl.NAryExpr(
              conversion.Token(),
              new Bpl.FunctionCall(this.sink.Heap.Int2Real),
              new Bpl.ExprSeq(exp,
                new Bpl.IdentifierExpr(tok, this.sink.FindOrCreateType(conversion.ValueToConvert.Type)),
                new Bpl.IdentifierExpr(tok, this.sink.FindOrCreateType(conversion.TypeAfterConversion))
                )
                );
            TranslatedExpressions.Push(convExpr);
            return;
          } else {
            throw new NotImplementedException();
          }
        default:
          throw new NotImplementedException();
      }
    }

    public override void Visit(IUnaryNegation unaryNegation)
    {
      base.Visit(unaryNegation);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      Bpl.Expr zero = Bpl.Expr.Literal(0); // TODO: (mschaef) will this work in any case?
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, zero, exp));
    }

    public override void Visit(ILogicalNot logicalNot)
    {
      base.Visit(logicalNot.Operand);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Unary(
          logicalNot.Token(),
          Bpl.UnaryOperator.Opcode.Not, exp));
    }

    public override void Visit(ITypeOf typeOf) {
      var v = this.sink.FindOrCreateType(typeOf.TypeToGet);
      var callTypeOf = new Bpl.NAryExpr(
        typeOf.Token(),
        new Bpl.FunctionCall(this.sink.Heap.TypeOfFunction),
        new Bpl.ExprSeq(new Bpl.IdentifierExpr(typeOf.Token(), v))
        );
      TranslatedExpressions.Push(callTypeOf);
      //TranslatedExpressions.Push(new Bpl.IdentifierExpr(typeOf.Token(), v));
      return;
    }

    public override void Visit(IVectorLength vectorLength) {
      base.Visit(vectorLength.Vector);
      var e = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(
        Bpl.Expr.Select(new Bpl.IdentifierExpr(vectorLength.Token(), this.sink.Heap.ArrayLengthVariable), new Bpl.Expr[] { e })
        );
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
      if (this.sink.RetVariable == null)
      {
        throw new TranslationException(String.Format("Don't know what to do with return value {0}", returnValue.ToString()));
      }
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(returnValue.Token(),
        this.sink.RetVariable));

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

        if (ExpressionTraverser.IsAtomicInstance(boundExpression.Instance)) return boundExpression;

        // boundExpression == BE(inst, def), i.e., inst.def
        // return { loc := e; [assert loc != null;] | BE(BE(null,loc), def) }, i.e., "loc := e; loc.def"
        //   where e is the rewritten inst

        var e = base.Rewrite(boundExpression.Instance);

        var loc = new LocalDefinition() {
          Name = this.host.NameTable.GetNameFor("_loc" + this.sink.LocalCounter.ToString()),
          Type = boundExpression.Type,
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
          Type = arrayIndexer.Type,
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

      //public override IExpression Rewrite(IMethodCall methodCall) {

      //  var e = base.Rewrite(methodCall); // simplify anything deeper in the tree
      //  methodCall = e as IMethodCall;
      //  if (methodCall == null) return e;

      //  var loc = new LocalDefinition() {
      //    Name = this.host.NameTable.GetNameFor("_loc"), // TODO: should make the name unique within the method containing the assignment
      //    Type = methodCall.Type,
      //  };
      //  this.localDeclarations.Add(
      //    new LocalDeclarationStatement() {
      //      InitialValue = methodCall,
      //      LocalVariable = loc,
      //    }
      //    );
      //  return new BoundExpression() {
      //    Definition = loc,
      //    Instance = null,
      //    Type = methodCall.Type,
      //  };
      //}
    }
  }

}
