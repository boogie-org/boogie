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

    public readonly Bpl.Variable ArrayContentsVariable;
    public readonly Bpl.Variable ArrayLengthVariable;

    public readonly Stack<Bpl.Expr> TranslatedExpressions;

    protected readonly Sink sink;

    protected readonly StatementTraverser StmtTraverser;

    private Bpl.Expr assignmentSourceExpr;
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
      ArrayContentsVariable = sink.ArrayContentsVariable;
      ArrayLengthVariable = sink.ArrayLengthVariable;
      this.StmtTraverser = statementTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();

      assignmentSourceExpr = null;
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
      if (field != null)
      {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field.ResolvedField)));
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
      throw new NotImplementedException();
    }

    public override void Visit(IArrayIndexer arrayIndexer)
    {
      this.Visit(arrayIndexer.IndexedObject);
      Bpl.Expr arrayExpr = TranslatedExpressions.Pop();
      this.Visit(arrayIndexer.Indices);
      List<Bpl.Expr> indexExprs = new List<Bpl.Expr>();
      for (int i = 0; i < arrayIndexer.Indices.Count(); i++)
      {
        indexExprs.Insert(0, TranslatedExpressions.Pop());
      }
      if (assignmentSourceExpr != null)
      {
        Bpl.Expr currSelectExpr = new Bpl.IdentifierExpr(arrayIndexer.Token(), ArrayContentsVariable);
        Bpl.Expr currIndexExpr = arrayExpr;
        List<Bpl.Expr> selectExprs = new List<Bpl.Expr>();
        foreach (Bpl.Expr e in indexExprs)
        {
          currSelectExpr = Bpl.Expr.Select(currSelectExpr, currIndexExpr);
          selectExprs.Add(currSelectExpr);
          currIndexExpr = e;
        }
        Contract.Assert(selectExprs.Count == indexExprs.Count);
        Bpl.Expr currentStoreExpr = assignmentSourceExpr;
        for (int i = selectExprs.Count - 1; i >= 0; i--)
        {
          currentStoreExpr = Bpl.Expr.Store(selectExprs[i], indexExprs[i], currentStoreExpr);
        }
        TranslatedExpressions.Push(Bpl.Expr.Store(new Bpl.IdentifierExpr(arrayIndexer.Token(), ArrayContentsVariable), arrayExpr, currentStoreExpr));
      }
      else
      {
        Bpl.Expr currSelectExpr = Bpl.Expr.Select(new Bpl.IdentifierExpr(arrayIndexer.Token(), ArrayContentsVariable), arrayExpr);
        foreach (Bpl.Expr e in indexExprs)
        {
          currSelectExpr = Bpl.Expr.Select(currSelectExpr, e);
        }
        TranslatedExpressions.Push(currSelectExpr);
      }
    }

    public override void Visit(ITargetExpression targetExpression)
    {
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
        //ProcessFieldVariable(field, targetExpression.Instance, false);
        //return;
        var f = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(field.ResolvedField));
        TranslatedExpressions.Push(f);
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
      //if (boundExpression.Instance != null)
      //{
      //    this.Visit(boundExpression.Instance);
      //    // TODO: (mschaef) look where it's bound and do something
      //}
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
          Bpl.Expr instanceExpr = TranslatedExpressions.Pop();
          TranslatedExpressions.Push(this.sink.Heap.ReadHeap(instanceExpr, f, field.ContainingType.ResolvedType.IsStruct));
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

    /// <summary>
    /// 
    /// </summary>
    /// <param name="addressOf"></param>
    /// <remarks>Since we are doing Copy-In,Copy-Out for function calls we can ignore it.
    /// But will this work for the general case?</remarks>
    public override void Visit(IAddressOf addressOf)
    {
      Visit(addressOf.Expression);
    }
    #endregion

    #region Translate Constant Access

    public override void Visit(ICompileTimeConstant constant)
    {
      if (constant.Value == null)
      {
        var bplType = sink.CciTypeToBoogie(constant.Type);
        if (bplType == Bpl.Type.Int) {
          var lit = Bpl.Expr.Literal(0);
          lit.Type = Bpl.Type.Int;
          TranslatedExpressions.Push(lit);
        } else if (bplType == Bpl.Type.Bool) {
          TranslatedExpressions.Push(Bpl.Expr.False);
        } else {
          throw new NotImplementedException("Don't know how to translate type");
        }
     }
      else if (constant.Value is bool)
      {
        TranslatedExpressions.Push(((bool)constant.Value) ? Bpl.Expr.True : Bpl.Expr.False);
      }
      else if (constant.Value is string)
      {
        var c = this.sink.FindOrCreateConstant((string)(constant.Value));
        TranslatedExpressions.Push(Bpl.Expr.Ident(c));

        //throw new NotImplementedException("Strings are not translated");
      } else {
        // TODO: (mschaef) hack
        var lit = Bpl.Expr.Literal((int)constant.Value);
        lit.Type = Bpl.Type.Int;
        TranslatedExpressions.Push(lit);
      }
    }

    public override void Visit(IDefaultValue defaultValue) {
      var bplType = sink.CciTypeToBoogie(defaultValue.Type);
      if (bplType == Bpl.Type.Int) {
        var lit = Bpl.Expr.Literal(0);
        lit.Type = Bpl.Type.Int;
        TranslatedExpressions.Push(lit);
      } else if (bplType == Bpl.Type.Bool) {
        var lit = Bpl.Expr.False;
        lit.Type = Bpl.Type.Bool;
        TranslatedExpressions.Push(lit);
      } else {
        throw new NotImplementedException("Don't know how to translate type");
      }
    }

    #endregion

    #region Translate Method Calls
    /// <summary>
    /// 
    /// </summary>
    /// <param name="methodCall"></param>
    /// <remarks>Stub, This one really needs comments!</remarks>
    public override void Visit(IMethodCall methodCall)
    {
      var resolvedMethod = methodCall.MethodToCall.ResolvedMethod;
        
      #region Translate In Parameters

      var inexpr = new List<Bpl.Expr>();

      #region Create the 'this' argument for the function call
      Bpl.Expr thisExpr = null;
      if (!methodCall.IsStaticCall)
      {
        this.Visit(methodCall.ThisArgument);
        thisExpr = this.TranslatedExpressions.Pop();
        inexpr.Add(thisExpr);
      }
      #endregion

      Dictionary<IParameterDefinition, Bpl.Expr> p2eMap = new Dictionary<IParameterDefinition, Bpl.Expr>();
      IEnumerator<IParameterDefinition> penum = resolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in methodCall.Arguments)
      {
        if (penum.Current == null)
        {
          throw new TranslationException("More Arguments than Parameters in functioncall");
        }
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();

        p2eMap.Add(penum.Current, e);
        if (!penum.Current.IsOut)
        {
          inexpr.Add(e);
        }

        penum.MoveNext();
      }
      #endregion

      Bpl.IToken cloc = methodCall.Token();

      // meeting a constructor is always something special
      if (false && resolvedMethod.IsConstructor)
      {
        // Todo: do something with the constructor call
      }
      else
      {
        // Todo: if there is no stmttraverser we are visiting a contract and should use a boogie function instead of procedure!

        #region Translate Out vars
        Bpl.IdentifierExpr outMap = null;
        var outvars = new List<Bpl.IdentifierExpr>();
        if (!methodCall.IsStaticCall && methodCall.MethodToCall.ContainingType.ResolvedType.IsStruct) {
          outMap = new Bpl.IdentifierExpr(methodCall.Token(), sink.CreateFreshLocal(new Bpl.MapType(Bpl.Token.NoToken, new Bpl.TypeVariableSeq(), new Bpl.TypeSeq(sink.Heap.FieldType), sink.Heap.BoxType)));
          outvars.Add(outMap);
        }
        foreach (KeyValuePair<IParameterDefinition, Bpl.Expr> kvp in p2eMap)
        {
          if (kvp.Key.IsOut || kvp.Key.IsByReference)
          {
            Bpl.IdentifierExpr iexp = kvp.Value as Bpl.IdentifierExpr;
            if (iexp == null)
            {
              throw new TranslationException("Trying to pass complex expression as out in functioncall");
            }
            outvars.Add(iexp);
          }
        }
        #endregion

        if (methodCall.Type.ResolvedType.TypeCode != PrimitiveTypeCode.Void)
        {
          Bpl.Variable v = this.sink.CreateFreshLocal(methodCall.Type.ResolvedType);
          outvars.Add(new Bpl.IdentifierExpr(cloc, v));
          TranslatedExpressions.Push(new Bpl.IdentifierExpr(cloc, v));
        }
        var proc = this.sink.FindOrCreateProcedure(resolvedMethod);
        string methodname = proc.Name;

        Bpl.QKeyValue attrib = null;
        foreach (var a in resolvedMethod.Attributes)
        {
          if (TypeHelper.GetTypeName(a.Type).EndsWith("AsyncAttribute"))
          {
            attrib = new Bpl.QKeyValue(cloc, "async", new List<object>(), null);
          }
        }

        Bpl.CallCmd call;
        bool isEventAdd = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("add_");
        bool isEventRemove = resolvedMethod.IsSpecialName && resolvedMethod.Name.Value.StartsWith("remove_");
        if (isEventAdd || isEventRemove)
        {
          IEventDefinition ed = null;
          foreach (var e in resolvedMethod.ContainingTypeDefinition.Events)
          {
            if (e.Adder != null && e.Adder.ResolvedMethod == resolvedMethod)
            {
              ed = e;
              break;
            }
          }
          Bpl.Variable eventVar = null;
          Bpl.Variable local = null;
          foreach (var f in resolvedMethod.ContainingTypeDefinition.Fields) {
            if (ed.Name == f.Name) {
              eventVar = this.sink.FindOrCreateFieldVariable(f);
              local = this.sink.CreateFreshLocal(f.Type);
              break;
            }
          }

          if (methodCall.IsStaticCall)
          {
            this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(local), Bpl.Expr.Ident(eventVar)));
            inexpr.Insert(0, Bpl.Expr.Ident(local));
          }
          else 
          {
            this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(local), this.sink.Heap.ReadHeap(thisExpr, Bpl.Expr.Ident(eventVar), resolvedMethod.ContainingType.ResolvedType.IsStruct)));
            inexpr[0] = Bpl.Expr.Ident(local);
          }

          System.Diagnostics.Debug.Assert(outvars.Count == 0);
          outvars.Add(Bpl.Expr.Ident(local));
          string methodName = isEventAdd ? this.sink.DelegateAddName : this.sink.DelegateRemoveName;
          call = new Bpl.CallCmd(methodCall.Token(), methodName, inexpr, outvars);
          this.StmtTraverser.StmtBuilder.Add(call);
          if (methodCall.IsStaticCall)
          {
            this.StmtTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(eventVar), Bpl.Expr.Ident(local)));
          }
          else
          {
            this.StmtTraverser.StmtBuilder.Add(this.sink.Heap.WriteHeap(methodCall.Token(), thisExpr, Bpl.Expr.Ident(eventVar), Bpl.Expr.Ident(local), resolvedMethod.ContainingType.ResolvedType.IsStruct));
          }
        }
        else
        {
          if (attrib != null)
            call = new Bpl.CallCmd(cloc, methodname, inexpr, outvars, attrib);
          else
            call = new Bpl.CallCmd(cloc, methodname, inexpr, outvars);
          this.StmtTraverser.StmtBuilder.Add(call);
        }
        if (outMap != null) {
          Debug.Assert(thisExpr != null);
          Bpl.AssignLhs lhs = new Bpl.SimpleAssignLhs(Bpl.Token.NoToken, (Bpl.IdentifierExpr) thisExpr);
          List<Bpl.AssignLhs> lhss = new List<Bpl.AssignLhs>();
          lhss.Add(lhs);
          List<Bpl.Expr> rhss = new List<Bpl.Expr>();
          rhss.Add(outMap);
          Bpl.AssignCmd acmd = new Bpl.AssignCmd(methodCall.Token(), lhss, rhss);
          this.StmtTraverser.StmtBuilder.Add(acmd);
        }
      }

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

      #region Transform Right Hand Side ...
      this.Visit(assignment.Source);
      Bpl.Expr sourceexp = this.TranslatedExpressions.Pop();
      #endregion

      var target = assignment.Target;

      this.assignmentSourceExpr = sourceexp;
      this.Visit(target);
      this.assignmentSourceExpr = null;

      if (target.Definition is IArrayIndexer) {
        StmtTraverser.StmtBuilder.Add(
          Bpl.Cmd.SimpleAssign(assignment.Token(),
                            new Bpl.IdentifierExpr(assignment.Token(), ArrayContentsVariable),
                            TranslatedExpressions.Pop()));
        return;
      }

      var fieldReference = target.Definition as IFieldReference;
      if (fieldReference != null) {
        Bpl.Expr o = null;
        if (target.Instance != null)
          o = TranslatedExpressions.Pop();
        Bpl.IdentifierExpr f = this.TranslatedExpressions.Pop() as Bpl.IdentifierExpr;
        Bpl.Cmd c;
        if (target.Instance == null) {
          c = Bpl.Cmd.SimpleAssign(assignment.Token(), f, sourceexp);
        }
        else {
          c = this.sink.Heap.WriteHeap(assignment.Token(), o, f, sourceexp, fieldReference.ContainingType.ResolvedType.IsStruct);
        }
        // In the struct case, I am making the assumption that we only see a single field dereference on the left side of the assignment
        //var c = (fieldReference.ContainingType.ResolvedType.IsStruct) ? this.sink.WriteStruct((Bpl.IdentifierExpr)o, f, sourceexp) : this.sink.Heap.WriteHeap(assignment.Token(), o, f, sourceexp);
        StmtTraverser.StmtBuilder.Add(c);
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

    #endregion

    #region Translate Object Creation

    /// <summary>
    /// For "new A(...)" generate "{ A a = Alloc(); A..ctor(a); return a; }" where
    /// "a" is a fresh local.
    /// </summary>
    public override void Visit(ICreateObjectInstance createObjectInstance)
    {
      TranslateObjectCreation(createObjectInstance.MethodToCall, createObjectInstance.Arguments, createObjectInstance.Type, createObjectInstance);
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

    private void TranslateObjectCreation(IMethodReference ctor, IEnumerable<IExpression> arguments, ITypeReference ctorType, IExpression creationAST)
    {
      Bpl.IToken token = creationAST.Token();

      var a = this.sink.CreateFreshLocal(creationAST.Type);

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(token, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));

      // Second, generate the call to the appropriate ctor
      var proc = this.sink.FindOrCreateProcedure(ctor.ResolvedMethod);
      Bpl.ExprSeq inexpr = new Bpl.ExprSeq();
      inexpr.Add(Bpl.Expr.Ident(a));
      IEnumerator<IParameterDefinition> penum = ctor.ResolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in arguments)
      {
        if (penum.Current == null)
        {
          throw new TranslationException("More Arguments than Parameters in functioncall");
        }
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();

        if (!penum.Current.IsOut)
        {
          inexpr.Add(e);
        }

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
                                                         new Bpl.ExprSeq(Bpl.Expr.Literal(0), Bpl.Expr.Ident(constant), instanceExpr), 
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
    public override void Visit(IConditional conditional)
    {
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
      base.Visit(conditional);
      var ifFalse = TranslatedExpressions.Pop();
      var ifTrue = TranslatedExpressions.Pop();
      var c = TranslatedExpressions.Pop();
      var tok = conditional.Token();
      TranslatedExpressions.Push(
        new Bpl.NAryExpr(tok, new Bpl.IfThenElse(tok), new Bpl.ExprSeq(c, ifTrue, ifFalse))
          ); 

    }

    #endregion

    #region Translate Unary Operators

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
        Bpl.Expr.Select(new Bpl.IdentifierExpr(vectorLength.Token(), this.sink.ArrayLengthVariable), new Bpl.Expr[] { e })
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
  }

}
