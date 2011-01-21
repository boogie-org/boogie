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

    #region Constructors

    /// <summary>
    /// Use this constructor for translating expressions that do *not* occur
    /// within the context of the statements in a method body.
    /// </summary>
    public ExpressionTraverser(Sink sink)
      : this(sink, null)
    { }

    /// <summary>
    /// Use this constructor for translating expressions that do occur within
    /// the context of the statements in a method body.
    /// </summary>
    public ExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser)
    {
      this.sink = sink;
      ArrayContentsVariable = sink.ArrayContentsVariable;
      ArrayLengthVariable = sink.ArrayLengthVariable;
      this.StmtTraverser = statementTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();

      assignmentSourceExpr = null;
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
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param)));
        return;
      }
      IFieldReference/*?*/ field = addressableExpression.Definition as IFieldReference;
      if (field != null)
      {
        //TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.ClassTraverser.FindOrCreateFieldVariable(field.ResolvedField)));
        throw new NotImplementedException();
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
      Debug.Assert(addressableExpression.Definition is IThisReference);
    }

    public override void Visit(IAddressDereference addressDereference)
    {
      IBoundExpression be = addressDereference.Address as IBoundExpression;
      if (be != null)
      {
        IParameterDefinition pd = be.Definition as IParameterDefinition;
        if (pd != null)
        {
          var pv = this.sink.FindParameterVariable(pd);
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
        Debug.Assert(selectExprs.Count == indexExprs.Count);
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
              var pv = this.sink.FindParameterVariable(pd);
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
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param)));
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
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param)));
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
          TranslatedExpressions.Push(this.sink.Heap.ReadHeap(instanceExpr, f));
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
        var bplType = TranslationHelper.CciTypeToBoogie(constant.Type);
        if (bplType == Bpl.Type.Int) {
          TranslatedExpressions.Push(Bpl.Expr.Literal(0));
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
        throw new NotImplementedException("Strings are not translated");
      }
      else
      {
        // TODO: (mschaef) hack
        TranslatedExpressions.Push(Bpl.Expr.Literal((int)constant.Value));
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
      if (!methodCall.IsStaticCall)
      {
        this.Visit(methodCall.ThisArgument);
        inexpr.Add(this.TranslatedExpressions.Pop());
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
      if (resolvedMethod.IsConstructor)
      {
        // Todo: do something with the constructor call
      }
      else
      {
        // Todo: if there is no stmttraverser we are visiting a contract and should use a boogie function instead of procedure!

        #region Translate Out vars
        var outvars = new List<Bpl.IdentifierExpr>();

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
        string methodname = TranslationHelper.CreateUniqueMethodName(resolvedMethod);


        Bpl.QKeyValue attrib = null;
        foreach (var a in resolvedMethod.Attributes)
        {
          if (TypeHelper.GetTypeName(a.Type).EndsWith("AsyncAttribute"))
          {
            attrib = new Bpl.QKeyValue(cloc, "async", new List<object>(), null);
          }
        }
        Bpl.CallCmd call;
        if (attrib != null)
          call = new Bpl.CallCmd(cloc, methodname, inexpr, outvars, attrib);
        else
          call = new Bpl.CallCmd(cloc, methodname, inexpr, outvars);
        this.StmtTraverser.StmtBuilder.Add(call);

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
      Debug.Assert(TranslatedExpressions.Count == 0);

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
        var c = this.sink.Heap.WriteHeap(assignment.Token(), o, f, sourceexp);
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
      // TranslateCreation(createDelegateInstance.MethodToCallViaDelegate, createDelegateInstance.Arguments, createDelegateInstance.Type, createDelegateInstance);
      base.Visit(createDelegateInstance);
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
      Bpl.IToken cloc = creationAST.Token();

      var a = this.sink.CreateFreshLocal(creationAST.Type);

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));

      // Second, generate the call to the appropriate ctor
      Bpl.ExprSeq inexpr = new Bpl.ExprSeq();
      Dictionary<IParameterDefinition, Bpl.Expr> p2eMap = new Dictionary<IParameterDefinition, Bpl.Expr>();
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

        p2eMap.Add(penum.Current, e);
        if (!penum.Current.IsOut)
        {
          inexpr.Add(e);
        }

        penum.MoveNext();
      }

      Bpl.IdentifierExprSeq outvars = new Bpl.IdentifierExprSeq();
      string methodname = TranslationHelper.CreateUniqueMethodName(ctor.ResolvedMethod);

      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, methodname, inexpr, outvars));

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
        if (v == 0)
        {
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfTrue);
          Bpl.Expr y = TranslatedExpressions.Pop();
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, x, y));
          return;
        }
      }
      ctc = conditional.ResultIfTrue as CompileTimeConstant;
      if (ctc != null && ctc.Type == BCT.Host.PlatformType.SystemInt32)
      {
        int v = (int)ctc.Value;
        if (v == 1)
        {
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfFalse);
          Bpl.Expr y = TranslatedExpressions.Pop();
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Or, x, y));
          return;
        }
      }
      base.Visit(conditional);
    }

    #endregion

    #region Translate Unary Operators

    public override void Visit(IUnaryNegation unaryNegation)
    {
      base.Visit(unaryNegation);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      Bpl.Expr zero = Bpl.Expr.Literal(0); // TODO: (mschaef) will this work in any case?
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, zero, exp));
    }

    public override void Visit(ILogicalNot logicalNot)
    {
      base.Visit(logicalNot);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Unary(
          logicalNot.Token(),
          Bpl.UnaryOperator.Opcode.Not, exp));

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
