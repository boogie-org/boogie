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


namespace BytecodeTranslator {
  public class ExpressionTraverser : BaseCodeTraverser {

    // warning! this has to be replaced by a HeapVariable from outside
    public readonly Bpl.Variable HeapVariable;        

    public readonly Stack<Bpl.Expr> TranslatedExpressions;

    protected readonly Sink sink;

    protected readonly StatementTraverser StmtTraverser;

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
    public ExpressionTraverser(Sink sink, StatementTraverser/*?*/ statementTraverser) {
      this.sink = sink;
      HeapVariable = sink.HeapVariable;
      this.StmtTraverser = statementTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();
    }

    #endregion

    #region Translate Variable Access

    /// <summary>
    /// 
    /// </summary>
    /// <param name="addressableExpression"></param>
    /// <remarks>still a stub</remarks>
    public override void Visit(IAddressableExpression addressableExpression) {
      ILocalDefinition/*?*/ local = addressableExpression.Definition as ILocalDefinition;
      if (local != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      IParameterDefinition/*?*/ param = addressableExpression.Definition as IParameterDefinition;
      if (param != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param)));
        return;
      }
      IFieldReference/*?*/ field = addressableExpression.Definition as IFieldReference;
      if (field != null) {
        //TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.ClassTraverser.FindOrCreateFieldVariable(field.ResolvedField)));
        throw new NotImplementedException();
      }
      IArrayIndexer/*?*/ arrayIndexer = addressableExpression.Definition as IArrayIndexer;
      if (arrayIndexer != null) {
        this.Visit(arrayIndexer);
        return;
      }
      IAddressDereference/*?*/ addressDereference = addressableExpression.Definition as IAddressDereference;
      if (addressDereference != null) {
        this.Visit(addressDereference);
        return;
      }
      IMethodReference/*?*/ method = addressableExpression.Definition as IMethodReference;
      if (method != null) {
        Console.WriteLine(MemberHelper.GetMethodSignature(method, NameFormattingOptions.Signature));
        //TODO
        throw new NotImplementedException();
      }
      Debug.Assert(addressableExpression.Definition is IThisReference);
    }

    public override void Visit(IAddressDereference addressDereference) {
      IBoundExpression be = addressDereference.Address as IBoundExpression;
      if (be != null) {
        IParameterDefinition pd = be.Definition as IParameterDefinition;
        if (pd != null) {
          var pv = this.sink.FindParameterVariable(pd);
          TranslatedExpressions.Push(Bpl.Expr.Ident(pv));
          return;
        }
      }
      this.Visit(addressDereference.Address);
      throw new NotImplementedException();
    }

    public override void Visit(IArrayIndexer arrayIndexer) {
      this.Visit(arrayIndexer.IndexedObject);
      this.Visit(arrayIndexer.Indices);
      //TODO            
    }

    public override void Visit(ITargetExpression targetExpression) {
      #region ArrayIndexer
      IArrayIndexer/*?*/ indexer = targetExpression.Definition as IArrayIndexer;
      if (indexer != null) {
        this.Visit(indexer);
        return;
      }
      #endregion

      #region AddressDereference
      IAddressDereference/*?*/ deref = targetExpression.Definition as IAddressDereference;
      if (deref != null) {
        IAddressOf/*?*/ addressOf = deref.Address as IAddressOf;
        if (addressOf != null) {
          this.Visit(addressOf.Expression);
          return;
        }
        IConversion/*?*/ conversion = deref.Address as IConversion;
        if (conversion != null) {
          IBoundExpression be = conversion.ValueToConvert as IBoundExpression;
          if (be != null) {
            IParameterDefinition pd = be.Definition as IParameterDefinition;
            if (pd != null) {
              var pv = this.sink.FindParameterVariable(pd);
              TranslatedExpressions.Push(Bpl.Expr.Ident(pv));
              return;
            }
          }
        }
        if (targetExpression.Instance != null) {
          // TODO
          throw new NotImplementedException("targetExpr->AddrDeRef->InstanceNull");
        } else if (deref.Address.Type is IPointerTypeReference)
          throw new NotImplementedException("targetExpr->AddrDeRef->Pointertype");
        this.Visit(deref.Address);
        return;
      }
      #endregion

      #region LocalDefinition
      ILocalDefinition/*?*/ local = targetExpression.Definition as ILocalDefinition;
      if (local != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      #endregion

      #region ParameterDefenition
      IParameterDefinition param = targetExpression.Definition as IParameterDefinition;
      if (param != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param)));
        return;
      }
      #endregion

      #region FieldReference
      IFieldReference field = targetExpression.Definition as IFieldReference;
      if (field != null) {
        ProcessFieldVariable(field, targetExpression.Instance, false);
        return;
      }
      #endregion

      #region PropertyDefiniton
      IPropertyDefinition prop = targetExpression.Definition as IPropertyDefinition;
      if (prop != null) {
        throw new NotImplementedException("targetExpr->Property");
      }
      #endregion
    }
    
    public override void Visit(IThisReference thisReference) {
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(thisReference.Token(),
        this.sink.ThisVariable));
    }

    public override void Visit(IBoundExpression boundExpression) {
      //if (boundExpression.Instance != null)
      //{
      //    this.Visit(boundExpression.Instance);
      //    // TODO: (mschaef) look where it's bound and do something
      //}
      #region LocalDefinition
      ILocalDefinition local = boundExpression.Definition as ILocalDefinition;
      if (local != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindOrCreateLocalVariable(local)));
        return;
      }
      #endregion

      #region ParameterDefiniton
      IParameterDefinition param = boundExpression.Definition as IParameterDefinition;
      if (param != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.sink.FindParameterVariable(param)));
        return;
      }
      #endregion

      #region FieldDefinition
      IFieldReference field = boundExpression.Definition as IFieldReference;
      if (field != null) {
        ProcessFieldVariable(field, boundExpression.Instance, true);
        return;
      }
      #endregion

      #region PropertyDefinition
      IPropertyDefinition prop = boundExpression.Definition as IPropertyDefinition;
      if (prop != null) {
        throw new NotImplementedException("Properties are not implemented");
      }
      #endregion

      #region ArrayIndexer
      IArrayIndexer/*?*/ indexer = boundExpression.Definition as IArrayIndexer;
      if (indexer != null) {
        this.Visit(indexer);
        return;
      }
      #endregion

      #region AddressDereference
      IAddressDereference/*?*/ deref = boundExpression.Definition as IAddressDereference;
      if (deref != null) {
        IAddressOf/*?*/ addressOf = deref.Address as IAddressOf;
        if (addressOf != null) {
          this.Visit(addressOf.Expression);
          return;
        }
        if (boundExpression.Instance != null) {
          // TODO
          this.Visit(boundExpression.Instance);
          Console.Write("->");
        } else if (deref.Address.Type is IPointerTypeReference)
          Console.Write("*");
        this.Visit(deref.Address);
        return;
      } else {
        if (boundExpression.Instance != null) {
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
    public override void Visit(IAddressOf addressOf) {
      Visit(addressOf.Expression);      
    }
    #endregion

    #region Variable Access Helpers
    private void ProcessFieldVariable(IFieldReference field, IExpression/*?*/ instance, bool buildSelectExpr) {

      TranslatedExpressions.Push( Bpl.Expr.Ident( 
        this.sink.FindOrCreateFieldVariable(field.ResolvedField) ) );

      if (instance != null) {
        this.Visit(instance);
      } else {
        //TranslatedExpressions.Push(
        //  TranslationHelper.FunctionCall(
        //    this.sink.StaticFieldFunction,
        //    TranslationHelper.CciTypeToBoogie(field.Type),
        //    new List<Bpl.Expr>{ new Bpl.IdentifierExpr(Bpl.Token.NoToken, new Bpl.Constant(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, TypeHelper.GetTypeName(field.Type), ))) }
        //    ));
      }

      // if the field access is not a targetexpression we build a select expression
      // otherwise the assignment visitor will build a mapassignment later on
      if (instance != null && buildSelectExpr) {
        List<Bpl.Expr> elist = new List<Bpl.Expr>();

        elist.Add(TranslatedExpressions.Pop());
        elist.Add(TranslatedExpressions.Pop());
        TranslatedExpressions.Push(Bpl.Expr.Select(new Bpl.IdentifierExpr(field.Token(), HeapVariable), elist));
      }
    }


    #endregion

    #region Translate Constant Access

    public override void Visit(ICompileTimeConstant constant) {
      if (constant.Value == null) {
        // TODO: (mschaef) hack
        TranslatedExpressions.Push(Bpl.Expr.False);
      } else if (constant.Value is bool) {
        TranslatedExpressions.Push(((bool)constant.Value) ? Bpl.Expr.True : Bpl.Expr.False);
      } else if (constant.Value is string) {
        throw new NotImplementedException("Strings are not translated");        
      } else {
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
    public override void Visit(IMethodCall methodCall) {

      #region Translate In Parameters


      Bpl.ExprSeq inexpr = new Bpl.ExprSeq();

      #region Create the 'this' argument for the function call
      this.Visit(methodCall.ThisArgument);
      inexpr.Add(this.TranslatedExpressions.Pop());
      #endregion

      Dictionary<IParameterDefinition, Bpl.Expr> p2eMap = new Dictionary<IParameterDefinition, Bpl.Expr>();
      IEnumerator<IParameterDefinition> penum = methodCall.MethodToCall.ResolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in methodCall.Arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More Arguments than Parameters in functioncall");
        }
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();

        p2eMap.Add(penum.Current, e);
        if (!penum.Current.IsOut) {
          inexpr.Add(e);
        }
        
        penum.MoveNext();
      }
      #endregion

      Bpl.IToken cloc = methodCall.Token();

      // meeting a constructor is always something special
      if (methodCall.MethodToCall.ResolvedMethod.IsConstructor) {
        // Todo: do something with the constructor call
      } else {
        // Todo: if there is no stmttraverser we are visiting a contract and should use a boogie function instead of procedure!

        #region Translate Out vars
        Bpl.IdentifierExprSeq outvars = new Bpl.IdentifierExprSeq();

        foreach (KeyValuePair<IParameterDefinition, Bpl.Expr> kvp in p2eMap) {
          if (kvp.Key.IsOut || kvp.Key.IsByReference) {
            Bpl.IdentifierExpr iexp = kvp.Value as Bpl.IdentifierExpr;
            if (iexp == null) {
              throw new TranslationException("Trying to pass complex expression as out in functioncall");
            }
            outvars.Add(iexp);
          }
        }
        #endregion

        if (methodCall.Type.ResolvedType.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Variable v = this.sink.CreateFreshLocal(methodCall.Type.ResolvedType);
          outvars.Add(new Bpl.IdentifierExpr(cloc, v));
          TranslatedExpressions.Push(new Bpl.IdentifierExpr(cloc, v));
        }
        string methodname = TranslationHelper.CreateUniqueMethodName(methodCall.MethodToCall.ResolvedMethod);

        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, methodname, inexpr, outvars));

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

      #region Transform Right Hand Side ...
      this.Visit(assignment.Source);
      Bpl.Expr sourceexp = this.TranslatedExpressions.Pop();
      #endregion

      this.Visit(assignment.Target);

      if (this.TranslatedExpressions.Count == 1) { // I think this is defintely the wrong test. there might be other stuff on the stack if the assignment is not a top-level statement!
        Bpl.Expr targetexp = this.TranslatedExpressions.Pop();
        Bpl.IdentifierExpr idexp = targetexp as Bpl.IdentifierExpr;
        if (idexp != null) {
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(assignment.Token(),
            idexp, sourceexp));
          return;
        } else {
          throw new TranslationException("Trying to create a SimpleAssign with complex/illegal lefthand side");
        }
      } else {
        // Assume it is always 2? What should we check?
        Bpl.ExprSeq args = new Bpl.ExprSeq();
        args.Add(this.TranslatedExpressions.Pop());
        args.Add(this.TranslatedExpressions.Pop());
        StmtTraverser.StmtBuilder.Add(
          Bpl.Cmd.MapAssign(assignment.Token(),
          new Bpl.IdentifierExpr(assignment.Token(), this.HeapVariable), args, sourceexp));
      }

    }

    #endregion

    #region Translate Object Creation

    /// <summary>
    /// For "new A(...)" generate "{ A a = Alloc(); A..ctor(a); return a; }" where
    /// "a" is a fresh local.
    /// </summary>
    public override void Visit(ICreateObjectInstance createObjectInstance) {

      Bpl.IToken cloc = createObjectInstance.Token();

      var a = this.sink.CreateFreshLocal(createObjectInstance.Type);

      // First generate an Alloc() call
      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, this.sink.AllocationMethodName, new Bpl.ExprSeq(), new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(a))));

      // Second, generate the call to the appropriate ctor
      Bpl.ExprSeq inexpr = new Bpl.ExprSeq();
      Dictionary<IParameterDefinition, Bpl.Expr> p2eMap = new Dictionary<IParameterDefinition, Bpl.Expr>();
      IEnumerator<IParameterDefinition> penum = createObjectInstance.MethodToCall.ResolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in createObjectInstance.Arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More Arguments than Parameters in functioncall");
        }
        this.Visit(exp);
        Bpl.Expr e = this.TranslatedExpressions.Pop();

        p2eMap.Add(penum.Current, e);
        if (!penum.Current.IsOut) {
          inexpr.Add(e);
        }

        penum.MoveNext();
      }

      Bpl.IdentifierExprSeq outvars = new Bpl.IdentifierExprSeq();
      string methodname = TranslationHelper.CreateUniqueMethodName(createObjectInstance.MethodToCall.ResolvedMethod);

      this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, methodname, inexpr, outvars));

      TranslatedExpressions.Push(Bpl.Expr.Ident(a));

    }
    #endregion
    
    #region Translate Binary Operators

    public override void Visit(IAddition addition) {
      base.Visit(addition);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Add, lexp, rexp));
    }

    public override void Visit(IDivision division) {
      base.Visit(division);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Div, lexp, rexp));
    }

    public override void Visit(ISubtraction subtraction) {
      base.Visit(subtraction);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, lexp, rexp));
    }

    public override void Visit(IMultiplication multiplication) {
      base.Visit(multiplication);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Mul, lexp, rexp));
    }

    public override void Visit(IModulus modulus) {
      base.Visit(modulus);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Mod, lexp, rexp));
    }

    public override void Visit(IGreaterThan greaterThan) {
      base.Visit(greaterThan);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Gt, lexp, rexp));
    }

    public override void Visit(IGreaterThanOrEqual greaterEqual) {
      base.Visit(greaterEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Ge, lexp, rexp));
    }

    public override void Visit(ILessThan lessThan) {
      base.Visit(lessThan);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Lt, lexp, rexp));
    }

    public override void Visit(ILessThanOrEqual lessEqual) {
      base.Visit(lessEqual);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Le, lexp, rexp));
    }

    public override void Visit(IEquality equal) {
      base.Visit(equal);
      Bpl.Expr rexp = TranslatedExpressions.Pop();
      Bpl.Expr lexp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, lexp, rexp));
    }

    public override void Visit(INotEquality nonEqual) {
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
      CompileTimeConstant ctc = conditional.ResultIfFalse as CompileTimeConstant;
      if (ctc != null && ctc.Type == BCT.Host.PlatformType.SystemInt32) {
        int v = (int)ctc.Value;
        if (v == 0) {
          Visit(conditional.Condition);
          Bpl.Expr x = TranslatedExpressions.Pop();
          Visit(conditional.ResultIfTrue);
          Bpl.Expr y = TranslatedExpressions.Pop();
          TranslatedExpressions.Push(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.And, x, y));
          return;
        }
      }
      ctc = conditional.ResultIfTrue as CompileTimeConstant;
      if (ctc != null && ctc.Type == BCT.Host.PlatformType.SystemInt32) {
        int v = (int)ctc.Value;
        if (v == 1) {
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

    public override void Visit(IUnaryNegation unaryNegation) {
      base.Visit(unaryNegation);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      Bpl.Expr zero = Bpl.Expr.Literal(0); // TODO: (mschaef) will this work in any case?
      TranslatedExpressions.Push( Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Sub, zero, exp) );
    }

    public override void Visit(ILogicalNot logicalNot) {
      base.Visit(logicalNot);
      Bpl.Expr exp = TranslatedExpressions.Pop();
      TranslatedExpressions.Push(Bpl.Expr.Unary(
          logicalNot.Token(),
          Bpl.UnaryOperator.Opcode.Not, exp));

    }
    #endregion

    #region CodeContract Expressions
    public override void Visit(IOldValue oldValue) {
      base.Visit(oldValue);
      TranslatedExpressions.Push(new Bpl.OldExpr(oldValue.Token(),
        TranslatedExpressions.Pop()));
    }
    
    public override void Visit(IReturnValue returnValue) {
      if (this.sink.RetVariable == null) {
        throw new TranslationException(String.Format("Don't know what to do with return value {0}", returnValue.ToString()));
      }
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(returnValue.Token(),
        this.sink.RetVariable));

    }
    #endregion
  }

}
