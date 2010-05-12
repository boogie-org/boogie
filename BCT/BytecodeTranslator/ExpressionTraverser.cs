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
  class ExpressionTraverser : BaseCodeTraverser {

    // warning! this has to be replaced by a HeapVariable from outside
    public readonly Bpl.Variable HeapVariable;        

    public readonly StatementTraverser StmtTraverser;

    public readonly Stack<Bpl.Expr> TranslatedExpressions;

    #region Constructors

    public ExpressionTraverser(StatementTraverser stmtTraverser) {
      HeapVariable = stmtTraverser.HeapVariable;
      StmtTraverser = stmtTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();
    }

    public ExpressionTraverser(ClassTraverser classTraverser) {
      // TODO
      //StmtTraverser = new StatementTraverser(classTraverser);
      HeapVariable = classTraverser.HeapVariable;
      TranslatedExpressions = new Stack<Bpl.Expr>();
    }

    public ExpressionTraverser(MethodTraverser methodTraverser) {
      HeapVariable = methodTraverser.HeapVariable;
      StmtTraverser = new StatementTraverser(methodTraverser);
      TranslatedExpressions = new Stack<Bpl.Expr>();
    }

    public ExpressionTraverser(StatementTraverser stmtTraverser, Bpl.Variable heapvar) {
      HeapVariable = heapvar;
      StmtTraverser = stmtTraverser;
      TranslatedExpressions = new Stack<Bpl.Expr>();
    }

    public ExpressionTraverser(ClassTraverser classTraverser, Bpl.Variable heapvar) {
      HeapVariable = heapvar;
      // TODO
      //StmtTraverser = new StatementTraverser(classTraverser);
      TranslatedExpressions = new Stack<Bpl.Expr>();
    }

    public ExpressionTraverser(MethodTraverser methodTraverser, Bpl.Variable heapvar) {
      HeapVariable = heapvar;
      StmtTraverser = new StatementTraverser(methodTraverser);
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
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.FindOrCreateLocalVariable(local)));
        return;
      }
      IParameterDefinition/*?*/ param = addressableExpression.Definition as IParameterDefinition;
      if (param != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.FindParameterVariable(param)));
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
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.FindOrCreateLocalVariable(local)));
        return;
      }
      #endregion

      #region ParameterDefenition
      IParameterDefinition param = targetExpression.Definition as IParameterDefinition;
      if (param != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.FindParameterVariable(param)));
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
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(TranslationHelper.CciLocationToBoogieToken(thisReference.Locations),
        this.StmtTraverser.MethodTraverser.ClassTraverser.ThisVariable));
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
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.FindOrCreateLocalVariable(local)));
        return;
      }
      #endregion

      #region ParameterDefiniton
      IParameterDefinition param = boundExpression.Definition as IParameterDefinition;
      if (param != null) {
        TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.FindParameterVariable(param)));
        return;
      }
      #endregion

      #region FieldDefinition
      IFieldReference field = boundExpression.Definition as IFieldReference;
      if (field != null) {
        if (boundExpression.Instance != null) {
          ProcessFieldVariable(field, boundExpression.Instance,true);
          return;
        } else {
          throw new NotImplementedException(String.Format("Field {0} with Instance NULL.", boundExpression.ToString()));
        }
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
    private void ProcessFieldVariable(IFieldReference field, IExpression instance, bool buildSelectExpr) {

      //TranslatedExpressions.Push(Bpl.Expr.Ident(this.StmtTraverser.MethodTraverser.ClassTraverser.FindOrCreateFieldVariable(field.ResolvedField))
      TranslatedExpressions.Push( Bpl.Expr.Ident( 
        this.StmtTraverser.MethodTraverser.ClassTraverser.ToplevelTraverser.FindOrCreateClassField(
        field.ContainingType.ResolvedType, 
        field.ResolvedField) ) );

      ExpressionTraverser etrav = new ExpressionTraverser(StmtTraverser);
      etrav.Visit(instance);

      TranslatedExpressions.Push(etrav.TranslatedExpressions.Pop());

      // if the field access is not a targetexpression we build a select expression
      // otherwise the assignment visitor will build a mapassignment later on
      if (buildSelectExpr) {
        List<Bpl.Expr> elist = new List<Bpl.Expr>();

        while (TranslatedExpressions.Count > 0) {
          elist.Add(TranslatedExpressions.Pop());
        }
        TranslatedExpressions.Push(Bpl.Expr.Select(new Bpl.IdentifierExpr(TranslationHelper.CciLocationToBoogieToken(field.Locations), HeapVariable), elist));
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
      ExpressionTraverser thistraverser = new ExpressionTraverser(StmtTraverser);
      thistraverser.Visit(methodCall.ThisArgument);
      inexpr.Add(thistraverser.TranslatedExpressions.Pop());
      #endregion

      Dictionary<IParameterDefinition, Bpl.Expr> p2eMap = new Dictionary<IParameterDefinition, Bpl.Expr>();
      IEnumerator<IParameterDefinition> penum = methodCall.MethodToCall.ResolvedMethod.Parameters.GetEnumerator();
      penum.MoveNext();
      foreach (IExpression exp in methodCall.Arguments) {
        if (penum.Current == null) {
          throw new TranslationException("More Arguments than Parameters in functioncall");
        }
        ExpressionTraverser etrav = new ExpressionTraverser(this.StmtTraverser);
        etrav.Visit(exp);
        Bpl.Expr e = etrav.TranslatedExpressions.Pop();
        p2eMap.Add(penum.Current, e);
        if (!penum.Current.IsOut) {
          inexpr.Add(e);
        }
        
        penum.MoveNext();
      }
      #endregion

      Bpl.IToken cloc = TranslationHelper.CciLocationToBoogieToken(methodCall.Locations);

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
          Bpl.Variable v = this.StmtTraverser.MethodTraverser.CreateFreshLocal(methodCall.Type.ResolvedType);
          outvars.Add(new Bpl.IdentifierExpr(cloc, v));
          TranslatedExpressions.Push(new Bpl.IdentifierExpr(cloc, v));
        }
        string methodname = TranslationHelper.CreateUniqueMethodName(methodCall.MethodToCall.ResolvedMethod);

        this.StmtTraverser.StmtBuilder.Add(new Bpl.CallCmd(cloc, methodname, inexpr, outvars));
        
      }

    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub </remarks>
    /// <param name="assignment"></param>
    public override void Visit(IAssignment assignment) {
      ExpressionTraverser sourcetrav = new ExpressionTraverser(this.StmtTraverser);
      ExpressionTraverser targettrav = new ExpressionTraverser(this.StmtTraverser);

      #region Transform Right Hand Side ...
      sourcetrav.Visit(assignment.Source);
      Bpl.Expr sourceexp = sourcetrav.TranslatedExpressions.Pop();
      #endregion

      #region ... and now Left Hand Side and build the bpl statement

      targettrav.Visit(assignment.Target);

      if (targettrav.TranslatedExpressions.Count == 1) {

        Bpl.Expr targetexp = targettrav.TranslatedExpressions.Pop();
        Bpl.IdentifierExpr idexp = targetexp as Bpl.IdentifierExpr;
        if (idexp != null) {
          StmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(TranslationHelper.CciLocationToBoogieToken(assignment.Locations),
              idexp, sourceexp));
          return;
        } else {
          throw new TranslationException("Trying to create a SimpleAssign with complex/illegal lefthand side");
        }

      } else if (targettrav.TranslatedExpressions.Count > 1) {

        Bpl.ExprSeq eseq = new Bpl.ExprSeq();

        while (targettrav.TranslatedExpressions.Count > 0) {
          eseq.Add(targettrav.TranslatedExpressions.Pop());
        }

        StmtTraverser.StmtBuilder.Add(Bpl.Cmd.MapAssign(TranslationHelper.CciLocationToBoogieToken(assignment.Locations),
          new Bpl.IdentifierExpr(TranslationHelper.CciLocationToBoogieToken(assignment.Target.Locations),
            HeapVariable), eseq, sourceexp));
        return;
      } else {
        throw new TranslationException("Trying to create an Assignment but lefthand side cannot be created");
      }

      #endregion

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

    // TODO: (mschaef) AND and OR are not yet implemented

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
          TranslationHelper.CciLocationToBoogieToken(logicalNot.Locations),
          Bpl.UnaryOperator.Opcode.Not, exp));

    }
    #endregion

    #region CodeContract Expressions
    public override void Visit(IOldValue oldValue) {
      base.Visit(oldValue);
      TranslatedExpressions.Push(new Bpl.OldExpr(TranslationHelper.CciLocationToBoogieToken(oldValue.Locations),
        TranslatedExpressions.Pop()));
    }
    
    public override void Visit(IReturnValue returnValue) {
      if (this.StmtTraverser.MethodTraverser.RetVariable == null) {
        throw new TranslationException(String.Format("Don't know what to do with return value {0}", returnValue.ToString()));
      }
      TranslatedExpressions.Push(new Bpl.IdentifierExpr(TranslationHelper.CciLocationToBoogieToken(returnValue.Locations),
        this.StmtTraverser.MethodTraverser.RetVariable));

    }
    #endregion
  }
}
