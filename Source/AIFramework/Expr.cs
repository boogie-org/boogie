//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
// This file specifies the expression language used by the Abstract
// Interpretation Framework.
//
//   expressions   e  ::=  x              variables
//                      |  f(e1,...,en)   uninterpreted functions
//                      |  \x:t.e         lambda expressions
//
//   types         t  ::= b                   user-defined/built-in base types
//                      | t1 * ... * tn -> t' function type

namespace Microsoft.AbstractInterpretationFramework
{
    using System.Collections;
  using System;
    using System.Diagnostics.Contracts;

    //----------------------------- Expressions -----------------------------

    /// <summary>
    ///  An interface for expressions.  This expression language is specified
    ///  by interfaces to allow the client to be able to use their existing
    ///  AST nodes as AIF expressions.
    /// 
    ///  This only serves as a place for operations on expressions.  Clients
    ///  should implement directly IVariable, IFunApp, ...
    /// </summary>
    [ContractClass(typeof(IExprContracts))]
    public interface IExpr
    {
        /// <summary>
        /// Execute a visit over the expression.
        /// </summary>
        /// <param name="visitor">The expression visitor.</param>
        /// <returns>The result of the visit.</returns>
        [Pure] object DoVisit(ExprVisitor/*!*/ visitor);

        // TODO: Type checking of the expressions.
    }
  [ContractClassFor(typeof(IExpr))]
  public abstract class IExprContracts:IExpr{
  #region IExpr Members

public object  DoVisit(ExprVisitor visitor)
{
  Contract.Requires(visitor != null);
 	throw new System.NotImplementedException();
}

#endregion
}

    /// <summary>
    ///  An interface for variables.
    /// 
    ///  This interface should be implemented by the client.
    /// </summary>
    [ContractClass(typeof(IVariableContracts))]
    public interface IVariable : IExpr
    {
      string/*!*/ Name { get; }    // Each client must define the name for variables
    }
  [ContractClassFor(typeof(IVariable))]
  public abstract class IVariableContracts:IVariable{
    string IVariable.Name{get{Contract.Ensures(Contract.Result<string>() != null);throw new NotImplementedException();}

    }

    #region IExpr Members

    object IExpr.DoVisit(ExprVisitor visitor) {
      throw new NotImplementedException();
    }

    #endregion
  }

    /// <summary>
    ///  An interface for function applications.
    /// 
    ///  This interface should be implemented by the client.
    /// </summary>
    /// 
  [ContractClass(typeof(IFunAppContracts))]
    public interface IFunApp : IExpr
    {
        IFunctionSymbol/*!*/ FunctionSymbol { get; }
        IList/*<IExpr!>*//*!*/ Arguments
        {
            [Pure][Rep] get;
            
        }

        /// <summary>
        ///  Provides a method to create a new uninterpreted function
        ///  with the same function symbol but with the arguments with
        ///  args.
        /// </summary>
        /// <param name="args">The new arguments.</param>
        /// <returns>A copy of the function with the new arguments.</returns>
        IFunApp/*!*/ CloneWithArguments(IList/*<IExpr!>*//*!*/ args)
        //TODO  Contract.Requires(this.Arguments.Count == args.Count);
        ;
    }
  [ContractClassFor(typeof(IFunApp))]
public abstract class IFunAppContracts:IFunApp{

#region IFunApp Members

public IFunctionSymbol  FunctionSymbol
{
	get {Contract.Ensures(Contract.Result<IFunctionSymbol>() != null);
 throw new System.NotImplementedException(); }
}

public IList  Arguments
{
	get {Contract.Ensures(Contract.Result<IList>() != null);
    Contract.Ensures(Contract.Result<IList>().IsReadOnly);
 throw new System.NotImplementedException(); }
}

public IFunApp  CloneWithArguments(IList args)
{
  Contract.Requires(args != null);
  Contract.Ensures(Contract.Result<IFunApp>() != null);


 	throw new System.NotImplementedException();
}

#endregion

#region IExpr Members

object IExpr.DoVisit(ExprVisitor visitor) {
  throw new NotImplementedException();
}

#endregion
}

    /// <summary>
    ///  An interface for anonymous functions (i.e., lambda expressions)
    /// </summary>
    [ContractClass(typeof(IFunctionContracts))]
    public interface IFunction : IExpr
    {
        IVariable/*!*/ Param { get; }
        AIType/*!*/ ParamType { get; }
        IExpr/*!*/ Body { get; }

        IFunction/*!*/ CloneWithBody(IExpr/*!*/ body);
    }
  [ContractClassFor(typeof(IFunction))]
  public abstract class IFunctionContracts:IFunction{

    #region IFunction Members

    IVariable IFunction.Param {
      get {
        Contract.Ensures(Contract.Result<IVariable>() != null);
        throw new NotImplementedException();
      }
    }

    AIType IFunction.ParamType {
      get {
        Contract.Ensures(Contract.Result<AIType>() != null);
        throw new NotImplementedException();
      }
    }

    IExpr IFunction.Body {
      get {
        Contract.Ensures(Contract.Result<IExpr>() != null);
        throw new NotImplementedException();
      }
    }

    IFunction IFunction.CloneWithBody(IExpr body) {
      Contract.Requires(body != null);
      Contract.Ensures(Contract.Result<IFunction>() != null);
      throw new NotImplementedException();
    }

    #endregion

    #region IExpr Members

    object IExpr.DoVisit(ExprVisitor visitor) {
      throw new NotImplementedException();
    }

    #endregion
  }

    /// <summary>
    /// An interface representing an expression that at any moment could, in principle, evaluate
    /// to a different value.  That is, the abstract interpreter should treat these IExpr's
    /// as unknown values.  They are used when there is no other IExpr corresponding to the
    /// expression to be modeled.
    /// </summary>
    public interface IUnknown : IExpr {}
    
    /// <summary>
    /// An abstract class that provides an interface for expression visitors.
    /// </summary>
    [ContractClass(typeof(ExprVisitorContracts))]
    public abstract class ExprVisitor
    {
        public abstract object Default(IExpr/*!*/ expr);

        public virtual object VisitVariable(IVariable/*!*/ var){
Contract.Requires(var != null);
            return Default(var);
        }

        public virtual object VisitFunApp(IFunApp/*!*/ funapp){
Contract.Requires(funapp != null);
            return Default(funapp);
        }

        public virtual object VisitFunction(IFunction/*!*/ fun){
Contract.Requires(fun != null);
            return Default(fun);
        }
    }
  [ContractClassFor(typeof(ExprVisitor))]
  public abstract class ExprVisitorContracts:ExprVisitor{
    public override object  Default(IExpr expr)
{
 	Contract.Requires(expr != null); throw new NotImplementedException();
}}

    /// <summary>
    ///  A utility class for dealing with expressions.
    /// </summary>
    public sealed class ExprUtil
    {
        /// <summary>
        ///  Yield an expression that is 'inexpr' with 'var' replaced by 'subst'.
        /// </summary>
        /// <param name="subst">The expression to substitute.</param>
        /// <param name="var">The variable to substitute for.</param>
        /// <param name="inexpr">The expression to substitute into.</param>
        public static IExpr/*!*/ Substitute(IExpr/*!*/ subst, IVariable/*!*/ var, IExpr/*!*/ inexpr){
Contract.Requires(inexpr != null);
Contract.Requires(var != null);
Contract.Requires(subst != null);
Contract.Ensures(Contract.Result<IExpr>() != null);
            IExpr result = null;

            if (inexpr is IVariable)
            {
                result = inexpr.Equals(var) ? subst : inexpr;
            }
            else if (inexpr is IFunApp)
            {
                IFunApp/*!*/ funapp = (IFunApp/*!*/)cce.NonNull(inexpr);
                IList newargs = null;
              
              var x = new System.Collections.Generic.List<IExpr>();
              foreach (IExpr arg in funapp.Arguments){
                x.Add(Substitute(subst,var, arg));
              }
              newargs = new ArrayList(x);
                //newargs = new ArrayList{ IExpr/*!*/ arg in funapp.Arguments; Substitute(subst, var, arg) };
                result = funapp.CloneWithArguments(newargs);
            }
            else if (inexpr is IFunction)
            {
                IFunction/*!*/ fun = (IFunction/*!*/)cce.NonNull(inexpr);

                if (fun.Param.Equals(var))
                    result = fun;
                else
                    result = fun.CloneWithBody(Substitute(subst, var, fun.Body));
            }
            else if (inexpr is IUnknown)
            {
                result = inexpr;
            }
            else
            {
                {Contract.Assert(false);throw new cce.UnreachableException();}
            }

            return result;
        }
        
        
        //
        // Poor man's pattern matching.
        //
        // The methods below implement pattern matching for AI expressions.
        //
        // Example Usage:
        //   Match(e, Prop.Imp,
        //            (Matcher)delegate (IExpr e) { return Match(e, Prop.And, out x, out y); }
        //            out z)
        //   which sees if 'e' matches Prop.Imp(Prop.And(x,y),z) binding x,y,z to the subtrees.
        //
        public delegate bool Matcher(IExpr/*!*/ expr);
        
        private static IFunApp/*?*/ MatchFunctionSymbol(IExpr/*!*/ expr, IFunctionSymbol/*!*/ f){
Contract.Requires(f != null);
Contract.Requires(expr != null);
            IFunApp app = expr as IFunApp;
            if (app != null)
            {
                if (app.FunctionSymbol.Equals(f))
                    return app;
                else
                    return null;
            }
            else
                return null;
        }
        
        public static bool Match(IExpr/*!*/ expr, IFunctionSymbol/*!*/ f, params Matcher[]/*!*/ subs){
Contract.Requires(subs != null);
Contract.Requires(f != null);
Contract.Requires(expr != null);
            IFunApp app = MatchFunctionSymbol(expr,f);
            if (app != null)
            {
                int i = 0; // Note ***0***
                foreach(Matcher/*!*/ s in subs){
Contract.Assert(s != null);
                    if (!s(cce.NonNull((IExpr)app.Arguments[i]))) { return false; }
                    i++;
                }
                return true;
            }
            else { return false; }
        }
        
        // Unary Binding
        public static bool Match(IExpr/*!*/ expr, IFunctionSymbol/*!*/ f, out IExpr arg0, params Matcher[]/*!*/ subs){
Contract.Requires(subs != null);
Contract.Requires(f != null);
Contract.Requires(expr != null);
            arg0 = null;
        
            IFunApp app = MatchFunctionSymbol(expr,f);
            if (app != null)
            {
                arg0 = (IExpr/*!*/)cce.NonNull(app.Arguments[0]);
                
                int i = 1; // Note ***1***
                foreach(Matcher/*!*/ s in subs){
Contract.Assert(s != null);
                    if (!s(cce.NonNull((IExpr/*!*/)app.Arguments[i]))) { return false; }
                    i++;
                }
                return true;
            }
            else { return false; }
        }
        
        // Binary Binding       
        public static bool Match(IExpr/*!*/ expr, IFunctionSymbol/*!*/ f, Matcher/*!*/ sub0, out IExpr arg1, params Matcher[]/*!*/ subs){
Contract.Requires(subs != null);
Contract.Requires(sub0 != null);
Contract.Requires(f != null);
Contract.Requires(expr != null);
            arg1 = null;
        
            IFunApp app = MatchFunctionSymbol(expr,f);
            if (app != null)
            {
                if (!sub0(cce.NonNull((IExpr/*!*/)app.Arguments[0]))) { return false; }
            
                arg1 = (IExpr/*!*/)cce.NonNull(app.Arguments[1]);
                
                int i = 2; // Note ***2***
                foreach(Matcher/*!*/ s in subs){
Contract.Assert(s != null);
                    if (!s(cce.NonNull((IExpr)app.Arguments[i]))) { return false; }
                    i++;
                }
                return true;
            }
            else { return false; }
        }
        
        public static bool Match(IExpr/*!*/ expr, IFunctionSymbol/*!*/ f, out IExpr arg0, out IExpr arg1, params Matcher[]/*!*/ subs){
Contract.Requires(subs != null);
Contract.Requires(f != null);
Contract.Requires(expr != null);
            arg0 = null;
            arg1 = null;
        
            IFunApp app = MatchFunctionSymbol(expr,f);
            if (app != null)
            {
                arg0 = (IExpr/*!*/)cce.NonNull(app.Arguments[0]);
                arg1 = (IExpr/*!*/)cce.NonNull(app.Arguments[1]);
                
                int i = 2; // Note ***2***
                foreach(Matcher/*!*/ s in subs){
Contract.Assert(s != null);
                    if (!s(cce.NonNull((IExpr/*!*/)app.Arguments[i]))) { return false; }
                    i++;
                }
                return true;
            }
            else { return false; }
        }

        // Ternary Binding
        public static bool Match(IExpr/*!*/ expr, IFunctionSymbol/*!*/ f, out IExpr arg0, out IExpr arg1, out IExpr arg2, params Matcher[]/*!*/ subs){
Contract.Requires(subs != null);
Contract.Requires(f != null);
Contract.Requires(expr != null);
            arg0 = null;
            arg1 = null;
            arg2 = null;
        
            IFunApp app = MatchFunctionSymbol(expr,f);
            if (app != null)
            {
                arg0 = (IExpr/*!*/)cce.NonNull(app.Arguments[0]);
                arg1 = (IExpr/*!*/)cce.NonNull(app.Arguments[1]);
                arg2 = (IExpr/*!*/)cce.NonNull(app.Arguments[2]);
                
                int i = 3; // Note ***3***
                foreach(Matcher/*!*/ s in subs){
Contract.Assert(s != null);
                    if (!s(cce.NonNull((IExpr/*!*/)app.Arguments[i]))) { return false; }
                    i++;
                }
                return true;
            }
            else { return false; }
        }

        /// <summary>
        ///  Not intended to be instantiated.
        /// </summary>
        private ExprUtil() { }
    }

    //------------------------------ Symbols --------------------------------

    /// <summary>
    ///  An interface for function symbols.  Constants are represented by
    ///  0-ary function symbols.
    /// 
    ///  This interface should be implemented by abstract domains, but client
    ///  expressions need keep track of function symbols.
    /// </summary>
    [ContractClass(typeof(IFunctionSymbolContracts))]
    public interface IFunctionSymbol
    {
        AIType/*!*/ AIType { [Rep][ResultNotNewlyAllocated]
                         get; }
    }
  [ContractClassFor(typeof(IFunctionSymbol))]
  public abstract class IFunctionSymbolContracts:IFunctionSymbol{
    #region IFunctionSymbol Members

    AIType IFunctionSymbol.AIType {
      get {
        Contract.Ensures(Contract.Result<AIType>() != null);
        throw new NotImplementedException();
      }
    }

    #endregion
  }

    /// <summary>
    ///  The type of the arguments to ExprUtil.Match, a poor man's pattern
    ///  matching.
    /// </summary>
    public interface IMatchable
    {
    }

    //-------------------------------- Types --------------------------------

    /// <summary>
    ///  Types.
    /// </summary>
    public interface AIType
    {
    }

    /// <summary>
    ///  Function type constructor.
    /// </summary>
    public sealed class FunctionType : AIType
    {
        /*[Own]*/ private readonly IList/*<Type!>*//*!*/ argTypes;
        /*[Own]*/ private readonly AIType/*!*/ retType;
      [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(argTypes != null);
        Contract.Invariant(retType != null);
}


        public FunctionType(params AIType[]/*!*/ types){
Contract.Requires(types != null);
 Contract.Requires(types.Length >= 2);
            AIType type = types[types.Length-1];
            Contract.Assume(type != null);
            this.retType = type;
            ArrayList argTypes = new ArrayList();
            for (int i = 0; i < types.Length-1; i++)
            {
                 type = types[i];
                 Contract.Assume(type != null);
                 argTypes.Add(types);
            }
            this.argTypes = ArrayList.ReadOnly(argTypes);
        }

        public IList/*<AIType!>*//*!*/ Arguments
        {
            [Pure][Rep]
            get 
              {
              Contract.Ensures(Contract.Result<IList>() != null);
 Contract.Ensures(Contract.Result<IList>().IsReadOnly);
                return argTypes;
            }
        }

        public int Arity
        {
            get { return argTypes.Count; }
        }

        public AIType/*!*/ ReturnType
        {
            get {Contract.Ensures(Contract.Result<AIType>() != null); return retType; }
        }

        /* TODO Do we have the invariant that two functions are equal iff they're the same object.
        public override bool Equals(object o)
        {
            if (o != null && o is FunctionType)
            {
                FunctionType other = (FunctionType) o;
                
                if (Arity == other.Arity
                    && ReturnType.Equals(other.ReturnType))
                {
                    for (int i = 0; i < Arity; i++)
                    {
                        if (!argTypes[i].Equals(other.argTypes[i]))
                            return false;
                    }
                    return true;
                } 
                else
                    return false;
            }
            else
                return false;
        }
        */
    }

    //------------------------------ Queries -------------------------------

    public enum Answer { Yes, No, Maybe };
    
    /// <summary>
    ///  An interface that specifies a queryable object that can answer
    ///  whether a predicate holds.
    /// </summary>
    /// 
  [ContractClass(typeof(IQueryableContracts))]
    public interface IQueryable
    {
        /// <summary>
        ///  Answers the query whether the given predicate holds.
        /// </summary>
        /// <param name="pred">The given predicate.</param>
        /// <returns>Yes, No, or Maybe.</returns>
        Answer CheckPredicate(IExpr/*!*/ pred);

        /// <summary>
        ///  A simplified interface for disequalities.  One can always
        ///  implement this by calling CheckPredicate, but it may be
        ///  more efficient with this method.
        /// </summary>
        Answer CheckVariableDisequality(IVariable/*!*/ var1, IVariable/*!*/ var2);
    }
  [ContractClassFor(typeof(IQueryable))]
    public abstract class IQueryableContracts : IQueryable {
      #region IQueryable Members

      public Answer CheckPredicate(IExpr pred) {
        Contract.Requires(pred != null);
        throw new NotImplementedException();
      }

      public Answer CheckVariableDisequality(IVariable var1, IVariable var2) {
        Contract.Requires(var1 != null);
        Contract.Requires(var2 != null);
        throw new NotImplementedException();
      }

      #endregion
    }
    
    public static class QueryUtil
    {
        public static Answer Negate(Answer ans)
        {
            switch (ans)
            {
              case Answer.Yes:
                return Answer.No;
              case Answer.No:
                return Answer.Yes;
              default:
                return Answer.Maybe;
            }
        }
    }

    //----------------------------- Exceptions -----------------------------

    public class CheckedException : System.Exception {
    }
    public class TypeError : CheckedException
    {
    }
}
