//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie.AbstractInterpretation
{
using System;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Contracts;
using AI = Microsoft.AbstractInterpretationFramework;
using Boogie = Microsoft.Boogie;
  /// <summary>
  /// A visitor of an abstract interpretation expression that collects the free variables 
  /// </summary>      
  class FreeVariablesVisitor : AI.ExprVisitor 
  {
    [Peer] List<AI.IVariable!>! variables;
    public List<AI.IVariable!>! FreeVariables 
    {
      get
      {
        return this.variables;
      }    
    }

    List<string!>! varNames;    // used to check the consinstency!

    public FreeVariablesVisitor() 
    {
      this.variables = new List<AI.IVariable!>(); 
      this.varNames = new List<string!>();
    }

    override public object Default(AI.IExpr! expr)
    {
      if (expr is AI.IVariable) 
      {
        if(!variables.Contains((AI.IVariable) expr)) 
        {
          this.variables.Add((AI.IVariable) expr);
                      
          assert ! this.varNames.Contains(expr.ToString());     // If we get there, we have an error: two variables with the same name but different identity  
             
          this.varNames.Add(expr.ToString());
        }
        return null;
      }
      else if (expr is AI.IFunApp)
        return VisitFunApp((AI.IFunApp) expr);
      else if (expr is AI.IFunction)
        return VisitFunction((AI.IFunction)expr);
      else 
      {
        assert false;
      }
    }

    public override object VisitFunApp(AI.IFunApp! funapp)
    {
      foreach (AI.IExpr! arg in funapp.Arguments)
      {
        arg.DoVisit(this);
      }
      return true;
    }
                
    public override object VisitFunction(AI.IFunction! fun)
    {
      fun.Body.DoVisit(this);
      this.variables.Remove(fun.Param);
      return true;
    }

  } 

}