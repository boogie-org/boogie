//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

  /////////////////////////////////////////////////////////////////////////////////
  // The Abstract domain for determining "constant" expressions
  // i.e. It determines which expression are statically binded
  /////////////////////////////////////////////////////////////////////////////////
/*
using System;

namespace Microsoft.AbstractInterpretationFramework
{
  using Microsoft.Contracts;
  using System.Collections.Generic;
  using Microsoft.AbstractInterpretationFramework;

  /// <summary> 
  /// This is an abstract domain for inferring constant expressions 
  /// </summary>

  public class ConstantExpressions : Lattice
  {
    /// <summary>
    /// An abstract element is made of two maps: 
    ///   + A map from variables to expressions \cup top ( i.e. for each variable, the expression it is binded )
    ///   + A map from variables to set of variabes      ( i.e. for each variable, the set of variables that depends on its value )
    /// </summary>
    private class AbstractElement: Element 
    {
      private Dictionary<IVariable!, BindExpr> variableBindings;
      private Dictionary<IVariable!, List<IVariable>> variableDependences;
      
      static private AbstractElement! bottom;
      static public Element! Bottom 
      {
        get
        {
          if(bottom == null)
          {
            bottom = new AbstractElement();
            bottom.variableBindings = null;
            bottom.variableDependences = null;
          }
          assert bottom.variableBindings == null && bottom.variableDependences == null;
          return bottom;
        }
      }        
   
      static public Element! Top
      {
        get
        {
          return new AbstractElement();
        }
      }
      
      AbstractElement() 
      {
        this.variableBindings = new Dictionary<IVariable!, BindExpr>();
        this.variableDependences = new Dictionary<IVariable!, List<IVariable>>();
      }
      
      /// <summary>
      /// Our abstract element is top if and only if it has any constraint on variables
      /// </summary>
      public bool IsTop
      {
        get
        {
          return this.variableBindings.Keys.Count == 0 && this.variableDependences.Keys.Count == 0;
        }      
      }

      /// <summary>
      /// Our abstract element is bottom if and only if the maps are null
      /// </summary>
      public bool IsBottom
      {
        get
        {    
          assert (this.variableBindings == null) <==> (this.variableDependences == null);
          return this.variableBindings == null && this.variableDependences == null;
        }      
      }

      /// <summary>
      /// The pointwise join...
      /// </summary>
      public static AbstractElement! Join(AbstractElement! left, AbstractElement! right)
      {
        AbstractElement! result = new AbstractElement();
        
        // Put all the variables in the left
        foreach(IVariable! var in left.variableBindings.Keys)
        {
          BindExpr leftVal = left.variableBindings[var];
          assert leftVal != null;
          
          BindExpr rightVal = right.variableBindings[var];

          if(rightVal== null)   // the expression is not there
          {
            result.variableBindings.Add(var, leftVal);
          }
          else    // both abstract elements have a definition for the variable....
          {
            result.variableBindings.Add(var, BindExpr.Join(leftVal, rightVal));
          }
        }
      
        // Put all the variables in the right
        foreach(IVariable! var in right.variableBindings.Keys)
        {
          BindExpr rightVal = right.variableBindings[var];
          assert rightVal != null;
          
          BindExpr leftVal = left.variableBindings[var];
          
          if(rightVal== null)   // the expression is not there
          {
            result.variableBindings.Add(var, rightVal);
          }
          else    // both abstract elements have a definition for the variable....
          {
            result.variableBindings.Add(var, BindExpr.Join(rightVal, leftVal));
          }
        }        

        // Join the dependencies...
        foreach(IVariable! var in left.variableDependences.Keys)
        {
          List<IVariable> dependencies = left.variableDependences[var];
          List<IVariable> dup = new List<IVariable>(dependencies);
          
          result.variableDependences.Add(var, dup);
        }

        foreach(IVariable! var in right.variableDependences.Keys)
        {
          if(result.variableDependences.ContainsKey(var))
          {
            List<IVariable> dependencies = result.variableDependences[var];
            dependencies.AddRange(right.variableDependences[var]);
          } 
          else
          {
            List<IVariable> dependencies = right.variableDependences[var];
            List<IVariable> dup = new List<IVariable>(dependencies);
          
            result.variableDependences.Add(var, dup);
          }
        }

        // Normalize... i.e. for the variables such thas they point to an unknown expression (top) we have to update also their values
        result.Normalize();

        return result;
      }
      

      ///<summary>
      /// Normalize the current abstract element, in that it propagetes the "dynamic" information throughtout the abstract element
      ///</summary>
      public void Normalize() 
      {
        if(this.IsBottom)
          return;
        if(this.IsTop)
          return;
        assert this.variableBindings != null;
        
        bool atFixpoint = false;

        while(!atFixpoint)
        {
          atFixpoint = true;                          // guess that we've got the fixpoint...

          foreach(IVariable x in this.variableBindings.Keys) 
          {
            if(this.variableBindings[x].IsTop)  // It means that the variable is tied to a dynamic expression
            {
              foreach(IVariable y in this.variableDependences[x])   // The all the variables that depend on x are also dynamic...
              {
                assert x != y;                  // A variable cannot depend on itself...
                if(!this.variableBindings[y].IsTop)
                {
                  this.variableBindings[y] = BindExpr.Top;
                  atFixpoint = false;                // the assumption that we were at the fixpoint was false, we have still to propagate some information...   
                }
              }
            }
          }
        }
      }

      /// <summary>
      /// The pointwise meet...
      /// </summary>
      public static AbstractElement! Meet(AbstractElement! left, AbstractElement! right)
      {
        AbstractElement! result = new AbstractElement();

        // Put the variables that are both in left and right
        foreach(IVariable var in left.variableBindings.Keys)
        {
          if(right.variableBindings.ContainsKey(var))
          {
            result.variableBindings.Add(var, BindExpr.Meet(left.variableBindings[var], right.variableBindings[var]));
          }
        }
      
        // Intersect the dependencies
        foreach(IVariable var in result.variableBindings.Keys)
        {
          List<IVariable> depLeft = left.variableDependences[var];
          List<IVariable> depRight = right.variableDependences[var];

          // Intersect the two sets
          result.variableDependences.Add(var, depLeft);
          foreach(IVariable v in depRight) 
          {
            if(!result.variableDependences.ContainsKey(v))
            {
              result.variableDependences.Remove(v);
            }
          }              
        } 

        // Now we remove the dependencies with variables not in variableBindings
        List<IVariable>! varsToRemove = new List<IVariable>();
    
       foreach(IVariable var in result.
          

      }

      /// <summary>
      /// Clone the current abstract element
      /// </summary>
      public override Element! Clone() 
      {
        AbstractElement cloned = new AbstractElement();
        foreach(IVariable var in this.variableBindings.Keys)
        {
          cloned.variableBindings.Add(var, this.variableBindings[var]);
        }

        foreach(IVariable var in this.variableDependences.Keys)
        {
          List<IVariable> dependingVars = this.variableDependences[var];
          List<IVariable> clonedDependingVars = new List<IVariable>(dependingVars);
          cloned.variableDependences.Add(var, clonedDependingVars);
        }
      }

      /// <summary>
      /// Return the variables that have a binding
      /// </summary>
      public override ICollection<IVariable!>! FreeVariables() 
      {
        List<IVariable!> vars = new List<IVariable!>(this.variableBindings.Keys);

        return vars;
      }

      public override string! ToString() 
      {
        string! retString = "";
        retString += "Bindings";
        
        foreach(IVariable var in this.variableBindings.Keys)
        {
          string! toAdd = var.ToString() + " -> " + this.variableBindings[var];
          retString += toAdd + ",";
        }
        
        retString += "\nDependencies";
        foreach(IVariable var in this.variableDependences.Keys)
        {
          string! toAdd = var.ToString() + " -> " + this.variableDependences[var];
          retString += toAdd + ",";
        }

        return retString;
      }  
    }     

    public override Element! Top 
    {
      get
      {
        return AbstractElement.Top;
      }
    }

    public override Element! Bottom
    {
      get
      {
        return AbstractElement.Bottom;
      }
    }

    public override bool IsTop(Element! e)
    {
      assert e is AbstractElement;
      AbstractElement! absElement = (AbstractElement) e;
      
      return absElement.IsTop;
    }

    public override bool IsBottom(Element! e)
    {
      assert e is AbstractElement;
      AbstractElement absElement = (AbstractElement) e;
      return absElement.IsBottom;
    }       

    /// <summary>
    /// Perform the pointwise join of the two abstract elements
    /// </summary>
    public override Element! NontrivialJoin(Element! a, Element! b)
    {
      assert a is AbstractElement;
      assert b is AbstractElement;

      AbstractElement! left = (AbstractElement!) a;
      AbstractElement! right = (AbstractElement!) b;

      return AbstractElement.Join(left, right);
    }

    /// <summary>
    /// Perform the pointwise meet of two abstract elements
    /// </summary>
    public override Element! NontrivialMeet(Element! a, Element!b)
    {
      assert a is AbstractElement;
      assert b is AbstractElement;

      AbstractElement! left = (AbstractElement!) a;
      AbstractElement! right = (AbstractElement!) b;

      return AbstractElement.Meet(left, right);
    }

    
  }

  /// <summary>
  /// A wrapper in order to have the algebraic datatype BindExpr := IExpr | Top
  /// </summary>
  abstract class BindExpr 
  {    
    /// <summary>
    /// True iff this expression is instance of BindExprTop
    /// </summary>
    public bool IsTop
    {
      get
      {
        return this is BindExprTop;
      }
    }

    static public BindExpr Top
    {
      get
      {
        return BindExprTop.UniqueTop;
      }
    }

    /// <summary>
    /// True iff this expression is instance of BindExprBottom
    /// </summary>  
    public bool IsBottom
    {
      get
      {
        return this is BindExprBottom;
      }
    }

    static public BindExpr Bottom
    {
      get
      {
        return BindExprBottom.UniqueBottom;
      }
    }
    
    public static BindExpr! Join(BindExpr! left, BindExpr! right)
    {
      if(left.IsTop || right.IsTop)
      {
        return BindExpr.Top;
      }
      else if(left.IsBottom)
      {
        return right;
      }
      else if(right.IsBottom)
      {
        return left;
      }
      else if(left.EmbeddedExpr != right.EmbeddedExpr)
      {
        return BindExpr.Top;
      }
      else  // left.EmbeddedExpr == right.EmbeddedExpr
      {
        return left;
      }      
    }

    public static BindExpr! Meet(BindExpr! left, BindExpr! right)
    {
      if(left.IsTop)
      {
        return right;
      } 
      else if(right.IsTop)
      {
        return right;
      }
      else if(left.IsBottom || right.IsBottom)
      {
        return BindExpr.Bottom;
      }
      else if(left.EmbeddedExpr != right.EmbeddedExpr)
      {
        return BindExpr.Bottom;
      }
      else  // left.EmbeddedExpr == right.EmbeddedExpr
      {
        return left;
      }      
    }

    abstract public IExpr! EmbeddedExpr
    {
      get;
    }

  }
  
  /// <summary>
  /// A wrapper for an integer
  /// </summary>
  class Expr : BindExpr
  {
    private IExpr! exp;
    
    public Expr(IExpr! exp) 
    {
      this.exp = exp;
    }

    override public IExpr! EmbeddedExpr 
    {
      get 
      {
        return this.exp;
      }
    }

    public override string! ToString()
    {
      return this.exp.ToString();
    }
  }

  /// <summary>
  /// The dynamic expression 
  /// </summary>
  class BindExprTop : BindExpr
  {
    private BindExprTop top = new BindExprTop();
    static public BindExprTop! UniqueTop
    {
      get
      {
        return this.top;
      }
    }

    private BindExprTop() {}

    override public IExpr! EmbeddedExpr
    {
      get
      {
        assert false;     // If we get there, we have an error
      }
    }

    public override string! ToString() 
    {
      return "<dynamic expression>";
    }
  }

  /// <summary>
  /// The unreachable expression
  /// </summary>    
  class BindExprBottom : BindExpr
  {
    private BindExprBottom! bottom = new BindExprBottom();
    static public BindExprBottom! UniqueBottom
    {
      get
      {
        return this.bottom;
      }
    }
    
    private BindExprBottom() {}

    override public IExpr! EmbeddedExpr
    {
      get
      {
        assert false;
      }
    }
  
    public override string! ToString() 
    {
      return "<unreachable expression>";
    }
  }

} // end namespace Microsoft.AbstractInterpretationFramework
*/