using System;
using System.Collections.Generic;
using System.ComponentModel;
using Microsoft.Boogie;

class QuantifierInstantiationEngine
{
  //private Dictionary<Function, ForallExpr> lambdaAxiomExpr;
  private Dictionary<PredicateCmd, Expr> rewrittenCmdExpr;
  private Dictionary<Axiom, Expr> rewrittenAxiomExpr;
  private Dictionary<BoundVariable, string> instantiationLabel;
  
  private Dictionary<Variable, QuantifierExpr> quantifierBinding;
  private Dictionary<QuantifierExpr, List<Expr>> quantifierInstances;
  private HashSet<Variable> skolemVariables;

  /*
   * Walk over the entire implementation and convert each assume/assert with quantifier in let form.
   * Put the result in a dictionary.
   * During this walk skolemize quantifiers appropriately before putting into let form.
   * This walk should initialize labelToInstances and lambdas to instances.
   *
   * How do we maintain the worklist?
   * 
   */

  private Dictionary<string, HashSet<Expr>> labelToInstances;
  //private Dictionary<Function, HashSet<List<Expr>>> lambdaToInstances;

  public static void Instantiate(Implementation impl)
  {
    var qiEngine = new QuantifierInstantiationEngine(impl);
    qiEngine.Execute();
    // collect instances and create assumes in block 0
  }

  private QuantifierInstantiationEngine(Implementation impl)
  {
    
  }

  private void Execute()
  {
    
  }
}