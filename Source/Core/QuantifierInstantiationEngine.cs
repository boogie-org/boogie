using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace VC
{
  public class QuantifierInstantiationEngine
  {
    private class QuantifierInstantiationInfo
    {
      public Dictionary<Variable, HashSet<string>> boundVariableToLabels;
      public HashSet<string> relevantLabels;
      public Dictionary<List<Expr>, Expr> instances;

      public QuantifierInstantiationInfo(Dictionary<Variable, HashSet<string>> boundVariableToLabels)
      {
        this.boundVariableToLabels = boundVariableToLabels;
        this.relevantLabels = boundVariableToLabels.Values.SelectMany(x => x).ToHashSet();
        this.instances = new Dictionary<List<Expr>, Expr>(new ListComparer<Expr>());
      }
    }

    private Implementation impl;
    private Dictionary<Variable, QuantifierExpr> quantifierBinding;
    private Dictionary<Function, QuantifierExpr> lambdaDefinition;
    private Dictionary<QuantifierExpr, QuantifierInstantiationInfo> quantifierInstantiationInfo;
    private HashSet<Variable> skolemConstants;
    private Dictionary<string, HashSet<Expr>> labelToInstances;
    private Dictionary<string, HashSet<Expr>> accLabelToInstances;
    private Dictionary<Function, HashSet<List<Expr>>> lambdaToInstances;
    private Dictionary<Function, HashSet<List<Expr>>> accLambdaToInstances;
    private string quantifierBindingNamePrefix;
    private string skolemConstantNamePrefix;
    
    private static void AddInstances<T,U>(Dictionary<T, HashSet<U>> @from, Dictionary<T, HashSet<U>> to)
    {
      @from.Iter(kv =>
      {
        if (!to.ContainsKey(kv.Key))
        {
          to[kv.Key] = new HashSet<U>();
        }
        to[kv.Key].UnionWith(@from[kv.Key]);
      });
    }

    public static void Instantiate(Implementation impl)
    {
      var qiEngine = new QuantifierInstantiationEngine(impl);
      qiEngine.Start();
      qiEngine.Execute();
      qiEngine.Finish();
    }

    public static void SubstituteIncarnationInInstantiationAttribute(Cmd cmd, Substitution incarnationSubst, Substitution oldFrameSubst)
    {
      QKeyValue iter = null;
      if (cmd is AssignCmd assignCmd)
      {
        iter = assignCmd.Attributes;
      }
      else if (cmd is PredicateCmd predicateCmd)
      {
        iter = predicateCmd.Attributes;
      }
      while (iter != null)
      {
        if (iter.Key == "inst")
        {
          var label = iter.Params[0] as string;
          var instance = iter.Params[1] as Expr;
          if (label != null && instance != null)
          {
            instance = Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, instance);
            iter.ClearParams();
            iter.AddParams(new List<object> {label, instance});
          }
        }
        iter = iter.Next;
      }
    }
    
    public bool BindLambdaFunction(Function lambdaFunction)
    {
      if (lambdaDefinition.ContainsKey(lambdaFunction))
      {
        return true;
      }
      var lambdaDefinitionExpr = lambdaFunction.DefinitionAxiom.Expr as QuantifierExpr;
      var boundVariableToLabels = lambdaDefinitionExpr.Dummies.ToDictionary(x => x, x => FindLabels(x));
      if (Enumerable
          .Range(lambdaFunction.InParams.Count, lambdaDefinitionExpr.Dummies.Count - lambdaFunction.InParams.Count)
          .All(i => boundVariableToLabels[lambdaDefinitionExpr.Dummies[i]].Count > 0))
      {
        lambdaDefinition[lambdaFunction] = lambdaDefinitionExpr;
        quantifierInstantiationInfo[lambdaDefinitionExpr] = new QuantifierInstantiationInfo(boundVariableToLabels);
        return true;
      }
      return false;
    }

    public Expr BindQuantifier(QuantifierExpr quantifierExpr)
    {
      var boundVariableToLabels = quantifierExpr.Dummies.ToDictionary(x => x, x => FindLabels(x));
      if (boundVariableToLabels.All(kv => kv.Value.Count > 0))
      {
        var v = new BoundVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, $"{quantifierBindingNamePrefix}{quantifierBinding.Count}", Type.Bool));
        quantifierBinding[v] = quantifierExpr;
        quantifierInstantiationInfo[quantifierExpr] = new QuantifierInstantiationInfo(boundVariableToLabels);
        return Expr.Ident(v);
      }
      else
      {
        return quantifierExpr;
      }
    }

    public Variable FreshSkolemConstant(Variable variable)
    {
      var type = variable.TypedIdent.Type;
      var skolemConstant = new LocalVariable(Token.NoToken,
        new TypedIdent(Token.NoToken, $"{skolemConstantNamePrefix}{skolemConstants.Count}", type));
      skolemConstants.Add(skolemConstant);
      var subst = Substituter.SubstitutionFromDictionary(
        new Dictionary<Variable, Expr> {{variable, Expr.Ident(skolemConstant)}});
      AddInstancesForLabels(variable, subst);
      return skolemConstant;
    }

    public bool IsQuantifierBinding(Variable variable)
    {
      return this.quantifierBinding.ContainsKey(variable);
    }

    private QuantifierInstantiationEngine(Implementation impl)
    {
      this.impl = impl;
      this.quantifierBinding = new Dictionary<Variable, QuantifierExpr>();
      this.lambdaDefinition = new Dictionary<Function, QuantifierExpr>();
      this.quantifierInstantiationInfo = new Dictionary<QuantifierExpr, QuantifierInstantiationInfo>();
      this.skolemConstants = new HashSet<Variable>();
      this.labelToInstances = new Dictionary<string, HashSet<Expr>>();
      this.accLabelToInstances = new Dictionary<string, HashSet<Expr>>();
      this.lambdaToInstances = new Dictionary<Function, HashSet<List<Expr>>>();
      this.accLambdaToInstances = new Dictionary<Function, HashSet<List<Expr>>>();
      this.quantifierBindingNamePrefix = "quantifierBinding";
      this.skolemConstantNamePrefix = "skolemConstant";
    }

    private static HashSet<string> FindLabels(ICarriesAttributes o)
    {
      var labels = new HashSet<string>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "inst_label")
        {
          iter.Params.OfType<string>().Iter(x => labels.Add(x));
        }
        iter = iter.Next;
      }
      return labels;
    }

    private static Dictionary<string, HashSet<Expr>> FindInstancesForLabels(ICarriesAttributes o)
    {
      var freshInstances = new Dictionary<string, HashSet<Expr>>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "inst")
        {
          var label = iter.Params[0] as string;
          var instance = iter.Params[1] as Expr;
          if (label != null && instance != null)
          {
            if (!freshInstances.ContainsKey(label))
            {
              freshInstances[label] = new HashSet<Expr>();
            }
            freshInstances[label].Add(instance);
          }
        }
        iter = iter.Next;
      }
      return freshInstances;
    }

    private void Start()
    {
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().Iter(predicateCmd =>
      {
        AddInstances(FindInstancesForLabels(predicateCmd), labelToInstances);
        predicateCmd.Expr = Skolemizer.Skolemize(this,
          predicateCmd is AssumeCmd ? InstStatus.SkolemizeExists : InstStatus.SkolemizeForall, predicateCmd.Expr);
        AddInstances(LambdaInstanceCollector.CollectInstances(this, predicateCmd.Expr), lambdaToInstances);
      }));
    }

    private void Execute()
    {
      while (labelToInstances.Count > 0)
      {
        var currLabelToInstances = this.labelToInstances;
        this.labelToInstances = new Dictionary<string, HashSet<Expr>>();
        AddInstances(currLabelToInstances, accLabelToInstances);

        var currLambdaToInstances = this.lambdaToInstances;
        this.lambdaToInstances = new Dictionary<Function, HashSet<List<Expr>>>();
        AddInstances(currLambdaToInstances, accLambdaToInstances);
        
        foreach (var quantifierExpr in quantifierBinding.Values)
        {
          var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
          if (quantifierInfo.relevantLabels.Overlaps(currLabelToInstances.Keys))
          {
            InstantiateQuantifier(quantifierExpr);
          }
        }

        foreach (var lambdaFunction in lambdaDefinition.Keys)
        {
          var quantifierExpr = lambdaDefinition[lambdaFunction];
          var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
          if (quantifierInfo.relevantLabels.Overlaps(currLabelToInstances.Keys) || currLambdaToInstances[lambdaFunction].Count > 0)
          {
            InstantiateLambdaDefinition(lambdaFunction);
          }
        }
      }
    }

    private void Finish()
    {
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().Iter(predicateCmd =>
      {
        predicateCmd.Expr = LetConvert(predicateCmd.Expr);
      }));
      impl.LocVars.AddRange(skolemConstants);
      var cmds = lambdaDefinition.Values.SelectMany(quantifierExpr => quantifierInstantiationInfo[quantifierExpr].instances.Values)
        .Select(expr => new AssumeCmd(Token.NoToken, expr)).ToList<Cmd>();
      cmds.AddRange(impl.Blocks[0].Cmds);
      impl.Blocks[0].Cmds = cmds;
    }

    private Expr LetConvert(Expr expr)
    {
      var bindings = BindingCollector.CollectBindings(this, expr).ToList();
      if (bindings.Count == 0)
      {
        return expr;
      }
      var rhss = new List<Expr>();
      foreach (var binding in bindings)
      {
        rhss.Add(LetConvert(this.AugmentWithInstances(quantifierBinding[binding])));
      }
      return new LetExpr(Token.NoToken, bindings, rhss, null, expr);
    }

    private Expr AugmentWithInstances(QuantifierExpr quantifierExpr)
    {
      if (quantifierExpr is ForallExpr)
      {
        return Expr.And(quantifierExpr, Expr.And(quantifierInstantiationInfo[quantifierExpr].instances.Values));
      }
      else
      {
        return Expr.Or(quantifierExpr, Expr.Or(quantifierInstantiationInfo[quantifierExpr].instances.Values));
      }
    }

    private void InstantiateLambdaDefinition(Function lambdaFunction)
    {
      var quantifierExpr = lambdaDefinition[lambdaFunction];
      var quantifierInstantiationInfo = this.quantifierInstantiationInfo[quantifierExpr];
      var boundVariableToExprs = quantifierInstantiationInfo.boundVariableToLabels.Keys.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          quantifierInstantiationInfo
            .boundVariableToLabels[boundVariable]
            .SelectMany(label => accLabelToInstances[label]).ToHashSet());
      foreach (var instance in accLambdaToInstances[lambdaFunction])
      {
        ConstructInstances(quantifierExpr, boundVariableToExprs, lambdaFunction.InParams.Count, instance);
      }
    }

    private void InstantiateQuantifier(QuantifierExpr quantifierExpr)
    {
      var quantifierInstantiationInfo = this.quantifierInstantiationInfo[quantifierExpr];
      var boundVariableToExprs = quantifierInstantiationInfo.boundVariableToLabels.Keys.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          quantifierInstantiationInfo
            .boundVariableToLabels[boundVariable]
            .SelectMany(label => accLabelToInstances[label]).ToHashSet());
      ConstructInstances(quantifierExpr, boundVariableToExprs, 0, new List<Expr>());
    }

    private void ConstructInstances(QuantifierExpr quantifierExpr,
      Dictionary<Variable, HashSet<Expr>> boundVariableToExprs, int n, List<Expr> instance)
    {
      if (quantifierExpr.Dummies.Count == n)
      {
        InstantiateQuantifierAtInstance(quantifierExpr, instance);
        return;
      }
      var boundVariable = quantifierExpr.Dummies[n];
      foreach (var expr in boundVariableToExprs[boundVariable])
      {
        instance.Add(expr);
        ConstructInstances(quantifierExpr, boundVariableToExprs, n + 1, instance);
        instance.RemoveAt(n);
      }
    }

    private void InstantiateQuantifierAtInstance(QuantifierExpr quantifierExpr, List<Expr> instance)
    {
      var quantifierInstantiationInfo = this.quantifierInstantiationInfo[quantifierExpr];
      if (quantifierInstantiationInfo.instances.ContainsKey(instance))
      {
        return;
      }
      var subst = Substituter.SubstitutionFromDictionary(
        Enumerable.Range(0, quantifierExpr.Dummies.Count).ToDictionary(
          x => quantifierExpr.Dummies[x],
          x => instance[x]));
      var instantiation = Substituter.Apply(subst, quantifierExpr.Body);
      quantifierInstantiationInfo.instances[new List<Expr>(instance)] = Skolemizer.Skolemize(this,
        quantifierExpr is ForallExpr ? InstStatus.SkolemizeExists : InstStatus.SkolemizeForall, instantiation);
      quantifierExpr.Dummies.Iter(variable => AddInstancesForLabels(variable, subst));
    }
    
    private void AddInstancesForLabels(Variable variable, Substitution subst)
    {
      FindInstancesForLabels(variable).Iter(kv =>
      {
        if (!labelToInstances.ContainsKey(kv.Key))
        {
          labelToInstances[kv.Key] = new HashSet<Expr>();
        }

        kv.Value.Iter(expr => { labelToInstances[kv.Key].Add(Substituter.Apply(subst, expr)); });
      });
    }
  }

  enum InstStatus
  {
    SkolemizeForall,
    SkolemizeExists,
    None,
  }

  class Skolemizer : Duplicator
  {
    public static Expr Skolemize(QuantifierInstantiationEngine qiEngine, InstStatus instStatus, Expr expr)
    {
      var skolemizer = new Skolemizer(qiEngine, instStatus);
      var skolemizedExpr = skolemizer.VisitExpr(expr);
      return Factorizer.Factorize(qiEngine, instStatus, skolemizedExpr);
    }

    private Skolemizer(QuantifierInstantiationEngine qiEngine, InstStatus instStatus)
    {
      this.qiEngine = qiEngine;
      this.instStatus = instStatus;
      this.bound = new Dictionary<Variable, Expr>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private InstStatus instStatus;
    private Dictionary<Variable, Expr> bound;

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (bound.ContainsKey(node.Decl))
      {
        return bound[node.Decl];
      }

      return base.VisitIdentifierExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (instStatus == InstStatus.None)
      {
        return base.VisitNAryExpr(node);
      }
      var savedInstStatus = instStatus;
      var unaryOperator = node.Fun as UnaryOperator;
      if (unaryOperator != null && unaryOperator.Op == UnaryOperator.Opcode.Not)
      {
        instStatus = instStatus == InstStatus.SkolemizeExists ? InstStatus.SkolemizeForall : InstStatus.SkolemizeExists;
      }
      var binaryOperator = node.Fun as BinaryOperator;
      if (binaryOperator != null &&
          (binaryOperator.Op == BinaryOperator.Opcode.Iff ||
           binaryOperator.Op == BinaryOperator.Opcode.Imp ||
           binaryOperator.Op == BinaryOperator.Opcode.Eq && node.Args[0].Type.Equals(Type.Bool)))
      {
        instStatus = InstStatus.None;
      }
      var returnExpr = base.VisitNAryExpr(node);
      instStatus = savedInstStatus;
      return returnExpr;
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      if (instStatus == InstStatus.SkolemizeForall)
      {
        return PerformSkolemization(node);
      }

      var savedInstStatus = instStatus;
      if (instStatus != InstStatus.None)
      {
        instStatus = InstStatus.None;
      }

      var returnExpr = base.VisitForallExpr(node);
      instStatus = savedInstStatus;
      return returnExpr;
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      if (instStatus == InstStatus.SkolemizeExists)
      {
        return PerformSkolemization(node);
      }

      var savedInstStatus = instStatus;
      if (instStatus != InstStatus.None)
      {
        instStatus = InstStatus.None;
      }

      var returnExpr = base.VisitExistsExpr(node);
      instStatus = savedInstStatus;
      return returnExpr;
    }

    private Expr PerformSkolemization(BinderExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => qiEngine.FreshSkolemConstant(x));
      foreach (var x in node.Dummies)
      {
        bound.Add(x, Expr.Ident(oldToNew[x]));
      }

      var expr = base.VisitExpr(node.Body);
      foreach (var x in node.Dummies)
      {
        bound.Remove(x);
      }

      return expr;
    }
  }

  class Factorizer : Duplicator
  {
    private QuantifierInstantiationEngine qiEngine;
    private InstStatus instStatus;

    public static Expr Factorize(QuantifierInstantiationEngine qiEngine, InstStatus instStatus, Expr expr)
    {
      var factorizer = new Factorizer(qiEngine, instStatus);
      return factorizer.VisitExpr(expr);
    }

    private Factorizer(QuantifierInstantiationEngine qiEngine, InstStatus instStatus)
    {
      this.qiEngine = qiEngine;
      this.instStatus = instStatus;
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      if (instStatus != InstStatus.SkolemizeForall)
      {
        return qiEngine.BindQuantifier(node);
      }

      return base.VisitForallExpr(node);
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      if (instStatus != InstStatus.SkolemizeExists)
      {
        return qiEngine.BindQuantifier(node);
      }

      return base.VisitExistsExpr(node);
    }
  }

  class BindingCollector : ReadOnlyVisitor
  {
    public static HashSet<Variable> CollectBindings(QuantifierInstantiationEngine qiEngine, Expr expr)
    {
      var bindingCollector = new BindingCollector(qiEngine);
      bindingCollector.VisitExpr(expr);
      return bindingCollector.bindings;
    }

    private BindingCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.bindings = new HashSet<Variable>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<Variable> bindings;

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (qiEngine.IsQuantifierBinding(node.Decl))
      {
        bindings.Add(node.Decl);
      }

      return base.VisitIdentifierExpr(node);
    }
  }

  class LambdaInstanceCollector : ReadOnlyVisitor
  {
    public static Dictionary<Function, HashSet<List<Expr>>> CollectInstances(QuantifierInstantiationEngine qiEngine, Expr expr)
    {
      var lambdaInstanceCollector = new LambdaInstanceCollector(qiEngine);
      lambdaInstanceCollector.VisitExpr(expr);
      return lambdaInstanceCollector.instances;
    }

    private LambdaInstanceCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.instances = new Dictionary<Function, HashSet<List<Expr>>>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private Dictionary<Function, HashSet<List<Expr>>> instances;

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is FunctionCall functionCall)
      {
        var function = functionCall.Func;
        if (function.OriginalLambdaExprAsString != null && qiEngine.BindLambdaFunction(function))
        {
          if (!instances.ContainsKey(function))
          {
            instances[function] = new HashSet<List<Expr>>(new ListComparer<Expr>());
          }
          instances[function].Add(node.Args.ToList());
        }
      }
      return base.VisitNAryExpr(node);
    }
  }
}