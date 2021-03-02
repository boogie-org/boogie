using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie.VCExprAST
{
  public class QuantifierInstantiationEngine
  {
    private class QuantifierInstantiationInfo
    {
      public HashSet<string> relevantLabels;
      public Dictionary<List<VCExpr>, VCExpr> instances;

      public QuantifierInstantiationInfo(Dictionary<VCExprVar, HashSet<string>> boundVariableToLabels)
      {
        this.relevantLabels = boundVariableToLabels.Values.SelectMany(x => x).ToHashSet();
        this.instances = new Dictionary<List<VCExpr>, VCExpr>(new ListComparer<VCExpr>());
      }
    }
    
    private Dictionary<VCExprVar, VCExprQuantifier> quantifierBinding;
    private Dictionary<Function, VCExprQuantifier> lambdaDefinition;
    private Dictionary<VCExprQuantifier, QuantifierInstantiationInfo> quantifierInstantiationInfo;
    private HashSet<VCExprVar> skolemConstants;
    private Dictionary<string, HashSet<VCExpr>> labelToInstances;
    private Dictionary<string, HashSet<VCExpr>> accLabelToInstances;
    private Dictionary<Function, HashSet<List<VCExpr>>> lambdaToInstances;
    private Dictionary<Function, HashSet<List<VCExpr>>> accLambdaToInstances;
    private string quantifierBindingNamePrefix;
    private string skolemConstantNamePrefix;
    internal VCExpressionGenerator vcExprGen;
    internal Boogie2VCExprTranslator exprTranslator;

    public static VCExpr Instantiate(Implementation impl, VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator exprTranslator, VCExpr vcExpr)
    {
      var qiEngine = new QuantifierInstantiationEngine(vcExprGen, exprTranslator);
      return qiEngine.Execute(impl, vcExpr);
    }

    private QuantifierInstantiationEngine(VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator exprTranslator)
    {
      this.quantifierBinding = new Dictionary<VCExprVar, VCExprQuantifier>();
      this.lambdaDefinition = new Dictionary<Function, VCExprQuantifier>();
      this.quantifierInstantiationInfo = new Dictionary<VCExprQuantifier, QuantifierInstantiationInfo>();
      this.skolemConstants = new HashSet<VCExprVar>();
      this.labelToInstances = new Dictionary<string, HashSet<VCExpr>>();
      this.accLabelToInstances = new Dictionary<string, HashSet<VCExpr>>();
      this.lambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      this.accLambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      this.quantifierBindingNamePrefix = "quantifierBinding";
      this.skolemConstantNamePrefix = "skolemConstant";
      this.vcExprGen = vcExprGen;
      this.exprTranslator = exprTranslator;
    }
    
    public static void SubstituteIncarnationInInstantiationSources(Cmd cmd, Substitution incarnationSubst)
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
            instance = Substituter.Apply(incarnationSubst, instance);
            iter.ClearParams();
            iter.AddParams(new List<object> {label, instance});
          }
        }
        iter = iter.Next;
      }
    }

    public VCExpr BindQuantifier(VCExprQuantifier node)
    {
      if (node.TypeParameters.Count > 0)
      {
        return node;
      }
      var boundVariableToLabels = node.Info.instantiationLabels;
      if (boundVariableToLabels.Count < node.BoundVars.Count ||
          boundVariableToLabels.Any(kv => kv.Value.Count == 0))
      {
        return node;
      }
      var v = new VCExprVar($"{quantifierBindingNamePrefix}{quantifierBinding.Count}", Type.Bool);
      quantifierBinding[v] = node;
      quantifierInstantiationInfo[node] = new QuantifierInstantiationInfo(boundVariableToLabels);
      return v;
    }

    public Dictionary<VCExprVar, VCExpr> FreshSkolemConstants(VCExprQuantifier node)
    {
      var variableMapping = node.BoundVars.ToDictionary(v => v, v => (VCExpr) FreshSkolemConstant(v));
      var subst =
        new VCExprSubstitution(variableMapping, new Dictionary<TypeVariable, Type>());
      AddInstancesForLabels(node, subst);
      return variableMapping;
    }

    private void AddInstancesForLabels(VCExprQuantifier node, VCExprSubstitution subst)
    {
      var substituter = new SubstitutingVCExprVisitor(vcExprGen);
      node.Info.instantiationExprs.Iter(kv =>
      {
        if (!labelToInstances.ContainsKey(kv.Key))
        {
          labelToInstances[kv.Key] = new HashSet<VCExpr>();
        }
        kv.Value.Iter(expr => { labelToInstances[kv.Key].Add(substituter.Mutate(expr, subst)); });
      });
    }

    public bool IsQuantifierBinding(VCExprVar vcExprVar)
    {
      return this.quantifierBinding.ContainsKey(vcExprVar);
    }

    private VCExprVar FreshSkolemConstant(VCExprVar variable)
    {
      var skolemConstant = new VCExprVar($"{skolemConstantNamePrefix}{skolemConstants.Count}", variable.Type);
      skolemConstants.Add(skolemConstant);
      return skolemConstant;
    }

    public bool BindLambdaFunction(Function lambdaFunction)
    {
      if (lambdaDefinition.ContainsKey(lambdaFunction))
      {
        return true;
      }
      var lambdaDefinitionExpr = lambdaFunction.DefinitionAxiom.Expr as QuantifierExpr;
      if (lambdaDefinitionExpr.TypeParameters.Count > 0)
      {
        return false;
      }
      var translatedExpr = exprTranslator.Translate(lambdaDefinitionExpr) as VCExprQuantifier;
      var boundVariableToLabels = translatedExpr.Info.instantiationLabels;
      var numParametersInLambdaDefinition = lambdaDefinitionExpr.Dummies.Count - lambdaFunction.InParams.Count;
      if (boundVariableToLabels.Count < numParametersInLambdaDefinition ||
          Enumerable.Range(lambdaFunction.InParams.Count, numParametersInLambdaDefinition)
            .Any(i => boundVariableToLabels[translatedExpr.BoundVars[i]].Count == 0))
      {
        return false;
      }
      lambdaDefinition[lambdaFunction] = translatedExpr;
      quantifierInstantiationInfo[translatedExpr] = new QuantifierInstantiationInfo(boundVariableToLabels);
      return true;
    }

    private Dictionary<string, HashSet<VCExpr>> FindInstantiationSources(ICarriesAttributes o)
    {
      var freshInstances = new Dictionary<string, HashSet<VCExpr>>();
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
              freshInstances[label] = new HashSet<VCExpr>();
            }

            freshInstances[label].Add(exprTranslator.Translate(instance));
          }
        }
        iter = iter.Next;
      }
      return freshInstances;
    }

    private static void AddDictionary<T, U>(Dictionary<T, HashSet<U>> @from, Dictionary<T, HashSet<U>> to)
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
    
    private VCExpr Execute(Implementation impl, VCExpr vcExpr)
    {
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().Iter(predicateCmd =>
      {
        AddDictionary(FindInstantiationSources(predicateCmd), labelToInstances);
      }));
      vcExpr = Skolemizer.Skolemize(this, QuantifierStatus.Forall, vcExpr);
      lambdaToInstances = LambdaInstanceCollector.CollectInstances(this, vcExpr);
      while (labelToInstances.Count > 0)
      {
        var currLabelToInstances = labelToInstances;
        labelToInstances = new Dictionary<string, HashSet<VCExpr>>();
        AddDictionary(currLabelToInstances, accLabelToInstances);

        var currLambdaToInstances = lambdaToInstances;
        lambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
        AddDictionary(currLambdaToInstances, accLambdaToInstances);

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
          if (quantifierInfo.relevantLabels.Overlaps(currLabelToInstances.Keys) ||
              currLambdaToInstances[lambdaFunction].Count > 0)
          {
            InstantiateLambdaDefinition(lambdaFunction);
          }
        }
      }
      return vcExprGen.And(LetConvert(vcExpr), vcExprGen.NAry(VCExpressionGenerator.AndOp, lambdaDefinition.Values
        .SelectMany(quantifierExpr =>
          quantifierInstantiationInfo[quantifierExpr].instances.Values.ToList()).ToList()));
    }
    
    private VCExpr LetConvert(VCExpr vcExpr)
    {
      var bindings = BindingCollector.CollectBindings(this, vcExpr).ToList();
      if (bindings.Count == 0)
      {
        return vcExpr;
      }
      var rhss = new List<VCExprLetBinding>();
      foreach (var binding in bindings)
      {
        rhss.Add(new VCExprLetBinding(binding, LetConvert(this.AugmentWithInstances(quantifierBinding[binding]))));
      }
      return vcExprGen.Let(rhss, vcExpr);
    }

    private VCExpr AugmentWithInstances(VCExprQuantifier quantifierExpr)
    {
      if (quantifierExpr.Quan == Quantifier.ALL)
      {
        return vcExprGen.And(quantifierExpr,
          vcExprGen.NAry(VCExpressionGenerator.AndOp,
            quantifierInstantiationInfo[quantifierExpr].instances.Values.ToList()));
      }
      else
      {
        return vcExprGen.Or(quantifierExpr,
          vcExprGen.NAry(VCExpressionGenerator.OrOp,
            quantifierInstantiationInfo[quantifierExpr].instances.Values.ToList()));
      }
    }

    private void InstantiateLambdaDefinition(Function lambdaFunction)
    {
      var quantifierExpr = lambdaDefinition[lambdaFunction];
      var boundVariableToLabels = quantifierExpr.Info.instantiationLabels;
      var boundVariableToExprs = boundVariableToLabels.Keys.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          boundVariableToLabels[boundVariable]
            .SelectMany(label =>
              accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<VCExpr>()).ToHashSet());
      foreach (var instance in accLambdaToInstances[lambdaFunction])
      {
        ConstructInstances(quantifierExpr, boundVariableToExprs, lambdaFunction.InParams.Count, instance);
      }
    }

    private void InstantiateQuantifier(VCExprQuantifier quantifierExpr)
    {
      var boundVariableToLabels = quantifierExpr.Info.instantiationLabels;
      var boundVariableToExprs = boundVariableToLabels.Keys.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          boundVariableToLabels[boundVariable]
            .SelectMany(label =>
              accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<VCExpr>()).ToHashSet());
      ConstructInstances(quantifierExpr, boundVariableToExprs, 0, new List<VCExpr>());
    }

    private void ConstructInstances(VCExprQuantifier quantifierExpr,
      Dictionary<VCExprVar, HashSet<VCExpr>> boundVariableToExprs, int n, List<VCExpr> instance)
    {
      if (quantifierExpr.BoundVars.Count == n)
      {
        InstantiateQuantifierAtInstance(quantifierExpr, instance);
        return;
      }
      var boundVariable = quantifierExpr.BoundVars[n];
      foreach (var expr in boundVariableToExprs[boundVariable])
      {
        instance.Add(expr);
        ConstructInstances(quantifierExpr, boundVariableToExprs, n + 1, instance);
        instance.RemoveAt(n);
      }
    }

    private void InstantiateQuantifierAtInstance(VCExprQuantifier quantifierExpr, List<VCExpr> instance)
    {
      var quantifierInstantiationInfo = this.quantifierInstantiationInfo[quantifierExpr];
      if (quantifierInstantiationInfo.instances.ContainsKey(instance))
      {
        return;
      }
      var subst = new VCExprSubstitution(
        Enumerable.Range(0, quantifierExpr.BoundVars.Count).ToDictionary(
          x => quantifierExpr.BoundVars[x],
          x => instance[x]), new Dictionary<TypeVariable, Type>());
      var substituter = new SubstitutingVCExprVisitor(vcExprGen);
      var instantiation = substituter.Mutate(quantifierExpr.Body, subst);
      quantifierInstantiationInfo.instances[new List<VCExpr>(instance)] = Skolemizer.Skolemize(this,
        quantifierExpr.Quan == Quantifier.ALL ? QuantifierStatus.Exists : QuantifierStatus.Forall, instantiation);
    }
  }

  enum QuantifierStatus
  {
    Exists,
    Forall,
    None,
  }
  
  class Skolemizer : MutatingVCExprVisitor<bool>
  {
    public static VCExpr Skolemize(QuantifierInstantiationEngine qiEngine, QuantifierStatus quantifierStatus, VCExpr vcExpr)
    {
      Contract.Requires(quantifierStatus != QuantifierStatus.None);
      var skolemizer = new Skolemizer(qiEngine, quantifierStatus);
      var skolemizedExpr = skolemizer.Mutate(vcExpr, true);
      return Factorizer.Factorize(qiEngine,
        quantifierStatus == QuantifierStatus.Exists ? Quantifier.ALL : Quantifier.EX,
        skolemizedExpr);
    }

    private Skolemizer(QuantifierInstantiationEngine qiEngine, QuantifierStatus quantifierStatus) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifierStatus = quantifierStatus;
      this.bound = new Dictionary<VCExprVar, VCExpr>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private QuantifierStatus quantifierStatus;
    private Dictionary<VCExprVar, VCExpr> bound;

    public override VCExpr Visit(VCExprVar node, bool arg)
    {
      if (bound.ContainsKey(node))
      {
        return bound[node];
      }
      return base.Visit(node, arg);
    }

    public override VCExpr Visit(VCExprNAry node, bool arg)
    {
      if (quantifierStatus == QuantifierStatus.None)
      {
        return base.Visit(node, arg);
      }
      var savedQuantifierStatus = quantifierStatus;
      if (node.Op.Equals(VCExpressionGenerator.NotOp))
      {
        quantifierStatus = quantifierStatus == QuantifierStatus.Exists ? QuantifierStatus.Forall : QuantifierStatus.Exists;
      }
      if (node.Op.Equals(VCExpressionGenerator.ImpliesOp))
      {
        quantifierStatus = QuantifierStatus.None;
      }
      if (node.Op.Equals(VCExpressionGenerator.EqOp) || node.Op.Equals(VCExpressionGenerator.NeqOp))
      {
        if (node[0].Type.Equals(Type.Bool))
        {
          quantifierStatus = QuantifierStatus.None;
        }
      }
      if (node.Op.Equals(VCExpressionGenerator.IfThenElseOp))
      {
        quantifierStatus = QuantifierStatus.None;
      }
      var returnExpr = base.Visit(node, arg);
      quantifierStatus = savedQuantifierStatus;
      return returnExpr;
    }

    public override VCExpr Visit(VCExprLet node, bool arg)
    {
      var savedQuantifierStatus = quantifierStatus;
      quantifierStatus = QuantifierStatus.None;
      var returnExpr = base.Visit(node, arg);
      quantifierStatus = savedQuantifierStatus;
      return returnExpr;
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      if (node.TypeParameters.Count == 0 && 
          (node.Quan == Quantifier.ALL && quantifierStatus == QuantifierStatus.Forall ||
          node.Quan == Quantifier.EX && quantifierStatus == QuantifierStatus.Exists))
      {
        return PerformSkolemization(node, arg);
      }
      var savedQuantifierStatus = quantifierStatus;
      quantifierStatus = QuantifierStatus.None;
      var returnExpr = base.Visit(node, arg);
      quantifierStatus = savedQuantifierStatus;
      return returnExpr;
    }

    private VCExpr PerformSkolemization(VCExprQuantifier node, bool arg)
    {
      var oldToNew = qiEngine.FreshSkolemConstants(node);
      foreach (var x in node.BoundVars)
      {
        bound.Add(x, oldToNew[x]);
      }
      var expr = base.Visit(node, arg);
      foreach (var x in node.BoundVars)
      {
        bound.Remove(x);
      }
      return expr;
    }
  }
  
  class Factorizer : MutatingVCExprVisitor<bool>
  {
    private QuantifierInstantiationEngine qiEngine;
    private Quantifier quantifier;

    public static VCExpr Factorize(QuantifierInstantiationEngine qiEngine, Quantifier quantifier, VCExpr vcExpr)
    {
      var factorizer = new Factorizer(qiEngine, quantifier);
      return factorizer.Mutate(vcExpr, true);
    }

    private Factorizer(QuantifierInstantiationEngine qiEngine, Quantifier quantifier) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifier = quantifier;
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      if (node.Quan == quantifier)
      {
        return qiEngine.BindQuantifier(node);
      }
      return base.Visit(node, arg);
    }
  }
  
  class BindingCollector : TraversingVCExprVisitor<bool, bool>
  {
    public static HashSet<VCExprVar> CollectBindings(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr)
    {
      var bindingCollector = new BindingCollector(qiEngine);
      bindingCollector.Traverse(vcExpr, true);
      return bindingCollector.bindings;
    }

    private BindingCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.bindings = new HashSet<VCExprVar>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprVar> bindings;

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      if (qiEngine.IsQuantifierBinding(node))
      {
        bindings.Add(node);
      }
      return base.Visit(node, arg);
    }
  }
  
  class LambdaInstanceCollector : BoundVarTraversingVCExprVisitor<bool, bool>
  {
    public static Dictionary<Function, HashSet<List<VCExpr>>> CollectInstances(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr)
    {
      var lambdaInstanceCollector = new LambdaInstanceCollector(qiEngine);
      lambdaInstanceCollector.Traverse(vcExpr, true);
      var lambdaFunctionToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      foreach (var instance in lambdaInstanceCollector.instances)
      {
        var function = (instance.Op as VCExprBoogieFunctionOp).Func;
        if (!lambdaFunctionToInstances.ContainsKey(function))
        {
          lambdaFunctionToInstances[function] = new HashSet<List<VCExpr>>();
        }
        lambdaFunctionToInstances[function].Add(instance.UniformArguments.ToList());
      }
      return lambdaFunctionToInstances;
    }

    private LambdaInstanceCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.instances = new HashSet<VCExprNAry>();
      this.instancesOnStack = new Stack<VCExprNAry>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprNAry> instances;
    private Stack<VCExprNAry> instancesOnStack;

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }

    public override bool Visit(VCExprNAry node, bool arg)
    {
      if (node.Op is VCExprBoogieFunctionOp functionOp)
      {
        var function = functionOp.Func;
        if (function.OriginalLambdaExprAsString != null && qiEngine.BindLambdaFunction(function))
        {
          instances.Add(node);
          instancesOnStack.Push(node);
          var retVal = base.Visit(node, arg);
          instancesOnStack.Pop();
          return retVal;
        }
      }
      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      if (BoundTermVars.Contains(node))
      {
        foreach (var instance in instancesOnStack)
        {
          instances.Remove(instance);
        }
      }
      return base.Visit(node, arg);
    }
  }
}