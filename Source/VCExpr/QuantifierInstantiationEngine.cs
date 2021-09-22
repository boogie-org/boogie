using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie.VCExprAST
{
  public class QuantifierInstantiationEngine
  {
    /*
     * The algorithm implemented by QuantifierInstantiationEngine is a fixpoint. There are two phases.
     *
     * Start:
     *   - find instantiation sources in commands
     *   - skolemize quantifiers in the verification condition
     *
     * At this point, a collection of quantifiers to be instantiated and a collection of instances
     * are installed.
     *
     * Execute: Repeatedly, instantiate quantifiers based on existing instances, skolemize and install new quantifiers
     * that are discovered, and install new instances discovered.
     *
     * Finish:
     *   - Rewrite quantifiers based on the discovered instances. Forall quantifiers are rewritten as a conjunction of
     *     the original quantifier and the instances. Exists quantifiers are rewritten as a disjunction of the original
     *     quantifier and the instances.
     *   - Add instances of the axioms for lambdas as assume statements in the starting block of impl.
     */

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
      if (!InstantiationSourceChecker.HasInstantiationSources(impl))
      {
        return vcExpr;
      }
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
        if (iter.Key == "add_to_pool" && iter.Params.Count > 1)
        {
          var label = iter.Params[0] as string;
          if (label != null)
          {
            var newParams = new List<object> {label};
            for (int i = 1; i < iter.Params.Count; i++)
            {
              var instance = iter.Params[i] as Expr;
              if (instance != null)
              {
                instance = Substituter.Apply(incarnationSubst, instance);
                newParams.Add(instance);
              }
            }
            iter.ClearParams();
            iter.AddParams(newParams);
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

    public void AddTerm(string label, VCExpr term)
    {
      if (!labelToInstances.ContainsKey(label))
      {
        labelToInstances[label] = new HashSet<VCExpr>();
      }
      labelToInstances[label].Add(term);
    }

    public bool IsQuantifierBinding(VCExprVar vcExprVar)
    {
      return this.quantifierBinding.ContainsKey(vcExprVar);
    }

    public VCExprVar FreshSkolemConstant(VCExprVar variable)
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

    public static HashSet<string> FindInstantiationHints(ICarriesAttributes o)
    {
      var labels = new HashSet<string>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "pool")
        {
          iter.Params.OfType<string>().Iter(x => labels.Add(x));
        }
        iter = iter.Next;
      }
      return labels;
    }
    
    public static Dictionary<string, HashSet<VCExpr>> FindInstantiationSources(ICarriesAttributes o, string attrName, Boogie2VCExprTranslator exprTranslator)
    {
      var freshInstances = new Dictionary<string, HashSet<VCExpr>>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == attrName && iter.Params.Count > 1)
        {
          var label = iter.Params[0] as string;
          if (label != null)
          {
            for (int i = 1; i < iter.Params.Count; i++)
            {
              var instance = iter.Params[i] as Expr;
              if (instance != null)
              {
                if (!freshInstances.ContainsKey(label))
                {
                  freshInstances[label] = new HashSet<VCExpr>();
                }
                freshInstances[label].Add(exprTranslator.Translate(instance));
              }
            }
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
    
    private static void AddDictionary<T, U>(Dictionary<T, HashSet<List<U>>> @from, Dictionary<T, HashSet<List<U>>> to)
    {
      @from.Iter(kv =>
      {
        if (!to.ContainsKey(kv.Key))
        {
          to[kv.Key] = new HashSet<List<U>>(new ListComparer<U>());
        }
        to[kv.Key].UnionWith(@from[kv.Key]);
      });
    }
    
    private VCExpr Execute(Implementation impl, VCExpr vcExpr)
    {
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().Iter(predicateCmd =>
      {
        AddDictionary(FindInstantiationSources(predicateCmd, "add_to_pool", exprTranslator), labelToInstances);
      }));
      vcExpr = Skolemizer.Skolemize(this, Polarity.Negative, vcExpr);
      lambdaToInstances = LambdaInstanceCollector.CollectInstances(this, vcExpr);
      while (labelToInstances.Count > 0)
      {
        var currLabelToInstances = labelToInstances;
        labelToInstances = new Dictionary<string, HashSet<VCExpr>>();
        AddDictionary(currLabelToInstances, accLabelToInstances);

        var currLambdaToInstances = lambdaToInstances;
        lambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
        AddDictionary(currLambdaToInstances, accLambdaToInstances);

        var visitedQuantifierBindings = new HashSet<VCExprVar>();
        while (visitedQuantifierBindings.Count < quantifierBinding.Count)
        {
          foreach (var v in quantifierBinding.Keys)
          {
            if (visitedQuantifierBindings.Contains(v))
            {
              continue;
            }

            visitedQuantifierBindings.Add(v);
            var quantifierExpr = quantifierBinding[v];
            var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
            if (quantifierInfo.relevantLabels.Overlaps(currLabelToInstances.Keys))
            {
              InstantiateQuantifier(quantifierExpr);
            }
          }
        }

        var visitedLambdaFunctions = new HashSet<Function>();
        while (visitedLambdaFunctions.Count < lambdaDefinition.Count)
        {
          foreach (var lambdaFunction in lambdaDefinition.Keys)
          {
            if (visitedLambdaFunctions.Contains(lambdaFunction))
            {
              continue;
            }

            visitedLambdaFunctions.Add(lambdaFunction);
            var quantifierExpr = lambdaDefinition[lambdaFunction];
            var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
            if (quantifierInfo.relevantLabels.Overlaps(currLabelToInstances.Keys) ||
                currLambdaToInstances[lambdaFunction].Count > 0)
            {
              InstantiateLambdaDefinition(lambdaFunction);
            }
          }
        }
      }

      var lambdaAxioms = vcExprGen.NAry(VCExpressionGenerator.AndOp, lambdaDefinition.Values
        .SelectMany(quantifierExpr =>
          quantifierInstantiationInfo[quantifierExpr].instances.Values.ToList()).ToList());
      return vcExprGen.Implies(lambdaAxioms, LetConvert(vcExpr));
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
      quantifierInstantiationInfo.instances[new List<VCExpr>(instance)] =
        Skolemizer.Skolemize(this, quantifierExpr.Quan == Quantifier.ALL ? Polarity.Positive : Polarity.Negative,
          instantiation);
    }
  }

  enum Polarity
  {
    Positive,
    Negative,
    Unknown,
  }
  
  class QuantifierCollector : BoundVarTraversingVCExprVisitor<Dictionary<VCExprVar, Polarity>, Polarity>
  {
    public static HashSet<VCExprQuantifier> CollectQuantifiers(VCExpr vcExpr, Polarity polarity)
    {
      var visitor = new QuantifierCollector();
      visitor.Traverse(vcExpr, polarity);
      return visitor.quantifiers;
    }

    public static Polarity Flip(Polarity polarity)
    {
      switch (polarity)
      {
        case Polarity.Positive:
          return Polarity.Negative;
        case Polarity.Negative:
          return Polarity.Positive;
        case Polarity.Unknown:
          return Polarity.Unknown;
      }
      Contract.Assert(false);
      return Polarity.Unknown;
    }

    private HashSet<VCExprQuantifier> quantifiers = new HashSet<VCExprQuantifier>();
    
    private static Polarity Join(Polarity first, Polarity second)
    {
      if (first == second)
      {
        return first;
      }
      return Polarity.Unknown;
    }

    private static Dictionary<VCExprVar, Polarity> Join(IEnumerable<Dictionary<VCExprVar, Polarity>> elems)
    {
      var result = new Dictionary<VCExprVar, Polarity>();
      foreach (var elem in elems)
      {
        foreach (var x in elem.Keys)
        {
          if (result.ContainsKey(x))
          {
            result[x] = Join(result[x], elem[x]);
          }
          else
          {
            result[x] = elem[x];
          }
        }
      }
      return result;
    }
    
    private static Dictionary<VCExprVar, Polarity> Join(params Dictionary<VCExprVar, Polarity>[] elems)
    {
      return Join(elems.Select(x => x));
    }
    
    public override Dictionary<VCExprVar, Polarity> Visit(VCExprNAry node, Polarity arg)
    {
      if (arg != Polarity.Unknown)
      {
        if (node.Op.Equals(VCExpressionGenerator.NotOp))
        {
          return node[0].Accept(this, Flip(arg));
        }
        if (node.Op.Equals(VCExpressionGenerator.AndOp) || node.Op.Equals(VCExpressionGenerator.OrOp))
        {
          return Join(node[0].Accept(this, arg), node[1].Accept(this, arg));
        }
        if (node.Op.Equals(VCExpressionGenerator.ImpliesOp))
        {
          return Join(node[0].Accept(this, Flip(arg)), node[1].Accept(this, arg));
        }
      }
      return Join(node.UniformArguments.Select(x => x.Accept(this, Polarity.Unknown)));
    }

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprVar node, Polarity arg)
    {
      return new Dictionary<VCExprVar, Polarity> {{node, arg}};
    }

    protected override Dictionary<VCExprVar, Polarity> VisitAfterBinding(VCExprLet node, Polarity arg)
    {
      var result = node.Body.Accept(this, arg);
      for (int i = node.Length - 1; i >= 0; i--)
      {
        if (result.ContainsKey(node[i].V))
        {
          result = Join(result, node[i].E.Accept(this, result[node[i].V]));
        }
      }
      foreach (var x in node.BoundVars)
      {
        result.Remove(x);
      }
      return result;
    }

    protected override Dictionary<VCExprVar, Polarity> VisitAfterBinding(VCExprQuantifier node, Polarity arg)
    {
      var result = node.Body.Accept(this, arg);
      foreach (var x in node.BoundVars)
      {
        result.Remove(x);
      }
      return result;
    }

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprQuantifier node, Polarity arg)
    {
      var result = base.Visit(node, arg);
      if (arg != Polarity.Unknown && !result.Keys.Intersect(BoundTermVars).Any())
      {
        if ((arg == Polarity.Positive) == (node.Quan == Quantifier.EX))
        {
          quantifiers.Add(node);
        }
      }
      return result;
    }

    protected override Dictionary<VCExprVar, Polarity> StandardResult(VCExpr node, Polarity arg)
    {
      return null;
    }

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprLiteral node, Polarity arg)
    {
      return new Dictionary<VCExprVar, Polarity>();
    }
  }
  
  class Skolemizer : MutatingVCExprVisitor<bool>
  {
    /*
     * The method Skolemize performs best-effort skolemization of the input expression expr.
     * If polarity == Polarity.Negative, a quantifier F embedded in expr is skolemized
     * provided it can be proved that F is a forall quantifier in the NNF version of expr.
     * If polarity == Polarity.Positive, a quantifier F embedded in expr is skolemized
     * provided it can be proved that F is an exists quantifier in the NNF version of expr.
     *
     * Factorization is performed on the resulting expression.
     */
    public static VCExpr Skolemize(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr)
    {
      var skolemizer = new Skolemizer(qiEngine, polarity, vcExpr);
      var skolemizedExpr = skolemizer.Mutate(vcExpr, true);
      return Factorizer.Factorize(qiEngine, QuantifierCollector.Flip(polarity), skolemizedExpr);
    }

    private Skolemizer(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifiers = QuantifierCollector.CollectQuantifiers(vcExpr, polarity);
      this.bound = new Dictionary<VCExprVar, VCExpr>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprQuantifier> quantifiers;
    private Dictionary<VCExprVar, VCExpr> bound;

    public override VCExpr Visit(VCExprVar node, bool arg)
    {
      if (bound.ContainsKey(node))
      {
        return bound[node];
      }
      return base.Visit(node, arg);
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      if (node.TypeParameters.Count == 0 && quantifiers.Contains(node))
      {
        return PerformSkolemization(node, arg);
      }
      return base.Visit(node, arg);
    }

    private VCExpr PerformSkolemization(VCExprQuantifier node, bool arg)
    {
      var oldToNew = node.BoundVars.ToDictionary(v => v, v => (VCExpr) qiEngine.FreshSkolemConstant(v));
      foreach (var x in node.BoundVars)
      {
        bound.Add(x, oldToNew[x]);
      }
      var retExpr = (VCExprQuantifier) base.Visit(node, arg);
      retExpr.Info.instantiationExprs.Iter(kv =>
      {
        kv.Value.Iter(expr => { qiEngine.AddTerm(kv.Key, expr.Accept(this, arg)); });
      });
      foreach (var x in node.BoundVars)
      {
        bound.Remove(x);
      }
      return retExpr.Body;
    }
  }
  
  class Factorizer : MutatingVCExprVisitor<bool>
  {
    /* 
     * The method Factorize factors out quantified expressions in expr replacing them with a bound variable.
     * The binding between the bound variable and the quantifier replaced by it is registered in qiEngine.
     * If polarity == Polarity.Positive, forall quantifiers are factorized.
     * If polarity == Polarity.Negative, exists quantifiers are factorized.
     */
    
    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprQuantifier> quantifiers;

    public static VCExpr Factorize(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr)
    {
      var factorizer = new Factorizer(qiEngine, polarity, vcExpr);
      return factorizer.Mutate(vcExpr, true);
    }

    private Factorizer(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifiers = QuantifierCollector.CollectQuantifiers(vcExpr, polarity);
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      if (quantifiers.Contains(node))
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
      var lambdaFunctionToInstances =
        lambdaInstanceCollector.lambdaFunctions.ToDictionary(
          x => x, x => new HashSet<List<VCExpr>>(new ListComparer<VCExpr>()));
      foreach (var instance in lambdaInstanceCollector.instances)
      {
        var function = (instance.Op as VCExprBoogieFunctionOp).Func;
        lambdaFunctionToInstances[function].Add(instance.UniformArguments.ToList());
      }
      return lambdaFunctionToInstances;
    }

    private LambdaInstanceCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.lambdaFunctions = new HashSet<Function>();
      this.instances = new HashSet<VCExprNAry>();
      this.instancesOnStack = new Stack<VCExprNAry>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<Function> lambdaFunctions;
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
          lambdaFunctions.Add(function);
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
  
  class InstantiationSourceChecker : ReadOnlyVisitor
  {
    private bool hasInstances;

    private void FindInstantiationSources(ICarriesAttributes o, string attrName)
    {
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == attrName)
        {
          var label = iter.Params[0] as string;
          var instance = iter.Params[1] as Expr;
          if (label != null && instance != null)
          {
            hasInstances = true;
          }
        }
        iter = iter.Next;
      }
    }
    
    public static bool HasInstantiationSources(Implementation impl)
    {
      var instanceChecker = new InstantiationSourceChecker();
      instanceChecker.VisitImplementation(impl);
      return instanceChecker.hasInstances;
    }

    private InstantiationSourceChecker()
    {
      this.hasInstances = false;
    }
    
    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      FindInstantiationSources(node, "skolem_add_to_pool");
      return base.VisitQuantifierExpr(node);
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      cmdSeq.OfType<ICarriesAttributes>().Iter(cmd => FindInstantiationSources(cmd, "add_to_pool"));
      return base.VisitCmdSeq(cmdSeq);
    }
  }
}
