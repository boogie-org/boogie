using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie.VCExprAST
{
  public class QuantifierInstantiationEngine
  {
    /*
     * The algorithm implemented by QuantifierInstantiationEngine is a fixpoint. There are three phases.
     *
     * Start:
     *   - find instantiation sources in commands
     *   - skolemize quantifiers in the verification condition
     * At this point, a collection of quantifiers to be instantiated and a collection of instances
     * are installed.
     *
     * Execute: Repeatedly, instantiate quantifiers based on existing instances, skolemize and install new quantifiers
     * that are discovered, instantiate set extensionality axioms, and install new instances discovered.
     *
     * Finish:
     *   - Rewrite quantifiers based on the discovered instances. Forall quantifiers are rewritten as a conjunction of
     *     the original quantifier and the instances. Exists quantifiers are rewritten as a disjunction of the original
     *     quantifier and the instances. Dropping the original requires a suitable polarity.
     *   - Add instances of the axioms for lambdas and set extensionality as assumptions.
     *   - Omit background axioms containing pool quantifiers that produced instances, unless KeepQuantifier is set.
     */

    private class QuantifierInstantiationInfo
    {
      public HashSet<string> relevantLabels;
      public Dictionary<List<VCExpr>, VCExpr> instances;
      public Polarity polarity;

      public QuantifierInstantiationInfo(Dictionary<VCExprVar, HashSet<string>> boundVariableToLabels, Polarity polarity)
      {
        this.relevantLabels = boundVariableToLabels.Values.SelectMany(x => x).ToHashSet();
        this.instances = new Dictionary<List<VCExpr>, VCExpr>(new ListComparer<VCExpr>());
        this.polarity = polarity;
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
    private readonly Dictionary<(VCExpr Left, VCExpr Right), VCExpr> setEqualityAxioms = new(new SetEqualityComparer());
    private readonly Queue<(VCExpr Left, VCExpr Right)> pendingSetEqualities = new();
    private readonly Dictionary<Type, HashSet<VCExprVar>> setEqualityWitnesses = new();
    private readonly HashSet<int> instantiatedPoolQuantifiers = new();
    private string quantifierBindingNamePrefix;
    private string skolemConstantNamePrefix;
    internal VCExpressionGenerator vcExprGen;
    private Boogie2VCExprTranslator exprTranslator;
    internal static ConcurrentDictionary<string, ConcurrentBag<Type>> labelToTypes = new(); // pool name may map to multiple types

    public static VCExpr Instantiate(Implementation impl, VCExpressionGenerator vcExprGen,
      Boogie2VCExprTranslator exprTranslator, VCExpr vcExpr,
      IReadOnlyList<VCExpr> axioms, out VCExpr queryAxioms)
    {
      queryAxioms = null;
      if (!InstantiationSourceChecker.HasInstantiationSources(impl))
      {
        return vcExpr;
      }
      var qiEngine = new QuantifierInstantiationEngine(vcExprGen, exprTranslator);
      var result = qiEngine.Execute(impl, vcExpr);
      if (!exprTranslator.GenerationOptions.Options.KeepQuantifier && qiEngine.instantiatedPoolQuantifiers.Count > 0)
      {
        var retainedAxioms = new List<VCExpr>();
        foreach (var axiom in axioms)
        {
          var finder = new InstantiatedQuantifierFinder();
          finder.Traverse(axiom, qiEngine.instantiatedPoolQuantifiers);
          if (!finder.Found)
          {
            retainedAxioms.Add(axiom);
          }
        }
        if (retainedAxioms.Count < axioms.Count)
        {
          queryAxioms = vcExprGen.NAry(VCExpressionGenerator.AndOp, retainedAxioms);
        }
      }
      return result;
    }

    private sealed class InstantiatedQuantifierFinder : TraversingVCExprVisitor<bool, HashSet<int>>
    {
      public bool Found { get; private set; }

      public override bool Visit(VCExprQuantifier node, HashSet<int> instantiatedQuantifiers)
      {
        Found |= instantiatedQuantifiers.Contains(node.Info.uniqueId);
        return Found || base.Visit(node, instantiatedQuantifiers);
      }

      protected override bool StandardResult(VCExpr node, HashSet<int> instantiatedQuantifiers)
      {
        return false;
      }
    }

    private QuantifierInstantiationEngine(VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator exprTranslator)
    {
      this.quantifierBinding = new Dictionary<VCExprVar, VCExprQuantifier>();
      this.lambdaDefinition = new Dictionary<Function, VCExprQuantifier>();
      this.quantifierInstantiationInfo = new Dictionary<VCExprQuantifier, QuantifierInstantiationInfo>(ReferenceEqualityComparer.Instance);
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
      var attrCmd = cmd as ICarriesAttributes;
      if (attrCmd == null)
      {
        return;
      }
      attrCmd.Attributes = CivlAttributes.ApplySubstitutionToPoolHints(incarnationSubst, attrCmd.Attributes);
    }

    internal VCExpr BindQuantifier(VCExprQuantifier node, Polarity polarity)
    {
      var v = new VCExprVar($"{quantifierBindingNamePrefix}{quantifierBinding.Count}", Type.Bool);
      quantifierBinding[v] = node;
      Contract.Assert(!quantifierInstantiationInfo.ContainsKey(node));
      quantifierInstantiationInfo[node] = new QuantifierInstantiationInfo(node.Info.instantiationLabels, polarity);
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

    internal static bool IsSetType(Type type)
    {
      return type.IsMap && type.AsMap.TypeParameters.Count == 0 &&
             type.AsMap.Arguments.Count == 1 && type.AsMap.Result.IsBool;
    }

    internal void AddSetEquality(VCExprNAry equality)
    {
      var pair = (Left: equality[0], Right: equality[1]);
      if (setEqualityAxioms.ContainsKey(pair))
      {
        return;
      }
      var indexType = pair.Left.Type.AsMap.Arguments[0];
      var witness = FreshSkolemConstant(vcExprGen.Variable("setEqualityWitness", indexType));
      setEqualityAxioms.Add(pair, vcExprGen.Or(vcExprGen.Eq(pair.Left, pair.Right),
        vcExprGen.Neq(vcExprGen.Select(pair.Left, witness), vcExprGen.Select(pair.Right, witness))));
      pendingSetEqualities.Enqueue(pair);
      if (!setEqualityWitnesses.TryGetValue(indexType, out var witnesses))
      {
        witnesses = new HashSet<VCExprVar>(ReferenceEqualityComparer.Instance);
        setEqualityWitnesses.Add(indexType, witnesses);
      }
      witnesses.Add(witness);
    }

    private class SetEqualityComparer : IEqualityComparer<(VCExpr Left, VCExpr Right)>
    {
      public bool Equals((VCExpr Left, VCExpr Right) first, (VCExpr Left, VCExpr Right) second)
      {
        return first.Left.Equals(second.Left) && first.Right.Equals(second.Right) ||
               first.Left.Equals(second.Right) && first.Right.Equals(second.Left);
      }

      public int GetHashCode((VCExpr Left, VCExpr Right) pair)
      {
        return pair.Left.GetHashCode() ^ pair.Right.GetHashCode();
      }

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
      lambdaDefinition[lambdaFunction] = translatedExpr;
      quantifierInstantiationInfo[translatedExpr] = new QuantifierInstantiationInfo(boundVariableToLabels, Polarity.Positive);
      lambdaToInstances[lambdaFunction] = new HashSet<List<VCExpr>>(new ListComparer<VCExpr>());
      return true;
    }

    public void AddLambdaInstances(Dictionary<Function, HashSet<List<VCExpr>>> lambdaFunctionToInstances)
    {
      AddDictionary(lambdaFunctionToInstances, this.lambdaToInstances);
    }

    public static HashSet<string> FindInstantiationHints(Variable v)
    {
      var labels = new HashSet<string>();
      for(var iter = v.Attributes; iter != null; iter = iter.Next)
      {
        if (iter.Key != "pool")
        {
          continue;
        }

        var tok = iter.tok;
        foreach(var x in iter.Params)
        {
          if (x is string poolName)
          {
            labels.Add(poolName);
            var types = labelToTypes.GetOrAdd(poolName, _ => new());
            
            types.Add(v.TypedIdent.Type);
          }
          else
          {
            Console.WriteLine($"{tok.filename}({tok.line},{tok.col}): expected pool name");
          }
        }
      }
      return labels;
    }
    
    public static Dictionary<string, HashSet<VCExpr>> FindInstantiationSources(ICarriesAttributes o, Boogie2VCExprTranslator exprTranslator)
    {
      var freshInstances = new Dictionary<string, HashSet<VCExpr>>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "add_to_pool" && iter.Params.Count > 1)
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
      @from.ForEach(kv =>
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
      @from.ForEach(kv =>
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
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().ForEach(predicateCmd =>
      {
        AddDictionary(FindInstantiationSources(predicateCmd, exprTranslator), labelToInstances);
      }));
      vcExpr = Skolemizer.Skolemize(this, Polarity.Negative, vcExpr);
      while (labelToInstances.Count > 0 || lambdaToInstances.Count > 0 || pendingSetEqualities.Count > 0)
      {
        /*
         * Each iteration of this loop
         * (1) moves the contents of labelToInstances into accLabelToInstances
         * (2) moves the contents of lambdaToInstances into accLambdaToInstances
         * (3) processes pending set extensionality instances and their index witnesses
         * (4) instantiates lambdas in lambdaDefinition against accLabelToInstances, accLambdaToInstances,
         *     and the set equality witnesses
         *     and quantifiers in quantifierBinding against accLabelToInstances to a shared inner fixpoint.
         * Steps (3) and (4) could add more entries to quantifierBinding and lambdaDefinition.
         * These entries are handled by the inner fixpoint using the accumulated instances.
         * Steps (3) and (4) could also discover set equalities or re-populate labelToInstances and lambdaToInstances;
         * these new entries are handled in the next iteration of this top-level loop.
         */
        AddDictionary(labelToInstances, accLabelToInstances);
        labelToInstances = new Dictionary<string, HashSet<VCExpr>>();

        AddDictionary(lambdaToInstances, accLambdaToInstances);
        lambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();

        while (pendingSetEqualities.Count > 0)
        {
          var pair = pendingSetEqualities.Dequeue();
          setEqualityAxioms[pair] = Skolemizer.Skolemize(this, Polarity.Positive, setEqualityAxioms[pair]);
        }

        var visitedQuantifierBindings = new HashSet<VCExprVar>(ReferenceEqualityComparer.Instance);
        var visitedLambdaFunctions = new HashSet<Function>(ReferenceEqualityComparer.Instance);
        while (visitedQuantifierBindings.Count < quantifierBinding.Count ||
               visitedLambdaFunctions.Count < lambdaDefinition.Count)
        {
          // Instantiation can register new lambdas and quantifiers, so iterate over snapshots.
          foreach (var lambdaFunction in lambdaDefinition.Keys.ToList())
          {
            if (visitedLambdaFunctions.Contains(lambdaFunction))
            {
              continue;
            }
            visitedLambdaFunctions.Add(lambdaFunction);
            if (accLambdaToInstances.TryGetValue(lambdaFunction, out var instances) && instances.Count > 0)
            {
              InstantiateLambdaDefinition(lambdaFunction);
            }
          }

          foreach (var v in quantifierBinding.Keys.ToList())
          {
            if (visitedQuantifierBindings.Contains(v))
            {
              continue;
            }
            visitedQuantifierBindings.Add(v);
            var quantifierExpr = quantifierBinding[v];
            var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
            if (quantifierInfo.relevantLabels.Overlaps(accLabelToInstances.Keys))
            {
              InstantiateQuantifier(quantifierExpr);
            }
          }
        }
      }

      var generatedAxioms = vcExprGen.NAry(VCExpressionGenerator.AndOp, lambdaDefinition.Values
        .SelectMany(quantifierExpr =>
          quantifierInstantiationInfo[quantifierExpr].instances.Values.ToList())
        .Concat(setEqualityAxioms.Values).ToList());
      return LetConvert(vcExprGen.Implies(generatedAxioms, vcExpr));
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
      var info = quantifierInstantiationInfo[quantifierExpr];
      var instances = info.instances;
      var keepQuantifier = exprTranslator.GenerationOptions.Options.KeepQuantifier;
      if (quantifierExpr.Quan == Quantifier.ALL)
      {
        var instantiatedConjuncts = vcExprGen.NAry(VCExpressionGenerator.AndOp, instances.Values.ToList());
        if (keepQuantifier || info.polarity != Polarity.Positive)
        {
          return vcExprGen.And(quantifierExpr, instantiatedConjuncts);
        }
        else
        {
          return instantiatedConjuncts;
        }
      }
      else
      {
        var instantiatedDisjuncts = vcExprGen.NAry(VCExpressionGenerator.OrOp, instances.Values.ToList());
        if (keepQuantifier || info.polarity != Polarity.Negative)
        {
          return vcExprGen.Or(quantifierExpr, instantiatedDisjuncts);
        }
        else
        {
          return instantiatedDisjuncts;
        }
      }
    }

    private void InstantiateLambdaDefinition(Function lambdaFunction)
    {
      var quantifierExpr = lambdaDefinition[lambdaFunction];
      var boundVariableToLabels = quantifierExpr.Info.instantiationLabels;
      var boundVariableToExprs = quantifierExpr.BoundVars.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          boundVariableToLabels.TryGetValue(boundVariable, out var labels) ? labels
            .SelectMany(label =>
              accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<VCExpr>()).ToHashSet()
            : new HashSet<VCExpr>());
      var resultType = lambdaFunction.OutParams[0].TypedIdent.Type;
      if (IsSetType(resultType) &&
          setEqualityWitnesses.TryGetValue(resultType.AsMap.Arguments[0], out var witnesses))
      {
        var indexVariable = quantifierExpr.BoundVars[lambdaFunction.InParams.Count];
        boundVariableToExprs[indexVariable].UnionWith(witnesses);
      }
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

      // Since a pool name may be used with multiple types, we have to prune invalid instances
      for (int i = 0; i < quantifierExpr.BoundVars.Count; i++)
      {
        if (!quantifierExpr.BoundVars[i].Type.Equals(instance[i].Type))
        {
          return;
        }
      }

      var subst = new VCExprSubstitution(
        Enumerable.Range(0, quantifierExpr.BoundVars.Count).ToDictionary(
          x => quantifierExpr.BoundVars[x],
          x => instance[x]), new Dictionary<TypeVariable, Type>());
      var substituter = new SubstitutingVCExprVisitor(vcExprGen);
      var instantiation = substituter.Mutate(quantifierExpr.Body, subst);
      quantifierInstantiationInfo.instances[new List<VCExpr>(instance)] =
        Skolemizer.Skolemize(this, quantifierInstantiationInfo.polarity, instantiation);
      // The following guard ensures that a lambda that is instantiated via set-equality witnesses
      // is not dropped by virtue of those instantiations.
      if (quantifierExpr.Info.instantiationLabels.Values.Any(labels => labels.Count > 0))
      {
        instantiatedPoolQuantifiers.Add(quantifierExpr.Info.uniqueId);
      }
    }
  }

  enum Polarity
  {
    Positive,
    Negative,
    Unknown,
  }
  
  class PolarityCollector : TraversingVCExprVisitor<Dictionary<VCExprVar, Polarity>, Polarity>
  {
    public static Dictionary<VCExprQuantifier, Polarity> CollectPolarities(VCExpr vcExpr, Polarity polarity)
    {
      var visitor = new PolarityCollector();
      visitor.Traverse(vcExpr, polarity);
      return visitor.quantifierPolarities;
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

    private Dictionary<VCExprQuantifier, Polarity> quantifierPolarities = new(ReferenceEqualityComparer.Instance);
    
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

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprLet node, Polarity arg)
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

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprQuantifier node, Polarity arg)
    {
      quantifierPolarities[node] = quantifierPolarities.TryGetValue(node, out var previous)
        ? Join(previous, arg)
        : arg;
      var result = node.Body.Accept(this, arg);
      foreach (var x in node.BoundVars)
      {
        result.Remove(x);
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

  class SkolemizableQuantifierCollector : TraversingVCExprVisitor<HashSet<VCExprQuantifier>, bool>
  {
    /*
     * Collect polarities, then dependencies on enclosing quantifiers, then select skolemizable
     * quantifiers with their dependencies selected first. Dependencies include pool-source expressions.
     * Let bindings are resolved during dependency collection but are not nodes in the dependency graph.
     */
    public static HashSet<VCExprQuantifier> CollectQuantifiers(VCExpr vcExpr, Polarity polarity)
    {
      var polarities = PolarityCollector.CollectPolarities(vcExpr, polarity);
      var visitor = new SkolemizableQuantifierCollector();
      visitor.Traverse(vcExpr, true);
      var quantifiers = new HashSet<VCExprQuantifier>(ReferenceEqualityComparer.Instance);
      var visited = new HashSet<VCExprQuantifier>(ReferenceEqualityComparer.Instance);

      void Collect(VCExprQuantifier quantifier)
      {
        if (!visited.Add(quantifier))
        {
          return;
        }
        var dependencies = visitor.quantifierDependencies[quantifier];
        foreach (var dependency in dependencies)
        {
          Collect(dependency);
        }
        if (quantifier.TypeParameters.Count == 0 &&
            polarities.TryGetValue(quantifier, out var quantifierPolarity) &&
            quantifierPolarity != Polarity.Unknown &&
            (quantifierPolarity == Polarity.Positive) == (quantifier.Quan == Quantifier.EX) &&
            dependencies.IsSubsetOf(quantifiers))
        {
          quantifiers.Add(quantifier);
        }
      }

      foreach (var quantifier in visitor.quantifierDependencies.Keys)
      {
        Collect(quantifier);
      }
      return quantifiers;
    }

    private Dictionary<VCExprQuantifier, HashSet<VCExprQuantifier>> quantifierDependencies = new(ReferenceEqualityComparer.Instance);
    private Dictionary<VCExprVar, HashSet<VCExprQuantifier>> variableDependencies = new();

    public override HashSet<VCExprQuantifier> Visit(VCExprNAry node, bool arg)
    {
      var result = new HashSet<VCExprQuantifier>(ReferenceEqualityComparer.Instance);
      foreach (var argument in node.UniformArguments)
      {
        result.UnionWith(argument.Accept(this, arg));
      }
      return result;
    }

    public override HashSet<VCExprQuantifier> Visit(VCExprVar node, bool arg)
    {
      return variableDependencies.TryGetValue(node, out var dependencies)
        ? new HashSet<VCExprQuantifier>(dependencies, ReferenceEqualityComparer.Instance)
        : new HashSet<VCExprQuantifier>(ReferenceEqualityComparer.Instance);
    }

    public override HashSet<VCExprQuantifier> Visit(VCExprLet node, bool arg)
    {
      foreach (var binding in node)
      {
        variableDependencies.Add(binding.V, binding.E.Accept(this, arg));
      }
      var result = node.Body.Accept(this, arg);
      foreach (var variable in node.BoundVars)
      {
        variableDependencies.Remove(variable);
      }
      return result;
    }

    public override HashSet<VCExprQuantifier> Visit(VCExprQuantifier node, bool arg)
    {
      foreach (var variable in node.BoundVars)
      {
        variableDependencies.Add(variable, new HashSet<VCExprQuantifier>(ReferenceEqualityComparer.Instance) { node });
      }
      var result = node.Body.Accept(this, arg);
      foreach (var expression in node.Info.instantiationExprs.Values.SelectMany(expressions => expressions))
      {
        result.UnionWith(expression.Accept(this, arg));
      }
      foreach (var variable in node.BoundVars)
      {
        variableDependencies.Remove(variable);
      }
      result.Remove(node);
      quantifierDependencies[node] = new HashSet<VCExprQuantifier>(result, ReferenceEqualityComparer.Instance);
      return result;
    }

    protected override HashSet<VCExprQuantifier> StandardResult(VCExpr node, bool arg)
    {
      return new HashSet<VCExprQuantifier>(ReferenceEqualityComparer.Instance);
    }
  }
  
  class SetEqualityCollector : BoundVarTraversingVCExprVisitor<bool, bool>
  {
    private readonly List<VCExprNAry> equalities = new();

    public static List<VCExprNAry> Collect(VCExpr expression)
    {
      var collector = new SetEqualityCollector();
      collector.Traverse(expression, true);
      return collector.equalities;
    }

    public override bool Visit(VCExprNAry node, bool arg)
    {
      if ((node.Op.Equals(VCExpressionGenerator.EqOp) || node.Op.Equals(VCExpressionGenerator.NeqOp)) &&
          QuantifierInstantiationEngine.IsSetType(node[0].Type))
      {
        var freeVariables = new FreeVariableCollector();
        freeVariables.Collect(node);
        if (!freeVariables.FreeTermVars.Any(BoundTermVars.ContainsKey) &&
            !freeVariables.FreeTypeVars.Any(BoundTypeVars.Contains))
        {
          equalities.Add(node);
        }
      }
      return base.Visit(node, arg);
    }

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }
  }

  class BooleanEqualityExpander : MutatingVCExprVisitor<bool>
  {
    public BooleanEqualityExpander(VCExpressionGenerator gen) : base(gen)
    {
    }

    protected override VCExpr UpdateModifiedNode(VCExprNAry originalNode,
      List<VCExpr> newSubExprs, bool changed, bool arg)
    {
      if ((originalNode.Op.Equals(VCExpressionGenerator.EqOp) ||
           originalNode.Op.Equals(VCExpressionGenerator.NeqOp)) && originalNode[0].Type.IsBool)
      {
        var duplicator = new SubstitutingVCExprVisitor(Gen);
        VCExpr Copy(VCExpr expr) => duplicator.Mutate(expr, new VCExprSubstitution());

        // Separate quantifier nodes keep the polarities of the two implications independent.
        var equality = Gen.And(
          Gen.Implies(Copy(newSubExprs[0]), Copy(newSubExprs[1])),
          Gen.Implies(Copy(newSubExprs[1]), Copy(newSubExprs[0])));
        return originalNode.Op.Equals(VCExpressionGenerator.NeqOp) ? Gen.Not(equality) : equality;
      }
      return base.UpdateModifiedNode(originalNode, newSubExprs, changed, arg);
    }
  }

  abstract class LetBindingScopeVisitor : MutatingVCExprVisitor<bool>
  {
    protected readonly List<VCExprLetBinding> letBindings = new();

    protected LetBindingScopeVisitor(VCExpressionGenerator gen) : base(gen)
    {
    }

    public override VCExpr Visit(VCExprLet node, bool arg)
    {
      var bindingByVariable = node.ToDictionary(binding => binding.V);
      var dependencies = new GraphUtil.Graph<VCExprLetBinding>();
      foreach (var binding in node)
      {
        dependencies.Nodes.Add(binding);
        foreach (var variable in FreeVariables(binding.E))
        {
          if (bindingByVariable.TryGetValue(variable, out var referencedBinding))
          {
            // Since binding depends on referencedBinding,
            // binding must appear before referencedBinding in letBindings.
            // Therefore, add an edge.
            dependencies.AddEdge(referencedBinding, binding);
          }
        }
      }
      var sortedBindings = dependencies.TopologicalSort();
      Contract.Assert(sortedBindings.Count == node.Length);
      var start = letBindings.Count;
      var bindings = new List<VCExprLetBinding>();
      foreach (var binding in sortedBindings)
      {
        // Visit the RHS of each binding before adding its variable to the
        // enclosing let scope. This traversal makes sure that let bindings
        // encountered during the traversal of the RHS are popped by the time
        // processing of this let expression continues.
        var translated = Gen.LetBinding(binding.V, binding.E.Accept(this, arg));
        bindings.Add(translated);
        letBindings.Add(translated);
      }
      var result = Gen.Let(bindings, node.Body.Accept(this, arg));
      letBindings.RemoveRange(start, letBindings.Count - start);
      return result;
    }

    protected VCExpr Close(VCExpr expression)
    {
      if (letBindings.Count == 0)
      {
        return expression;
      }
      var needed = FreeVariables(expression);
      for (int i = letBindings.Count - 1; i >= 0; i--)
      {
        var binding = letBindings[i];
        if (needed.Contains(binding.V))
        {
          needed.UnionWith(FreeVariables(binding.E));
        }
      }
      for (int i = letBindings.Count - 1; i >= 0; i--)
      {
        var binding = letBindings[i];
        if (needed.Contains(binding.V))
        {
          expression = Gen.Let(new List<VCExprLetBinding> { binding }, expression);
        }
      }
      return expression;
    }

    private static HashSet<VCExprVar> FreeVariables(VCExpr expression)
    {
      var collector = new PoolFreeVariableCollector();
      collector.Traverse(expression, true);
      return collector.FreeTermVars;
    }

    private class PoolFreeVariableCollector : FreeVariableCollector
    {
      protected override bool VisitAfterBinding(VCExprQuantifier node, bool arg)
      {
        // Pool metadata may be the only reference to an enclosing let variable.
        foreach (var expression in node.Info.instantiationExprs.Values.SelectMany(expressions => expressions))
        {
          expression.Accept(this, arg);
        }
        return base.VisitAfterBinding(node, arg);
      }
    }
  }

  class Skolemizer : LetBindingScopeVisitor
  {
    /*
     * The method Skolemize performs best-effort skolemization of the input expression expr.
     * Boolean equalities and disequalities are expanded into conjunctions of implications
     * and their negations first.
     * Factorization is performed on the resulting expression.
     */
    public static VCExpr Skolemize(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr)
    {
      vcExpr = new BooleanEqualityExpander(qiEngine.vcExprGen).Mutate(vcExpr, true);
      var skolemizer = new Skolemizer(qiEngine, polarity, vcExpr);
      var skolemizedExpr = skolemizer.Mutate(vcExpr, true);
      foreach (var equality in SetEqualityCollector.Collect(skolemizedExpr))
      {
        qiEngine.AddSetEquality(equality);
      }
      LambdaInstanceCollector.CollectInstances(qiEngine, skolemizedExpr);
      return Factorizer.Factorize(qiEngine, skolemizedExpr, polarity);
    }

    private Skolemizer(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifiers = SkolemizableQuantifierCollector.CollectQuantifiers(vcExpr, polarity);
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
      retExpr.Info.instantiationExprs.ForEach(kv =>
      {
        CollectionExtensions.ForEach(kv.Value, expr => { qiEngine.AddTerm(kv.Key, Close(expr.Accept(this, arg))); });
      });
      foreach (var x in node.BoundVars)
      {
        bound.Remove(x);
      }
      return retExpr.Body;
    }
  }
  
  class Factorizer : LetBindingScopeVisitor
  {
    /* 
     * The method Factorize factors out quantified expressions in expr replacing them with a bound variable.
     * The binding between the bound variable and the quantifier replaced by it is registered in qiEngine.
     * Needed enclosing let definitions are retained in bodies, triggers, and pool expressions.
     */
    
    private QuantifierInstantiationEngine qiEngine;
    private Dictionary<VCExprQuantifier, Polarity> quantifierPolarities;

    public static VCExpr Factorize(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr, Polarity polarity)
    {
      var factorizer = new Factorizer(qiEngine, PolarityCollector.CollectPolarities(vcExpr, polarity));
      return factorizer.Mutate(vcExpr, true);
    }

    private Factorizer(QuantifierInstantiationEngine qiEngine,
      Dictionary<VCExprQuantifier, Polarity> quantifierPolarities) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifierPolarities = quantifierPolarities;
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      if (!quantifierPolarities.TryGetValue(node, out var polarity))
      {
        return node;
      }
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
      return qiEngine.BindQuantifier(CloseOverLetBindings(node), polarity);
    }

    private VCExprQuantifier CloseOverLetBindings(VCExprQuantifier node)
    {
      if (letBindings.Count == 0)
      {
        return node;
      }

      var triggers = node.Triggers.Select(trigger =>
        Gen.Trigger(trigger.Pos, trigger.Exprs.Select(Close).ToList())).ToList();
      var sources = node.Info.instantiationExprs.ToDictionary(
        pair => pair.Key, pair => pair.Value.Select(Close).ToHashSet());
      var info = new VCQuantifierInfo(node.Info.qid, node.Info.uniqueId, node.Info.weight,
        node.Info.instantiationLabels, sources);
      return (VCExprQuantifier)Gen.Quantify(node.Quan, node.TypeParameters, node.BoundVars,
        triggers, info, Close(node.Body));
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
    public static void CollectInstances(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr)
    {
      var lambdaInstanceCollector = new LambdaInstanceCollector(qiEngine);
      lambdaInstanceCollector.Traverse(vcExpr, true);
      var lambdaFunctionToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      foreach (var instance in lambdaInstanceCollector.instances)
      {
        var function = (instance.Op as VCExprBoogieFunctionOp).Func;
        if (!lambdaFunctionToInstances.ContainsKey(function))
        {
          lambdaFunctionToInstances[function] = new HashSet<List<VCExpr>>(new ListComparer<VCExpr>());
        }
        lambdaFunctionToInstances[function].Add(instance.UniformArguments.ToList());
      }
      qiEngine.AddLambdaInstances(lambdaFunctionToInstances);
    }

    private LambdaInstanceCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.instances = new HashSet<VCExprNAry>();
      this.instancesOnStack = new Stack<Tuple<VCExprNAry, HashSet<VCExprVar>>>();
      this.letBoundVarsOnStack = new Stack<List<VCExprVar>>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprNAry> instances;
    private Stack<Tuple<VCExprNAry, HashSet<VCExprVar>>> instancesOnStack;
    private Stack<List<VCExprVar>> letBoundVarsOnStack;

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }

    private VCExprNAry Substitute(VCExprNAry vcExpr)
    {
      foreach (var letBoundVars in letBoundVarsOnStack)
      {
        var subst = new VCExprSubstitution(
          letBoundVars.ToDictionary(x => x, x => BoundTermVars[x]),
          new Dictionary<TypeVariable, Type>());
        var substituter = new SubstitutingVCExprVisitor(qiEngine.vcExprGen);
        vcExpr = (VCExprNAry) substituter.Mutate(vcExpr, subst);
      }
      return vcExpr;
    }
    
    public override bool Visit(VCExprNAry node, bool arg)
    {
      if (node.Op is VCExprBoogieFunctionOp functionOp)
      {
        var function = functionOp.Func;
        if (function.OriginalLambdaExprAsString != null && qiEngine.BindLambdaFunction(function))
        {
          // substitute all let-bound variables in the lambda expr
          var substExpr = Substitute(node);
          instances.Add(substExpr);
          // push the pair of substituted lambda expr and variables bound via quantifiers
          // if one of these bound variables is mentioned in the lambda term,
          // then this term is ineligible and should be removed
          instancesOnStack.Push(new Tuple<VCExprNAry, HashSet<VCExprVar>>(substExpr,
            BoundTermVars.Keys.Where(x => BoundTermVars[x] == null).ToHashSet()));
          var retVal = base.Visit(node, arg);
          instancesOnStack.Pop();
          return retVal;
        }
      }
      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      // check each lambda term going down the stack and remove ineligible terms if any
      // once an eligible term is found, all terms below it must be eligible as well
      foreach (var pair in instancesOnStack)
      {
        if (pair.Item2.Contains(node))
        {
          instances.Remove(pair.Item1);
        }
        else
        {
          break;
        }
      }
      return base.Visit(node, arg);
    }
    
    public override bool Visit(VCExprLet node, bool arg)
    {
      letBoundVarsOnStack.Push(node.BoundVars);
      var retVal = base.Visit(node, arg);
      letBoundVarsOnStack.Pop();
      return retVal;
    }
  }
  
  class InstantiationSourceChecker : ReadOnlyVisitor
  {
    private bool hasInstances;

    private void FindInstantiationSources(ICarriesAttributes o)
    {
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "add_to_pool")
        {
          if (iter.Params[0] is string poolName && QuantifierInstantiationEngine.labelToTypes.ContainsKey(poolName))
          {
            var tok = iter.tok;
            var poolTypes = QuantifierInstantiationEngine.labelToTypes[poolName];
            iter.Params.Skip(1).ForEach(x =>
            {
              if (x is Expr e && poolTypes.Contains(e.Type))
              {
                hasInstances = true;
              }
            });
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
      FindInstantiationSources(node);
      return base.VisitQuantifierExpr(node);
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      cmdSeq.OfType<PredicateCmd>().ForEach(FindInstantiationSources);
      return base.VisitCmdSeq(cmdSeq);
    }
  }
}
