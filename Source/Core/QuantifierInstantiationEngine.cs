using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace VC
{
  public class QuantifierInstantiationEngine
  {
    /*
     * The algorithm implemented by QuantifierInstantiationEngine is a fixpoint. There are three phases.
     *
     * Start:
     *   - find instantiation sources in commands
     *   - skolemize quantifiers in the expressions in commands
     *
     * At this point, a collection of quantifiers to be instantiated and a collection of instantiation sources
     * are installed.
     *
     * Execute: Repeatedly, instantiate quantifiers based on instantiation sources, skolemize and install new quantifiers
     * that are discovered, and install new instantiation sources.
     *
     * Finish:
     *   - Rewrite quantifiers based on the discovered instances. Forall quantifiers are rewritten as a conjunction of
     *     the original quantifier and the instances. Exists quantifiers are rewritten as a disjunction of the original
     *     quantifier and the instances.
     *   - Add all skolem constants generated as local variables of impl.
     *   - Add instances of the axioms for lambdas as assume statements in the starting block of impl.
     */
    
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
    
    public static void Instantiate(Implementation impl)
    {
      if (!InstantiationSourceChecker.HasInstantiationSources(impl))
      {
        return;
      }
      var qiEngine = new QuantifierInstantiationEngine(impl);
      qiEngine.Start();     // initialize data structures
      qiEngine.Execute();   // execute fixpoint
      qiEngine.Finish();    // install generated instances in impl  
    }

    public static HashSet<string> FindInstantiationHints(ICarriesAttributes o)
    {
      var labels = new HashSet<string>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "inst_at")
        {
          iter.Params.OfType<string>().Iter(x => labels.Add(x));
        }
        iter = iter.Next;
      }
      return labels;
    }

    public static Dictionary<string, HashSet<Expr>> FindInstantiationSources(ICarriesAttributes o)
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
      var boundVariableToLabels = lambdaDefinitionExpr.Dummies.ToDictionary(x => x, x => FindInstantiationHints(x));
      if (Enumerable
        .Range(lambdaFunction.InParams.Count, lambdaDefinitionExpr.Dummies.Count - lambdaFunction.InParams.Count)
        .Any(i => boundVariableToLabels[lambdaDefinitionExpr.Dummies[i]].Count == 0))
      {
        return false;
      }
      lambdaDefinition[lambdaFunction] = lambdaDefinitionExpr;
      quantifierInstantiationInfo[lambdaDefinitionExpr] = new QuantifierInstantiationInfo(boundVariableToLabels);
      return true;
    }

    public Expr BindQuantifier(QuantifierExpr quantifierExpr)
    {
      if (quantifierExpr.TypeParameters.Count > 0)
      {
        return quantifierExpr;
      }
      var boundVariableToLabels = quantifierExpr.Dummies.ToDictionary(x => x, x => FindInstantiationHints(x));
      if (boundVariableToLabels.Any(kv => kv.Value.Count == 0))
      {
        return quantifierExpr;
      }
      var v = new BoundVariable(Token.NoToken,
        new TypedIdent(Token.NoToken, $"{quantifierBindingNamePrefix}{quantifierBinding.Count}", Type.Bool));
      quantifierBinding[v] = quantifierExpr;
      quantifierInstantiationInfo[quantifierExpr] = new QuantifierInstantiationInfo(boundVariableToLabels);
      return Expr.Ident(v);
    }

    public Dictionary<Variable, Expr> FreshSkolemConstants(BinderExpr binderExpr)
    {
      var variableMapping = binderExpr.Dummies.ToDictionary(v => v, v => FreshSkolemConstant(v));
      var substMap = variableMapping.ToDictionary(kv => kv.Key, kv => (Expr) Expr.Ident(kv.Value));
      var subst = Substituter.SubstitutionFromDictionary(substMap);
      AddInstancesForLabels(binderExpr, subst);
      return substMap;
    }

    public bool IsQuantifierBinding(Variable variable)
    {
      return this.quantifierBinding.ContainsKey(variable);
    }

    private Variable FreshSkolemConstant(Variable variable)
    {
      var skolemConstant = new LocalVariable(Token.NoToken,
        new TypedIdent(Token.NoToken, $"{skolemConstantNamePrefix}{skolemConstants.Count}", variable.TypedIdent.Type));
      skolemConstants.Add(skolemConstant);
      return skolemConstant;
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

    private static void AddDictionary<T,U>(Dictionary<T, HashSet<U>> @from, Dictionary<T, HashSet<U>> to)
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
    
    private void Start()
    {
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().Iter(predicateCmd =>
      {
        AddDictionary(FindInstantiationSources(predicateCmd), labelToInstances);
        predicateCmd.Expr = Skolemizer.Skolemize(this,
          predicateCmd is AssumeCmd ? InstStatus.SkolemizeExists : InstStatus.SkolemizeForall, predicateCmd.Expr);
        AddDictionary(LambdaInstanceCollector.CollectInstances(this, predicateCmd.Expr), lambdaToInstances);
      }));
    }

    private void Execute()
    {
      while (labelToInstances.Count > 0)
      {
        var currLabelToInstances = this.labelToInstances;
        this.labelToInstances = new Dictionary<string, HashSet<Expr>>();
        AddDictionary(currLabelToInstances, accLabelToInstances);

        var currLambdaToInstances = this.lambdaToInstances;
        this.lambdaToInstances = new Dictionary<Function, HashSet<List<Expr>>>();
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
            .SelectMany(label => accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<Expr>()).ToHashSet());
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
            .SelectMany(label => accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<Expr>()).ToHashSet());
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
      AddInstancesForLabels(quantifierExpr, subst);
    }
    
    private void AddInstancesForLabels(ICarriesAttributes o, Substitution subst)
    {
      FindInstantiationSources(o).Iter(kv =>
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
    SkolemizeForall,  // skolemize forall quantifiers
    SkolemizeExists,  // skolemize exists quantifiers
    None,             // do not skolemize quantifiers
  }

  class Skolemizer : Duplicator
  {
    /*
     * The method Skolemize performs best-effort skolemization of the input expression expr.
     * If instStatus = InstStatus.Forall, a quantifier F embedded in expr is skolemized
     * provided it can be proved that F is a forall quantifier in the NNF version of expr.
     * If instStatus = InstStatus.Exists, a quantifier F embedded in expr is skolemized
     * provided it can be proved that F is an exists quantifier in the NNF version of expr.
     *
     * Factorization is performed on the resulting expression.
     */
    public static Expr Skolemize(QuantifierInstantiationEngine qiEngine, InstStatus instStatus, Expr expr)
    {
      Contract.Requires(instStatus != InstStatus.None);
      var skolemizer = new Skolemizer(qiEngine, instStatus);
      var skolemizedExpr = skolemizer.VisitExpr(expr);
      return Factorizer.Factorize(qiEngine,
        instStatus == InstStatus.SkolemizeExists ? InstStatus.SkolemizeForall : InstStatus.SkolemizeExists,
        skolemizedExpr);
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
      var ifThenElse = node.Fun as IfThenElse;
      if (ifThenElse != null)
      {
        instStatus = InstStatus.None;
      }
      var returnExpr = base.VisitNAryExpr(node);
      instStatus = savedInstStatus;
      return returnExpr;
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      var savedInstStatus = instStatus;
      instStatus = InstStatus.None;
      var returnExpr = base.VisitLetExpr(node);
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
      var oldToNew = qiEngine.FreshSkolemConstants(node);
      foreach (var x in node.Dummies)
      {
        bound.Add(x, oldToNew[x]);
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
    /* 
     * The method Factorize factors out quantified expressions in expr replacing them with a bound variable.
     * The binding between the bound variable and the quantifier replaced by it is registered in qiEngine.
     * If instStatus == InstStatus.Forall, forall quantifiers are factorized.
     * If instStatus == InstStatus.Exists, exists quantifiers are factorized.
     */
    
    private QuantifierInstantiationEngine qiEngine;
    private InstStatus instStatus;

    public static Expr Factorize(QuantifierInstantiationEngine qiEngine, InstStatus instStatus, Expr expr)
    {
      Contract.Assert(instStatus != InstStatus.None);
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
      if (instStatus == InstStatus.SkolemizeForall)
      {
        return qiEngine.BindQuantifier(node);
      }

      return base.VisitForallExpr(node);
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      if (instStatus == InstStatus.SkolemizeExists)
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
        if (function.OriginalLambdaExprAsString != null && 
            !VariableCollector.Collect(node.Args).OfType<BoundVariable>().Any() &&
            qiEngine.BindLambdaFunction(function))
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

  class InstantiationSourceChecker : ReadOnlyVisitor
  {
    private bool hasInstances;

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
      if (QuantifierInstantiationEngine.FindInstantiationSources(node).Count > 0)
      {
        hasInstances = true;
      }
      return base.VisitQuantifierExpr(node);
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      if (cmdSeq.OfType<ICarriesAttributes>()
        .Any(cmd => QuantifierInstantiationEngine.FindInstantiationSources(cmd).Count > 0))
      {
        hasInstances = true;
      }
      return base.VisitCmdSeq(cmdSeq);
    }
  }
}