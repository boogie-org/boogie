using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class MonomorphismChecker : ReadOnlyVisitor
  {
    public static bool DoesTypeCtorDeclNeedMonomorphization(TypeCtorDecl typeCtorDecl)
    {
      return typeCtorDecl.Arity > 0 && typeCtorDecl.FindStringAttribute("builtin") == null;
    }

    public static bool IsMonomorphic(Program program)
    {
      var checker = new MonomorphismChecker();
      checker.VisitProgram(program);
      return checker.isMonomorphic;
    }
    
    bool isMonomorphic;

    private MonomorphismChecker()
    {
      isMonomorphic = true;
    }
    
    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitDeclWithFormals(node);
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitBinderExpr(node);
    }

    public override Type VisitMapType(MapType node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitMapType(node);
    }

    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      if (DoesTypeCtorDeclNeedMonomorphization(node))
      {
        isMonomorphic = false;
      }
      return base.VisitTypeCtorDecl(node);
    }
  }

  class TypeDependencyVisitor : ReadOnlyVisitor
  {
    private Graph<TypeVariable> typeVariableDependencyGraph;
    private HashSet<Tuple<TypeVariable, TypeVariable>> strongDependencyEdges;
    private TypeVariable formal;
    private int insideContructedType;
    
    public TypeDependencyVisitor(Graph<TypeVariable> typeVariableDependencyGraph,
      HashSet<Tuple<TypeVariable, TypeVariable>> strongDependencyEdges, TypeVariable formal)
    {
      this.typeVariableDependencyGraph = typeVariableDependencyGraph;
      this.strongDependencyEdges = strongDependencyEdges;
      this.formal = formal;
      this.insideContructedType = 0;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      insideContructedType++;
      base.VisitCtorType(node);
      insideContructedType--;
      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      insideContructedType++;
      base.VisitMapType(node);
      insideContructedType--;
      return node;
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      typeVariableDependencyGraph.AddEdge(node, formal);
      if (insideContructedType > 0)
      {
        strongDependencyEdges.Add(new Tuple<TypeVariable, TypeVariable>(node, formal));
      }
      return base.VisitTypeVariable(node);
    }
  }

  public enum MonomorphizableStatus
  {
    UnhandledPolymorphism,
    ExpandingTypeCycle,
    Monomorphizable,
  }
  
  class MonomorphizableChecker : ReadOnlyVisitor
  {
    public static MonomorphizableStatus IsMonomorphizable(Program program,
      out Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated, out HashSet<Axiom> polymorphicFunctionAxioms)
    {
      var checker = new MonomorphizableChecker(program);
      checker.VisitProgram(program);
      axiomsToBeInstantiated = checker.axiomsToBeInstantiated;
      polymorphicFunctionAxioms = checker.polymorphicFunctionAxioms;
      if (!checker.isMonomorphizable)
      {
        return MonomorphizableStatus.UnhandledPolymorphism;
      }
      if (!checker.IsFinitelyInstantiable())
      {
        return MonomorphizableStatus.ExpandingTypeCycle;
      }
      return MonomorphizableStatus.Monomorphizable;
    }

    private Program program;
    private bool isMonomorphizable;
    private Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated;
    private HashSet<Axiom> polymorphicFunctionAxioms;
    private Graph<TypeVariable> typeVariableDependencyGraph; // (T,U) in this graph iff T flows to U
    private HashSet<Tuple<TypeVariable, TypeVariable>> strongDependencyEdges; // (T,U) in this set iff a type constructed from T flows into U

    private MonomorphizableChecker(Program program)
    {
      this.program = program;
      this.isMonomorphizable = true;
      this.polymorphicFunctionAxioms = program.TopLevelDeclarations.OfType<Function>()
        .Where(f => f.TypeParameters.Count > 0 && f.DefinitionAxiom != null)
        .Select(f => f.DefinitionAxiom).ToHashSet();
      this.axiomsToBeInstantiated = new Dictionary<Axiom, TypeCtorDecl>();
      this.typeVariableDependencyGraph = new Graph<TypeVariable>();
      this.strongDependencyEdges = new HashSet<Tuple<TypeVariable, TypeVariable>>();
    }

    private bool IsFinitelyInstantiable()
    {
      var sccs = new StronglyConnectedComponents<TypeVariable>(typeVariableDependencyGraph.Nodes,
        typeVariableDependencyGraph.Predecessors, typeVariableDependencyGraph.Successors);
      sccs.Compute();
      foreach (var scc in sccs)
      {
        foreach (var edge in strongDependencyEdges)
        {
          if (scc.Contains(edge.Item1) && scc.Contains(edge.Item2))
          {
            return false;
          }
        }
      }
      return true;
    }
    
    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is FunctionCall functionCall)
      {
        functionCall.Func.TypeParameters.Iter(t =>
        {
          var visitor = new TypeDependencyVisitor(typeVariableDependencyGraph, strongDependencyEdges, t);
          visitor.Visit(node.TypeParameters[t]);
        });
      }
      Visit(node.Type);
      return base.VisitNAryExpr(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      node.Proc.TypeParameters.Iter(t =>
      {
        var visitor = new TypeDependencyVisitor(typeVariableDependencyGraph, strongDependencyEdges, t);
        visitor.Visit(node.TypeParameters[t]);
      });
      return base.VisitCallCmd(node);
    }
    
    private void CheckTypeCtorInstantiatedAxiom(Axiom axiom, string typeCtorName)
    {
      var tcDecl = program.TopLevelDeclarations.OfType<TypeCtorDecl>().FirstOrDefault(tcd => tcd.Name == typeCtorName);
      if (tcDecl == null)
      {
        isMonomorphizable = false;
        return;
      }
      var forallExpr = (ForallExpr) axiom.Expr;
      if (tcDecl.Arity != forallExpr.TypeParameters.Count)
      {
        isMonomorphizable = false;
        return;
      }
      axiomsToBeInstantiated.Add(axiom, tcDecl);
      VisitExpr(forallExpr.Body);
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      if (polymorphicFunctionAxioms.Contains(node))
      {
        return node;
      }
      var typeCtorName = node.FindStringAttribute("ctor");
      if (typeCtorName == null || !(node.Expr is ForallExpr))
      {
        return base.VisitAxiom(node);
      }
      CheckTypeCtorInstantiatedAxiom(node, typeCtorName);
      return node;
    }

    public override Function VisitFunction(Function node)
    {
      if (polymorphicFunctionAxioms.Contains(node.DefinitionAxiom))
      {
        var forallExpr = (ForallExpr) node.DefinitionAxiom.Expr;
        LinqExtender.Map(node.TypeParameters, forallExpr.TypeParameters)
          .Iter(x => typeVariableDependencyGraph.AddEdge(x.Key, x.Value));
        VisitExpr(forallExpr.Body);
      }
      return base.VisitFunction(node);
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      LinqExtender.Map(node.Proc.TypeParameters, node.TypeParameters)
        .Iter(x => typeVariableDependencyGraph.AddEdge(x.Key, x.Value));
      return base.VisitImplementation(node);
    }

    public override Absy Visit(Absy node)
    {
      if (node is ICarriesAttributes attrNode && attrNode.Attributes != null)
      {
        VisitQKeyValue(attrNode.Attributes);
      }
      return base.Visit(node);
    }
    
    public override Type VisitTypeProxy(TypeProxy node)
    {
      if (node.ProxyFor == null)
      {
        isMonomorphizable = false;
      }
      else
      {
        Visit(TypeProxy.FollowProxy(node));
      }
      return node;
    }
  }

  public class InstantiationHintCollector : ReadOnlyVisitor
  {
    private Dictionary<TypeVariable, int> typeParameterIndexes;
    private List<Dictionary<NamedDeclaration, List<int>>> instantiationHints;

    public static List<Dictionary<NamedDeclaration, List<int>>> CollectInstantiationHints(QuantifierExpr quantifierExpr)
    {
      var instantiationHintCollector = new InstantiationHintCollector(quantifierExpr);
      instantiationHintCollector.VisitExpr(quantifierExpr);
      return instantiationHintCollector.instantiationHints;
    }

    private InstantiationHintCollector(QuantifierExpr quantifierExpr)
    {
      typeParameterIndexes = new Dictionary<TypeVariable, int>();
      for (int i = 0; i < quantifierExpr.TypeParameters.Count; i++)
      {
        typeParameterIndexes[quantifierExpr.TypeParameters[i]] = i;
      }
      instantiationHints = Enumerable.Range(0, quantifierExpr.TypeParameters.Count)
        .Select(_ => new Dictionary<NamedDeclaration, List<int>>()).ToList();
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is FunctionCall functionCall)
      {
        var actualTypeParams = node.TypeParameters.FormalTypeParams.Select(x => node.TypeParameters[x]).ToList();
        PopulateInstantiationHints(actualTypeParams, functionCall.Func);
      }
      return base.VisitNAryExpr(node);
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      PopulateInstantiationHints(node.Arguments, node.Decl);
      return base.VisitCtorType(node);
    }

    private void PopulateInstantiationHints(List<Type> actualTypeParams, NamedDeclaration decl)
    {
      for (int i = 0; i < actualTypeParams.Count; i++)
      {
        if (actualTypeParams[i] is TypeVariable typeVariable && typeParameterIndexes.ContainsKey(typeVariable))
        {
          var index = typeParameterIndexes[typeVariable];
          if (!instantiationHints[index].ContainsKey(decl))
          {
            instantiationHints[index][decl] = new List<int>();
          }
          instantiationHints[index][decl].Add(i);
        }
      }
    }
  }

  abstract class BinderExprMonomorphizer
  {
    protected MonomorphizationVisitor monomorphizationVisitor;
    protected Dictionary<List<Type>, Expr> instanceExprs;

    public BinderExprMonomorphizer(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.instanceExprs = new Dictionary<List<Type>, Expr>(new ListComparer<Type>());
    }

    public abstract BinderExpr BinderExpr { get; }

    public abstract bool Instantiate();

    public abstract Expr MonomorphicExpr();
  }

  class LambdaExprMonomorphizer : BinderExprMonomorphizer
  {
    private LambdaExpr lambdaExpr;

    public LambdaExprMonomorphizer(LambdaExpr lambdaExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(monomorphizationVisitor)
    {
      this.lambdaExpr = lambdaExpr;
    }

    public override BinderExpr BinderExpr => lambdaExpr;

    public override bool Instantiate()
    {
      var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(lambdaExpr.Type);
      Debug.Assert(instanceExprs.Count <= polymorphicMapInfo.Instances.Count);
      if (instanceExprs.Count == polymorphicMapInfo.Instances.Count)
      {
        return false;
      }
      polymorphicMapInfo.Instances.Skip(instanceExprs.Count).Iter(x =>
        instanceExprs[x] = monomorphizationVisitor.InstantiateBinderExpr(lambdaExpr, x));
      return true;
    }

    public override Expr MonomorphicExpr()
    {
      return monomorphizationVisitor.RegisterPolymorphicMapType(lambdaExpr.Type)
        .GetLambdaConstructor(instanceExprs);
    }
  }

  abstract class QuantifierExprMonomorphizer : BinderExprMonomorphizer
  {
    private QuantifierExpr quantifierExpr;
    private List<Dictionary<NamedDeclaration, List<int>>> instantiationHints;

    public QuantifierExprMonomorphizer(QuantifierExpr quantifierExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(monomorphizationVisitor)
    {
      this.quantifierExpr = quantifierExpr;
      this.instantiationHints = InstantiationHintCollector.CollectInstantiationHints(quantifierExpr);
    }

    public override BinderExpr BinderExpr => quantifierExpr;

    public override bool Instantiate()
    {
      var instanceExprsCount = instanceExprs.Count;
      var typeParameterIndexToTypeHints = Enumerable.Range(0, quantifierExpr.TypeParameters.Count)
        .Select(_ => new HashSet<Type>()).ToList();
      for (int typeParamterIndex = 0; typeParamterIndex < quantifierExpr.TypeParameters.Count; typeParamterIndex++)
      {
        foreach (var (decl, actualIndexes) in instantiationHints[typeParamterIndex])
        {
          foreach (var actualTypeParameters in monomorphizationVisitor.NamedDeclarationInstantiations(decl))
          {
            foreach (var actualIndex in actualIndexes)
            {
              typeParameterIndexToTypeHints[typeParamterIndex].Add(actualTypeParameters[actualIndex]);
            }
          }
        }
      }
      InstantiateOne(typeParameterIndexToTypeHints, new List<Type>());
      return instanceExprsCount < instanceExprs.Count;
    }

    private void InstantiateOne(List<HashSet<Type>> typeParameterIndexToTypeHints, List<Type> actualTypeParams)
    {
      if (typeParameterIndexToTypeHints.Count == actualTypeParams.Count)
      {
        if (!instanceExprs.ContainsKey(actualTypeParams))
        {
          instanceExprs[new List<Type>(actualTypeParams)] =
            monomorphizationVisitor.InstantiateBinderExpr(quantifierExpr, actualTypeParams);
        }
        return;
      }

      foreach (var type in typeParameterIndexToTypeHints[actualTypeParams.Count])
      {
        var addPosition = actualTypeParams.Count;
        actualTypeParams.Add(type);
        InstantiateOne(typeParameterIndexToTypeHints, actualTypeParams);
        actualTypeParams.RemoveAt(addPosition);
      }
    }
  }

  class ForallExprMonomorphizer : QuantifierExprMonomorphizer
  {
    public ForallExprMonomorphizer(ForallExpr forallExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(forallExpr, monomorphizationVisitor)
    {
    }

    public override Expr MonomorphicExpr()
    {
      return Expr.And(instanceExprs.Values);
    }
  }

  class ExistsExprMonomorphizer : QuantifierExprMonomorphizer
  {
    public ExistsExprMonomorphizer(ExistsExpr existsExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(existsExpr, monomorphizationVisitor)
    {
    }

    public override Expr MonomorphicExpr()
    {
      return Expr.Or(instanceExprs.Values);
    }
  }

  class PolymorphicMapInfo
  {
    class FieldInfo
    {
      public Type type;

      public int index;

      // actualParameters is the original parameter list that created this instance of FieldInfo
      public List<Type> actualParameters;

      public FieldInfo(Type type, int index, List<Type> actualParameters)
      {
        this.type = type;
        this.index = index;
        this.actualParameters = actualParameters;
      }
    }

    private MonomorphizationVisitor monomorphizationVisitor;
    private MapType mapType;
    private Dictionary<List<Type>, FieldInfo> fieldInfos;
    private List<List<Type>> instances;
    private DatatypeTypeCtorDecl datatypeTypeCtorDecl;

    public PolymorphicMapInfo(MonomorphizationVisitor monomorphizationVisitor, MapType mapType)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.mapType = mapType;
      fieldInfos = new Dictionary<List<Type>, FieldInfo>(new ListComparer<Type>());
      instances = new List<List<Type>>();
      datatypeTypeCtorDecl = new DatatypeTypeCtorDecl(new TypeCtorDecl(Token.NoToken, MapTypeName, 0,
        new QKeyValue(Token.NoToken, "datatype", new List<object>(), null)));
    }

    public CtorType Datatype => new(Token.NoToken, datatypeTypeCtorDecl, new List<Type>());

    public List<List<Type>> Instances => instances;

    public DatatypeTypeCtorDecl CreateDatatypeTypeCtorDecl()
    {
      var inParams = instances.Select(x =>
          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, FieldName(x), fieldInfos[x].type), true))
        .ToList<Variable>();
      var outParam = new Formal(Token.NoToken,
        new TypedIdent(Token.NoToken, MapTypeName, new CtorType(Token.NoToken, datatypeTypeCtorDecl, new List<Type>())),
        false);
      var function = new Function(Token.NoToken, MapTypeName, new List<TypeVariable>(), inParams, outParam, null,
        new QKeyValue(Token.NoToken, "constructor", new List<object>(), null));
      var constructor = new DatatypeConstructor(function);
      datatypeTypeCtorDecl.AddConstructor(constructor);
      return datatypeTypeCtorDecl;
    }

    public Expr GetLambdaConstructor(Dictionary<List<Type>, Expr> instanceExprs)
    {
      var returnExpr = new NAryExpr(Token.NoToken, new FunctionCall(datatypeTypeCtorDecl.Constructors[0]),
        instances.Select(x => instanceExprs[x]).ToList());
      returnExpr.Type = Datatype;
      returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      return returnExpr;
    }

    public FieldAccess GetFieldAccess(List<Type> actualParameters)
    {
      actualParameters = PopulateField(actualParameters);
      return new FieldAccess(Token.NoToken, FieldName(actualParameters), datatypeTypeCtorDecl,
        new List<DatatypeAccessor> { new(0, fieldInfos[actualParameters].index) });
    }

    public Type GetFieldType(List<Type> actualParameters)
    {
      actualParameters = PopulateField(actualParameters);
      return fieldInfos[actualParameters].type;
    }

    public List<Type> PopulateField(List<Type> actualParameters)
    {
      if (!fieldInfos.ContainsKey(actualParameters))
      {
        fieldInfos[actualParameters] = new FieldInfo(Instantiate(actualParameters), instances.Count, actualParameters);
        instances.Add(actualParameters);
      }
      return fieldInfos[actualParameters].actualParameters;
    }

    private string MapTypeName => $"PolymorphicMapType_{mapType.UniqueId}";

    private string FieldName(List<Type> actualParameters)
    {
      return MonomorphizationVisitor.MkInstanceName(MapTypeName, actualParameters);
    }

    private MapType Instantiate(List<Type> actualParameters)
    {
      var subst = LinqExtender.Map(mapType.TypeParameters, actualParameters);
      List<Type> newArgs = new List<Type>();
      foreach (Type t in mapType.Arguments)
      {
        newArgs.Add(t.Substitute(subst));
      }
      Type newResult = mapType.Result.Substitute(subst);
      var returnType = new MapType(mapType.tok, new List<TypeVariable>(), newArgs, newResult);
      return (MapType)new MonomorphizationDuplicator(monomorphizationVisitor).VisitMapType(returnType);
    }
  }

  class PolymorphicMapAndBinderSubstituter : StandardVisitor
  {
    private MonomorphizationVisitor monomorphizationVisitor;
    private Dictionary<BinderExpr, Expr> binderExprSubstitution;

    public PolymorphicMapAndBinderSubstituter(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.binderExprSubstitution = monomorphizationVisitor.SubstitututionForBinderExprs();
    }

    private List<Type> ActualTypeParams(TypeParamInstantiation typeParamInstantiation)
    {
      return typeParamInstantiation.FormalTypeParams.Select(x => TypeProxy.FollowProxy(typeParamInstantiation[x]))
        .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (!(node.Fun is MapSelect || node.Fun is MapStore) || node.TypeParameters.FormalTypeParams.Count == 0)
      {
        return base.VisitNAryExpr(node);
      }
      var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(node.Args[0].Type);
      var actualTypeParams = ActualTypeParams(node.TypeParameters);
      var fieldAccess = polymorphicMapInfo.GetFieldAccess(actualTypeParams);
      node = (NAryExpr)base.VisitNAryExpr(node);
      var polymorphicMapDatatypeExpr = node.Args[0];
      var fieldAccessExpr = new NAryExpr(Token.NoToken, fieldAccess, new List<Expr> { polymorphicMapDatatypeExpr });
      fieldAccessExpr.Type = polymorphicMapInfo.GetFieldType(actualTypeParams);
      fieldAccessExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      node.Args[0] = fieldAccessExpr;
      node.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      if (node.Fun is MapStore)
      {
        node.Type = fieldAccessExpr.Type;
        var fieldUpdate = new FieldUpdate(fieldAccess);
        node = new NAryExpr(Token.NoToken, fieldUpdate, new List<Expr>() { polymorphicMapDatatypeExpr, node });
        node.Type = polymorphicMapInfo.Datatype;
      }
      return node;
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(node.Map.Type);
      var actualTypeParams = ActualTypeParams(node.TypeParameters);
      var fieldAccess = polymorphicMapInfo.GetFieldAccess(actualTypeParams);
      node = (MapAssignLhs)base.VisitMapAssignLhs(node);
      if (node.TypeParameters.FormalTypeParams.Count > 0)
      {
        node.Map = new FieldAssignLhs(Token.NoToken, node.Map, fieldAccess);
      }
      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      node = (MapType)base.VisitMapType(node);
      if (node.TypeParameters.Count > 0)
      {
        var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(node);
        return polymorphicMapInfo.Datatype;
      }
      return node;
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      if (binderExprSubstitution.ContainsKey(node))
      {
        return VisitExpr(binderExprSubstitution[node]);
      }
      return base.VisitBinderExpr(node);
    }

    public override Expr VisitLambdaExpr(LambdaExpr node)
    {
      return VisitBinderExpr(node);
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      return VisitBinderExpr(node);
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      return VisitBinderExpr(node);
    }

    public override Type VisitType(Type node)
    {
      return (Type)Visit(node);
    }

    public override Type VisitBasicType(BasicType node)
    {
      return node;
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      return node;
    }

    public override Expr VisitExpr(Expr node)
    {
      node = base.VisitExpr(node);
      node.Type = VisitType(node.Type);
      return node;
    }
    
    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      var identifierExpr = base.VisitIdentifierExpr(node);
      identifierExpr.Type = VisitType(identifierExpr.Type);
      return identifierExpr;
    }
    
    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      node.Body = VisitType(node.Body);
      return node;
    }
  }

  class MonomorphizationDuplicator : Duplicator
  {
    private MonomorphizationVisitor monomorphizationVisitor;
    private Dictionary<TypeVariable, Type> typeParamInstantiation;
    private Dictionary<Variable, Variable> variableMapping;
    private Dictionary<Variable, Variable> boundVarSubst;

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      typeParamInstantiation = new Dictionary<TypeVariable, Type>();
      variableMapping = new Dictionary<Variable, Variable>();
      boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor,
      Dictionary<TypeVariable, Type> typeParamInstantiation)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.typeParamInstantiation = typeParamInstantiation;
      this.variableMapping = new Dictionary<Variable, Variable>();
      this.boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor,
      Dictionary<TypeVariable, Type> typeParamInstantiation, Dictionary<Variable, Variable> variableMapping)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.typeParamInstantiation = typeParamInstantiation;
      this.variableMapping = variableMapping;
      this.boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      var fieldAssignLhs = (FieldAssignLhs)base.VisitFieldAssignLhs(node);
      var actualTypeParams =
        fieldAssignLhs.TypeParameters.FormalTypeParams.Select(x =>
            TypeProxy.FollowProxy(fieldAssignLhs.TypeParameters[x]).Substitute(typeParamInstantiation))
          .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
      fieldAssignLhs.TypeParameters =
        SimpleTypeParamInstantiation.From(fieldAssignLhs.TypeParameters.FormalTypeParams, actualTypeParams);
      if (actualTypeParams.Any(IsPolymorphic))
      {
        return fieldAssignLhs;
      }
      var fieldAccess = fieldAssignLhs.FieldAccess;
      var datatypeTypeCtorDecl = fieldAccess.DatatypeTypeCtorDecl;
      if (datatypeTypeCtorDecl.Arity == 0)
      {
        monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
      }
      else
      {
        fieldAssignLhs.FieldAccess =
          monomorphizationVisitor.InstantiateFieldAccess(fieldAssignLhs.FieldAccess, actualTypeParams);
      }
      return fieldAssignLhs;
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      var mapAssignLhs = (MapAssignLhs)base.VisitMapAssignLhs(node);
      var actualTypeParams =
        mapAssignLhs.TypeParameters.FormalTypeParams.Select(x =>
            TypeProxy.FollowProxy(mapAssignLhs.TypeParameters[x]).Substitute(typeParamInstantiation))
          .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
      mapAssignLhs.TypeParameters =
        SimpleTypeParamInstantiation.From(mapAssignLhs.TypeParameters.FormalTypeParams, actualTypeParams);
      if (!actualTypeParams.Any(IsPolymorphic) && actualTypeParams.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(node.Map.Type);
      }
      return mapAssignLhs;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var returnExpr = (NAryExpr)base.VisitNAryExpr(node);
      returnExpr.Type = VisitType(node.Type);
      var actualTypeParams =
        returnExpr.TypeParameters.FormalTypeParams.Select(x =>
            TypeProxy.FollowProxy(returnExpr.TypeParameters[x]).Substitute(typeParamInstantiation))
          .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
      returnExpr.TypeParameters =
        SimpleTypeParamInstantiation.From(returnExpr.TypeParameters.FormalTypeParams, actualTypeParams);
      if (returnExpr.Fun is TypeCoercion)
      {
        return returnExpr.Args[0];
      }

      if (actualTypeParams.Any(IsPolymorphic))
      {
        return returnExpr;
      }
      
      if (returnExpr.Fun is MapSelect && returnExpr.TypeParameters.FormalTypeParams.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(returnExpr.Args[0].Type).PopulateField(actualTypeParams);
      }
      else if (returnExpr.Fun is MapStore && returnExpr.TypeParameters.FormalTypeParams.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(returnExpr.Type).PopulateField(actualTypeParams);
      }
      else if (returnExpr.Fun is IsConstructor isConstructor)
      {
        var datatypeTypeCtorDecl = isConstructor.DatatypeTypeCtorDecl;
        if (datatypeTypeCtorDecl.Arity == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
        }
        else
        {
          returnExpr.Fun = monomorphizationVisitor.InstantiateIsConstructor(isConstructor, actualTypeParams);
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }
      else if (returnExpr.Fun is FieldAccess fieldAccess)
      {
        var datatypeTypeCtorDecl = fieldAccess.DatatypeTypeCtorDecl;
        if (datatypeTypeCtorDecl.Arity == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
        }
        else
        {
          returnExpr.Fun = monomorphizationVisitor.InstantiateFieldAccess(fieldAccess, actualTypeParams);
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }
      else if (returnExpr.Fun is FieldUpdate fieldUpdate)
      {
        var datatypeTypeCtorDecl = fieldUpdate.DatatypeTypeCtorDecl;
        if (datatypeTypeCtorDecl.Arity == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
        }
        else
        {
          returnExpr.Fun = monomorphizationVisitor.InstantiateFieldUpdate(fieldUpdate, actualTypeParams);
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }
      else if (returnExpr.Fun is FunctionCall functionCall)
      {
        // a non-generic function must be processed to rewrite any generic types it uses
        // to the corresponding instantiated types
        if (functionCall.Func.TypeParameters.Count == 0)
        {
          if (functionCall.Func is DatatypeConstructor constructor)
          {
            monomorphizationVisitor.VisitTypeCtorDecl(constructor.datatypeTypeCtorDecl);
          }
          else
          {
            monomorphizationVisitor.VisitFunction(functionCall.Func);
          }
          returnExpr.Fun = new FunctionCall(functionCall.Func);
        }
        else
        {
          if (functionCall.Func is DatatypeConstructor constructor)
          {
            var datatypeTypeCtorDecl =
              (DatatypeTypeCtorDecl)monomorphizationVisitor.InstantiateTypeCtorDecl(constructor.datatypeTypeCtorDecl,
                actualTypeParams);
            returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[constructor.index]);
          }
          else
          {
            returnExpr.Fun =
              new FunctionCall(monomorphizationVisitor.InstantiateFunction(functionCall.Func, actualTypeParams));
          }
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }

      return returnExpr;
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var returnCallCmd = (CallCmd)base.VisitCallCmd(node);
      if (returnCallCmd.Proc.TypeParameters.Count > 0)
      {
        var actualTypeParams =
          returnCallCmd.TypeParameters.FormalTypeParams.Select(x =>
              TypeProxy.FollowProxy(returnCallCmd.TypeParameters[x]).Substitute(typeParamInstantiation))
            .Select(monomorphizationVisitor.LookupType).ToList();
        returnCallCmd.Proc = monomorphizationVisitor.InstantiateProcedure(node.Proc, actualTypeParams);
        returnCallCmd.callee = returnCallCmd.Proc.Name;
        returnCallCmd.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        monomorphizationVisitor.InlineCallCmd(node, actualTypeParams);
      }
      return returnCallCmd;
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      if (typeParamInstantiation.ContainsKey(node))
      {
        return typeParamInstantiation[node];
      }
      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      node = (MapType)node.Clone();
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        node.Arguments[i] = (Type)this.Visit(node.Arguments[i]);
      }
      node.Result = (Type)this.Visit(node.Result);
      if (node.TypeParameters.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(node);
      }
      return node;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      node = (CtorType)node.Clone();
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        node.Arguments[i] = (Type)this.Visit(node.Arguments[i]);
      }

      if (node.Arguments.Any(IsPolymorphic))
      {
        return node;
      }
      
      var typeCtorDecl = node.Decl;
      monomorphizationVisitor.AddTriggerType(typeCtorDecl, node);

      if (MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(typeCtorDecl))
      {
        return new CtorType(node.tok, monomorphizationVisitor.InstantiateTypeCtorDecl(typeCtorDecl, node.Arguments),
          new List<Type>());
      }

      return node;
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      base.VisitTypeSynonymAnnotation(node);
      return node.ExpandedType;
    }

    public override Type VisitType(Type node)
    {
      return (Type)Visit(node);
    }
    
    public override Type VisitTypeProxy(TypeProxy node)
    {
      return VisitType(TypeProxy.FollowProxy(node));
    }

    public override Expr VisitExpr(Expr node)
    {
      node = base.VisitExpr(node);
      node.Type = VisitType(node.Type);
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (variableMapping.ContainsKey(node.Decl))
      {
        return new IdentifierExpr(node.tok, variableMapping[node.Decl], node.Immutable);
      }

      if (boundVarSubst.ContainsKey(node.Decl))
      {
        return new IdentifierExpr(node.tok, boundVarSubst[node.Decl], node.Immutable);
      }

      var identifierExpr = base.VisitIdentifierExpr(node);
      identifierExpr.Type = VisitType(identifierExpr.Type);
      return identifierExpr;
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(x.tok, new TypedIdent(x.tok, x.Name, VisitType(x.TypedIdent.Type)),
          x.Attributes));
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Add(x, oldToNew[x]);
      }

      var expr = (BinderExpr)base.VisitBinderExpr(node);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
      // We process triggers of quantifier expressions here, because otherwise the
      // substitutions for bound variables have to be leaked outside this procedure.
      if (node is QuantifierExpr quantifierExpr)
      {
        if (quantifierExpr.Triggers != null)
        {
          ((QuantifierExpr)expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
        }
      }

      if (node.Attributes != null)
      {
        expr.Attributes = VisitQKeyValue(node.Attributes);
      }

      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }

      if (expr.TypeParameters.Count > 0)
      {
        if (expr is LambdaExpr lambdaExpr)
        {
          monomorphizationVisitor.AddBinderExprMonomorphizer(new LambdaExprMonomorphizer(lambdaExpr, monomorphizationVisitor));
        }
        else if (expr is ForallExpr forallExpr)
        {
          monomorphizationVisitor.AddBinderExprMonomorphizer(new ForallExprMonomorphizer(forallExpr, monomorphizationVisitor));
        }
        else if (expr is ExistsExpr existsExpr)
        {
          monomorphizationVisitor.AddBinderExprMonomorphizer(new ExistsExprMonomorphizer(existsExpr, monomorphizationVisitor));
        }
        else
        {
          throw new cce.UnreachableException();
        }
      }

      return expr;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
      return (QuantifierExpr)this.VisitBinderExpr(node);
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(x.tok, new TypedIdent(x.tok, x.Name, VisitType(x.TypedIdent.Type)),
          x.Attributes));
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Add(x, oldToNew[x]);
      }

      var expr = (LetExpr)base.VisitLetExpr(node);
      expr.Type = VisitType(expr.Type);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }

      return expr;
    }

    private bool IsPolymorphic(Type type)
    {
      type = TypeProxy.FollowProxy(type).Expanded;
      if (type is BasicType)
      {
        return false;
      }
      if (type is TypeVariable)
      {
        return true;
      }
      if (type is CtorType ctorType)
      {
        return ctorType.Arguments.Any(IsPolymorphic);
      }
      if (type is MapType mapType)
      {
        return mapType.Arguments.Any(IsPolymorphic) || IsPolymorphic(mapType.Result);
      }
      throw new cce.UnreachableException();
    }
  }

  class MonomorphizationVisitor : StandardVisitor
  {
    /*
     * This class monomorphizes a Boogie program. Monomorphization starts from
     * a traversal of monomorphic procedures. Any polymorphic function or type
     * encountered is monomorphized based on actual type parameters. The body of
     * each encountered function is recursively traversed.
     *
     * If the program contains a polymorphic procedure, a monomorphic version of
     * the procedure is created by substituting a fresh uninterpreted type for
     * each type parameter.
     *
     * MonomorphizationVisitor uses a helper class MonomorphizationDuplicator.
     * While the former does in-place update as a result of monomorphization,
     * the latter creates a duplicate copy. MonomorphizationDuplicator is needed
     * because a polymorphic function, type, or procedure may be visited several
     * times in different type contexts.
     */

    public CoreOptions Options { get; }
    
    private Program program;
    private Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated;
    private Dictionary<string, Function> nameToFunction;
    private Dictionary<string, Procedure> nameToProcedure;
    private Dictionary<string, Implementation> nameToImplementation;
    private Dictionary<string, TypeCtorDecl> nameToTypeCtorDecl;
    private Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations;
    private Dictionary<Procedure, Dictionary<List<Type>, Procedure>> procInstantiations;
    private Dictionary<Implementation, Dictionary<List<Type>, Implementation>> implInstantiations;
    private Dictionary<TypeCtorDecl, Dictionary<List<Type>, TypeCtorDecl>> typeInstantiations;
    private HashSet<Declaration> newInstantiatedDeclarations;
    private List<BinderExprMonomorphizer> binderExprMonomorphizers;
    private Dictionary<MapType, PolymorphicMapInfo> polymorphicMapInfos;
    private Dictionary<DeclWithFormals, Tuple<DeclWithFormals, Dictionary<string, Type>>> declWithFormalsToTypeInstantiation;
    private Dictionary<TypeCtorDecl, Tuple<TypeCtorDecl, List<Type>>> typeCtorDeclToTypeInstantiation;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> triggerTypes;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> newTriggerTypes;
    private HashSet<TypeCtorDecl> visitedTypeCtorDecls;
    private HashSet<Function> visitedFunctions;
    private Dictionary<Procedure, Implementation> procToImpl;

    private MonomorphizationVisitor(CoreOptions options, Program program,
      Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated, HashSet<Axiom> polymorphicFunctionAxioms)
    {
      Options = options;
      this.program = program;
      this.axiomsToBeInstantiated = axiomsToBeInstantiated;
      implInstantiations = new Dictionary<Implementation, Dictionary<List<Type>, Implementation>>();
      nameToImplementation = new Dictionary<string, Implementation>();
      program.TopLevelDeclarations.OfType<Implementation>().Where(impl => impl.TypeParameters.Count > 0).Iter(
        impl =>
        {
          nameToImplementation.Add(impl.Name, impl);
          implInstantiations.Add(impl, new Dictionary<List<Type>, Implementation>(new ListComparer<Type>()));
        });
      procInstantiations = new Dictionary<Procedure, Dictionary<List<Type>, Procedure>>();
      nameToProcedure = new Dictionary<string, Procedure>();
      program.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.TypeParameters.Count > 0).Iter(
        proc =>
        {
          nameToProcedure.Add(proc.Name, proc);
          procInstantiations.Add(proc, new Dictionary<List<Type>, Procedure>(new ListComparer<Type>()));
        });
      functionInstantiations = new Dictionary<Function, Dictionary<List<Type>, Function>>();
      nameToFunction = new Dictionary<string, Function>();
      program.TopLevelDeclarations.OfType<Function>().Where(function => function.TypeParameters.Count > 0).Iter(
        function =>
        {
          nameToFunction.Add(function.Name, function);
          functionInstantiations.Add(function, new Dictionary<List<Type>, Function>(new ListComparer<Type>()));
        });
      declWithFormalsToTypeInstantiation = new Dictionary<DeclWithFormals, Tuple<DeclWithFormals, Dictionary<string, Type>>>();
      typeCtorDeclToTypeInstantiation = new Dictionary<TypeCtorDecl, Tuple<TypeCtorDecl, List<Type>>>();
      typeInstantiations = new Dictionary<TypeCtorDecl, Dictionary<List<Type>, TypeCtorDecl>>();
      newInstantiatedDeclarations = new HashSet<Declaration>();
      binderExprMonomorphizers = new List<BinderExprMonomorphizer>();
      polymorphicMapInfos = new Dictionary<MapType, PolymorphicMapInfo>();
      nameToTypeCtorDecl = new Dictionary<string, TypeCtorDecl>();
      program.TopLevelDeclarations.OfType<TypeCtorDecl>()
        .Where(typeCtorDecl => MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(typeCtorDecl)).Iter(
          typeCtorDecl =>
          {
            nameToTypeCtorDecl.Add(typeCtorDecl.Name, typeCtorDecl);
            typeInstantiations.Add(typeCtorDecl, new Dictionary<List<Type>, TypeCtorDecl>(new ListComparer<Type>()));
          });
      triggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
      newTriggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
      axiomsToBeInstantiated.Values.ToHashSet().Iter(typeCtorDecl =>
      {
        triggerTypes.Add(typeCtorDecl, new HashSet<CtorType>());
        newTriggerTypes.Add(typeCtorDecl, new HashSet<CtorType>());
      });
      this.visitedTypeCtorDecls = new HashSet<TypeCtorDecl>();
      this.visitedFunctions = new HashSet<Function>();
      this.procToImpl = new Dictionary<Procedure, Implementation>();
      program.TopLevelDeclarations.OfType<Implementation>().Iter(impl => this.procToImpl[impl.Proc] = impl);
      program.RemoveTopLevelDeclarations(decl => 
        decl is Implementation impl && implInstantiations.ContainsKey(impl) ||
        decl is Procedure proc && procInstantiations.ContainsKey(proc) ||
        decl is Function function && functionInstantiations.ContainsKey(function) ||
        decl is TypeCtorDecl typeCtorDecl && typeInstantiations.ContainsKey(typeCtorDecl) ||
        decl is TypeSynonymDecl typeSynonymDecl && typeSynonymDecl.TypeParameters.Count > 0 ||
        decl is Axiom axiom && (axiomsToBeInstantiated.ContainsKey(axiom) || polymorphicFunctionAxioms.Contains(axiom)));
    }
    
    public static MonomorphizationVisitor Initialize(CoreOptions options, Program program,
      Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated,
      HashSet<Axiom> polymorphicFunctionAxioms)
    {
      var monomorphizationVisitor = new MonomorphizationVisitor(options, program, axiomsToBeInstantiated, polymorphicFunctionAxioms);
      // ctorTypes contains all the uninterpreted types created for monomorphizing top-level polymorphic implementations 
      // that must be verified. The types in ctorTypes are reused across different implementations.
      var ctorTypes = new List<Type>();
      var typeCtorDecls = new HashSet<TypeCtorDecl>();
      monomorphizationVisitor.implInstantiations.Keys.Where(impl => !impl.IsSkipVerification(options)).Iter(impl =>
      {
        for (int i = ctorTypes.Count; i < impl.TypeParameters.Count; i++)
        {
          var typeParam = impl.TypeParameters[i];
          var typeCtorDecl = new TypeCtorDecl(typeParam.tok, $"{typeParam.Name}_{typeParam.UniqueId}", 0);
          typeCtorDecls.Add(typeCtorDecl);
          ctorTypes.Add(new CtorType(typeParam.tok, typeCtorDecl,  new List<Type>()));
        }
        var actualTypeParams = ctorTypes.GetRange(0, impl.TypeParameters.Count);
        var instantiatedImpl = monomorphizationVisitor.InstantiateImplementation(impl, actualTypeParams);
        instantiatedImpl.Proc = monomorphizationVisitor.InstantiateProcedure(impl.Proc, actualTypeParams);
      });
      monomorphizationVisitor.VisitProgram(program);
      monomorphizationVisitor.InstantiateAxioms();
      monomorphizationVisitor.AddInstantiatedDeclarations();
      program.AddTopLevelDeclarations(typeCtorDecls);
      monomorphizationVisitor.FixpointOnBinderExprMonomorphizers();
      var polymorphicMapDatatypeCtorDecls =
        monomorphizationVisitor.polymorphicMapInfos.Values.Select(polymorphicMapInfo =>
          polymorphicMapInfo.CreateDatatypeTypeCtorDecl()).ToList();
      var polymorphicMapSubstituter = new PolymorphicMapAndBinderSubstituter(monomorphizationVisitor);
      polymorphicMapSubstituter.Visit(program);
      program.AddTopLevelDeclarations(polymorphicMapDatatypeCtorDecls);
      Contract.Assert(MonomorphismChecker.IsMonomorphic(program));
      return monomorphizationVisitor;
    }

    private void FixpointOnBinderExprMonomorphizers()
    {
      var moreWorkNeeded = true;
      while (moreWorkNeeded)
      {
        moreWorkNeeded = false;

        // binderExprMonomorphizers is modified inside the loop so iterate over a copy of it
        var oldBinderExprMonomorphizers = new List<BinderExprMonomorphizer>(binderExprMonomorphizers);
        foreach (var binderExprMonomorphizer in oldBinderExprMonomorphizers)
        {
          if (binderExprMonomorphizer.Instantiate())
          {
            moreWorkNeeded = true;
          }
        }

        if (newInstantiatedDeclarations.Count > 0)
        {
          AddInstantiatedDeclarations();
          moreWorkNeeded = true;
        }

        if (oldBinderExprMonomorphizers.Count < binderExprMonomorphizers.Count)
        {
          moreWorkNeeded = true;
        }
      }
    }

    public Dictionary<BinderExpr, Expr> SubstitututionForBinderExprs()
    {
      return binderExprMonomorphizers.ToDictionary(x => x.BinderExpr, x => x.MonomorphicExpr());
    }

    public IEnumerable<List<Type>> NamedDeclarationInstantiations(NamedDeclaration decl)
    {
      if (decl is Function function)
      {
        return functionInstantiations[function].Keys;
      }
      if (decl is TypeCtorDecl typeCtorDecl)
      {
        return typeInstantiations[typeCtorDecl].Keys;
      }
      throw new cce.UnreachableException();
    }

    public PolymorphicMapInfo RegisterPolymorphicMapType(Type type)
    {
      var mapType = (MapType)LookupType(type);
      if (!polymorphicMapInfos.ContainsKey(mapType))
      {
        polymorphicMapInfos[mapType] = new PolymorphicMapInfo(this, mapType);
      }
      return polymorphicMapInfos[mapType];
    }

    public void AddBinderExprMonomorphizer(BinderExprMonomorphizer binderExprMonomorphizer)
    {
      binderExprMonomorphizers.Add(binderExprMonomorphizer);
    }

    public void AddTriggerType(TypeCtorDecl typeCtorDecl, CtorType ctorType)
    {
      if (triggerTypes.ContainsKey(typeCtorDecl) &&
          !triggerTypes[typeCtorDecl].Contains(ctorType))
      {
        triggerTypes[typeCtorDecl].Add(ctorType);
        newTriggerTypes[typeCtorDecl].Add(ctorType);
      }
    }

    public void InlineCallCmd(CallCmd callCmd, List<Type> actualTypeParams)
    {
      if (procToImpl.ContainsKey(callCmd.Proc))
      {
        var impl = procToImpl[callCmd.Proc];
        if (IsInlined(impl))
        {
          InstantiateImplementation(impl, actualTypeParams);
        }
      }  
    }
    
    private bool IsInlined(Implementation impl)
    {
      if (Options.ProcedureInlining == CoreOptions.Inlining.None)
      {
        return false;
      }
      Expr inlineAttr = impl.FindExprAttribute("inline");
      if (inlineAttr == null)
      {
        inlineAttr = impl.Proc.FindExprAttribute("inline");
      }
      return inlineAttr != null;
    }

    private Axiom InstantiateAxiom(Axiom axiom, List<Type> actualTypeParams)
    {
      var axiomExpr = InstantiateBinderExpr((BinderExpr)axiom.Expr, actualTypeParams);
      var instantiatedAxiom = new Axiom(axiom.tok, axiomExpr, axiom.Comment, axiom.Attributes);
      newInstantiatedDeclarations.Add(instantiatedAxiom);
      return instantiatedAxiom;
    }

    public Expr InstantiateBinderExpr(BinderExpr binderExpr, List<Type> actualTypeParams)
    {
      var binderExprTypeParameters = binderExpr.TypeParameters;
      binderExpr.TypeParameters = new List<TypeVariable>();
      var newBinderExpr = (BinderExpr)InstantiateAbsy(binderExpr, LinqExtender.Map(binderExprTypeParameters, actualTypeParams),
        new Dictionary<Variable, Variable>());
      binderExpr.TypeParameters = binderExprTypeParameters;
      if (newBinderExpr is QuantifierExpr quantifierExpr && quantifierExpr.Dummies.Count == 0)
      {
        return quantifierExpr.Body;
      }
      if (binderExpr is LambdaExpr)
      {
        var polymorphicMapInfo = RegisterPolymorphicMapType(newBinderExpr.Type);
        newBinderExpr.Type = polymorphicMapInfo.GetFieldType(actualTypeParams);
      }
      return newBinderExpr;
    }
      
    public Function InstantiateFunction(Function func, List<Type> actualTypeParams)
    {
      if (!functionInstantiations[func].ContainsKey(actualTypeParams))
      {
        var funcTypeParamInstantiation = LinqExtender.Map(func.TypeParameters, actualTypeParams);
        var instantiatedFunction =
          InstantiateFunctionSignature(func, actualTypeParams, funcTypeParamInstantiation);
        var variableMapping = LinqExtender.Map(func.InParams, instantiatedFunction.InParams);
        newInstantiatedDeclarations.Add(instantiatedFunction);
        functionInstantiations[func][actualTypeParams] = instantiatedFunction;
        declWithFormalsToTypeInstantiation[instantiatedFunction] =
          Tuple.Create<DeclWithFormals, Dictionary<string, Type>>(func,
            LinqExtender.Map(func.TypeParameters.Select(x => x.Name), actualTypeParams));
        if (func.Body != null)
        {
          instantiatedFunction.Body = (Expr) InstantiateAbsy(func.Body, funcTypeParamInstantiation, variableMapping);
        }
        else if (func.DefinitionBody != null)
        {
          instantiatedFunction.DefinitionBody =
            (NAryExpr) InstantiateAbsy(func.DefinitionBody, funcTypeParamInstantiation, variableMapping);
        }
        else if (func.DefinitionAxiom != null)
        {
          instantiatedFunction.DefinitionAxiom =
            this.InstantiateAxiom(func.DefinitionAxiom, actualTypeParams);
        }
      }
      return functionInstantiations[func][actualTypeParams];
    }

    private void AddInstantiatedDeclarations()
    {
      program.AddTopLevelDeclarations(newInstantiatedDeclarations);
      newInstantiatedDeclarations = new HashSet<Declaration>();
    }

    private Absy InstantiateAbsy(Absy absy, Dictionary<TypeVariable, Type> typeParamInstantiation,
      Dictionary<Variable, Variable> variableMapping)
    {
      var monomorphizationDuplicator =
        new MonomorphizationDuplicator(this, typeParamInstantiation, variableMapping);
      return monomorphizationDuplicator.Visit(absy);
    }  

    public Procedure InstantiateProcedure(Procedure proc, List<Type> actualTypeParams)
    {
      if (!procInstantiations[proc].ContainsKey(actualTypeParams))
      {
        var procTypeParamInstantiation = LinqExtender.Map(proc.TypeParameters, actualTypeParams);
        var instantiatedInParams = InstantiateFormals(proc.InParams, procTypeParamInstantiation);
        var instantiatedOutParams = InstantiateFormals(proc.OutParams, procTypeParamInstantiation);
        var variableMapping = LinqExtender.Map(proc.InParams.Union(proc.OutParams),
          instantiatedInParams.Union(instantiatedOutParams));
        var requires = proc.Requires.Select(requires => new Requires(requires.tok, requires.Free,
          (Expr) InstantiateAbsy(requires.Condition, procTypeParamInstantiation, variableMapping), requires.Comment)).ToList();
        var modifies = proc.Modifies.Select(ie =>
          (IdentifierExpr) InstantiateAbsy(ie, procTypeParamInstantiation, variableMapping)).ToList();
        var ensures = proc.Ensures.Select(ensures => new Ensures(ensures.tok, ensures.Free,
          (Expr) InstantiateAbsy(ensures.Condition, procTypeParamInstantiation, variableMapping), ensures.Comment)).ToList();
        var instantiatedProc = new Procedure(proc.tok, MkInstanceName(proc.Name, actualTypeParams),
          new List<TypeVariable>(), instantiatedInParams, instantiatedOutParams, requires, modifies, ensures,
          proc.Attributes == null ? null : VisitQKeyValue(proc.Attributes));
        newInstantiatedDeclarations.Add(instantiatedProc);
        procInstantiations[proc][actualTypeParams] = instantiatedProc;
        declWithFormalsToTypeInstantiation[instantiatedProc] =
          Tuple.Create<DeclWithFormals, Dictionary<string, Type>>(proc,
            LinqExtender.Map(proc.TypeParameters.Select(x => x.Name), actualTypeParams));
      }
      return procInstantiations[proc][actualTypeParams];
    }

    public Implementation InstantiateImplementation(Implementation impl, List<Type> actualTypeParams)
    {
      if (!implInstantiations[impl].ContainsKey(actualTypeParams))
      {
        var implTypeParamInstantiation = LinqExtender.Map(impl.TypeParameters, actualTypeParams);
        var instantiatedInParams = InstantiateFormals(impl.InParams, implTypeParamInstantiation);
        var instantiatedOutParams = InstantiateFormals(impl.OutParams, implTypeParamInstantiation);
        var instantiatedLocalVariables = InstantiateLocalVariables(impl.LocVars, implTypeParamInstantiation);
        var variableMapping = LinqExtender.Map(impl.InParams.Union(impl.OutParams).Union(impl.LocVars),
          instantiatedInParams.Union(instantiatedOutParams).Union(instantiatedLocalVariables));
        var blocks = impl.Blocks
          .Select(block => (Block)InstantiateAbsy(block, implTypeParamInstantiation, variableMapping)).ToList();
        var blockMapping = LinqExtender.Map(impl.Blocks, blocks);
        blocks.Iter(block =>
        {
          if (block.TransferCmd is GotoCmd gotoCmd)
          {
            gotoCmd.labelTargets = gotoCmd.labelTargets.Select(target => blockMapping[target]).ToList();
            gotoCmd.labelNames = new List<string>(gotoCmd.labelNames);
          }
        });
        var instantiatedImpl = new Implementation(impl.tok, MkInstanceName(impl.Name, actualTypeParams),
          new List<TypeVariable>(), instantiatedInParams, instantiatedOutParams, instantiatedLocalVariables, blocks,
          impl.Attributes == null ? null : VisitQKeyValue(impl.Attributes));
        instantiatedImpl.Proc = InstantiateProcedure(impl.Proc, actualTypeParams);
        newInstantiatedDeclarations.Add(instantiatedImpl);
        implInstantiations[impl][actualTypeParams] = instantiatedImpl;
        declWithFormalsToTypeInstantiation[instantiatedImpl] =
          Tuple.Create<DeclWithFormals, Dictionary<string, Type>>(impl,
            LinqExtender.Map(impl.TypeParameters.Select(x => x.Name), actualTypeParams));
      }
      return implInstantiations[impl][actualTypeParams];
    }

    private List<Variable> InstantiateFormals(List<Variable> variables,
      Dictionary<TypeVariable, Type> declTypeParamInstantiation)
    {
      var monomorphizationDuplicator = new MonomorphizationDuplicator(this, declTypeParamInstantiation);
      var instantiatedVariables =
        variables.Select(x => (Formal)x).Select(x =>
            new Formal(x.tok,
              new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name,
                monomorphizationDuplicator.VisitType(x.TypedIdent.Type)),
              x.InComing, x.Attributes == null ? null : monomorphizationDuplicator.VisitQKeyValue(x.Attributes)))
          .ToList<Variable>();
      return instantiatedVariables;
    }

    private List<Variable> InstantiateLocalVariables(List<Variable> variables,
      Dictionary<TypeVariable, Type> declTypeParamInstantiation)
    {
      var monomorphizationDuplicator = new MonomorphizationDuplicator(this, declTypeParamInstantiation);
      var instantiatedVariables =
        variables.Select(x =>
            new LocalVariable(x.tok,
              new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name,
                monomorphizationDuplicator.VisitType(x.TypedIdent.Type))))
          .ToList<Variable>();
      return instantiatedVariables;
    }

    private Function InstantiateFunctionSignature(Function func, List<Type> actualTypeParams,
      Dictionary<TypeVariable, Type> funcTypeParamInstantiation)
    {
      var instantiatedInParams = InstantiateFormals(func.InParams, funcTypeParamInstantiation);
      var instantiatedOutParams = InstantiateFormals(func.OutParams, funcTypeParamInstantiation);
      var instantiatedFunction = new Function(
        func.tok,
        MkInstanceName(func.Name, actualTypeParams),
        new List<TypeVariable>(),
        instantiatedInParams,
        instantiatedOutParams.First(),
        func.Comment,
        func.Attributes);
      return instantiatedFunction;
    }

    public TypeCtorDecl InstantiateTypeCtorDecl(TypeCtorDecl typeCtorDecl, List<Type> actualTypeParams)
    {
      if (!typeInstantiations[typeCtorDecl].ContainsKey(actualTypeParams))
      {
        if (typeCtorDecl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
        {
          var newDatatypeTypeCtorDecl = new DatatypeTypeCtorDecl(
            new TypeCtorDecl(datatypeTypeCtorDecl.tok,
              MkInstanceName(datatypeTypeCtorDecl.Name, actualTypeParams), 0,
              datatypeTypeCtorDecl.Attributes));
          newInstantiatedDeclarations.Add(newDatatypeTypeCtorDecl);
          typeInstantiations[datatypeTypeCtorDecl]
            .Add(actualTypeParams, newDatatypeTypeCtorDecl);
          typeCtorDeclToTypeInstantiation[newDatatypeTypeCtorDecl] = Tuple.Create(typeCtorDecl, actualTypeParams);
          datatypeTypeCtorDecl.Constructors.Iter(constructor =>
          {
            var function = InstantiateFunctionSignature(constructor, actualTypeParams,
              LinqExtender.Map(constructor.TypeParameters, actualTypeParams));
            newDatatypeTypeCtorDecl.AddConstructor(new DatatypeConstructor(function));
          });
        }
        else
        {
          var newTypeCtorDecl =
            new TypeCtorDecl(typeCtorDecl.tok, MkInstanceName(typeCtorDecl.Name, actualTypeParams), 0,
              typeCtorDecl.Attributes);
          newInstantiatedDeclarations.Add(newTypeCtorDecl);
          typeInstantiations[typeCtorDecl].Add(actualTypeParams, newTypeCtorDecl);
          typeCtorDeclToTypeInstantiation[newTypeCtorDecl] = Tuple.Create(typeCtorDecl, actualTypeParams);
        }
      }

      return typeInstantiations[typeCtorDecl][actualTypeParams];
    }

    public static string MkInstanceName(string name, List<Type> actualTypeParams)
    {
      actualTypeParams.Iter(x => name = $"{name}_{x.UniqueId}");
      return name;
    }

    public Type LookupType(Type type)
    {
      type = TypeProxy.FollowProxy(type.Expanded);
      if (type is CtorType ctorType && MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(ctorType.Decl))
      {
        var instantiatedTypeArguments = ctorType.Arguments.Select(x => LookupType(x)).ToList();
        return new CtorType(Token.NoToken, typeInstantiations[ctorType.Decl][instantiatedTypeArguments],
          new List<Type>());
      }
      else
      {
        return type;
      }
    }

    public IsConstructor InstantiateIsConstructor(IsConstructor isConstructor, List<Type> actualTypeParams)
    {
      InstantiateTypeCtorDecl(isConstructor.DatatypeTypeCtorDecl, actualTypeParams);
      var instantiatedDatatypeTypeCtorDecl =
        (DatatypeTypeCtorDecl)typeInstantiations[isConstructor.DatatypeTypeCtorDecl][
          actualTypeParams];
      return new IsConstructor(isConstructor.tok, instantiatedDatatypeTypeCtorDecl, isConstructor.ConstructorIndex);
    }

    public FieldAccess InstantiateFieldAccess(FieldAccess fieldAccess, List<Type> actualTypeParams)
    {
      InstantiateTypeCtorDecl(fieldAccess.DatatypeTypeCtorDecl, actualTypeParams);
      var instantiatedDatatypeTypeCtorDecl =
        (DatatypeTypeCtorDecl)typeInstantiations[fieldAccess.DatatypeTypeCtorDecl][
          actualTypeParams];
      return new FieldAccess(fieldAccess.tok, fieldAccess.FieldName, instantiatedDatatypeTypeCtorDecl,
        fieldAccess.Accessors);
    }

    public FieldUpdate InstantiateFieldUpdate(FieldUpdate fieldUpdate, List<Type> actualTypeParams)
    {
      return new FieldUpdate(InstantiateFieldAccess(fieldUpdate.FieldAccess, actualTypeParams));
    }

    public TypeCtorDecl InstantiateTypeCtorDecl(string typeName, List<Type> actualTypeParams)
    {
      if (!GetType(typeName, out TypeCtorDecl typeCtorDecl))
      {
        return null;
      }
      var instantiatedFunction = InstantiateTypeCtorDecl(typeCtorDecl, actualTypeParams);
      InstantiateAxioms();
      AddInstantiatedDeclarations();
      return instantiatedFunction;
    }
    
    public Function InstantiateFunction(string functionName, Dictionary<string, Type> typeParamInstantiationMap)
    {
      if (!GetFunction(functionName, out Function function))
      {
        return null;
      }
      var actualTypeParams = function.TypeParameters.Select(tp => typeParamInstantiationMap[tp.Name]).ToList();
      var instantiatedFunction = InstantiateFunction(function, actualTypeParams);
      InstantiateAxioms();
      AddInstantiatedDeclarations();
      return instantiatedFunction;
    }

    private void InstantiateAxioms()
    {
      while (newTriggerTypes.Any(x => x.Value.Count != 0))
      {
        var nextTriggerTypes = this.newTriggerTypes;
        newTriggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
        nextTriggerTypes.Iter(x => { newTriggerTypes.Add(x.Key, new HashSet<CtorType>()); });
        foreach ((var axiom, var tcDecl) in axiomsToBeInstantiated)
        {
          nextTriggerTypes[tcDecl].Iter(trigger => InstantiateAxiom(axiom, trigger.Arguments));
        }
      }
    }

    public bool GetFunction(string functionName, out Function function)
    {
      return nameToFunction.TryGetValue(functionName, out function);
    }

    public bool GetType(string typeName, out TypeCtorDecl typeCtorDecl)
    {
      return nameToTypeCtorDecl.TryGetValue(typeName, out typeCtorDecl);
    }
    
    public bool GetTypeInstantiation(DeclWithFormals decl, out Tuple<DeclWithFormals, Dictionary<string, Type>> value)
    {
      return declWithFormalsToTypeInstantiation.TryGetValue(decl, out value);
    }

    public bool GetTypeInstantiation(TypeCtorDecl decl, out Tuple<TypeCtorDecl, List<Type>> value)
    {
      return typeCtorDeclToTypeInstantiation.TryGetValue(decl, out value);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      if (node.Proc.TypeParameters.Count == 0)
      {
        return base.VisitCallCmd(node);
      }
      else
      {
        return new MonomorphizationDuplicator(this).VisitCallCmd(node);
      }
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      return (CtorType) new MonomorphizationDuplicator(this).VisitType(node);
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      base.VisitTypeSynonymAnnotation(node);
      return node.ExpandedType;
    }

    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      node.Body = new MonomorphizationDuplicator(this).VisitType(node.Body);
      return node;
    }

    public override Expr VisitExpr(Expr node)
    {
      return new MonomorphizationDuplicator(this).VisitExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      return new MonomorphizationDuplicator(this).VisitExpr(node);
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      return new MonomorphizationDuplicator(this).VisitExpr(node);
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      return new MonomorphizationDuplicator(this).VisitFieldAssignLhs(node);
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      return new MonomorphizationDuplicator(this).VisitMapAssignLhs(node);
    }

    // this function may be called directly by monomorphizationDuplicator
    // if a non-generic call to a datatype constructor/selector/membership
    // is discovered in an expression
    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      if (visitedTypeCtorDecls.Contains(node))
      {
        return node;
      }
      visitedTypeCtorDecls.Add(node);
      if (node is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        datatypeTypeCtorDecl.Constructors.Iter(constructor => base.VisitFunction(constructor));
      }
      return base.VisitTypeCtorDecl(node);
    }

    // this function may be called directly by monomorphizationDuplicator
    // if a non-generic function call is discovered in an expression
    public override Function VisitFunction(Function node)
    {
      if (visitedFunctions.Contains(node))
      {
        return node;
      }
      visitedFunctions.Add(node);
      return base.VisitFunction(node);
    }

    public override Constant VisitConstant(Constant node)
    {
      node = base.VisitConstant(node);
      node.TypedIdent = new TypedIdent(node.TypedIdent.tok, node.TypedIdent.Name,
        new MonomorphizationDuplicator(this).VisitType(node.TypedIdent.Type));
      return node;
    }
  }
  
  public class Monomorphizer
  {
    public static MonomorphizableStatus Monomorphize(CoreOptions options, Program program)
    {
      var monomorphizableStatus = MonomorphizableChecker.IsMonomorphizable(program, out var axiomsToBeInstantiated,
        out var polymorphicFunctionAxioms);
      if (monomorphizableStatus == MonomorphizableStatus.Monomorphizable)
      {
        var monomorphizationVisitor = MonomorphizationVisitor.Initialize(options, program, axiomsToBeInstantiated, polymorphicFunctionAxioms);
        program.monomorphizer = new Monomorphizer(monomorphizationVisitor);
      }
      return monomorphizableStatus;
    }

    public Function InstantiateFunction(string functionName, Dictionary<string, Type> typeParamInstantiationMap)
    {
      return monomorphizationVisitor.InstantiateFunction(functionName, typeParamInstantiationMap);
    }

    public TypeCtorDecl InstantiateTypeCtorDecl(string typeCtorDeclName, List<Type> actualTypeParams)
    {
      return monomorphizationVisitor.InstantiateTypeCtorDecl(typeCtorDeclName, actualTypeParams);
    }

    public DeclWithFormals GetOriginalDecl(DeclWithFormals decl)
    {
      if (!monomorphizationVisitor.GetTypeInstantiation(decl, out Tuple<DeclWithFormals, Dictionary<string, Type>> value))
      {
        return decl;
      }
      return value.Item1;
    }
    
    public Dictionary<string, Type> GetTypeInstantiation(DeclWithFormals decl)
    {
      if (!monomorphizationVisitor.GetTypeInstantiation(decl, out Tuple<DeclWithFormals, Dictionary<string, Type>> value))
      {
        return null;
      }
      return value.Item2;
    }
    
    public TypeCtorDecl GetOriginalDecl(TypeCtorDecl decl)
    {
      if (!monomorphizationVisitor.GetTypeInstantiation(decl, out Tuple<TypeCtorDecl, List<Type>> value))
      {
        return decl;
      }
      return value.Item1;
    }
    
    public List<Type> GetTypeInstantiation(TypeCtorDecl decl)
    {
      if (!monomorphizationVisitor.GetTypeInstantiation(decl, out Tuple<TypeCtorDecl, List<Type>> value))
      {
        return null;
      }
      return value.Item2;
    }

    private MonomorphizationVisitor monomorphizationVisitor;
    private Monomorphizer(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
    }
  }
}