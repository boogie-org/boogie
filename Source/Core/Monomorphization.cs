using System;
using System.Collections.Generic;
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

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      BinaryOperator op = node.Fun as BinaryOperator;
      if (op != null && op.Op == BinaryOperator.Opcode.Subtype)
      {
        isMonomorphic = false;
      }
      return base.VisitNAryExpr(node);
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
    
    public override Expr VisitBinderExpr(BinderExpr node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphizable = false;
      }
      return base.VisitBinderExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is BinaryOperator op && op.Op == BinaryOperator.Opcode.Subtype)
      {
        isMonomorphizable = false;
      }
      else if (node.Fun is FunctionCall functionCall)
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

    public override Type VisitMapType(MapType node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphizable = false;
      }
      return base.VisitMapType(node);
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

  class MonomorphizationDuplicator : Duplicator
  {
    private MonomorphizationVisitor monomorphizationVisitor;
    private Absy parentAbsy;
    private Dictionary<TypeVariable, Type> typeParamInstantiation;
    private Dictionary<Variable, Variable> variableMapping;
    private Dictionary<Variable, Variable> boundVarSubst;

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.parentAbsy = null;
      typeParamInstantiation = new Dictionary<TypeVariable, Type>();
      variableMapping = new Dictionary<Variable, Variable>();
      boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor,
      Dictionary<TypeVariable, Type> typeParamInstantiation)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.parentAbsy = null;
      this.typeParamInstantiation = typeParamInstantiation;
      this.variableMapping = new Dictionary<Variable, Variable>();
      this.boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor, Absy parentAbsy,
      Dictionary<TypeVariable, Type> typeParamInstantiation, Dictionary<Variable, Variable> variableMapping)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.parentAbsy = parentAbsy;
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

      if (returnExpr.Fun is IsConstructor isConstructor)
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
      if (typeParamInstantiation.Count == 0)
      {
        return node;
      }
      return typeParamInstantiation[node];
    }

    public override Type VisitMapType(MapType node)
    {
      node = (MapType)node.Clone();
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        node.Arguments[i] = (Type)this.Visit(node.Arguments[i]);
      }

      node.Result = (Type)this.Visit(node.Result);
      return node;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      node = (CtorType)node.Clone();
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        node.Arguments[i] = (Type)this.Visit(node.Arguments[i]);
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
      monomorphizationVisitor.AddInstantiatedDeclarations(program);
      program.AddTopLevelDeclarations(typeCtorDecls);
      Contract.Assert(MonomorphismChecker.IsMonomorphic(program));
      return monomorphizationVisitor;
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
      var forallExpr = (ForallExpr)InstantiateBinderExpr((BinderExpr)axiom.Expr, actualTypeParams);
      var instantiatedAxiom = new Axiom(axiom.tok, forallExpr.Dummies.Count == 0 ? forallExpr.Body : forallExpr,
        axiom.Comment, axiom.Attributes);
      newInstantiatedDeclarations.Add(instantiatedAxiom);
      return instantiatedAxiom;
    }  

    public BinderExpr InstantiateBinderExpr(BinderExpr binderExpr, List<Type> actualTypeParams)
    {
      binderExpr = (BinderExpr)InstantiateAbsy(binderExpr, LinqExtender.Map(binderExpr.TypeParameters, actualTypeParams),
        new Dictionary<Variable, Variable>());
      binderExpr.TypeParameters = new List<TypeVariable>();
      return binderExpr;
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

    private void AddInstantiatedDeclarations(Program program)
    {
      program.AddTopLevelDeclarations(newInstantiatedDeclarations);
      newInstantiatedDeclarations = new HashSet<Declaration>();
    }

    private Absy InstantiateAbsy(Absy absy, Dictionary<TypeVariable, Type> typeParamInstantiation,
      Dictionary<Variable, Variable> variableMapping)
    {
      var monomorphizationDuplicator =
        new MonomorphizationDuplicator(this, absy, typeParamInstantiation, variableMapping);
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
      type = TypeProxy.FollowProxy(type);
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
      AddInstantiatedDeclarations(program);
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
      AddInstantiatedDeclarations(program);
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