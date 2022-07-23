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

    public override BinderExpr VisitBinderExpr(BinderExpr node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitBinderExpr(node);
    }

    public override MapType VisitMapType(MapType node)
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

    public override MapType VisitMapType(MapType node)
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
      var sccs = new StronglyConnectedComponents<TypeVariable>(typeVariableDependencyGraph.Nodes, typeVariableDependencyGraph.Predecessors, typeVariableDependencyGraph.Successors);
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
    
    public override BinderExpr VisitBinderExpr(BinderExpr node)
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

    public override MapType VisitMapType(MapType node)
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
  
  class MonomorphizationVisitor : StandardVisitor
  {
    public CoreOptions Options { get; }
    /*
     * This class monomorphizes a Boogie program.
     * Monomorphization starts from a traversal of monomorphic procedures.
     * Any polymorphic functions and types encountered are monomorphized based on
     * actual type parameters and then the bodies of those functions are recursively
     * traversed.
     *
     * If the program contains polymorphic procedures, a monomorphic version of the procedure
     * is created by substituting a fresh uninterpreted type for each type parameter.
     *
     * MonomorphizationVisitor uses a helper class MonomorphizationDuplicator.
     * While the former does in-place update as a result of monomorphization,
     * the latter creates a duplicate copy.  MonomorphizationDuplicator is needed
     * because a polymorphic function, type, or procedure may be visited several
     * types in different type contexts.
     */
    
    class MonomorphizationDuplicator : Duplicator
    {
      private MonomorphizationVisitor monomorphizationVisitor;
      private HashSet<Declaration> newInstantiatedDeclarations;
      private Dictionary<TypeVariable, Type> typeParamInstantiation;
      private Dictionary<Variable, Variable> variableMapping;
      private Dictionary<Variable, Variable> boundVarSubst;

      public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor)
      {
        this.monomorphizationVisitor = monomorphizationVisitor;
        newInstantiatedDeclarations = new HashSet<Declaration>();
        typeParamInstantiation = new Dictionary<TypeVariable, Type>();
        variableMapping = new Dictionary<Variable, Variable>();
        boundVarSubst = new Dictionary<Variable, Variable>();
      }

      public Axiom InstantiateAxiom(Axiom axiom, List<Type> actualTypeParams)
      {
        var forallExpr = (ForallExpr) axiom.Expr;
        var savedTypeParamInstantiation = this.typeParamInstantiation;
        this.typeParamInstantiation = LinqExtender.Map(forallExpr.TypeParameters, actualTypeParams);
        forallExpr = (ForallExpr) VisitExpr(forallExpr);
        this.typeParamInstantiation = savedTypeParamInstantiation;
        forallExpr.TypeParameters = new List<TypeVariable>();
        var instantiatedAxiom = new Axiom(axiom.tok, forallExpr.Dummies.Count == 0 ? forallExpr.Body : forallExpr,
          axiom.Comment, axiom.Attributes);
        newInstantiatedDeclarations.Add(instantiatedAxiom);
        return instantiatedAxiom;
      }

      public Function InstantiateFunction(Function func, List<Type> actualTypeParams)
      {
        if (!monomorphizationVisitor.functionInstantiations[func].ContainsKey(actualTypeParams))
        {
          var funcTypeParamInstantiation = LinqExtender.Map(func.TypeParameters, actualTypeParams);
          var instantiatedFunction =
            InstantiateFunctionSignature(func, actualTypeParams, funcTypeParamInstantiation);
          var variableMapping = LinqExtender.Map(func.InParams, instantiatedFunction.InParams);
          newInstantiatedDeclarations.Add(instantiatedFunction);
          monomorphizationVisitor.functionInstantiations[func][actualTypeParams] = instantiatedFunction;
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
        return monomorphizationVisitor.functionInstantiations[func][actualTypeParams];
      }

      public void AddInstantiatedDeclarations(Program program)
      {
        program.AddTopLevelDeclarations(newInstantiatedDeclarations);
        newInstantiatedDeclarations = new HashSet<Declaration>();
      }

      private Absy InstantiateAbsy(Absy absy, Dictionary<TypeVariable, Type> typeParamInstantiation,
        Dictionary<Variable, Variable> variableMapping)
      {
        var savedTypeParamInstantiation = this.typeParamInstantiation;
        this.typeParamInstantiation = typeParamInstantiation;
        var savedVariableMapping = this.variableMapping;
        this.variableMapping = variableMapping;
        var newAbsy = Visit(absy);
        this.variableMapping = savedVariableMapping;
        this.typeParamInstantiation = savedTypeParamInstantiation;
        return newAbsy;
      }

      public Procedure InstantiateProcedure(Procedure proc, List<Type> actualTypeParams)
      {
        if (!monomorphizationVisitor.procInstantiations[proc].ContainsKey(actualTypeParams))
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
          monomorphizationVisitor.procInstantiations[proc][actualTypeParams] = instantiatedProc;
        }
        return monomorphizationVisitor.procInstantiations[proc][actualTypeParams];
      }
      
      public Implementation InstantiateImplementation(Implementation impl, List<Type> actualTypeParams)
      {
        if (!monomorphizationVisitor.implInstantiations[impl].ContainsKey(actualTypeParams))
        {
          var implTypeParamInstantiation = LinqExtender.Map(impl.TypeParameters, actualTypeParams);
          var instantiatedInParams = InstantiateFormals(impl.InParams, implTypeParamInstantiation);
          var instantiatedOutParams = InstantiateFormals(impl.OutParams, implTypeParamInstantiation);
          var instantiatedLocalVariables = InstantiateLocalVariables(impl.LocVars, implTypeParamInstantiation);
          var variableMapping = LinqExtender.Map(impl.InParams.Union(impl.OutParams).Union(impl.LocVars),
            instantiatedInParams.Union(instantiatedOutParams).Union(instantiatedLocalVariables));
          var blocks = impl.Blocks
            .Select(block => (Block) InstantiateAbsy(block, implTypeParamInstantiation, variableMapping)).ToList();
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
          monomorphizationVisitor.implInstantiations[impl][actualTypeParams] = instantiatedImpl;
        }
        return monomorphizationVisitor.implInstantiations[impl][actualTypeParams];
      }

      private List<Variable> InstantiateFormals(List<Variable> variables, Dictionary<TypeVariable, Type> declTypeParamInstantiation)
      {
        var savedTypeParamInstantiation = this.typeParamInstantiation;
        this.typeParamInstantiation = declTypeParamInstantiation;
        var instantiatedVariables =
          variables.Select(x => (Formal) x).Select(x =>
              new Formal(x.tok, new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name, VisitType(x.TypedIdent.Type)),
                x.InComing))
            .ToList<Variable>();
        this.typeParamInstantiation = savedTypeParamInstantiation;
        return instantiatedVariables;
      }

      private List<Variable> InstantiateLocalVariables(List<Variable> variables, Dictionary<TypeVariable, Type> declTypeParamInstantiation)
      {
        var savedTypeParamInstantiation = this.typeParamInstantiation;
        this.typeParamInstantiation = declTypeParamInstantiation;
        var instantiatedVariables =
          variables.Select(x =>
              new LocalVariable(x.tok, new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name, VisitType(x.TypedIdent.Type))))
            .ToList<Variable>();
        this.typeParamInstantiation = savedTypeParamInstantiation;
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

      private void InstantiateType(TypeCtorDecl typeCtorDecl, List<Type> actualTypeParams)
      {
        if (!monomorphizationVisitor.typeInstantiations[typeCtorDecl].ContainsKey(actualTypeParams))
        {
          if (typeCtorDecl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
          {
            var newDatatypeTypeCtorDecl = new DatatypeTypeCtorDecl(
              new TypeCtorDecl(datatypeTypeCtorDecl.tok,
                MkInstanceName(datatypeTypeCtorDecl.Name, actualTypeParams), 0,
                datatypeTypeCtorDecl.Attributes));
            newInstantiatedDeclarations.Add(newDatatypeTypeCtorDecl);
            monomorphizationVisitor.typeInstantiations[datatypeTypeCtorDecl]
              .Add(actualTypeParams, newDatatypeTypeCtorDecl);
            datatypeTypeCtorDecl.Constructors.Iter(constructor =>
              InstantiateDatatypeConstructor(newDatatypeTypeCtorDecl, constructor, actualTypeParams));
          }
          else
          {
            var newTypeCtorDecl =
              new TypeCtorDecl(typeCtorDecl.tok, MkInstanceName(typeCtorDecl.Name, actualTypeParams), 0,
                typeCtorDecl.Attributes);
            newInstantiatedDeclarations.Add(newTypeCtorDecl);
            monomorphizationVisitor.typeInstantiations[typeCtorDecl].Add(actualTypeParams, newTypeCtorDecl);
          }
        }
      }

      private void InstantiateDatatypeConstructor(DatatypeTypeCtorDecl newDatatypeTypeCtorDecl,
        DatatypeConstructor constructor, List<Type> actualTypeParams)
      {
        var newConstructor = new DatatypeConstructor(newDatatypeTypeCtorDecl,
          InstantiateFunctionSignature(constructor, actualTypeParams,
            LinqExtender.Map(constructor.TypeParameters, actualTypeParams)));
        newConstructor.membership = DatatypeMembership.NewDatatypeMembership(newConstructor);
        for (int i = 0; i < newConstructor.InParams.Count; i++)
        {
          newConstructor.AddSelector(DatatypeSelector.NewDatatypeSelector(newConstructor, i));
        }
      }

      private static string MkInstanceName(string name, List<Type> actualTypeParams)
      {
        actualTypeParams.Iter(x => name = $"{name}_{x.UniqueId}");
        return name;
      }
      
      private Type LookupType(Type type)
      {
        type = TypeProxy.FollowProxy(type);
        if (type is CtorType ctorType && MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(ctorType.Decl))
        {
          var instantiatedTypeArguments = ctorType.Arguments.Select(x => LookupType(x)).ToList();
          return new CtorType(Token.NoToken, monomorphizationVisitor.typeInstantiations[ctorType.Decl][instantiatedTypeArguments],
            new List<Type>());
        }
        else
        {
          return type;
        }
      }

      private FieldAccess InstantiateFieldAccess(FieldAccess fieldAccess, TypeParamInstantiation typeParameters)
      {
        var selector = fieldAccess.Selector;
        var constructor = selector.constructor;
        var actualTypeParams =
          typeParameters.FormalTypeParams.Select(x =>
              TypeProxy.FollowProxy(typeParameters[x]).Substitute(typeParamInstantiation))
            .Select(x => LookupType(x)).ToList();
        InstantiateType(constructor.datatypeTypeCtorDecl, actualTypeParams);
        var datatypeTypeCtorDecl =
          (DatatypeTypeCtorDecl)monomorphizationVisitor.typeInstantiations[constructor.datatypeTypeCtorDecl][
            actualTypeParams];
        return new FieldAccess(fieldAccess.tok, datatypeTypeCtorDecl.Constructors[constructor.index].selectors[selector.index]);
      }
      
      public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
      {
        var fieldAssignLhs = (FieldAssignLhs)base.VisitFieldAssignLhs(node);
        var fieldAccess = fieldAssignLhs.FieldAccess;
        var constructor = fieldAccess.Selector.constructor;
        if (constructor.TypeParameters.Count == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(constructor.datatypeTypeCtorDecl);
        }
        else
        {
          fieldAssignLhs.FieldAccess = InstantiateFieldAccess(fieldAssignLhs.FieldAccess, fieldAssignLhs.TypeParameters);
        }
        return fieldAssignLhs;
      }

      public override Expr VisitNAryExpr(NAryExpr node)
      {
        var returnExpr = (NAryExpr) base.VisitNAryExpr(node);
        returnExpr.Type = VisitType(node.Type);
        if (returnExpr.Fun is TypeCoercion)
        {
          return returnExpr.Args[0];
        }
        if (returnExpr.Fun is FieldAccess fieldAccess)
        {
          var constructor = fieldAccess.Selector.constructor;
          if (constructor.TypeParameters.Count == 0)
          {
            monomorphizationVisitor.VisitTypeCtorDecl(constructor.datatypeTypeCtorDecl);
          }
          else
          {
            returnExpr.Fun = InstantiateFieldAccess(fieldAccess, returnExpr.TypeParameters);
            returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          }
        }
        else if (returnExpr.Fun is FunctionCall functionCall)
        {
          // a non-generic function must be processed to rewrite any generic types it uses
          // to the corresponding instantiated types
          if (functionCall.Func.TypeParameters.Count == 0)
          {
            if (functionCall.Func is DatatypeMembership membership)
            {
              monomorphizationVisitor.VisitTypeCtorDecl(membership.constructor.datatypeTypeCtorDecl);
            }
            else if (functionCall.Func is DatatypeSelector selector)
            {
              monomorphizationVisitor.VisitTypeCtorDecl(selector.constructor.datatypeTypeCtorDecl);
            }
            else if (functionCall.Func is DatatypeConstructor constructor)
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
            var actualTypeParams =
              returnExpr.TypeParameters.FormalTypeParams.Select(x =>
                  TypeProxy.FollowProxy(returnExpr.TypeParameters[x]).Substitute(typeParamInstantiation))
                .Select(x => LookupType(x)).ToList();
            if (functionCall.Func is DatatypeMembership membership)
            {
              InstantiateType(membership.constructor.datatypeTypeCtorDecl, actualTypeParams);
              var datatypeTypeCtorDecl =
                (DatatypeTypeCtorDecl) monomorphizationVisitor.typeInstantiations[membership.constructor.datatypeTypeCtorDecl][actualTypeParams];
              returnExpr.Fun =
                new FunctionCall(datatypeTypeCtorDecl.Constructors[membership.constructor.index].membership);
            }
            else if (functionCall.Func is DatatypeSelector selector)
            {
              InstantiateType(selector.constructor.datatypeTypeCtorDecl, actualTypeParams);
              var datatypeTypeCtorDecl =
                (DatatypeTypeCtorDecl) monomorphizationVisitor.typeInstantiations[selector.constructor.datatypeTypeCtorDecl][actualTypeParams];
              returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[selector.constructor.index]
                .selectors[selector.index]);
            }
            else if (functionCall.Func is DatatypeConstructor constructor)
            {
              InstantiateType(constructor.datatypeTypeCtorDecl, actualTypeParams);
              var datatypeTypeCtorDecl =
                (DatatypeTypeCtorDecl) monomorphizationVisitor.typeInstantiations[constructor.datatypeTypeCtorDecl][actualTypeParams];
              returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[constructor.index]);
            }
            else
            {
              returnExpr.Fun = new FunctionCall(InstantiateFunction(functionCall.Func, actualTypeParams));
            }
            returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          }
        }
        return returnExpr;
      }

      private bool IsInlined(Implementation impl)
      {
        if (monomorphizationVisitor.Options.ProcedureInlining == CoreOptions.Inlining.None)
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

      public override Cmd VisitCallCmd(CallCmd node)
      {
        var returnCallCmd = (CallCmd) base.VisitCallCmd(node);
        if (returnCallCmd.Proc.TypeParameters.Count > 0)
        {
          var actualTypeParams =
            returnCallCmd.TypeParameters.FormalTypeParams.Select(x =>
                TypeProxy.FollowProxy(returnCallCmd.TypeParameters[x]).Substitute(typeParamInstantiation))
              .Select(LookupType).ToList();
          returnCallCmd.Proc = InstantiateProcedure(node.Proc, actualTypeParams);
          returnCallCmd.callee = returnCallCmd.Proc.Name;
          returnCallCmd.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          if (monomorphizationVisitor.procToImpl.ContainsKey(node.Proc))
          {
            var impl = monomorphizationVisitor.procToImpl[node.Proc];
            if (IsInlined(impl))
            {
              InstantiateImplementation(impl, actualTypeParams);
            }
          }
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

      public override MapType VisitMapType(MapType node)
      {
        node = (MapType) node.Clone();
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = (Type) this.Visit(node.Arguments[i]);
        }

        node.Result = (Type) this.Visit(node.Result);
        return node;
      }

      public override CtorType VisitCtorType(CtorType node)
      {
        node = (CtorType) node.Clone();
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = (Type) this.Visit(node.Arguments[i]);
        }
        var typeCtorDecl = node.Decl;
        if (monomorphizationVisitor.triggerTypes.ContainsKey(typeCtorDecl) && !monomorphizationVisitor.triggerTypes[typeCtorDecl].Contains(node))
        {
          monomorphizationVisitor.triggerTypes[typeCtorDecl].Add(node);
          monomorphizationVisitor.newTriggerTypes[typeCtorDecl].Add(node);
        }
        if (MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(typeCtorDecl))
        {
          InstantiateType(typeCtorDecl, node.Arguments);
          return new CtorType(node.tok, monomorphizationVisitor.typeInstantiations[typeCtorDecl][node.Arguments],
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
        return (Type) Visit(node);
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

      public override BinderExpr VisitBinderExpr(BinderExpr node)
      {
        var oldToNew = node.Dummies.ToDictionary(x => x,
          x => new BoundVariable(x.tok, new TypedIdent(x.tok, x.Name, VisitType(x.TypedIdent.Type)),
            x.Attributes));
        foreach (var x in node.Dummies)
        {
          boundVarSubst.Add(x, oldToNew[x]);
        }

        BinderExpr expr = base.VisitBinderExpr(node);
        expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
        // We process triggers of quantifier expressions here, because otherwise the
        // substitutions for bound variables have to be leaked outside this procedure.
        if (node is QuantifierExpr quantifierExpr)
        {
          if (quantifierExpr.Triggers != null)
          {
            ((QuantifierExpr) expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
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
        return (QuantifierExpr) this.VisitBinderExpr(node);
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

        var expr = (LetExpr) base.VisitLetExpr(node);
        expr.Type = VisitType(expr.Type);
        expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
        foreach (var x in node.Dummies)
        {
          boundVarSubst.Remove(x);
        }

        return expr;
      }
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
        var instantiatedImpl =
          monomorphizationVisitor.monomorphizationDuplicator.InstantiateImplementation(impl, actualTypeParams);
        instantiatedImpl.Proc = monomorphizationVisitor.monomorphizationDuplicator.InstantiateProcedure(impl.Proc, actualTypeParams);
      });
      monomorphizationVisitor.VisitProgram(program);
      monomorphizationVisitor.InstantiateAxioms();
      monomorphizationVisitor.monomorphizationDuplicator.AddInstantiatedDeclarations(program);
      program.AddTopLevelDeclarations(typeCtorDecls);
      Contract.Assert(MonomorphismChecker.IsMonomorphic(program));
      return monomorphizationVisitor;
    }
    
    public Function Monomorphize(string functionName, Dictionary<string, Type> typeParamInstantiationMap)
    {
      if (!nameToFunction.ContainsKey(functionName))
      {
        return null;
      }
      var function = nameToFunction[functionName];
      var actualTypeParams = function.TypeParameters.Select(tp => typeParamInstantiationMap[tp.Name]).ToList();
      var instantiatedFunction = monomorphizationDuplicator.InstantiateFunction(function, actualTypeParams);
      InstantiateAxioms();
      monomorphizationDuplicator.AddInstantiatedDeclarations(program);
      return instantiatedFunction;
    }

    private Program program;
    private Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated;
    private Dictionary<string, Function> nameToFunction;
    private Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations;
    private Dictionary<Implementation, Dictionary<List<Type>, Implementation>> implInstantiations;
    private Dictionary<Procedure, Dictionary<List<Type>, Procedure>> procInstantiations;
    private Dictionary<TypeCtorDecl, Dictionary<List<Type>, TypeCtorDecl>> typeInstantiations;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> triggerTypes;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> newTriggerTypes;
    private HashSet<TypeCtorDecl> visitedTypeCtorDecls;
    private HashSet<Function> visitedFunctions;
    private MonomorphizationDuplicator monomorphizationDuplicator;
    private Dictionary<Procedure, Implementation> procToImpl;
    
    private MonomorphizationVisitor(CoreOptions options, Program program,
      Dictionary<Axiom, TypeCtorDecl> axiomsToBeInstantiated, HashSet<Axiom> polymorphicFunctionAxioms)
    {
      Options = options;
      this.program = program;
      this.axiomsToBeInstantiated = axiomsToBeInstantiated;
      implInstantiations = new Dictionary<Implementation, Dictionary<List<Type>, Implementation>>();
      program.TopLevelDeclarations.OfType<Implementation>().Where(impl => impl.TypeParameters.Count > 0).Iter(
        impl =>
        {
          implInstantiations.Add(impl, new Dictionary<List<Type>, Implementation>(new ListComparer<Type>()));
        });
      procInstantiations = new Dictionary<Procedure, Dictionary<List<Type>, Procedure>>();
      program.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.TypeParameters.Count > 0).Iter(
        proc =>
        {
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
      typeInstantiations = new Dictionary<TypeCtorDecl, Dictionary<List<Type>, TypeCtorDecl>>();
      program.TopLevelDeclarations.OfType<TypeCtorDecl>()
        .Where(typeCtorDecl => MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(typeCtorDecl)).Iter(
          typeCtorDecl =>
            typeInstantiations.Add(typeCtorDecl, new Dictionary<List<Type>, TypeCtorDecl>(new ListComparer<Type>())));
      triggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
      newTriggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
      axiomsToBeInstantiated.Values.ToHashSet().Iter(typeCtorDecl =>
      {
        triggerTypes.Add(typeCtorDecl, new HashSet<CtorType>());
        newTriggerTypes.Add(typeCtorDecl, new HashSet<CtorType>());
      });
      this.visitedTypeCtorDecls = new HashSet<TypeCtorDecl>();
      this.visitedFunctions = new HashSet<Function>();
      monomorphizationDuplicator = new MonomorphizationDuplicator(this);
      this.procToImpl = new Dictionary<Procedure, Implementation>();
      program.TopLevelDeclarations.OfType<Implementation>().Iter(impl => this.procToImpl[impl.Proc] = impl);
      program.RemoveTopLevelDeclarations(decl => 
        decl is Implementation impl && implInstantiations.ContainsKey(impl) ||
        decl is Procedure proc && procInstantiations.ContainsKey(proc) ||
        decl is Function function && functionInstantiations.ContainsKey(function) ||
        decl is TypeCtorDecl typeCtorDecl && typeInstantiations.ContainsKey(typeCtorDecl) ||
        decl is Axiom axiom && (axiomsToBeInstantiated.ContainsKey(axiom) || polymorphicFunctionAxioms.Contains(axiom)));
    }

    public void InstantiateAxioms()
    {
      while (newTriggerTypes.Any(x => x.Value.Count != 0))
      {
        var nextTriggerTypes = this.newTriggerTypes;
        newTriggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
        nextTriggerTypes.Iter(x => { newTriggerTypes.Add(x.Key, new HashSet<CtorType>()); });
        foreach ((var axiom, var tcDecl) in axiomsToBeInstantiated)
        {
          nextTriggerTypes[tcDecl].Iter(trigger => monomorphizationDuplicator.InstantiateAxiom(axiom, trigger.Arguments));
        }
      }
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      if (node.Proc.TypeParameters.Count == 0)
      {
        return base.VisitCallCmd(node);
      }
      else
      {
        return monomorphizationDuplicator.VisitCallCmd(node);
      }
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      return (CtorType) monomorphizationDuplicator.VisitType(node);
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      base.VisitTypeSynonymAnnotation(node);
      return node.ExpandedType;
    }

    public override Expr VisitExpr(Expr node)
    {
      return monomorphizationDuplicator.VisitExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      return monomorphizationDuplicator.VisitExpr(node);
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      return monomorphizationDuplicator.VisitExpr(node);
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
        datatypeTypeCtorDecl.Constructors.Iter(constructor => VisitConstructor(constructor));
      }
      return base.VisitTypeCtorDecl(node);
    }

    private void VisitConstructor(DatatypeConstructor constructor)
    {
      base.VisitFunction(constructor);
      base.VisitFunction(constructor.membership);
      constructor.selectors.Iter(selector => base.VisitFunction(selector));
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
  }
  
  public class Monomorphizer
  {
    public static MonomorphizableStatus Monomorphize(CoreOptions options, Program program)
    {
      var monomorphizableStatus = MonomorphizableChecker.IsMonomorphizable(program, out var axiomsToBeInstantiated, out var polymorphicFunctionAxioms);
      if (monomorphizableStatus == MonomorphizableStatus.Monomorphizable)
      {
        var monomorphizationVisitor = MonomorphizationVisitor.Initialize(options, program, axiomsToBeInstantiated, polymorphicFunctionAxioms);
        program.monomorphizer = new Monomorphizer(monomorphizationVisitor);
      }
      return monomorphizableStatus;
    }

    public Function Monomorphize(string functionName, Dictionary<string, Type> typeParamInstantiationMap)
    {
      return monomorphizationVisitor.Monomorphize(functionName, typeParamInstantiationMap);
    }

    private MonomorphizationVisitor monomorphizationVisitor;
    private Monomorphizer(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
    }
  }
}