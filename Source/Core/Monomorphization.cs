using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.Reflection.Metadata;

namespace Microsoft.Boogie
{
  public class PolymorphismChecker : ReadOnlyVisitor
  {
    public static bool IsMonomorphic(Program program)
    {
      var checker = new PolymorphismChecker();
      checker.VisitProgram(program);
      return checker.isMonomorphic;
    }
    
    bool isMonomorphic;

    private PolymorphismChecker()
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
  }

  class MonomorphizableChecker : ReadOnlyVisitor
  {
    public static bool IsMonomorphizable(Program program, out HashSet<Axiom> axiomsToBeInstantiated, out HashSet<Axiom> polymorphicFunctionAxioms)
    {
      var checker = new MonomorphizableChecker(program);
      checker.VisitProgram(program);
      axiomsToBeInstantiated = checker.axiomsToBeInstantiated;
      polymorphicFunctionAxioms = checker.polymorphicFunctionAxioms;
      return checker.isMonomorphizable;
    }
    
    private Program program;
    private bool isMonomorphizable;
    private HashSet<Axiom> axiomsToBeInstantiated;
    private HashSet<Axiom> polymorphicFunctionAxioms;
    
    private MonomorphizableChecker(Program program)
    {
      this.program = program;
      this.isMonomorphizable = true;
      this.polymorphicFunctionAxioms = program.TopLevelDeclarations.OfType<Function>().Where(f => f.TypeParameters.Count > 0 && f.DefinitionAxiom != null)
        .Select(f => f.DefinitionAxiom).ToHashSet();
      this.axiomsToBeInstantiated = new HashSet<Axiom>();
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
      BinaryOperator op = node.Fun as BinaryOperator;
      if (op != null && op.Op == BinaryOperator.Opcode.Subtype)
      {
        isMonomorphizable = false;
      }
      return base.VisitNAryExpr(node);
    }

    public override MapType VisitMapType(MapType node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphizable = false;
      }
      return base.VisitMapType(node);
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphizable = false;
        return node;
      }
      return base.VisitImplementation(node);
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
      axiomsToBeInstantiated.Add(axiom);
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
  }
  
  class ExprMonomorphizationVisitor : Duplicator
  {
    private class TypeInstantiationComparer : IEqualityComparer<List<Type>>
    {
      public bool Equals(List<Type> l1, List<Type> l2)
      {
        if (l1.Count != l2.Count)
        {
          return false;
        }

        for (int i = 0; i < l1.Count; i++)
        {
          if (!l1[i].Equals(l2[i]))
          {
            return false;
          }
        }

        return true;
      }

      public int GetHashCode(List<Type> l)
      {
        int hCode = 0;
        l.Iter(x => { hCode = hCode ^ x.GetHashCode(); });
        return hCode.GetHashCode();
      }
    }

    private Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations;
    private Dictionary<DatatypeTypeCtorDecl, Dictionary<List<Type>, DatatypeTypeCtorDecl>> datatypeInstantiations;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> triggerTypes;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> newTriggerTypes;
    private Dictionary<TypeVariable, Type> typeParamInstantiation;
    private Dictionary<Variable, Variable> variableMapping;
    private Dictionary<Variable, Variable> boundVarSubst;

    public ExprMonomorphizationVisitor(
      Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations,
      Dictionary<DatatypeTypeCtorDecl, Dictionary<List<Type>, DatatypeTypeCtorDecl>> datatypeInstantiations,
      Dictionary<TypeCtorDecl, HashSet<CtorType>> triggerTypes,
      Dictionary<TypeCtorDecl, HashSet<CtorType>> newTriggerTypes)
    {
      this.functionInstantiations = functionInstantiations;
      this.datatypeInstantiations = datatypeInstantiations;
      this.triggerTypes = triggerTypes;
      this.newTriggerTypes = newTriggerTypes;
      typeParamInstantiation = new Dictionary<TypeVariable, Type>();
      variableMapping = new Dictionary<Variable, Variable>();
      boundVarSubst = new Dictionary<Variable, Variable>();
    }
    
    public static List<Axiom> InstantiateAxiom(
      Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations,
      Dictionary<DatatypeTypeCtorDecl, Dictionary<List<Type>, DatatypeTypeCtorDecl>> datatypeInstantiations,
      Dictionary<TypeCtorDecl, HashSet<CtorType>> triggerTypes,
      Dictionary<TypeCtorDecl, HashSet<CtorType>> newTriggerTypes,
      Axiom axiom,
      HashSet<CtorType> triggers)
    {
      var instantiatedAxioms = new List<Axiom>();
      var visitor = new ExprMonomorphizationVisitor(functionInstantiations, datatypeInstantiations, triggerTypes, newTriggerTypes);
      triggers.Iter(trigger =>
      {
        instantiatedAxioms.Add(visitor.InstantiateAxiom(axiom, trigger.Arguments));
      });
      return instantiatedAxioms;
    }
    
    private Axiom InstantiateAxiom(Axiom axiom, List<Type> funcTypeParamInstantiations)
    {
      var forallExpr = (ForallExpr) axiom.Expr;
      var savedTypeParamInstantiation = this.typeParamInstantiation;
      this.typeParamInstantiation = LinqExtender.Map(forallExpr.TypeParameters, funcTypeParamInstantiations);
      forallExpr = (ForallExpr) VisitExpr(forallExpr);
      this.typeParamInstantiation = savedTypeParamInstantiation;
      forallExpr.TypeParameters = new List<TypeVariable>();
      return new Axiom(axiom.tok, forallExpr.Dummies.Count == 0 ? forallExpr.Body : forallExpr, axiom.Comment, axiom.Attributes);
    }
    
    private Function InstantiateFunction(Function func, List<Type> funcTypeParamInstantiations, Dictionary<TypeVariable, Type> funcTypeParamInstantiation)
    {
      if (!functionInstantiations.ContainsKey(func))
      {
        functionInstantiations[func] = new Dictionary<List<Type>, Function>(new TypeInstantiationComparer());
      }
      if (!functionInstantiations[func].ContainsKey(funcTypeParamInstantiations))
      {
        var instantiatedFunction = InstantiateFunctionSignature(func, funcTypeParamInstantiations, funcTypeParamInstantiation);
        functionInstantiations[func][funcTypeParamInstantiations] = instantiatedFunction;
        var savedTypeParamInstantiation = this.typeParamInstantiation;
        this.typeParamInstantiation = funcTypeParamInstantiation;
        var savedVariableMapping = this.variableMapping;
        this.variableMapping = LinqExtender.Map(func.InParams, instantiatedFunction.InParams);
        if (func.Body != null)
        {
          instantiatedFunction.Body = VisitExpr(func.Body);
        }
        else if (func.DefinitionBody != null)
        {
          instantiatedFunction.DefinitionBody = (NAryExpr) VisitExpr(func.DefinitionBody);
        }
        else if (func.DefinitionAxiom != null)
        {
          instantiatedFunction.DefinitionAxiom =
            this.InstantiateAxiom(func.DefinitionAxiom, funcTypeParamInstantiations);
        }
        this.variableMapping = savedVariableMapping;
        this.typeParamInstantiation = savedTypeParamInstantiation;
      }
      return functionInstantiations[func][funcTypeParamInstantiations];
    }

    private Function InstantiateFunctionSignature(Function func, List<Type> funcTypeParamInstantiations, Dictionary<TypeVariable, Type> funcTypeParamInstantiation)
    {
      var savedTypeParamInstantiation = this.typeParamInstantiation;
      this.typeParamInstantiation = funcTypeParamInstantiation;
      var instantiatedInParams =
        func.InParams.Select(x =>
            new Formal(x.tok, new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name, VisitType(x.TypedIdent.Type)),
              true))
          .ToList<Variable>();
      var instantiatedOutParams =
        func.OutParams.Select(x =>
            new Formal(x.tok, new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name, VisitType(x.TypedIdent.Type)),
              false))
          .ToList<Variable>();
      var instantiatedFunction = new Function(
        func.tok, 
        MkInstanceName(func.Name, funcTypeParamInstantiations),
        new List<TypeVariable>(),
        instantiatedInParams, 
        instantiatedOutParams.First(), 
        func.Comment, 
        func.Attributes); 
      this.typeParamInstantiation = savedTypeParamInstantiation;
      return instantiatedFunction;
    }

    private void InstantiateDatatype(DatatypeTypeCtorDecl datatypeTypeCtorDecl,
      List<Type> typeParamInstantiations)
    {
      if (!datatypeInstantiations.ContainsKey(datatypeTypeCtorDecl))
      {
        datatypeInstantiations[datatypeTypeCtorDecl] =
          new Dictionary<List<Type>, DatatypeTypeCtorDecl>(new TypeInstantiationComparer());
      }
      if (!datatypeInstantiations[datatypeTypeCtorDecl].ContainsKey(typeParamInstantiations))
      {
        var newDatatypeTypeCtorDecl = new DatatypeTypeCtorDecl(
          new TypeCtorDecl(datatypeTypeCtorDecl.tok, MkInstanceName(datatypeTypeCtorDecl.Name, typeParamInstantiations),
            0, datatypeTypeCtorDecl.Attributes));
        datatypeInstantiations[datatypeTypeCtorDecl].Add(typeParamInstantiations, newDatatypeTypeCtorDecl);
        datatypeTypeCtorDecl.Constructors.Iter(constructor =>
          InstantiateDatatypeConstructor(newDatatypeTypeCtorDecl, constructor, typeParamInstantiations));
      }
    }

    private void InstantiateDatatypeConstructor(DatatypeTypeCtorDecl newDatatypeTypeCtorDecl, DatatypeConstructor constructor, List<Type> typeParamInstantiations)
    {
      var newConstructor = new DatatypeConstructor(newDatatypeTypeCtorDecl,
        InstantiateFunctionSignature(constructor, typeParamInstantiations, LinqExtender.Map(constructor.TypeParameters, typeParamInstantiations)));
      newConstructor.membership = DatatypeMembership.NewDatatypeMembership(newConstructor);
      for (int i = 0; i < newConstructor.InParams.Count; i++)
      {
        newConstructor.selectors.Add(DatatypeSelector.NewDatatypeSelector(newConstructor, i));
      }
    }
    
    private static string MkInstanceName(string name, List<Type> typeParamInstantiations)
    {
      typeParamInstantiations.Iter(x => name = $"{name}_{x.UniqueId}");
      return name;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var returnExpr = (NAryExpr) base.VisitNAryExpr(node);
      if (returnExpr.Fun is TypeCoercion)
      {
        return returnExpr.Args[0];
      }
      if (returnExpr.Fun is FunctionCall functionCall)
      {
        if (functionCall.Func.TypeParameters.Count > 0)
        {
          var typeParamInstantiations =
            returnExpr.TypeParameters.FormalTypeParams.Select(x =>
              TypeProxy.FollowProxy(returnExpr.TypeParameters[x]).Substitute(typeParamInstantiation)).ToList();
          if (functionCall.Func is DatatypeMembership membership)
          {
            InstantiateDatatype(membership.constructor.datatypeTypeCtorDecl, typeParamInstantiations);
            var datatypeTypeCtorDecl =
              datatypeInstantiations[membership.constructor.datatypeTypeCtorDecl][typeParamInstantiations];
            returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[membership.constructor.index].membership);
          }
          else if (functionCall.Func is DatatypeSelector selector)
          {
            InstantiateDatatype(selector.constructor.datatypeTypeCtorDecl, typeParamInstantiations);
            var datatypeTypeCtorDecl =
              datatypeInstantiations[selector.constructor.datatypeTypeCtorDecl][typeParamInstantiations];
            returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[selector.constructor.index].selectors[selector.index]);
          }
          else if (functionCall.Func is DatatypeConstructor constructor)
          {
            InstantiateDatatype(constructor.datatypeTypeCtorDecl, typeParamInstantiations);
            var datatypeTypeCtorDecl =
              datatypeInstantiations[constructor.datatypeTypeCtorDecl][typeParamInstantiations];
            returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[constructor.index]);
          }
          else
          {
            var funcTypeParamInstantiation = LinqExtender.Map(returnExpr.TypeParameters.FormalTypeParams, typeParamInstantiations);
            returnExpr.Fun = new FunctionCall(InstantiateFunction(functionCall.Func, typeParamInstantiations, funcTypeParamInstantiation));
          }
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          returnExpr.Type = TypeProxy.FollowProxy(returnExpr.Type);
        }
      }
      return returnExpr;
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
      if (typeCtorDecl is DatatypeTypeCtorDecl datatypeTypeCtorDecl && typeCtorDecl.Arity > 0)
      {
        InstantiateDatatype(datatypeTypeCtorDecl, node.Arguments);
        return new CtorType(node.tok, datatypeInstantiations[datatypeTypeCtorDecl][node.Arguments], new List<Type>());
      } 
      if (triggerTypes.ContainsKey(typeCtorDecl) && !triggerTypes[typeCtorDecl].Contains(node))
      {
        triggerTypes[typeCtorDecl].Add(node);
        newTriggerTypes[typeCtorDecl].Add(node);
      }
      return node;
    }

    public override Type VisitType(Type node)
    {
      return (Type) Visit(node);
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
      return base.VisitIdentifierExpr(node);
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
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }
      return expr;
    }
  }

  public class MonomorphizationVisitor : StandardVisitor
  {
    public static bool Monomorphize(Program program)
    {
      HashSet<Axiom> axiomsToBeInstantiated, polymorphicFunctionAxioms;
      var isMonomorphizable = MonomorphizableChecker.IsMonomorphizable(program, out axiomsToBeInstantiated, out polymorphicFunctionAxioms);
      if (isMonomorphizable)
      {
        var visitor = new MonomorphizationVisitor(program, axiomsToBeInstantiated, polymorphicFunctionAxioms);
        visitor.VisitProgram(program);
        visitor.InstantiateAxioms(axiomsToBeInstantiated);
        program.RemoveTopLevelDeclarations(x => x is Function && ((Function) x).TypeParameters.Count > 0);
        program.RemoveTopLevelDeclarations(x => axiomsToBeInstantiated.Contains(x) || polymorphicFunctionAxioms.Contains(x));
        program.RemoveTopLevelDeclarations(x => x is DatatypeTypeCtorDecl y && y.Arity > 0);
        visitor.functionInstantiations.Values.Iter(x =>
        {
          program.AddTopLevelDeclarations(x.Values);
          x.Values.Where(y => y.DefinitionAxiom != null).Iter(y => program.AddTopLevelDeclaration(y.DefinitionAxiom));
        });
        program.AddTopLevelDeclarations(visitor.axiomInstantiations);
        visitor.datatypeInstantiations.Values.Iter(x => program.AddTopLevelDeclarations(x.Values));
        Contract.Assert(PolymorphismChecker.IsMonomorphic(program));
        return true;
      }
      return false;
    }
    
    private Program program;
    private HashSet<Axiom> axiomsToBeInstantiated;
    private HashSet<Axiom> polymorphicFunctionAxioms;
    private Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations;
    private Dictionary<DatatypeTypeCtorDecl, Dictionary<List<Type>, DatatypeTypeCtorDecl>> datatypeInstantiations;
    private List<Axiom> axiomInstantiations;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> triggerTypes;
    private Dictionary<TypeCtorDecl, HashSet<CtorType>> newTriggerTypes;
    
    private MonomorphizationVisitor(Program program, HashSet<Axiom> axiomsToBeInstantiated, HashSet<Axiom> polymorphicFunctionAxioms)
    {
      this.program = program;
      this.axiomsToBeInstantiated = axiomsToBeInstantiated;
      this.polymorphicFunctionAxioms = polymorphicFunctionAxioms;
      functionInstantiations = new Dictionary<Function, Dictionary<List<Type>, Function>>();
      datatypeInstantiations = new Dictionary<DatatypeTypeCtorDecl, Dictionary<List<Type>, DatatypeTypeCtorDecl>>();
      axiomInstantiations = new List<Axiom>();
      triggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
      newTriggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
      axiomsToBeInstantiated.Select(axiom => GetTypeCtorDecl(axiom)).ToHashSet().Iter(typeCtorDecl =>
      {
        triggerTypes.Add(typeCtorDecl, new HashSet<CtorType>());
        newTriggerTypes.Add(typeCtorDecl, new HashSet<CtorType>());
      });
    }

    private TypeCtorDecl GetTypeCtorDecl(Axiom axiom)
    {
      return program.TopLevelDeclarations.OfType<TypeCtorDecl>()
        .First(tcd => tcd.Name == axiom.FindStringAttribute("ctor"));
    }

    private void InstantiateAxioms(HashSet<Axiom> axiomsToBeInstantiated)
    {
      while (newTriggerTypes.Any(x => x.Value.Count != 0))
      {
        var nextTriggerTypes = this.newTriggerTypes;
        newTriggerTypes = new Dictionary<TypeCtorDecl, HashSet<CtorType>>();
        nextTriggerTypes.Iter(x => { newTriggerTypes.Add(x.Key, new HashSet<CtorType>()); });
        foreach (var axiom in axiomsToBeInstantiated)
        {
          axiomInstantiations.AddRange(
            ExprMonomorphizationVisitor.InstantiateAxiom(functionInstantiations, datatypeInstantiations,
            triggerTypes, newTriggerTypes, axiom, nextTriggerTypes[GetTypeCtorDecl(axiom)]));
        }
      }
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      var exprVisitor = new ExprMonomorphizationVisitor(functionInstantiations, datatypeInstantiations, triggerTypes, newTriggerTypes);
      return (CtorType) exprVisitor.VisitType(node);
    }
    
    public override Expr VisitExpr(Expr node)
    {
      var exprVisitor = new ExprMonomorphizationVisitor(functionInstantiations, datatypeInstantiations, triggerTypes, newTriggerTypes);
      return exprVisitor.VisitExpr(node);
    }

    public override Function VisitFunction(Function node)
    {
      if (node.TypeParameters.Count > 0)
      {
        return node;
      }
      return base.VisitFunction(node);
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      if (axiomsToBeInstantiated.Contains(node) || polymorphicFunctionAxioms.Contains(node))
      {
        return node;
      }
      return base.VisitAxiom(node);
    }
  }
}