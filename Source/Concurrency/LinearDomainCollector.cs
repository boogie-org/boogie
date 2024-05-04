using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Boogie
{
  public enum LinearKind
  {
    ORDINARY,
    LINEAR,
    LINEAR_IN,
    LINEAR_OUT
  }

  public class LinearDomain
  {
    public Type permissionType;
    public MapType mapTypeBool;
    public MapType mapTypeInt;
    public Function mapConstBool;
    public Function mapConstInt;
    public Function mapAnd;
    public Function mapOr;
    public Function mapImp;
    public Function mapEqInt;
    public Function mapAdd;
    public Function mapIteInt;
    public Function mapLe;

    public LinearDomain(Program program, Type permissionType)
    {
      this.permissionType = permissionType;

      this.mapTypeBool = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.permissionType },
        Type.Bool);
      this.mapTypeInt = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.permissionType },
        Type.Int);

      this.mapConstBool = program.monomorphizer.InstantiateFunction("MapConst",
        new Dictionary<string, Type>() { { "T", permissionType }, { "U", Type.Bool } });
      this.mapConstInt = program.monomorphizer.InstantiateFunction("MapConst",
        new Dictionary<string, Type>() { { "T", permissionType }, { "U", Type.Int } });
      this.mapAnd = program.monomorphizer.InstantiateFunction("MapAnd",
        new Dictionary<string, Type>() { { "T", permissionType } });
      this.mapOr = program.monomorphizer.InstantiateFunction("MapOr",
        new Dictionary<string, Type>() { { "T", permissionType } });
      this.mapImp = program.monomorphizer.InstantiateFunction("MapImp",
        new Dictionary<string, Type>() { { "T", permissionType } });
      this.mapEqInt = program.monomorphizer.InstantiateFunction("MapEq",
        new Dictionary<string, Type>() { { "T", permissionType }, { "U", Type.Int } });
      this.mapAdd = program.monomorphizer.InstantiateFunction("MapAdd",
        new Dictionary<string, Type>() { { "T", permissionType } });
      this.mapIteInt = program.monomorphizer.InstantiateFunction("MapIte",
        new Dictionary<string, Type>() { { "T", permissionType }, { "U", Type.Int } });
      this.mapLe = program.monomorphizer.InstantiateFunction("MapLe",
        new Dictionary<string, Type>() { { "T", permissionType } });
    }
  }

  class LinearDomainCollector : ReadOnlyVisitor
  {
    private LinearTypeChecker linearTypeChecker;
    private Program program => linearTypeChecker.program;
    private Dictionary<Type, LinearDomain> permissionTypeToLinearDomain;
    // types not in the domain of collectors are guarantees not to contain permissions
    private Dictionary<Type, Dictionary<Type, Function>> collectors;
    private HashSet<Type> visitedTypes;

    private LinearDomainCollector(LinearTypeChecker linearTypeChecker)
    {
      this.linearTypeChecker = linearTypeChecker;
      this.permissionTypeToLinearDomain = new Dictionary<Type, LinearDomain>();
      this.collectors = new Dictionary<Type, Dictionary<Type, Function>>();
      this.visitedTypes = new HashSet<Type>();
    }

    public static (Dictionary<Type, LinearDomain>, Dictionary<Type, Dictionary<Type, Function>>) Collect(LinearTypeChecker linearTypeChecker)
    {
      var collector = new LinearDomainCollector(linearTypeChecker);
      collector.VisitProgram(linearTypeChecker.program);
      return (collector.permissionTypeToLinearDomain, collector.collectors);
    }
  
    public override Implementation VisitImplementation(Implementation node)
    {
      // Boogie parser strips the attributes from the parameters of the implementation
      // leaving them only on the parameters of the corresponding procedures.
      // This override exists only to patch this problem.
      var proc = node.Proc;
      for (int i = 0; i < proc.InParams.Count; i++)
      {
        var procInParam = proc.InParams[i];
        if (procInParam.Attributes != null)
        {
          var implInParam = node.InParams[i];
          implInParam.Attributes = (QKeyValue)procInParam.Attributes.Clone();
        }
      }
      for (int i = 0; i < proc.OutParams.Count; i++)
      {
        var procOutParam = proc.OutParams[i];
        if (procOutParam.Attributes != null)
        {
          var implOutParam = node.OutParams[i];
          implOutParam.Attributes = (QKeyValue)procOutParam.Attributes.Clone();
        }
      }
      return base.VisitImplementation(node);
    }

    public override Variable VisitVariable(Variable node)
    {
      RegisterType(node.TypedIdent.Type);
      return node;
    }

    private void RegisterType(Type type)
    {
      if (visitedTypes.Contains(type))
      {
        return;
      }
      visitedTypes.Add(type);
      if (!(type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl))
      {
        return;
      }
      var permissionType = linearTypeChecker.GetPermissionType(type);
      if (permissionType == null)
      {
        RegisterDatatype(ctorType);
        return;
      }
      if (!permissionTypeToLinearDomain.ContainsKey(permissionType))
      {
        permissionTypeToLinearDomain[permissionType] = new LinearDomain(program, permissionType);
      }
      collectors.Add(type, new Dictionary<Type, Function>());
      var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
      var typeName = originalTypeCtorDecl.Name;
      var actualTypeParams = program.monomorphizer.GetTypeInstantiation(datatypeTypeCtorDecl);
      if (typeName == "Map")
      {
        var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] }, { "U", actualTypeParams[1] } };
        var collector = program.monomorphizer.InstantiateFunction("Map_Collector", typeParamInstantiationMap);
        collectors[type][permissionType] = collector;
      }
      else if (typeName == "Set")
      {
        var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] } };
        var collector = program.monomorphizer.InstantiateFunction("Set_Collector", typeParamInstantiationMap);
        collectors[type][permissionType] = collector;
      }
      else if (typeName == "Cell")
      {
        var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] }, { "U", actualTypeParams[1] } };
        var collector = program.monomorphizer.InstantiateFunction("Cell_Collector", typeParamInstantiationMap);
        collectors[type][permissionType] = collector;
      }
      else
      {
        Debug.Assert(typeName == "One");
        var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] } };
        var collector = program.monomorphizer.InstantiateFunction("One_Collector", typeParamInstantiationMap);
        collectors[type][permissionType] = collector;
      }
    }

    private void RegisterDatatype(CtorType ctorType)
    {
      var datatypeTypeCtorDecl = (DatatypeTypeCtorDecl)ctorType.Decl;
      var collectionTarget = VarHelper.Formal("target", ctorType, true);
      var constructorsWithPermissions = new Dictionary<Type, Dictionary<DatatypeConstructor, List<Expr>>>();
      foreach (var constructor in datatypeTypeCtorDecl.Constructors)
      {
        foreach (var formal in constructor.InParams)
        {
          var formalType = formal.TypedIdent.Type;
          RegisterType(formalType);
          if (LinearTypeChecker.FindLinearKind(formal) == LinearKind.ORDINARY || !collectors.ContainsKey(formalType))
          {
            continue;
          }
          var permissionTypeToCollector = collectors[formal.TypedIdent.Type];
          permissionTypeToCollector.Keys.ForEach(permissionType => {
            var permissionExpr = ExprHelper.FunctionCall(
              permissionTypeToCollector[permissionType], 
              ExprHelper.FieldAccess(Expr.Ident(collectionTarget), formal.Name));
            if (!constructorsWithPermissions.ContainsKey(permissionType))
            {
              constructorsWithPermissions.Add(permissionType, new Dictionary<DatatypeConstructor, List<Expr>>());
            }
            if (!constructorsWithPermissions[permissionType].ContainsKey(constructor))
            {
              constructorsWithPermissions[permissionType].Add(constructor, new List<Expr>());
            }
            constructorsWithPermissions[permissionType][constructor].Add(permissionExpr);
          });
        }
      }
      if (constructorsWithPermissions.Count > 0)
      {
        collectors.Add(ctorType, new Dictionary<Type, Function>());
        constructorsWithPermissions.Keys.ForEach(permissionType => {
          var collectorFunction = new Function(
            Token.NoToken,
            $"Collector_{ctorType}_{permissionType}",
            new List<TypeVariable>(),
            new List<Variable>(){collectionTarget},
            VarHelper.Formal("perm", TypeHelper.MapType(permissionType, Type.Bool), false),
            null,
            new QKeyValue(Token.NoToken, "inline", new List<object>(), null));
          var domain = permissionTypeToLinearDomain[permissionType];
          var body = ExprHelper.FunctionCall(domain.mapConstBool, Expr.False);
          foreach (var constructor in constructorsWithPermissions[permissionType].Keys)
          {
            var permissionExpr = linearTypeChecker.UnionExprForPermissions(domain, constructorsWithPermissions[permissionType][constructor]);
            body = ExprHelper.IfThenElse(ExprHelper.IsConstructor(Expr.Ident(collectionTarget), constructor.Name), permissionExpr, body);
          }
          CivlUtil.ResolveAndTypecheck(linearTypeChecker.Options, body);
          collectorFunction.Body = body;
          collectors[ctorType].Add(permissionType, collectorFunction);
          program.AddTopLevelDeclaration(collectorFunction);
        });
      }
    }
  }
}