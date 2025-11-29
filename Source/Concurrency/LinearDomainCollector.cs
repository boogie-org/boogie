using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

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

  class LinearDomainCollector
  {
    private LinearTypeChecker linearTypeChecker;
    private Program program => linearTypeChecker.program;
    private Dictionary<Type, LinearDomain> permissionTypeToLinearDomain;
    // types not in the domain of collectors are guaranteed not to contain permissions
    private Dictionary<Type, Dictionary<Type, Function>> collectors;

    private LinearDomainCollector(LinearTypeChecker linearTypeChecker)
    {
      this.linearTypeChecker = linearTypeChecker;
      this.permissionTypeToLinearDomain = [];
      this.collectors = [];
    }

    public static (Dictionary<Type, LinearDomain>, Dictionary<Type, Dictionary<Type, Function>>)
      Collect(LinearTypeChecker linearTypeChecker, Dictionary<Type, HashSet<Type>> linearTypes)
    {
      var collector = new LinearDomainCollector(linearTypeChecker);
      collector.CreatePermissionCollectors(linearTypes);
      return (collector.permissionTypeToLinearDomain, collector.collectors);
    }

    private void CreatePermissionCollectors(Dictionary<Type, HashSet<Type>> linearTypes)
    {
      foreach (var type in linearTypes.Keys)
      {
        collectors[type] = [];
        var ctorType = (CtorType)type;
        var datatypeTypeCtorDecl = (DatatypeTypeCtorDecl)ctorType.Decl;
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        var actualTypeParams = program.monomorphizer.GetTypeInstantiation(datatypeTypeCtorDecl);
        var typeName = originalTypeCtorDecl.Name;
        if (typeName == "One")
        {
          var innerType = actualTypeParams[0];
          var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", innerType } };
          var collector = program.monomorphizer.InstantiateFunction("One_Collector", typeParamInstantiationMap);
          collectors[type][type] = collector;
          AddLinearDomain(type);
        }
        else if (typeName == "Set")
        {
          var keyType = actualTypeParams[0];
          var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", keyType } };
          var collector = program.monomorphizer.InstantiateFunction("Set_Collector", typeParamInstantiationMap);
          collectors[type][keyType] = collector;
          AddLinearDomain(keyType);
        }
        else if (typeName == "Map")
        {
          var keyType = actualTypeParams[0];
          var valueType = actualTypeParams[1];
          foreach (var permissionType in linearTypes[type])
          {
            if (permissionType.Equals(keyType))
            {
              // Permission collection for values stored in Map is unbounded and is not being done
              var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", keyType }, { "U", valueType } };
              collectors[type][permissionType] = program.monomorphizer.InstantiateFunction("Map_Collector", typeParamInstantiationMap);
            }
            else
            {
              var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", keyType }, { "U", valueType }, { "P", permissionType} };
              collectors[type][permissionType] = program.monomorphizer.InstantiateFunction("Map_Collector_Empty", typeParamInstantiationMap);
            }
            AddLinearDomain(permissionType);
          }
        }
        else
        {
          foreach (var permissionType in linearTypes[ctorType])
          {
            var collectionTarget = VarHelper.Formal("target", ctorType, true);
            var collectorFunction = new Function(
                Token.NoToken,
                $"Collector_{ctorType}_{permissionType}",
                [],
                [collectionTarget],
                VarHelper.Formal("perm", TypeHelper.MapType(permissionType, Type.Bool), false),
                null);
            collectors[ctorType].Add(permissionType, collectorFunction);
            program.AddTopLevelDeclaration(collectorFunction);
          }
        }
      }

      foreach (var ctorType in linearTypes.Keys.OfType<CtorType>())
      {
        var datatypeTypeCtorDecl = (DatatypeTypeCtorDecl)ctorType.Decl;
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        var typeName = originalTypeCtorDecl.Name;
        if (typeName == "One" || typeName == "Set" || typeName == "Map")
        {
          continue;
        }
        foreach (var permissionType in linearTypes[ctorType])
        {
          ComputeBodiesOfPermissionCollectors(ctorType, permissionType, linearTypes);
        }
      }
    }

    private void ComputeBodiesOfPermissionCollectors(CtorType ctorType, Type permissionType, Dictionary<Type, HashSet<Type>> linearTypes)
    {
      var datatypeTypeCtorDecl = (DatatypeTypeCtorDecl)ctorType.Decl;
      var constructorToPermissionExprs =
        datatypeTypeCtorDecl.Constructors.Select(constructor =>
          new KeyValuePair<DatatypeConstructor, List<Expr>>(constructor, [])).ToDictionary();
      var collectionTarget = collectors[ctorType][permissionType].InParams[0];
      foreach (var constructor in datatypeTypeCtorDecl.Constructors)
      {
        foreach (var formal in constructor.InParams.Where(formal => linearTypes.ContainsKey(formal.TypedIdent.Type)))
        {
          var permissionExpr = ExprHelper.FunctionCall(
            collectors[formal.TypedIdent.Type][permissionType],
            ExprHelper.FieldAccess(Expr.Ident(collectionTarget), formal.Name));
          constructorToPermissionExprs[constructor].Add(permissionExpr);
        }
      }
      var domain = permissionTypeToLinearDomain[permissionType];
      var body = ExprHelper.FunctionCall(domain.mapConstBool, Expr.False);
      foreach (var constructor in datatypeTypeCtorDecl.Constructors)
      {
        var permissionExpr = linearTypeChecker.UnionExprForPermissions(domain, constructorToPermissionExprs[constructor]);
        body = ExprHelper.IfThenElse(ExprHelper.IsConstructor(Expr.Ident(collectionTarget), constructor.Name), permissionExpr, body);
      }
      CivlUtil.ResolveAndTypecheck(linearTypeChecker.Options, body);
      collectors[ctorType][permissionType].Body = body;
    }

    private void AddLinearDomain(Type permissionType)
    {
      if (permissionTypeToLinearDomain.ContainsKey(permissionType))
      {
        return;
      }
      permissionTypeToLinearDomain[permissionType] = new LinearDomain(program, permissionType);
    }
  }
}