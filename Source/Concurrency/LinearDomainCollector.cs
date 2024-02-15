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
    public Dictionary<Type, Function> collectors;
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
      this.collectors = new Dictionary<Type, Function>();

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

    public void RegisterCollector(Function function)
    {
      var inType = function.InParams[0].TypedIdent.Type;
      if (!collectors.ContainsKey(inType))
      {
        collectors.Add(inType, function);
      }
    }
  }

  class LinearDomainCollector : ReadOnlyVisitor
  {
    private LinearTypeChecker linearTypeChecker;
    private Program program => linearTypeChecker.program;
    private Dictionary<Type, LinearDomain> permissionTypeToLinearDomain;

    private LinearDomainCollector(LinearTypeChecker linearTypeChecker)
    {
      this.linearTypeChecker = linearTypeChecker;
      this.permissionTypeToLinearDomain = new Dictionary<Type, LinearDomain>();
    }

    public static Dictionary<Type, LinearDomain> Collect(LinearTypeChecker linearTypeChecker)
    {
      var collector = new LinearDomainCollector(linearTypeChecker);
      collector.VisitProgram(linearTypeChecker.program);
      return collector.permissionTypeToLinearDomain;
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
      if (LinearTypeChecker.FindLinearKind(node) != LinearKind.ORDINARY)
      {
        RegisterLinearVariable(node);
      }
      return node;
    }

    private void RegisterLinearVariable(Variable v)
    {
      var type = v.TypedIdent.Type;
      var permissionType = linearTypeChecker.GetPermissionType(type);
      if (permissionType == null)
      {
        return;
      }
      var linearDomain = RegisterPermissionType(permissionType);
      if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        var typeName = originalTypeCtorDecl.Name;
        var actualTypeParams = program.monomorphizer.GetTypeInstantiation(datatypeTypeCtorDecl);
        if (typeName == "Map")
        {
          var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] }, { "U", actualTypeParams[1] } };
          linearDomain.RegisterCollector(program.monomorphizer.InstantiateFunction("Map_Collector", typeParamInstantiationMap));
        }
        else if (typeName == "Set")
        {
          var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] } };
          linearDomain.RegisterCollector(program.monomorphizer.InstantiateFunction("Set_Collector", typeParamInstantiationMap));
        }
        else
        {
          Debug.Assert(typeName == "One");
          var typeParamInstantiationMap = new Dictionary<string, Type> { { "T", actualTypeParams[0] } };
          linearDomain.RegisterCollector(program.monomorphizer.InstantiateFunction("One_Collector", typeParamInstantiationMap));
        }
      }
    }

    private LinearDomain RegisterPermissionType(Type permissionType)
    {
      if (!permissionTypeToLinearDomain.ContainsKey(permissionType))
      {
        permissionTypeToLinearDomain[permissionType] = new LinearDomain(program, permissionType);
      }
      return permissionTypeToLinearDomain[permissionType];
    }
  }
}