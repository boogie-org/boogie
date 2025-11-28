using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  class LinearTypeCollector
  {
    private readonly Program program;
    private readonly TypecheckingContext checkingContext;
    private readonly Dictionary<Type, HashSet<Type>> linearTypes;

    public static Dictionary<Type, HashSet<Type>> CollectLinearTypes(Program program, TypecheckingContext checkingContext)
    {
      var linearTypeCollector = new LinearTypeCollector(program, checkingContext);
      linearTypeCollector.Collect();
      linearTypeCollector.Check();
      return linearTypeCollector.linearTypes;
    }

    private void Collect()
    {
      var decls = program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>();
      var allDataTypes = decls.Select(decl => new CtorType(Token.NoToken, decl, []));
      while (true)
      {
        var count = linearTypes.Values.Select(x => x.Count).Sum();
        var visitedTypes = new HashSet<Type>();
        foreach (var type in allDataTypes)
        {
          VisitType(type, visitedTypes);
        }
        if (count == linearTypes.Values.Select(x => x.Count).Sum())
        {
          break;
        }
      }
    }
    private void Check()
    {
      foreach (var datatypeTypeCtorDecl in linearTypes.Keys.OfType<CtorType>().Select(ctorType => ctorType.Decl).OfType<DatatypeTypeCtorDecl>())
      {
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        var actualTypeParams = program.monomorphizer.GetTypeInstantiation(datatypeTypeCtorDecl);
        var typeName = originalTypeCtorDecl.Name;
        if (typeName == "One")
        {
          var innerType = actualTypeParams[0];
          if (linearTypes.ContainsKey(innerType))
          {
            checkingContext.Error(originalTypeCtorDecl, "One instantiated with a linear type");
          }
        }
        else if (typeName == "Map")
        {
          var keyType = actualTypeParams[0];
          if (!IsOneType(keyType) && linearTypes.ContainsKey(keyType))
          {
            checkingContext.Error(originalTypeCtorDecl, "Map instantiated with a key type that is neither One _ nor ordinary");
          }
        }
      }
    }

    

    private LinearTypeCollector(Program program, TypecheckingContext checkingContext)
    {
      this.program = program;
      this.checkingContext = checkingContext;
      this.linearTypes = [];
    }

    private void VisitType(Type type, HashSet<Type> visitedTypes)
    {
      if (visitedTypes.Contains(type))
      {
        return;
      }
      visitedTypes.Add(type);

      if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        var typeName = originalTypeCtorDecl.Name;
        if (!(typeName == "One" || typeName == "Set" || typeName == "Map"))
        {
          VisitDatatype(ctorType, visitedTypes);
          return;
        }
        var actualTypeParams = program.monomorphizer.GetTypeInstantiation(datatypeTypeCtorDecl);
        actualTypeParams.ForEach(type => VisitType(type, visitedTypes));
        var permissionType = typeName == "One" ? type : actualTypeParams[0];
        if (IsOneType(permissionType))
        {
          AddPermissionType(type, permissionType);
        }
        if (typeName == "Map")
        {
          var valueType = actualTypeParams[1];
          if (linearTypes.TryGetValue(valueType, out HashSet<Type> permissionTypes))
          {
            AddPermissionTypes(type, permissionTypes);
          }
        }
      }
    }

    private void VisitDatatype(CtorType ctorType, HashSet<Type> visitedTypes)
    {
      var datatypeTypeCtorDecl = (DatatypeTypeCtorDecl)ctorType.Decl;
      var constructors = datatypeTypeCtorDecl.Constructors;
      constructors.ForEach(constructor => constructor.InParams.ForEach(formal => VisitType(formal.TypedIdent.Type, visitedTypes)));
      constructors.ForEach(constructor =>
        constructor.InParams.Where(formal =>
          linearTypes.ContainsKey(formal.TypedIdent.Type)).ForEach(formal =>
            AddPermissionTypes(ctorType, linearTypes[formal.TypedIdent.Type])));
    }

    private static bool IsOneType(Type type)
    {
      if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        return originalTypeCtorDecl.Name == "One";
      }
      return false;
    }

    private void AddLinearType(Type linearType)
    {
      if (!linearTypes.ContainsKey(linearType))
      {
        linearTypes.Add(linearType, []);
      }
    }

    private void AddPermissionType(Type linearType, Type permissionType)
    {
      AddLinearType(linearType);
      linearTypes[linearType].Add(permissionType);
    }

    private void AddPermissionTypes(Type linearType, HashSet<Type> permissionTypes)
    {
      AddLinearType(linearType);
      linearTypes[linearType].UnionWith(permissionTypes);
    }
  }
}