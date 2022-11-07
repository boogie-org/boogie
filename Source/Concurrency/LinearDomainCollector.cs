using System.Collections.Generic;
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
    private string domainName;
    public string DomainName => domainName?? permissionType.ToString();
    public Type permissionType;
    public Dictionary<Type, Function> collectors;
    public MapType mapTypeBool;
    public MapType mapTypeInt;
    public Function mapConstBool;
    public Function mapConstInt;
    public Function mapOr;
    public Function mapImp;
    public Function mapEqInt;
    public Function mapAdd;
    public Function mapIteInt;
    public Function mapLe;

    public LinearDomain(Program program, string domainName, Type permissionType, Dictionary<Type, Function> collectors)
    {
      this.domainName = domainName;
      this.permissionType = permissionType;
      this.collectors = collectors;

      this.mapTypeBool = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.permissionType },
        Type.Bool);
      this.mapTypeInt = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.permissionType },
        Type.Int);

      this.mapConstBool = program.monomorphizer.InstantiateFunction("MapConst",
        new Dictionary<string, Type>() { { "T", permissionType }, { "U", Type.Bool } });
      this.mapConstInt = program.monomorphizer.InstantiateFunction("MapConst",
        new Dictionary<string, Type>() { { "T", permissionType }, { "U", Type.Int } });
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

    public Expr MapConstInt(int value)
    {
      return ExprHelper.FunctionCall(mapConstInt, Expr.Literal(value));
    }

    public Expr MapEqTrue(Expr expr)
    {
      return Expr.Eq(expr, ExprHelper.FunctionCall(mapConstBool, Expr.True));
    }
  }
  
  class LinearDomainCollector : ReadOnlyVisitor
  {
    private Program program;
    private CheckingContext checkingContext;
    private Dictionary<string, LinearDomain> linearDomains;
    private HashSet<Type> linearTypes;
    private HashSet<Type> permissionTypes;
    private HashSet<Type> visitedTypes;

    private LinearDomainCollector(Program program, CheckingContext checkingContext)
    {
      this.program = program;
      this.checkingContext = checkingContext;
      this.linearDomains = new Dictionary<string, LinearDomain>();
      this.linearTypes = new HashSet<Type>();
      this.permissionTypes = new HashSet<Type>();
      this.visitedTypes = new HashSet<Type>();
    }

    public static (Dictionary<string, LinearDomain>, Dictionary<Type, LinearDomain>) Collect(Program program, CheckingContext checkingContext)
    {
      var collector = new LinearDomainCollector(program, checkingContext);
      collector.PopulateLinearDomains();
      collector.VisitProgram(program);
      return (collector.linearDomains, collector.MakeLinearDomains());
    }

    public static LinearKind FindLinearKind(Variable v)
    {
      if (QKeyValue.FindAttribute(v.Attributes, x => x.Key == CivlAttributes.LINEAR) != null)
      {
        return LinearKind.LINEAR;
      }
      if (QKeyValue.FindAttribute(v.Attributes, x => x.Key == CivlAttributes.LINEAR_IN) != null)
      {
        return LinearKind.LINEAR_IN;
      }
      if (QKeyValue.FindAttribute(v.Attributes, x => x.Key == CivlAttributes.LINEAR_OUT) != null)
      {
        return LinearKind.LINEAR_OUT;
      }
      return LinearKind.ORDINARY;
    }

    public static string FindDomainName(Variable v)
    {
      string domainName = QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR);
      if (domainName != null)
      {
        return domainName;
      }
      domainName = QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_IN);
      if (domainName != null)
      {
        return domainName;
      }
      return QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_OUT);
    }
    
    private bool ContainsPermissionType(Type type)
    {
      if (program.monomorphizer == null)
      {
        return false;
      }
      if (!visitedTypes.Contains(type))
      {
        visitedTypes.Add(type);
        if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
        {
          var originalDecl = program.monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
          var originalDeclName = originalDecl.Name;
          if (originalDeclName == "Lmap" || originalDeclName == "Lset" || originalDeclName == "Lval")
          {
            permissionTypes.Add(type);
            linearTypes.Add(type);
            var innerType = program.monomorphizer.GetTypeInstantiation(datatypeTypeCtorDecl)[0];
            ContainsPermissionType(innerType);
          }
          else
          {
            datatypeTypeCtorDecl.Constructors.Iter(constructor => constructor.InParams.Iter(v =>
            {
              if (ContainsPermissionType(v.TypedIdent.Type))
              {
                linearTypes.Add(type);
              }
            }));
          }
        }
      }
      return linearTypes.Contains(type);
    }
    
    private Type GetPermissionType(Type type)
    {
      var typeCtorDecl = type.AsCtor.Decl;
      var originalTypeCtorDecl = program.monomorphizer.GetOriginalDecl(typeCtorDecl);
      var actualTypeParams = program.monomorphizer.GetTypeInstantiation(typeCtorDecl);
      return 
        originalTypeCtorDecl.Name == "Lmap"
          ? new CtorType(Token.NoToken, program.monomorphizer.InstantiateTypeCtorDecl("Ref", actualTypeParams),
            new List<Type>())
          : actualTypeParams[0];
    }
    
    private Dictionary<Type, LinearDomain> MakeLinearDomains()
    {
      var permissionTypeToCollectors = new Dictionary<Type, Dictionary<Type, Function>>();
      foreach (var type in permissionTypes)
      {
        var typeCtorDecl = type.AsCtor.Decl;
        var originalTypeCtorDecl = program.monomorphizer.GetOriginalDecl(typeCtorDecl);
        var actualTypeParams = program.monomorphizer.GetTypeInstantiation(typeCtorDecl);
        var permissionType = GetPermissionType(type); 
        if (!permissionTypeToCollectors.ContainsKey(permissionType))
        {
          permissionTypeToCollectors.Add(permissionType, new Dictionary<Type, Function>());
        }
        if (!permissionTypeToCollectors[permissionType].ContainsKey(type))
        {
          var collector = 
            originalTypeCtorDecl.Name == "Lmap" 
              ? program.monomorphizer.InstantiateFunction("Lmap_Collector",
                new Dictionary<string, Type> { { "V", actualTypeParams[0] } }) :
              originalTypeCtorDecl.Name == "Lset" 
                ? program.monomorphizer.InstantiateFunction("Lset_Collector",
                  new Dictionary<string, Type> { { "V", actualTypeParams[0] } }) :
                program.monomorphizer.InstantiateFunction("Lval_Collector",
                  new Dictionary<string, Type> { { "V", actualTypeParams[0] } });
          permissionTypeToCollectors[permissionType].Add(type, collector);
        }
      }
      var permissionTypeToLinearDomain =
        permissionTypeToCollectors.ToDictionary(kv => kv.Key, kv => new LinearDomain(program, null, kv.Key, kv.Value));
      return permissionTypes.ToDictionary(type => type, type => permissionTypeToLinearDomain[GetPermissionType(type)]);
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
      string domainName = FindDomainName(node);
      var nodeType = node.TypedIdent.Type;
      var containsPermissionType = ContainsPermissionType(nodeType);
      if (domainName != null)
      {
        if (!linearDomains.ContainsKey(domainName))
        {
          checkingContext.Error(node, $"Permission type not declared for domain {domainName}");
        } 
        else if (containsPermissionType)
        {
          checkingContext.Error(node, $"Variable of linear type must not have a domain name");
        }
      }
      if (containsPermissionType)
      {
        if (FindLinearKind(node) == LinearKind.ORDINARY)
        {
          node.Attributes = new QKeyValue(Token.NoToken, CivlAttributes.LINEAR, new List<object>(), node.Attributes);
        }
      }
      return node;
    }

    private void PopulateLinearDomains()
    {
      var permissionTypes = new Dictionary<string, Type>();
      foreach (var decl in program.TopLevelDeclarations.Where(decl => decl is TypeCtorDecl || decl is TypeSynonymDecl))
      {
        foreach (var domainName in FindDomainNames(decl.Attributes))
        {
          if (permissionTypes.ContainsKey(domainName))
          {
            checkingContext.Error(decl, $"Duplicate permission type for domain {domainName}");
          }
          else if (decl is TypeCtorDecl typeCtorDecl)
          {
            if (typeCtorDecl.Arity > 0)
            {
              checkingContext.Error(decl, "Permission type must be fully instantiated");
            }
            else
            {
              permissionTypes[domainName] = new CtorType(Token.NoToken, typeCtorDecl, new List<Type>());
            }
          }
          else
          {
            permissionTypes[domainName] =
              new TypeSynonymAnnotation(Token.NoToken, (TypeSynonymDecl)decl, new List<Type>());
          }
        }
      }

      var domainNameToCollectors = new Dictionary<string, Dictionary<Type, Function>>();
      foreach (var (domainName, permissionType) in permissionTypes)
      {
        domainNameToCollectors[domainName] = new Dictionary<Type, Function>();
        {
          domainNameToCollectors[domainName][permissionType] =
            program.monomorphizer.InstantiateFunction("MapOne",
              new Dictionary<string, Type>() { { "T", permissionType } });
        }
        {
          var type = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { permissionType }, Type.Bool);
          domainNameToCollectors[domainName][type] =
            program.monomorphizer.InstantiateFunction("Id", new Dictionary<string, Type>() { { "T", type } });
        }
      }

      foreach (var node in program.TopLevelDeclarations.OfType<Function>())
      {
        string domainName = QKeyValue.FindStringAttribute(node.Attributes, CivlAttributes.LINEAR);
        if (domainName == null)
        {
          continue;
        }

        if (!domainNameToCollectors.ContainsKey(domainName))
        {
          checkingContext.Error(node, "Domain name has not been declared");
          continue;
        }

        if (node.InParams.Count == 1 && node.OutParams.Count == 1)
        {
          Type inType = node.InParams[0].TypedIdent.Type;
          if (domainNameToCollectors[domainName].ContainsKey(inType))
          {
            checkingContext.Error(node, "A collector for domain for input type is already defined");
            continue;
          }

          var outType = node.OutParams[0].TypedIdent.Type;
          var expectedType = new MapType(Token.NoToken, new List<TypeVariable>(),
            new List<Type> { permissionTypes[domainName] }, Type.Bool);
          if (!outType.Equals(expectedType))
          {
            checkingContext.Error(node, "Output of a linear domain collector has unexpected type");
          }
          else
          {
            domainNameToCollectors[domainName].Add(inType, node);
          }
        }
        else
        {
          checkingContext.Error(node, "Linear domain collector should have one input and one output parameter");
        }
      }

      foreach (var (domainName, permissionType) in permissionTypes)
      {
        linearDomains.Add(domainName,
          new LinearDomain(program, domainName, permissionType, domainNameToCollectors[domainName]));
      }
    }

    private static List<string> FindDomainNames(QKeyValue kv)
    {
      List<string> domains = new List<string>();
      for (; kv != null; kv = kv.Next)
      {
        if (kv.Key != CivlAttributes.LINEAR)
        {
          continue;
        }
        foreach (var o in kv.Params)
        {
          if (o is string s)
          {
            domains.Add(s);
          }
        }
      }
      return domains;
    }
  }
}