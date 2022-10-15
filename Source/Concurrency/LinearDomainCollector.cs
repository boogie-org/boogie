using System.Collections.Generic;
using System.Linq;


namespace Microsoft.Boogie
{
  class LinearDomainCollector : ReadOnlyVisitor
  {
    public Program program;
    public CivlTypeChecker civlTypeChecker;
    public CheckingContext checkingContext;
    private Dictionary<string, LinearDomain> linearDomains;

    public LinearDomainCollector(Program program, CivlTypeChecker civlTypeChecker)
    {
      this.program = program;
      this.civlTypeChecker = civlTypeChecker;
      this.checkingContext = civlTypeChecker.checkingContext;
      this.linearDomains = new Dictionary<string, LinearDomain>();
    }

    public static Dictionary<string, LinearDomain> Collect(Program program, CivlTypeChecker civlTypeChecker)
    {
      var collector = new LinearDomainCollector(program, civlTypeChecker);
      collector.PopulateLinearDomains();
      collector.VisitProgram(program);
      return collector.linearDomains;
    }

    public static LinearKind FindLinearKind(Variable v)
    {
      if (QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR) != null)
      {
        return LinearKind.LINEAR;
      }
      if (QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_IN) != null)
      {
        return LinearKind.LINEAR_IN;
      }
      if (QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_OUT) != null)
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

    public override Implementation VisitImplementation(Implementation node)
    {
      var proc = node.Proc;
      if (civlTypeChecker.procToAtomicAction.ContainsKey(proc) ||
          civlTypeChecker.procToIntroductionAction.ContainsKey(proc) ||
          civlTypeChecker.procToIsAbstraction.ContainsKey(proc) ||
          civlTypeChecker.procToIsInvariant.ContainsKey(proc) ||
          civlTypeChecker.procToLemmaProc.ContainsKey(proc))
      {
        return node;
      }
      // Boogie parser strips the attributes from the parameters of the implementation
      // leaving them only on the parameters of the corresponding procedures.
      // The following code patches this problem.
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
      var kind = FindLinearKind(node);
      if (kind == LinearKind.LINEAR_IN || kind == LinearKind.LINEAR_OUT)
      {
        if (node is GlobalVariable || node is LocalVariable || (node is Formal formal && !formal.InComing))
        {
          checkingContext.Error(node, "Variable must be declared linear (as opposed to linear_in or linear_out)");
          return node;
        }
      }
      string domainName;
      if (kind == LinearKind.LINEAR)
      {
        domainName = QKeyValue.FindStringAttribute(node.Attributes, CivlAttributes.LINEAR);
      }
      else if (kind == LinearKind.LINEAR_IN)
      {
        domainName = QKeyValue.FindStringAttribute(node.Attributes, CivlAttributes.LINEAR_IN);
      }
      else if (kind == LinearKind.LINEAR_OUT)
      {
        domainName = QKeyValue.FindStringAttribute(node.Attributes, CivlAttributes.LINEAR_OUT);
      }
      else
      {
        return node;
      }
      if (!linearDomains.ContainsKey(domainName))
      {
        checkingContext.Error(node, $"Permission type not declared for domain {domainName}");
        return node;
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
          // add unit collector
          domainNameToCollectors[domainName][permissionType] =
            program.monomorphizer.InstantiateFunction("MapUnit",
              new Dictionary<string, Type>() { { "T", permissionType } });
        }
        {
          // add identity collector
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