using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.MutableCodeModel;

namespace BytecodeTranslator.Phone {
  public class PhoneNavigationCodeTraverser : BaseCodeTraverser {
    private MetadataReaderHost host;
    private bool navCallFound;
    private ITypeReference navigationSvcType;
    private ITypeReference typeTraversed;

    private static readonly string[] NAV_CALLS = { "GoBack", "GoForward", "Navigate", "StopLoading" };

    public PhoneNavigationCodeTraverser(MetadataReaderHost host, ITypeReference typeTraversed) : base() {
      this.host = host;
      this.typeTraversed = typeTraversed;
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;

      // TODO obtain version, culture and signature data dynamically
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");

      IAssembly phoneAssembly = host.FindAssembly(MSPhoneAssemblyId);

      // TODO determine the needed types dynamically
      navigationSvcType = platform.CreateReference(phoneAssembly, "System", "Windows", "Navigation", "NavigationService");
    }

    public override void Visit(IMethodDefinition method) {
      if (method.IsConstructor && PhoneCodeHelper.isPhoneApplicationClass(typeTraversed, host)) {
        // TODO initialize current navigation URI to mainpage, using a placeholder for now.
        // TODO BUG doing this is generating a fresh variable definition somewhere that the BCT then translates into two different (identical) declarations
        string URI_placeholder="URI_PLACEHOLDER";
        SourceMethodBody sourceBody = method.Body as SourceMethodBody;
        if (sourceBody != null) {
          BlockStatement bodyBlock = sourceBody.Block as BlockStatement;
          if (bodyBlock != null) {
            Assignment uriInitAssign = new Assignment() {
              Source = new CompileTimeConstant() {
                Type = host.PlatformType.SystemString,
                Value = URI_placeholder,
              },
              Type = host.PlatformType.SystemString,
              Target = new TargetExpression() {
                Type = host.PlatformType.SystemString,
                Definition = new FieldReference() {
                  ContainingType= typeTraversed,
                  IsStatic=true,
                  Type=host.PlatformType.SystemString,
                  Name=host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
                },
              },
            };
            Statement uriInitStmt= new ExpressionStatement() {
              Expression= uriInitAssign,
            };
            bodyBlock.Statements.Insert(0, uriInitStmt);
            bodyBlock.Statements.Insert(0, uriInitStmt);
          }
        }
      }
      base.Visit(method);
    }

    public override void Visit(IBlockStatement block) {
      IList<IStatement> navStmts = new List<IStatement>();
      foreach (IStatement statement in block.Statements) {
        navCallFound = false;
        this.Visit(statement);
        if (navCallFound) {
          navStmts.Add(statement);
        }
      }

      injectNavigationUpdateCode(block, navStmts);
    }

    private int navEvtCount= 0;
    private int staticNavEvtCount = 0;
    private int nonStaticNavEvtCount = 0;
    public override void Visit(IMethodCall methodCall) {
      // check whether it is a NavigationService call
      IMethodReference methodToCall= methodCall.MethodToCall;
      ITypeReference callType= methodToCall.ContainingType;
      if (!callType.ResolvedType.Equals(navigationSvcType.ResolvedType))
        return;

      string methodToCallName= methodToCall.Name.Value;
      if (!NAV_CALLS.Contains(methodToCallName))
        return;

      // TODO check what to do with these
      if (methodToCallName == "GoForward" || methodToCallName == "StopLoading") {
        // TODO forward navigation is not supported by the phone
        // TODO StopLoading is very async, I don't think we may verify this behaviour
        // TODO possibly log
        return;
      } else {
        navCallFound = true;
        bool isStatic=false;
        string notStaticReason = "";
        StaticURIMode staticMode = StaticURIMode.NOT_STATIC;

        if (methodToCallName == "GoBack")
          isStatic= true;
        else { // Navigate()
          // check for different static patterns that we may be able to verify
          IExpression uriArg= methodCall.Arguments.First();
          if (isArgumentURILocallyCreatedStatic(uriArg)) {
            isStatic = true;
            staticMode = StaticURIMode.STATIC_URI_CREATION_ONSITE;
          } else if (isArgumentURILocallyCreatedStaticRoot(uriArg)) {
            isStatic = true;
            staticMode = StaticURIMode.STATIC_URI_ROOT_CREATION_ONSITE;
          } else {
            // get reason
            ICreateObjectInstance creationSite = methodCall.Arguments.First() as ICreateObjectInstance;
            if (creationSite == null)
              notStaticReason = "URI not created at call site";
            else
              notStaticReason = "URI not initialized as a static string";
          }
        }

        Console.Write("Page navigation event found. Target is static? " + (isStatic ? "YES" : "NO"));
        if (!isStatic) {
          nonStaticNavEvtCount++;
          Console.WriteLine(" -- Reason: " + notStaticReason);
        } else {
          staticNavEvtCount++;
          Console.WriteLine("");
        }
        navEvtCount++;
      }
    }
    
    /// <summary>
    /// checks if argument is locally created URI with static URI target
    /// </summary>
    /// <param name="arg"></param>
    /// <returns></returns>
    private bool isArgumentURILocallyCreatedStatic(IExpression arg) {
      if (!arg.isCreateObjectInstance())
        return false;

      if (!arg.Type.isURIClass(host))
        return false;

      ICreateObjectInstance creationSite = arg as ICreateObjectInstance;
      IExpression uriTargetArg= creationSite.Arguments.First();

      if (!uriTargetArg.Type.isStringClass(host))
        return false;

      ICompileTimeConstant staticURITarget = uriTargetArg as ICompileTimeConstant;
      return (staticURITarget != null);
    }

    /// <summary>
    /// checks if argument is locally created URI where target has statically created URI root
    /// </summary>
    /// <param name="arg"></param>
    /// <returns></returns>
    private bool isArgumentURILocallyCreatedStaticRoot(IExpression arg) {
      // Pre: !isArgumentURILocallyCreatedStatic
      if (!arg.isCreateObjectInstance())
        return false;

      if (!arg.Type.isURIClass(host))
        return false;

      ICreateObjectInstance creationSite = arg as ICreateObjectInstance;
      IExpression uriTargetArg = creationSite.Arguments.First();

      if (!uriTargetArg.Type.isStringClass(host))
        return false;

      return uriTargetArg.IsStaticURIRootExtractable();
    }

    private void injectNavigationUpdateCode(IBlockStatement block, IEnumerable<IStatement> stmts) {
      // TODO Here there is the STRONG assumption that a given method will only navigate at most once per method call
      // TODO (or at most will re-navigate to the same page). Quick "page flipping" on the same method
      // TODO would not be captured correctly
    }
  }

  /// <summary>
  /// Traverse metadata looking only for PhoneApplicationPage's constructors
  /// </summary>
  public class PhoneNavigationMetadataTraverser : BaseMetadataTraverser {
    private MetadataReaderHost host;
    private ITypeDefinition typeBeingTraversed;

    public PhoneNavigationMetadataTraverser(MetadataReaderHost host)
      : base() {
      this.host = host;
    }

    public override void Visit(IModule module) {
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      base.Visit(assembly);
    }

    // TODO can we avoid visiting every type? Are there only a few, identifiable, types that may perform navigation?
    public override void Visit(ITypeDefinition typeDefinition) {
      typeBeingTraversed = typeDefinition;
      if (typeDefinition.isPhoneApplicationClass(host)) {
        NamespaceTypeDefinition mutableTypeDef = typeDefinition as NamespaceTypeDefinition;
        if (mutableTypeDef != null) {
          FieldDefinition fieldDef = new FieldDefinition() {
            ContainingTypeDefinition= mutableTypeDef,
            InternFactory= host.InternFactory,
            IsStatic= true,
            Name= host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
            Type= host.PlatformType.SystemString,
            Visibility= TypeMemberVisibility.Public,
          };
          mutableTypeDef.Fields.Add(fieldDef);
        }
      }
      base.Visit(typeDefinition);
    }

    // TODO same here. Are there specific methods (and ways to identfy those) that can perform navigation?
    public override void Visit(IMethodDefinition method) {

      PhoneNavigationCodeTraverser codeTraverser = new PhoneNavigationCodeTraverser(host, typeBeingTraversed);
      codeTraverser.Visit(method);
    }

    public void InjectPhoneCodeAssemblies(IEnumerable<IUnit> assemblies) {
      foreach (var a in assemblies) {
        a.Dispatch(this);
      }
    }
  }
}
