using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.MutableCodeModel;
using TranslationPlugins;

namespace BytecodeTranslator.Phone {
  public class PhoneNavigationCodeTraverser : BaseCodeTraverser {
    private MetadataReaderHost host;
    private ITypeReference navigationSvcType;
    private ITypeReference typeTraversed;

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
        string mainPageUri = PhoneCodeHelper.PhonePlugin.getMainPageXAML();
        SourceMethodBody sourceBody = method.Body as SourceMethodBody;
        if (sourceBody != null) {
          BlockStatement bodyBlock = sourceBody.Block as BlockStatement;
          if (bodyBlock != null) {
            Assignment uriInitAssign = new Assignment() {
              Source = new CompileTimeConstant() {
                Type = host.PlatformType.SystemString,
                Value = mainPageUri,
              },
              Type = host.PlatformType.SystemString,
              Target = new TargetExpression() {
                Type = host.PlatformType.SystemString,
                Definition = new FieldReference() {
                  // ContainingType= typeTraversed,
                  ContainingType= PhoneCodeHelper.getMainAppTypeReference(),
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
          }
        }
      }
      base.Visit(method);
    }


    private bool navCallFound=false;
    private bool navCallIsStatic = false;
    private StaticURIMode currentStaticMode= StaticURIMode.NOT_STATIC;
    private string unpurifiedFoundURI="";

    public override void Visit(IBlockStatement block) {
      IList<Tuple<IStatement,StaticURIMode,string>> staticNavStmts = new List<Tuple<IStatement,StaticURIMode,string>>();
      IList<IStatement> nonStaticNavStmts = new List<IStatement>();
      foreach (IStatement statement in block.Statements) {
        navCallFound = false;
        navCallIsStatic = false;
        this.Visit(statement);
        if (navCallFound && navCallIsStatic) {
          staticNavStmts.Add(new Tuple<IStatement, StaticURIMode, string>(statement, currentStaticMode, unpurifiedFoundURI));
        } else if (navCallFound) {
          nonStaticNavStmts.Add(statement);
        }
      }

      injectNavigationUpdateCode(block, staticNavStmts, nonStaticNavStmts);
    }

    public override void Visit(IMethodCall methodCall) {
      // check whether it is a NavigationService call
      IMethodReference methodToCall= methodCall.MethodToCall;
      ITypeReference callType= methodToCall.ContainingType;
      if (!callType.ResolvedType.Equals(navigationSvcType.ResolvedType))
        return;

      string methodToCallName= methodToCall.Name.Value;
      if (!PhoneCodeHelper.NAV_CALLS.Contains(methodToCallName))
        return;

      navCallFound = true;
      // TODO check what to do with these
      if (methodToCallName == "GoForward" || methodToCallName == "StopLoading") {
        // TODO forward navigation is not supported by the phone
        // TODO StopLoading is very async, I don't think we may verify this behaviour
        // TODO possibly log
        return;
      } else {
        currentStaticMode = StaticURIMode.NOT_STATIC;

        if (methodToCallName == "GoBack") {
          navCallIsStatic = false;
        } else { // Navigate()
          // check for different static patterns that we may be able to verify
          IExpression uriArg = methodCall.Arguments.First();
          if (isArgumentURILocallyCreatedStatic(uriArg, out unpurifiedFoundURI)) {
            navCallIsStatic = true;
            currentStaticMode = StaticURIMode.STATIC_URI_CREATION_ONSITE;
          } else if (isArgumentURILocallyCreatedStaticRoot(uriArg, out unpurifiedFoundURI)) {
            navCallIsStatic = true;
            currentStaticMode = StaticURIMode.STATIC_URI_ROOT_CREATION_ONSITE;
          } else {
            // get reason
            //ICreateObjectInstance creationSite = methodCall.Arguments.First() as ICreateObjectInstance;
            //if (creationSite == null)
            //  notStaticReason = "URI not created at call site";
            //else
            //  notStaticReason = "URI not initialized as a static string";
          }
        }

        //Console.Write("Page navigation event found. Target is static? " + (isStatic ? "YES" : "NO"));
        //if (!isStatic) {
        //  Console.WriteLine(" -- Reason: " + notStaticReason);
        //} else {
        //  Console.WriteLine("");
        //}
      }
    }
    
    /// <summary>
    /// checks if argument is locally created URI with static URI target
    /// </summary>
    /// <param name="arg"></param>
    /// <returns></returns>
    private bool isArgumentURILocallyCreatedStatic(IExpression arg, out string uri) {
      uri = null;
      if (!arg.isCreateObjectInstance())
        return false;

      if (!arg.Type.isURIClass(host))
        return false;

      ICreateObjectInstance creationSite = arg as ICreateObjectInstance;
      IExpression uriTargetArg= creationSite.Arguments.First();

      if (!uriTargetArg.Type.isStringClass(host))
        return false;

      ICompileTimeConstant staticURITarget = uriTargetArg as ICompileTimeConstant;
      if (staticURITarget == null)
        return false;

      uri= staticURITarget.Value as string;
      return true;
    }

    /// <summary>
    /// checks if argument is locally created URI where target has statically created URI root
    /// </summary>
    /// <param name="arg"></param>
    /// <returns></returns>
    private bool isArgumentURILocallyCreatedStaticRoot(IExpression arg, out string uri) {
      // Pre: !isArgumentURILocallyCreatedStatic
      uri = null;
      if (!arg.isCreateObjectInstance())
        return false;

      if (!arg.Type.isURIClass(host))
        return false;

      ICreateObjectInstance creationSite = arg as ICreateObjectInstance;
      IExpression uriTargetArg = creationSite.Arguments.First();

      if (!uriTargetArg.Type.isStringClass(host))
        return false;

      if (!uriTargetArg.IsStaticURIRootExtractable(out uri))
        return false;

      return true;
    }

    private void injectNavigationUpdateCode(IBlockStatement block, IEnumerable<Tuple<IStatement,StaticURIMode, string>> staticStmts, IEnumerable<IStatement> nonStaticStmts) {
      // TODO Here there is the STRONG assumption that a given method will only navigate at most once per method call
      // TODO (or at most will re-navigate to the same page). Quick "page flipping" on the same method
      // TODO would not be captured correctly
      Microsoft.Cci.MutableCodeModel.BlockStatement mutableBlock = block as Microsoft.Cci.MutableCodeModel.BlockStatement;
      
      foreach (IStatement stmt in nonStaticStmts) {
        int ndx = mutableBlock.Statements.ToList().IndexOf(stmt);
        if (ndx == -1) {
          // can't be
          throw new IndexOutOfRangeException("Statement must exist in original block");
        }

        Assignment currentURIAssign = new Assignment() {
          Source = new CompileTimeConstant() {
            Type = host.PlatformType.SystemString,
            Value = PhoneCodeHelper.BOOGIE_DO_HAVOC_CURRENTURI,
          },
          Type = host.PlatformType.SystemString,
          Target = new TargetExpression() {
            Type = host.PlatformType.SystemString,
            Definition = new FieldReference() {
              ContainingType=PhoneCodeHelper.getMainAppTypeReference(),
              IsStatic= true,
              Type = host.PlatformType.SystemString,
              Name = host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
            },
          },
        };
        Statement uriInitStmt = new ExpressionStatement() {
          Expression = currentURIAssign,
        };
        mutableBlock.Statements.Insert(ndx + 1, uriInitStmt);
      }


      foreach (Tuple<IStatement, StaticURIMode, string> entry in staticStmts) {
        int ndx= mutableBlock.Statements.ToList().IndexOf(entry.Item1);
        if (ndx == -1) {
          // can't be
          throw new IndexOutOfRangeException("Statement must exist in original block");
        }

        Assignment currentURIAssign = new Assignment() {
          Source = new CompileTimeConstant() {
            Type = host.PlatformType.SystemString,
            Value = PhoneCodeHelper.getURIBase(entry.Item3),
          },
          Type = host.PlatformType.SystemString,
          Target = new TargetExpression() {
            Type = host.PlatformType.SystemString,
            Definition = new FieldReference() {
              ContainingType = PhoneCodeHelper.getMainAppTypeReference(),
              IsStatic= true,
              Type = host.PlatformType.SystemString,
              Name = host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
            },
          },
        };
        Statement uriInitStmt = new ExpressionStatement() {
          Expression = currentURIAssign,
        };
        mutableBlock.Statements.Insert(ndx+1, uriInitStmt);
      }
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
