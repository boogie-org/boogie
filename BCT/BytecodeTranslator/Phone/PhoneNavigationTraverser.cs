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
    private ITypeReference cancelEventArgsType;
    private ITypeReference typeTraversed;
    private IMethodDefinition methodTraversed;
    private static HashSet<IMethodDefinition> navCallers= new HashSet<IMethodDefinition>();
    public static IEnumerable<IMethodDefinition> NavCallers { get { return navCallers; } }

    public PhoneNavigationCodeTraverser(MetadataReaderHost host, ITypeReference typeTraversed, IMethodDefinition methodTraversed) : base() {
      this.host = host;
      this.typeTraversed = typeTraversed;
      this.methodTraversed = methodTraversed;
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
 
      // TODO obtain version, culture and signature data dynamically
      IAssemblyReference assembly= PhoneTypeHelper.getPhoneAssemblyReference(host);
      // TODO determine the needed types dynamically
      navigationSvcType = platform.CreateReference(assembly, "System", "Windows", "Navigation", "NavigationService");

      assembly = PhoneTypeHelper.getSystemAssemblyReference(host);
      cancelEventArgsType = platform.CreateReference(assembly, "System", "ComponentModel", "CancelEventArgs");
    }

    public override void  Visit(IEnumerable<IAssemblyReference> assemblyReferences) {
 	    base.Visit(assemblyReferences);
    }


    public override void Visit(IMethodDefinition method) {
      if (method.IsConstructor && PhoneTypeHelper.isPhoneApplicationClass(typeTraversed, host)) {
        string mainPageUri = PhoneCodeHelper.instance().PhonePlugin.getMainPageXAML();
        SourceMethodBody sourceBody = method.Body as SourceMethodBody;
        if (sourceBody != null) {
          BlockStatement bodyBlock = sourceBody.Block as BlockStatement;
          if (bodyBlock != null) {
            Assignment uriInitAssign = new Assignment() {
              Source = new CompileTimeConstant() {
                Type = host.PlatformType.SystemString,
                Value = UriHelper.getURIBase(mainPageUri),
              },
              Type = host.PlatformType.SystemString,
              Target = new TargetExpression() {
                Type = host.PlatformType.SystemString,
                // TODO unify code for current uri fieldreference
                Definition = new FieldReference() {
                  ContainingType = PhoneCodeHelper.instance().getMainAppTypeReference(),
                  IsStatic=true,
                  Type=host.PlatformType.SystemString,
                  Name=host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
                  InternFactory= host.InternFactory,
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
    private bool navCallIsBack = false;
    private StaticURIMode currentStaticMode= StaticURIMode.NOT_STATIC;
    private string unpurifiedFoundURI="";

    public override void Visit(IBlockStatement block) {
      IList<Tuple<IStatement,StaticURIMode,string>> staticNavStmts = new List<Tuple<IStatement,StaticURIMode,string>>();
      IList<IStatement> nonStaticNavStmts = new List<IStatement>();
      foreach (IStatement statement in block.Statements) {
        navCallFound = false;
        navCallIsStatic = false;
        navCallIsBack = false;
        this.Visit(statement);
        if (navCallFound) {
          navCallers.Add(methodTraversed);
          if (navCallIsStatic) {
            staticNavStmts.Add(new Tuple<IStatement, StaticURIMode, string>(statement, currentStaticMode, unpurifiedFoundURI));
          } else if (!navCallIsBack) {
            nonStaticNavStmts.Add(statement);
          }
        }
      }

      injectNavigationUpdateCode(block, staticNavStmts, nonStaticNavStmts);
    }

    private bool isNavigationOnBackKeyPressHandler(IMethodCall call, out string target) {
      target = null;
      if (!PhoneCodeHelper.instance().isBackKeyPressOverride(methodTraversed.ResolvedMethod))
        return false;

      if (!call.MethodToCall.ContainingType.isNavigationServiceClass(host))
        return false;

      if (!PhoneCodeHelper.NAV_CALLS.Contains(call.MethodToCall.Name.Value) || call.MethodToCall.Name.Value == "GoBack") // back is actually ok
        return false;

      if (call.MethodToCall.Name.Value == "Navigate") {
        try {
          IExpression expr = call.Arguments.First();
          bool isStatic = UriHelper.isArgumentURILocallyCreatedStatic(expr, host, out target) ||
                         UriHelper.isArgumentURILocallyCreatedStaticRoot(expr, host, out target);
          if (!isStatic)
            target = "--Other non inferrable target--";
          else
            target = UriHelper.getURIBase(target);
        } catch (InvalidOperationException) { 
        }
      }

      return true;
    }

    private bool isCancelOnBackKeyPressHandler(IMethodCall call) {
      if (!PhoneCodeHelper.instance().isBackKeyPressOverride(methodTraversed.ResolvedMethod))
        return false;

      if (!call.MethodToCall.Name.Value.StartsWith("set_Cancel"))
        return false;

      if (call.Arguments.ToList()[0].Type != host.PlatformType.SystemBoolean)
        return false;

      ICompileTimeConstant constant = call.Arguments.ToList()[0] as ICompileTimeConstant;
      if (constant != null && constant.Value != null ) {
        CompileTimeConstant falseConstant = new CompileTimeConstant() {
          Type = host.PlatformType.SystemBoolean,
          Value = false,
        };
        if (constant.Value == falseConstant.Value)
          return false;
      }

      return true;
    }

    public override void Visit(IMethodCall methodCall) {
      string target;
      if (isNavigationOnBackKeyPressHandler(methodCall, out target)) {
        PhoneCodeHelper.instance().BackKeyPressNavigates = true;
        ICollection<string> targets;
        try {
          targets= PhoneCodeHelper.instance().BackKeyNavigatingOffenders[typeTraversed];
        } catch (KeyNotFoundException) {
          targets = new HashSet<string>();
        }
        targets.Add("\"" + target + "\"");
        PhoneCodeHelper.instance().BackKeyNavigatingOffenders[typeTraversed]= targets;
      } else if (isCancelOnBackKeyPressHandler(methodCall)) {
        PhoneCodeHelper.instance().BackKeyPressHandlerCancels = true;
        PhoneCodeHelper.instance().BackKeyCancellingOffenders.Add(typeTraversed);
      }

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
          navCallIsBack = true;
        } else { // Navigate()
          navCallIsBack = false;

          // check for different static patterns that we may be able to verify
          IExpression uriArg = methodCall.Arguments.First();
          if (UriHelper.isArgumentURILocallyCreatedStatic(uriArg, host, out unpurifiedFoundURI)) {
            navCallIsStatic = true;
            currentStaticMode = StaticURIMode.STATIC_URI_CREATION_ONSITE;
          } else if (UriHelper.isArgumentURILocallyCreatedStaticRoot(uriArg, host, out unpurifiedFoundURI)) {
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
            // TODO unify code for current uri fieldreference
            Definition = new FieldReference() {
              ContainingType = PhoneCodeHelper.instance().getMainAppTypeReference(),
              IsStatic= true,
              Type = host.PlatformType.SystemString,
              Name = host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
              InternFactory=host.InternFactory,
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
            Value = UriHelper.getURIBase(entry.Item3).ToLower(),
          },
          Type = host.PlatformType.SystemString,
          Target = new TargetExpression() {
            Type = host.PlatformType.SystemString,
            // TODO unify code for current uri fieldreference
            Definition = new FieldReference() {
              ContainingType = PhoneCodeHelper.instance().getMainAppTypeReference(),
              IsStatic= true,
              Type = host.PlatformType.SystemString,
              Name = host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
              InternFactory=host.InternFactory,
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
          // TODO unify code for current uri fieldreference
          FieldDefinition fieldDef = new FieldDefinition() {
            ContainingTypeDefinition= mutableTypeDef,
            InternFactory= host.InternFactory,
            IsStatic= true,
            Name= host.NameTable.GetNameFor(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE),
            Type= host.PlatformType.SystemString,
            Visibility= TypeMemberVisibility.Public,
          };
          PhoneCodeHelper.CurrentURIFieldDefinition = fieldDef;
          mutableTypeDef.Fields.Add(fieldDef);
        }
      }
      base.Visit(typeDefinition);
    }

    // TODO same here. Are there specific methods (and ways to identfy those) that can perform navigation?
    public override void Visit(IMethodDefinition method) {
      if (PhoneCodeHelper.instance().isBackKeyPressOverride(method)) {
        PhoneCodeHelper.instance().OnBackKeyPressOverriden = true;
      }

      PhoneNavigationCodeTraverser codeTraverser = new PhoneNavigationCodeTraverser(host, typeBeingTraversed, method);
      codeTraverser.Visit(method);
    }

    public void InjectPhoneCodeAssemblies(IEnumerable<IUnit> assemblies) {
      foreach (var a in assemblies) {
        a.Dispatch(this);
      }
    }
  }
}
