using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Bpl=Microsoft.Boogie;
using TranslationPlugins;

namespace BytecodeTranslator.Phone {
  public enum StaticURIMode {
    NOT_STATIC, STATIC_URI_CREATION_ONSITE, STATIC_URI_ROOT_CREATION_ONSITE,
  }

  public static class PhoneCodeHelper {
    // TODO ensure this name is unique in the program code, although it is esoteric enough
    // TODO externalize strings
    private const string IL_BOOGIE_VAR_PREFIX = "@__BOOGIE_";
    private const string BOOGIE_VAR_PREFIX= "__BOOGIE_";
    public const string IL_CURRENT_NAVIGATION_URI_VARIABLE = IL_BOOGIE_VAR_PREFIX + "CurrentNavigationURI__";
    public const string BOOGIE_CONTINUE_ON_PAGE_VARIABLE = BOOGIE_VAR_PREFIX + "ContinueOnPage__";
    public static readonly string[] NAV_CALLS = { /*"GoBack", "GoForward", "Navigate", "StopLoading"*/ "Navigate", "GoBack" };

    // awful hack. want to insert a nonexisting method call while traversing CCI AST, deferring it to Boogie translation
    public const string BOOGIE_DO_HAVOC_CURRENTURI = BOOGIE_VAR_PREFIX + "Havoc_CurrentURI__";

    public static PhoneControlsPlugin PhonePlugin { get; set; }
    private static IDictionary<string, Bpl.NamedDeclaration> boogieObjects = new Dictionary<string, Bpl.NamedDeclaration>();

    public static Bpl.Variable getBoogieVariableForName(string varName) {
      Bpl.Variable boogieVar = null;
      try {
        boogieVar = boogieObjects[varName] as Bpl.Variable;
      } catch (KeyNotFoundException) {
      }

      if (boogieVar == null)
        throw new ArgumentException("The boogie variable " + varName + " is not defined.");

      return boogieVar;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="name"></param>
    /// <param name="bplObject"></param>
    /// <returns>true if defining a new name, false if replacing</returns>
    public static bool setBoogieObjectForName(string name, Bpl.NamedDeclaration bplObject) {
      bool ret= true;
      if (boogieObjects.ContainsKey(name))
        ret = false;

      boogieObjects[name] = bplObject;
      return ret;
    }

    public static bool isCreateObjectInstance(this IExpression expr) {
      ICreateObjectInstance createObjExpr = expr as ICreateObjectInstance;
      return (createObjExpr != null);
    }

    public static bool isClass(this ITypeReference typeRef, ITypeReference targetTypeRef) {
      while (typeRef != null) {
        if (typeRef.ResolvedType.Equals(targetTypeRef.ResolvedType))
          return true;

        typeRef = typeRef.ResolvedType.BaseClasses.FirstOrDefault();
      }

      return false;
    }

    public static bool isStringClass(this ITypeReference typeRef, IMetadataHost host) {
      ITypeReference targetType = host.PlatformType.SystemString;
      return typeRef.isClass(targetType);
    }

    public static bool isURIClass (this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platformType = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      if (platformType == null)
        return false;

      IAssemblyReference coreRef = platformType.CoreAssemblyRef;
      AssemblyIdentity systemAssemblyId = new AssemblyIdentity(host.NameTable.GetNameFor("System"), "", coreRef.Version, coreRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(systemAssemblyId);

      ITypeReference uriTypeRef= platformType.CreateReference(systemAssembly, "System", "Uri");
      return typeRef.isClass(uriTypeRef);
    }

    public static bool isNavigationServiceClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");

      IAssemblyReference phoneAssembly = host.FindAssembly(MSPhoneAssemblyId);
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "System", "Windows", "Navigation", "NavigationService");

      ITypeReference baseClass = typeRef.ResolvedType.BaseClasses.FirstOrDefault();
      while (baseClass != null) {
        if (baseClass.ResolvedType.Equals(phoneApplicationPageTypeRef.ResolvedType)) {
          return true;
        }
        baseClass = baseClass.ResolvedType.BaseClasses.FirstOrDefault();
      }

      return false;
    }

    public static bool isPhoneApplicationClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");

      IAssemblyReference systemAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      ITypeReference applicationClass = platform.CreateReference(systemAssembly, "System", "Windows", "Application");
      return typeRef.isClass(applicationClass);
    }

    public static bool isPhoneApplicationPageClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");

      IAssemblyReference phoneAssembly = host.FindAssembly(MSPhoneAssemblyId);
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Controls", "PhoneApplicationPage");

      ITypeReference baseClass = typeRef.ResolvedType.BaseClasses.FirstOrDefault();
      while (baseClass != null) {
        if (baseClass.ResolvedType.Equals(phoneApplicationPageTypeRef.ResolvedType)) {
          return true;
        }
        baseClass = baseClass.ResolvedType.BaseClasses.FirstOrDefault();
      }

      return false;
    }

    /// <summary>
    /// checks whether a static URI root (a definite page base) can be extracted from the expression 
    /// </summary>
    /// <param name="expr"></param>
    /// <returns></returns>
    public static bool IsStaticURIRootExtractable(this IExpression expr, out string uri) {
      // Pre expr.type == string
      IMethodCall stringConcatExpr = expr as IMethodCall;
      uri = null;
      if (stringConcatExpr == null)
        return false;

      if (stringConcatExpr.MethodToCall.Name.Value != "Concat")
        return false;

      IList<string> constantStrings = new List<string>();

      // TODO this misses so many static strings, but let's start with this for now
      IExpression leftOp= stringConcatExpr.Arguments.FirstOrDefault();
      while (leftOp != null && leftOp is ICompileTimeConstant) {
        ICompileTimeConstant strConst= leftOp as ICompileTimeConstant;
        constantStrings.Add(strConst.Value as string);
        if (stringConcatExpr.Arguments.ToList()[1] is IMethodCall) {
          stringConcatExpr = stringConcatExpr.Arguments.ToList()[1] as IMethodCall;
          leftOp = stringConcatExpr.Arguments.FirstOrDefault();
        } else if (stringConcatExpr.Arguments.ToList()[1] is ICompileTimeConstant) {
          constantStrings.Add((stringConcatExpr.Arguments.ToList()[1] as ICompileTimeConstant).Value as string);
          break;
        } else {
          break;
        }
      }

      uri= constantStrings.Aggregate((aggr, elem) => aggr + elem);
      return Uri.IsWellFormedUriString(uri, UriKind.RelativeOrAbsolute);
    }

    public static bool isNavigationCall(IMethodCall call, IMetadataHost host) {
      ITypeReference callType = call.MethodToCall.ContainingType;
      if (!callType.isNavigationServiceClass(host))
        return false;

      return PhoneCodeHelper.NAV_CALLS.Contains(call.MethodToCall.Name.Value);
    }

    /// <summary>
    /// uri is a valid URI but possibly partial (incomplete ?arg= values) and overspecified (complete ?arg=values)
    /// This method returns a base URI
    /// </summary>
    /// <param name="uri"></param>
    /// <returns></returns>
    public static string getURIBase(string uri) {
      // I need to build an absolute URI just to call getComponents() ...
      Uri mockBaseUri = new Uri("mock://mock/", UriKind.RelativeOrAbsolute);
      Uri realUri = new Uri(mockBaseUri, uri);

      string str= realUri.GetComponents(UriComponents.Path|UriComponents.StrongAuthority|UriComponents.Scheme, UriFormat.UriEscaped);
      Uri mockStrippedUri = new Uri(str);
      return mockBaseUri.MakeRelativeUri(mockStrippedUri).ToString();
    }

    private static ITypeReference mainAppTypeRef;
    public static void setMainAppTypeReference(ITypeReference appType) {
      mainAppTypeRef = appType;
    }

    public static ITypeReference getMainAppTypeReference() {
      return mainAppTypeRef;
    }
  }
}
