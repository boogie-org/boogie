using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace BytecodeTranslator.Phone {
  public enum StaticURIMode {
    NOT_STATIC, STATIC_URI_CREATION_ONSITE, STATIC_URI_ROOT_CREATION_ONSITE,
  }

  public static class PhoneCodeHelper {
    // TODO ensure this name is unique in the program code, although it is esoteric enough
    private const string IL_BOOGIE_VAR_PREFIX = "@__BOOGIE_";
    public const string IL_CURRENT_NAVIGATION_URI_VARIABLE = IL_BOOGIE_VAR_PREFIX + "CurrentNavigationURI__";

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

    public static bool isStringClass(this ITypeReference typeRef, MetadataReaderHost host) {
      ITypeReference targetType = host.PlatformType.SystemString;
      return typeRef.isClass(targetType);
    }

    public static bool isURIClass (this ITypeReference typeRef, MetadataReaderHost host) {
      Microsoft.Cci.Immutable.PlatformType platformType = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      if (platformType == null)
        return false;

      IAssemblyReference coreRef = platformType.CoreAssemblyRef;
      AssemblyIdentity systemAssemblyId = new AssemblyIdentity(host.NameTable.GetNameFor("System"), "", coreRef.Version, coreRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(systemAssemblyId);

      ITypeReference uriTypeRef= platformType.CreateReference(systemAssembly, "System", "Uri");
      return typeRef.isClass(uriTypeRef);
    }


    public static bool isPhoneApplicationClass(this ITypeReference typeRef, MetadataReaderHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");

      IAssemblyReference systemAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      ITypeReference applicationClass = platform.CreateReference(systemAssembly, "System", "Windows", "Application");

      return typeRef.isClass(applicationClass);
    }

    public static bool isPhoneApplicationPageClass(ITypeReference typeDefinition, MetadataReaderHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");

      IAssemblyReference phoneAssembly = host.FindAssembly(MSPhoneAssemblyId);
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Controls", "PhoneApplicationPage");

      ITypeReference baseClass = typeDefinition.ResolvedType.BaseClasses.FirstOrDefault();
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
    public static bool IsStaticURIRootExtractable(this IExpression expr) {
      // Pre expr.type == string
      IMethodCall stringConcatExpr = expr as IMethodCall;
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

      string constantSubstring= constantStrings.Aggregate((aggr, elem) => aggr + elem);
      return Uri.IsWellFormedUriString(constantSubstring, UriKind.RelativeOrAbsolute);
    }
  }
}
