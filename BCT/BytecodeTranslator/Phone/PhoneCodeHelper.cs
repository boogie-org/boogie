using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Bpl=Microsoft.Boogie;
using TranslationPlugins;
using Microsoft.Cci.MutableCodeModel;

namespace BytecodeTranslator.Phone {
  public static class UriHelper {
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

      // TODO this misses so many "static" strings, but let's start with this for now
      IExpression leftOp = stringConcatExpr.Arguments.FirstOrDefault();
      while (leftOp != null && leftOp is ICompileTimeConstant) {
        ICompileTimeConstant strConst = leftOp as ICompileTimeConstant;
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

      uri = constantStrings.Aggregate((aggr, elem) => aggr + elem);
      return Uri.IsWellFormedUriString(uri, UriKind.RelativeOrAbsolute);
    }
  }

  public static class PhoneTypeHelper {
    public static IAssemblyReference getSystemAssemblyReference(IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");
      return host.FindAssembly(MSPhoneSystemAssemblyId);
    }

    public static IAssemblyReference getCoreAssemblyReference(IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      return platform.CoreAssemblyRef;
    }

    public static IAssemblyReference getSystemWindowsAssemblyReference(IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");
      return host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
    }

    public static IAssemblyReference getPhoneAssemblyReference(IMetadataHost host) {
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");
      return host.FindAssembly(MSPhoneAssemblyId);
    }

    public static bool isCancelEventArgsClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference systemAssembly = getSystemAssemblyReference(host);
      ITypeReference cancelEventArgsClass = platform.CreateReference(systemAssembly, "System", "ComponentModel", "CancelEventArgs");
      return typeRef.isClass(cancelEventArgsClass);
    }

    public static bool isPhoneApplicationClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference systemAssembly = PhoneTypeHelper.getSystemWindowsAssemblyReference(host);
      ITypeReference applicationClass = platform.CreateReference(systemAssembly, "System", "Windows", "Application");
      return typeRef.isClass(applicationClass);
    }

    public static bool isPhoneApplicationPageClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference phoneAssembly = PhoneTypeHelper.getPhoneAssemblyReference(host);
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Controls", "PhoneApplicationPage");

      return typeRef.isClass(phoneApplicationPageTypeRef);
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

    public static bool isURIClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platformType = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      if (platformType == null)
        return false;

      IAssemblyReference coreRef = platformType.CoreAssemblyRef;
      AssemblyIdentity systemAssemblyId = new AssemblyIdentity(host.NameTable.GetNameFor("System"), "", coreRef.Version, coreRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(systemAssemblyId);

      ITypeReference uriTypeRef = platformType.CreateReference(systemAssembly, "System", "Uri");
      return typeRef.isClass(uriTypeRef);
    }

    public static bool isNavigationServiceClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      IAssemblyReference phoneAssembly = getPhoneAssemblyReference(host);
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "System", "Windows", "Navigation", "NavigationService");

      return typeRef.isClass(phoneApplicationPageTypeRef);
    }

    public static bool isRoutedEventHandlerClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference systemAssembly = getSystemWindowsAssemblyReference(host);
      ITypeReference routedEvHandlerType = platform.CreateReference(systemAssembly, "System", "Windows", "RoutedEventHandler");
      return typeRef.isClass(routedEvHandlerType);

    }

    public static bool isMessageBoxClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference systemAssembly = getSystemWindowsAssemblyReference(host);
      ITypeReference mbType = platform.CreateReference(systemAssembly, "System", "Windows", "MessageBox");
      return typeRef.isClass(mbType);
    }

  }

  public enum StaticURIMode {
    NOT_STATIC, STATIC_URI_CREATION_ONSITE, STATIC_URI_ROOT_CREATION_ONSITE,
  }

  public class PhoneCodeHelper {
    // TODO refactor into Feedbakc and Navigation specific code, this is already a mess
    private const string IL_BOOGIE_VAR_PREFIX = "@__BOOGIE_";
    private const string BOOGIE_VAR_PREFIX = "__BOOGIE_";
    public const string IL_CURRENT_NAVIGATION_URI_VARIABLE = IL_BOOGIE_VAR_PREFIX + "CurrentNavigationURI__";
    public const string BOOGIE_CONTINUE_ON_PAGE_VARIABLE = BOOGIE_VAR_PREFIX + "ContinueOnPage__";
    public static readonly string[] NAV_CALLS = { /*"GoBack", "GoForward", "Navigate", "StopLoading"*/ "Navigate", "GoBack" };

    public bool OnBackKeyPressOverriden { get; set; }
    public bool BackKeyPressHandlerCancels { get; set; }
    public bool BackKeyPressNavigates { get; set; }

    private Dictionary<string, string[]> PHONE_UI_CHANGER_METHODS;

    private static IMetadataHost host;
    private Microsoft.Cci.Immutable.PlatformType platform;
    private static PhoneCodeHelper _instance;
    private static bool initialized= false;

    public static void initialize(IMetadataHost host) {
      if (initialized)
        return;

      PhoneCodeHelper.host = host;
      initialized = true;
    }

    public static PhoneCodeHelper instance() {
      if (_instance == null) {
        _instance = new PhoneCodeHelper(host);
      }

      return _instance;
    }

    private PhoneCodeHelper(IMetadataHost host) {
      if (host == null)
        throw new ArgumentNullException();
      platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      initializeKnownUIChangers();
    }

    private void initializeKnownUIChangers() {
      PHONE_UI_CHANGER_METHODS= new Dictionary<string,string[]>();
      IAssemblyReference systemAssembly = PhoneTypeHelper.getSystemAssemblyReference(host);
      IAssemblyReference systemWinAssembly = PhoneTypeHelper.getSystemWindowsAssemblyReference(host);
      IAssemblyReference phoneAssembly = PhoneTypeHelper.getPhoneAssemblyReference(host);
      
      ITypeReference textBoxType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "TextBox");
      PHONE_UI_CHANGER_METHODS[textBoxType.ToString()] =
        new string[] {"set_BaselineOffset", "set_CaretBrush", "set_FontSource", "set_HorizontalScrollBarVisibility", "set_IsReadOnly", "set_LineHeight",
                      "set_LineStackingStrategy", "set_MaxLength", "set_SelectedText", "set_SelectionBackground", "set_SelectionForeground", "set_SelectionLength",
                      "set_SelectionStart", "set_Text", "set_TextAlignment", "set_TextWrapping", "set_VerticalScrollBarVisibility", "set_Watermark",
                     };
      
      ITypeReference textBlockType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "TextBlock");
      PHONE_UI_CHANGER_METHODS[textBlockType.ToString()] =
        new string[] {"set_BaselineOffset", "set_FontFamily", "set_FontSize", "set_FontSource", "set_FontStretch", "set_FontStyle", "set_FontWeight", "set_Foreground",
                      "set_CharacterSpacing", "set_LineHeight", "set_LineStackingStrategy", "set_Padding", "set_Text", "set_TextAlignment", "set_TextDecorations",
                      "set_TextTrimming", "set_TextWrapping", 
                     };

      ITypeReference uiElementType = platform.CreateReference(systemAssembly, "System", "Windows", "UIElement");
      PHONE_UI_CHANGER_METHODS[uiElementType.ToString()] =
        new string[] {"set_Clip", "set_Opacity", "set_OpacityMask", "set_Projection", "set_RenderTransform",
                      "set_RenderTransformOrigin", "set_Visibility", "Arrange", "InvalidateArrange", "InvalidateMeasure", "SetValue", "ClearValue", // Set/ClearValue are quite unsafe
                      "UpdateLayout", "Measure",
                     };

      ITypeReference frameworkElementType = platform.CreateReference(systemAssembly, "System", "Windows", "FrameworkElement");
      PHONE_UI_CHANGER_METHODS[frameworkElementType.ToString()] =
        new string[] {"set_FlowDirection", "set_Height", "set_HorizontalAlignment", "set_Language", "set_Margin", "set_MaxHeight", "set_MaxWidth",
                      "set_MinHeight", "set_MinWidth", "set_Style", "set_VerticalAlignment", "set_Width", "set_Cursor", 
                     };

      ITypeReference borderType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Border");
      PHONE_UI_CHANGER_METHODS[borderType.ToString()] =
        new string[] {"set_Background", "set_BorderBrush", "set_BorderThickness", "set_CornerRadius", "set_Padding", 
                     };

      ITypeReference controlType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Control");
      PHONE_UI_CHANGER_METHODS[controlType.ToString()] =
        new string[] {"set_Background", "set_BorderBrush", "set_BorderThickness", "set_CharacterSpacing", "set_FontFamily", "set_FontSize", "set_FontStretch",
                      "set_FontStyle", "set_FontWeight", "set_Foreground", "set_HorizontalContentAlignment", "set_IsEnabled", "set_Padding", "set_VerticalContentAlignment",
                     };

      ITypeReference contentControlType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ContentControl");
      PHONE_UI_CHANGER_METHODS[contentControlType.ToString()] = new string[] { "set_Content", };

      ITypeReference panelType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Panel");
      PHONE_UI_CHANGER_METHODS[panelType.ToString()] = new string[] { "set_Background", };

      ITypeReference canvasType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Canvas");
      PHONE_UI_CHANGER_METHODS[canvasType.ToString()] = new string[] { "set_Left", "set_Top", "set_ZIndex", };

      ITypeReference toggleButtonType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Primitives", "ToggleButton");
      PHONE_UI_CHANGER_METHODS[toggleButtonType.ToString()] = new string[] { "set_IsChecked", };

      ITypeReference gridType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Grid");
      PHONE_UI_CHANGER_METHODS[gridType.ToString()] = new string[] { "set_ShowGridLines",  "set_Column", "set_ColumnSpan", "set_Row", "set_RowSpan", };

      ITypeReference imageType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Image");
      PHONE_UI_CHANGER_METHODS[imageType.ToString()] = new string[] { "set_Source", "set_Stretch", };

      ITypeReference inkPresenterType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "InkPresenter");
      PHONE_UI_CHANGER_METHODS[inkPresenterType.ToString()] = new string[] { "set_Strokes", };

      ITypeReference itemsControlType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ItemsControl");
      PHONE_UI_CHANGER_METHODS[itemsControlType.ToString()] = new string[] { "set_DisplayMemberPath", "set_ItemsSource", "set_ItemTemplate", };

      ITypeReference selectorType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Primitives", "Selector");
      PHONE_UI_CHANGER_METHODS[selectorType.ToString()] =
        new string[] { "set_SelectedIndex", "set_SelectedItem", "set_SelectedValue", "set_SelectedValuePath", };

      ITypeReference listBoxType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ListBox");
      PHONE_UI_CHANGER_METHODS[listBoxType.ToString()] = new string[] { "set_ItemContainerStyle", };

      ITypeReference passwordBoxType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "PasswordBox");
      PHONE_UI_CHANGER_METHODS[passwordBoxType.ToString()] =
        new string[] { "set_CaretBrush", "set_FontSource", "set_MaxLength", "set_Password", "set_PasswordChar",
                       "set_SelectionBackground", "set_SelectionForeground",
                     };

      ITypeReference rangeBaseType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Primitives", "RangeBase");
      PHONE_UI_CHANGER_METHODS[rangeBaseType.ToString()] = new string[] { "set_LargeChange", "set_Maximum", "set_Minimum", "set_SmallChange", "set_Value", };

      ITypeReference progressBarType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ProgressBar");
      PHONE_UI_CHANGER_METHODS[progressBarType.ToString()] = new string[] { "set_IsIndeterminate", };

      ITypeReference sliderType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Slider");
      PHONE_UI_CHANGER_METHODS[sliderType.ToString()] = new string[] { "set_IsDirectionReversed", "set_Orientation", };

      ITypeReference stackPanelType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "StackPanel");
      PHONE_UI_CHANGER_METHODS[stackPanelType.ToString()] = new string[] { "set_Orientation", };

      ITypeReference richTextBoxType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "RichTextBox");
      PHONE_UI_CHANGER_METHODS[richTextBoxType.ToString()] =
        new string[] { "set_BaselineOffset", "set_CaretBrush", "set_HorizontalScrollBartVisibility", "set_LineHeight", "set_LineStackingStrategy",
                       "set_TextAlignment", "set_TextWrapping", "set_VerticalScrollBarVisibility", "set_Xaml", };

      ITypeReference webBrowserTaskType = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Tasks", "WebBrowserTask");
      PHONE_UI_CHANGER_METHODS[webBrowserTaskType.ToString()] = new string[] { "Show", };

      ITypeReference appBarIconButtonType = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Shell", "ApplicationBarIconButton");
      PHONE_UI_CHANGER_METHODS[appBarIconButtonType.ToString()] = new string[] { "set_IsEnabled", "set_IconUri", "set_Text", };

      ITypeReference emailComposeTaskType = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Tasks", "EmailComposeTask");
      PHONE_UI_CHANGER_METHODS[emailComposeTaskType.ToString()] = new string[] { "Show", };

      ITypeReference scaleTransformType = platform.CreateReference(systemWinAssembly, "System", "Windows", "Media", "ScaleTransform");
      PHONE_UI_CHANGER_METHODS[scaleTransformType.ToString()] = new string[] { "set_CenterX", "set_CenterY", "set_ScaleX", "set_ScaleY",  };
    }

    // TODO externalize strings
    public static readonly string[] IgnoredEvents =
    { "Loaded",
    };

    // awful hack. want to insert a nonexisting method call while traversing CCI AST, deferring it to Boogie translation
    public const string BOOGIE_DO_HAVOC_CURRENTURI = BOOGIE_VAR_PREFIX + "Havoc_CurrentURI__";

    public PhoneControlsPlugin PhonePlugin { get; set; }
    private IDictionary<string, Bpl.NamedDeclaration> boogieObjects = new Dictionary<string, Bpl.NamedDeclaration>();

    public Bpl.Variable getBoogieVariableForName(string varName) {
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
    public bool setBoogieObjectForName(string name, Bpl.NamedDeclaration bplObject) {
      bool ret = true;
      if (boogieObjects.ContainsKey(name))
        ret = false;

      boogieObjects[name] = bplObject;
      return ret;
    }

    private bool isPhoneUIChangerClass(ITypeReference typeRef) {
      return PHONE_UI_CHANGER_METHODS.Keys.Contains(typeRef.ToString());
    }

    public bool isNavigationCall(IMethodCall call) {
      ITypeReference callType = call.MethodToCall.ContainingType;
      if (!callType.isNavigationServiceClass(host))
        return false;

      return NAV_CALLS.Contains(call.MethodToCall.Name.Value);
    }

    private ITypeReference mainAppTypeRef;
    public void setMainAppTypeReference(ITypeReference appType) {
      mainAppTypeRef = appType;
    }

    public ITypeReference getMainAppTypeReference() {
      return mainAppTypeRef;
    }

    public void setBoogieNavigationVariable(string var) {
      PhonePlugin.setBoogieNavigationVariable(var);
    }

    public string getBoogieNavigationVariable() {
      return PhonePlugin.getBoogieNavigationVariable();
    }

    public string getXAMLForPage(string pageClass) {
      return PhonePlugin.getXAMLForPage(pageClass);
    }

    public void setBoogieStringPageNameForPageClass(string pageClass, string boogieStringName) {
      PhonePlugin.setBoogieStringPageNameForPageClass(pageClass, boogieStringName);
    }

    public void setMainAppTypeName(string fullyQualifiedName) {
      PhonePlugin.setMainAppTypeName(fullyQualifiedName);
    }

    public string getMainAppTypeName() {
      return PhonePlugin.getMainAppTypeName();
    }

    public Bpl.AssignCmd createBoogieNavigationUpdateCmd(Sink sink) {
      // the block is a potential page changer
      List<Bpl.AssignLhs> lhs = new List<Bpl.AssignLhs>();
      List<Bpl.Expr> rhs = new List<Bpl.Expr>();
      Bpl.Expr value = new Bpl.LiteralExpr(Bpl.Token.NoToken, false);
      rhs.Add(value);
      Bpl.SimpleAssignLhs assignee =
        new Bpl.SimpleAssignLhs(Bpl.Token.NoToken,
                                new Bpl.IdentifierExpr(Bpl.Token.NoToken,
                                                       sink.FindOrCreateGlobalVariable(PhoneCodeHelper.BOOGIE_CONTINUE_ON_PAGE_VARIABLE, Bpl.Type.Bool)));
      lhs.Add(assignee);
      Bpl.AssignCmd assignCmd = new Bpl.AssignCmd(Bpl.Token.NoToken, lhs, rhs);
      return assignCmd;
    }

    // TODO do away with these whenever it is possible to make repeated passes at the translator, and handle from Program
    public bool PhoneNavigationToggled { get; set; }
    public bool PhoneFeedbackToggled { get; set; }

    public bool isMethodInputHandlerOrFeedbackOverride(IMethodDefinition method) {
      // FEEDBACK TODO: This is extremely coarse. There must be quite a few non-UI routed/non-routed events
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference coreAssembly= PhoneTypeHelper.getCoreAssemblyReference(host);
      ITypeReference eventArgsType= platform.CreateReference(coreAssembly, "System", "EventArgs");
      foreach (IParameterDefinition paramDef in method.Parameters) {
        if (paramDef.Type.isClass(eventArgsType))
          return true;
      }

      return false;
    }

    public bool isMethodKnownUIChanger(IMethodCall methodCall) {
      // FEEDBACK TODO join these two with the others
      if (methodCall.MethodToCall.ContainingType.isNavigationServiceClass(host)) {
        return NAV_CALLS.Contains(methodCall.MethodToCall.Name.Value);
      } else if (methodCall.IsStaticCall && methodCall.MethodToCall.ContainingType.isMessageBoxClass(host) &&
                 methodCall.MethodToCall.Name.Value == "Show") {
        return true;
      }

      // otherwise, it must be a control input call
      // before any method call checks, make sure the receiving object is a Control
      IExpression callee = methodCall.ThisArgument;
      if (callee == null)
        return false;

      ITypeReference calleeType = callee.Type;
      while (calleeType.ResolvedType.BaseClasses.Any()) {
        if (isPhoneUIChangerClass(calleeType) && isKnownUIChanger(calleeType, methodCall)) {
          return true;
        }

        calleeType = calleeType.ResolvedType.BaseClasses.First();
      }

      return false;
    }

    private bool isKnownUIChanger(ITypeReference typeRef, IMethodCall call) {
      string methodName= call.MethodToCall.Name.Value;
      IEnumerable<String> methodsForType = PHONE_UI_CHANGER_METHODS[typeRef.ToString()];
      return methodsForType != null && methodsForType.Contains(methodName);
    }

    private HashSet<string> ignoredHandlers = new HashSet<string>();
    public void ignoreEventHandler(string fullyQualifiedEventHandler) {
      ignoredHandlers.Add(fullyQualifiedEventHandler);
    }

    public bool isMethodIgnoredForFeedback(IMethodDefinition methodTranslated) {
      INamespaceTypeDefinition type= methodTranslated.ContainingType.ResolvedType as INamespaceTypeDefinition;

      if (type == null)
        return false;

      string methodName = type.ContainingUnitNamespace.Name.Value + "." + type.Name + "." + methodTranslated.Name.Value;
      return ignoredHandlers.Contains(methodName);
    }

    private HashSet<Bpl.Procedure> callableMethods = new HashSet<Bpl.Procedure>();
    public void trackCallableMethod(Bpl.Procedure proc) {
      callableMethods.Add(proc);
    }

    public IEnumerable<Bpl.Procedure> getCallableMethods() {
      return callableMethods;
    }

    public void CreateFeedbackCallingMethods(Sink sink) {
      Bpl.Program translatedProgram= sink.TranslatedProgram;
      foreach (Bpl.Procedure proc in callableMethods) {
        addMethodCalling(proc, translatedProgram, sink);
      }
    }

    private void addMethodCalling(Bpl.Procedure proc, Bpl.Program program, Sink sink) {
      Bpl.Procedure callingProc= new Bpl.Procedure(Bpl.Token.NoToken, "__BOOGIE_CALL_" + proc.Name, new Bpl.TypeVariableSeq(), new Bpl.VariableSeq(),
                                                   new Bpl.VariableSeq(), new Bpl.RequiresSeq(), new Bpl.IdentifierExprSeq(), new Bpl.EnsuresSeq());
      sink.TranslatedProgram.TopLevelDeclarations.Add(callingProc);

      Bpl.StmtListBuilder codeBuilder = new Bpl.StmtListBuilder();
      Bpl.VariableSeq localVars = new Bpl.VariableSeq(proc.InParams);
      Bpl.IdentifierExprSeq identVars= new Bpl.IdentifierExprSeq();

      for (int i = 0; i < localVars.Length; i++) {
        identVars.Add(new Bpl.IdentifierExpr(Bpl.Token.NoToken, localVars[i]));
      }
      codeBuilder.Add(new Bpl.HavocCmd(Bpl.Token.NoToken, identVars));

      // FEEDBACK TODO this is possibly too much, I'm guessing sometimes this args might well be null
      Bpl.Expr notNullExpr;
      foreach (Bpl.IdentifierExpr idExpr in identVars) {
        if (idExpr.Type.Equals(sink.Heap.RefType)) {
          notNullExpr= Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, idExpr, Bpl.Expr.Ident(sink.Heap.NullRef));
          codeBuilder.Add(new Bpl.AssumeCmd(Bpl.Token.NoToken, notNullExpr));
        }
      }

      Bpl.ExprSeq callParams = new Bpl.ExprSeq();
      for (int i = 0; i < identVars.Length; i++) {
        callParams.Add(identVars[i]);
      }
      Bpl.CallCmd callCmd = new Bpl.CallCmd(Bpl.Token.NoToken, proc.Name, callParams, new Bpl.IdentifierExprSeq());
      codeBuilder.Add(callCmd);
      Bpl.Implementation impl = new Bpl.Implementation(Bpl.Token.NoToken, callingProc.Name, new Bpl.TypeVariableSeq(), new Bpl.VariableSeq(),
                                                       new Bpl.VariableSeq(), localVars, codeBuilder.Collect(Bpl.Token.NoToken));
      sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
    }

    public bool isBackKeyPressOverride(IMethodDefinition method) {
      if (!method.IsVirtual || method.Name.Value != "OnBackKeyPress" || !method.ContainingType.isPhoneApplicationPageClass(host) ||
          method.ParameterCount != 1 || !method.Parameters.ToList()[0].Type.isCancelEventArgsClass(host))
        return false;
      else
        return true;
    }
  }
}
