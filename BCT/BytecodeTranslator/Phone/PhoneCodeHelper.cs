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

  public enum PHONE_CONTROL_TYPE {
    None=0x0000, UIElement=0x0001, FrameworkElement= 0x0002, Border=0x0004, Control=0x0008, ContentControl=0x0010, Panel=0x0020, Canvas=0x0040,
    ToggleButton=0x0080, Grid=0x0100, Image=0x0200, InkPresenter=0x0400, ItemsControl=0x0800, Selector=0x1000, ListBox=0x2000, PasswordBox=0x4000,
    RangeBase=0x8000, ProgressBar=0x00010000, Slider=0x00020000, StackPanel=0x00040000, RichTextBox=0x00080000, TextBlock=0x00100000,
    TextBox=0x00200000,
  }

  public static class PhoneCodeHelper {
    // TODO externalize strings
    public static readonly string[] IgnoredEvents =
    { "Loaded",
    };

    private static readonly string[] TextBoxChangeCalls =
    { "set_BaselineOffset", "set_CaretBrush", "set_FontSource", "set_HorizontalScrollBarVisibility", "set_IsReadOnly", "set_LineHeight",
      "set_LineStackingStrategy", "set_MaxLength", "set_SelectedText", "set_SelectionBackground", "set_SelectionForeground", "set_SelectionLength",
      "set_SelectionStart", "set_Text", "set_TextAlignment", "set_TextWrapping", "set_VerticalScrollBarVisibility", "set_Watermark",
    };

    private static readonly string[] TextBlockChangeCalls =
    { "set_BaselineOffset", "set_FontFamily", "set_FontSize", "set_FontSource", "set_FontStretch", "set_FontStyle", "set_FontWeight", "set_Foreground",
      "set_CharacterSpacing", "set_LineHeight", "set_LineStackingStrategy", "set_Padding", "set_Text", "set_TextAlignment", "set_TextDecorations",
      "set_TextTrimming", "set_TextWrapping", 
    };

    private static readonly string[] UIElementChangeCalls =
    { "set_Clip", "set_Opacity", "set_OpacityMask", "set_Projection", "set_RenderTransform",
      "set_RenderTransformOrigin", "set_Visibility", "Arrange", "InvalidateArrange", "InvalidateMeasure", "SetValue", "ClearValue", // Set/ClearValue are quite unsafe
      "UpdateLayout", "Measure",
    };

    private static readonly string[] FrameworkElementChangeCalls =
    { "set_FlowDirection", "set_Height", "set_HorizontalAlignment", "set_Language", "set_Margin", "set_MaxHeight", "set_MaxWidth", "set_MinHeight",
      "set_MinWidth", "set_Style", "set_VerticalAlignment", "set_Width", "set_Cursor", 
    };

    private static readonly string[] BorderChangeCalls =
    { "set_Background", "set_BorderBrush", "set_BorderThickness", "set_CornerRadius", "set_Padding", 
    };

    private static readonly string[] ControlChangeCalls =
    { "set_Background", "set_BorderBrush", "set_BorderThickness", "set_CharacterSpacing", "set_FontFamily", "set_FontSize", "set_FontStretch",
      "set_FontStyle", "set_FontWeight", "set_Foreground", "set_HorizontalContentAlignment", "set_IsEnabled", "set_Padding", "set_VerticalContentAlignment",
    };

    private static readonly string[] ContentControlChangeCalls =
    { "set_Content", 
    };

    private static readonly string[] PanelChangeCalls =
    { "set_Background", 
    };

    private static readonly string[] CanvasChangeCalls =
    { "set_Left", "set_Top", "set_ZIndex", 
    };

    private static readonly string[] ToggleButtonChangeCalls =
    { "set_IsChecked", 
    };

    private static readonly string[] GridChangeCalls =
    { "set_ShowGridLines",  "set_Column", "set_ColumnSpan", "set_Row", "set_RowSpan", 
    };

    private static readonly string[] ImageChangeCalls =
    { "set_Source", "set_Stretch", 
    };

    private static readonly string[] InkPresenterChangeCalls =
    { "set_Strokes",
    };

    private static readonly string[] ItemsControlChangeCalls =
    { "set_DisplayMemberPath", "set_ItemsSource", "set_ItemTemplate", 
    };

    private static readonly string[] SelectorChangeCalls =
    { "set_SelectedIndex", "set_SelectedItem", "set_SelectedValue", "set_SelectedValuePath",
    };

    private static readonly string[] ListBoxChangeCalls =
    { "set_ItemContainerStyle", 
    };

    private static readonly string[] PasswordBoxChangeCalls =
    { "set_CaretBrush", "set_FontSource", "set_MaxLength", "set_Password", "set_PasswordChar", "set_SelectionBackground", "set_SelectionForeground",
    };

    private static readonly string[] RangeBaseChangeCalls =
    { "set_LargeChange", "set_Maximum", "set_Minimum", "set_SmallChange", "set_Value",
    };

    private static readonly string[] ProgressBarChangeCalls =
    { "set_IsIndeterminate",
    };

    private static readonly string[] SliderChangeCalls =
    { "set_IsDirectionReversed", "set_Orientation",
    };

    private static readonly string[] StackPanelChangeCalls =
    { "set_Orientation", 
    };

    private static readonly string[] RichTextBoxChangeCalls =
    { "set_BaselineOffset", "set_CaretBrush", "set_HorizontalScrollBartVisibility", "set_LineHeight", "set_LineStackingStrategy", "set_TextAlignment",
      "set_TextWrapping", "set_VerticalScrollBarVisibility", "set_Xaml",
    };

    private const string IL_BOOGIE_VAR_PREFIX = "@__BOOGIE_";
    private const string BOOGIE_VAR_PREFIX = "__BOOGIE_";
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
      bool ret = true;
      if (boogieObjects.ContainsKey(name))
        ret = false;

      boogieObjects[name] = bplObject;
      return ret;
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
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");

      IAssemblyReference phoneAssembly = host.FindAssembly(MSPhoneAssemblyId);
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "System", "Windows", "Navigation", "NavigationService");

      return typeRef.isClass(phoneApplicationPageTypeRef);
    }

    public static bool isRoutedEventHandler(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      ITypeReference routedEvHandlerType = platform.CreateReference(systemAssembly, "System", "Windows", "RoutedEventHandler");
      return typeRef.isClass(routedEvHandlerType);
      
    }

    public static bool isMessageBoxClass(this ITypeReference typeRef, IMetadataHost host) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      ITypeReference mbType = platform.CreateReference(systemAssembly, "System", "Windows", "MessageBox");
      return typeRef.isClass(mbType);
    }

    public static bool isPhoneControlClass(this ITypeReference typeRef, IMetadataHost host, out PHONE_CONTROL_TYPE controlType) {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      ITypeReference uiElementType = platform.CreateReference(systemAssembly, "System", "Windows", "UIElement");
      ITypeReference frameworkElementType = platform.CreateReference(systemAssembly, "System", "Windows", "FrameworkElement");

      controlType = PHONE_CONTROL_TYPE.None;
      if (typeRef.isClass(uiElementType)) {
        controlType |= PHONE_CONTROL_TYPE.UIElement;
      }

      if (typeRef.isClass(frameworkElementType)) {
        controlType |= PHONE_CONTROL_TYPE.FrameworkElement;
        ITypeReference imageType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Image");
        ITypeReference borderType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Border");
        ITypeReference winControlType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Control");
        ITypeReference panelType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Panel");
        ITypeReference textBlockType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "TextBlock");

        if (typeRef.isClass(textBlockType)) {
          controlType |= PHONE_CONTROL_TYPE.TextBlock;
        } else if (typeRef.isClass(imageType)) {
          controlType |= PHONE_CONTROL_TYPE.Image;
        } else if (typeRef.isClass(borderType)) {
          controlType |= PHONE_CONTROL_TYPE.Border;
        } else if (typeRef.isClass(winControlType)) {
          controlType |= PHONE_CONTROL_TYPE.Control;
          ITypeReference contentControlType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ContentControl");
          ITypeReference itemsControlType= platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ItemsControl");
          ITypeReference passwordBoxType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "PasswordBox");
          ITypeReference rangeBaseType= platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Primitives","RangeBase");
          ITypeReference richTextBoxType= platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "RichTextBox");
          ITypeReference textBoxType= platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "TextBox");

          if (typeRef.isClass(textBoxType)) {
            controlType |= PHONE_CONTROL_TYPE.TextBox;
          } else if (typeRef.isClass(contentControlType)) {
            controlType |= PHONE_CONTROL_TYPE.ContentControl;
            ITypeReference toggleButtonType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Primitives", "ToggleButton");
            if (typeRef.isClass(toggleButtonType)) {
              controlType |= PHONE_CONTROL_TYPE.ToggleButton;
            }
          } else if (typeRef.isClass(itemsControlType)) {
            controlType |= PHONE_CONTROL_TYPE.ItemsControl;
            ITypeReference selectorType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Primitives", "Selector");
            if (typeRef.isClass(selectorType)) {
              controlType |= PHONE_CONTROL_TYPE.Selector;
              ITypeReference listBoxType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ListBox");
              if (typeRef.isClass(listBoxType)) {
                controlType |= PHONE_CONTROL_TYPE.ListBox;
              }
            }
          } else if (typeRef.isClass(passwordBoxType)) {
            controlType |= PHONE_CONTROL_TYPE.PasswordBox;
          } else if (typeRef.isClass(rangeBaseType)) {
            controlType |= PHONE_CONTROL_TYPE.RangeBase;
            ITypeReference progressBarType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "ProgressBar");
            ITypeReference sliderType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Slider");
            if (typeRef.isClass(progressBarType)) {
              controlType |= PHONE_CONTROL_TYPE.ProgressBar;
            } else if (typeRef.isClass(sliderType)) {
              controlType |= PHONE_CONTROL_TYPE.Slider;
            }
          } else if (typeRef.isClass(richTextBoxType)) {
            controlType |= PHONE_CONTROL_TYPE.RichTextBox;
          }
        } else if (typeRef.isClass(panelType)) {
          controlType |= PHONE_CONTROL_TYPE.Panel;
          ITypeReference canvasType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Canvas");
          ITypeReference gridType = platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "Grid");
          ITypeReference stackPanelType= platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "StackPanel");
          if (typeRef.isClass(canvasType)) {
            controlType |= PHONE_CONTROL_TYPE.Canvas;
            ITypeReference inkPresenterType= platform.CreateReference(systemAssembly, "System", "Windows", "Controls", "InkPresenter");
            if (typeRef.isClass(inkPresenterType)) {
              controlType |= PHONE_CONTROL_TYPE.InkPresenter;
            }
          } else if (typeRef.isClass(gridType)) {
            controlType |= PHONE_CONTROL_TYPE.Grid;
          } else if (typeRef.isClass(stackPanelType)) {
            controlType |= PHONE_CONTROL_TYPE.StackPanel;
          }
        }
      }

      return controlType != PHONE_CONTROL_TYPE.None;
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
      ITypeReference phoneApplicationPageTypeRef = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Controls" , "PhoneApplicationPage");
      
      return typeRef.isClass(phoneApplicationPageTypeRef);
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
      Uri realUri;
      try {
        realUri = new Uri(uri, UriKind.Absolute);
      } catch (UriFormatException) {
        // uri string is relative
        realUri = new Uri(mockBaseUri, uri);
      }

      string str = realUri.GetComponents(UriComponents.Path | UriComponents.StrongAuthority | UriComponents.Scheme, UriFormat.UriEscaped);
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

    public static void setBoogieNavigationVariable(string var) {
      PhonePlugin.setBoogieNavigationVariable(var);
    }

    public static string getBoogieNavigationVariable() {
      return PhonePlugin.getBoogieNavigationVariable();
    }

    public static string getXAMLForPage(string pageClass) {
      return PhonePlugin.getXAMLForPage(pageClass);
    }

    public static void setBoogieStringPageNameForPageClass(string pageClass, string boogieStringName) {
      PhonePlugin.setBoogieStringPageNameForPageClass(pageClass, boogieStringName);
    }

    public static void setMainAppTypeName(string fullyQualifiedName) {
      PhonePlugin.setMainAppTypeName(fullyQualifiedName);
    }

    public static string getMainAppTypeName() {
      return PhonePlugin.getMainAppTypeName();
    }

    public static Bpl.AssignCmd createBoogieNavigationUpdateCmd(Sink sink) {
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
    public static bool PhoneNavigationToggled { get; set; }
    public static bool PhoneFeedbackToggled { get; set; }

    public static bool isMethodInputHandlerOrFeedbackOverride(IMethodDefinition method, IMetadataHost host) {
      // FEEDBACK TODO: This is extremely coarse. There must be quite a few non-UI routed events
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType; ;
      IAssemblyReference coreAssemblyRef = platform.CoreAssemblyRef;
      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");
      IAssemblyReference systemAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      ITypeReference routedEventType= platform.CreateReference(systemAssembly, "System", "Windows", "RoutedEventArgs");
      foreach (IParameterDefinition paramDef in method.Parameters) {
        if (paramDef.Type.isClass(routedEventType))
          return true;
      }

      return false;
    }

    public static bool isMethodKnownUIChanger(IMethodCall methodCall, IMetadataHost host) {
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
      PHONE_CONTROL_TYPE controlType;
      if (calleeType.isPhoneControlClass(host, out controlType)) {
        return isKnownUIChanger(calleeType, methodCall, controlType);
      } else {
        return false;
      }
    }

    private static bool isKnownUIChanger(ITypeReference typeRef, IMethodCall call, PHONE_CONTROL_TYPE controlType) {
      bool result= false;
      string methodName= call.MethodToCall.Name.Value;

      if (!result && (controlType & PHONE_CONTROL_TYPE.UIElement) != 0)
        result|= UIElementChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.FrameworkElement) != 0)
        result|= FrameworkElementChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Border) != 0)
        result|= BorderChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Control) != 0)
        result|= ControlChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.ContentControl) != 0)
        result|= ContentControlChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Panel) != 0)
        result|= PanelChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Canvas) != 0)
        result|= CanvasChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.ToggleButton) != 0)
        result|= ToggleButtonChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Grid) != 0)
        result|= GridChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Image) != 0)
        result|= ImageChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.InkPresenter) != 0)
        result|= InkPresenterChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.ItemsControl) != 0)
        result|= ItemsControlChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Selector) != 0)
        result|= SelectorChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.ListBox) != 0)
        result|= ListBoxChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.PasswordBox) != 0)
        result|= PasswordBoxChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.RangeBase) != 0)
        result|= RangeBaseChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.ProgressBar) != 0)
        result|= ProgressBarChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.Slider) != 0)
        result|= SliderChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.StackPanel) != 0)
        result|= StackPanelChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.RichTextBox) != 0)
        result|= RichTextBoxChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.TextBlock) != 0)
        result|= TextBlockChangeCalls.Contains(methodName);
      if (!result && (controlType & PHONE_CONTROL_TYPE.TextBox) != 0)
        result|= TextBoxChangeCalls.Contains(methodName);

      return result;
    }

    private static HashSet<string> ignoredHandlers = new HashSet<string>();
    public static void ignoreEventHandler(string fullyQualifiedEventHandler) {
      ignoredHandlers.Add(fullyQualifiedEventHandler);
    }

    public static bool isMethodIgnoredForFeedback(IMethodDefinition methodTranslated) {
      INamespaceTypeDefinition type= methodTranslated.ContainingType.ResolvedType as INamespaceTypeDefinition;

      if (type == null)
        return false;

      string methodName = type.ContainingUnitNamespace.Name.Value + "." + type.Name + "." + methodTranslated.Name.Value;
      return ignoredHandlers.Contains(methodName);
    }
  }
}
