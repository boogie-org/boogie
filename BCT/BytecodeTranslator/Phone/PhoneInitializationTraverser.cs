//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;
using TranslationPlugins;


namespace BytecodeTranslator.Phone {

  /// <summary>
  /// Traverse code looking for phone specific points of interest, possibly injecting necessary code in-between
  /// </summary>
  public class PhoneInitializationCodeTraverser : CodeTraverser {
    private readonly IMethodDefinition methodBeingTraversed;
    private static bool initializationFound= false;
    private MetadataReaderHost host;

    private IAssemblyReference coreAssemblyRef;
    private IAssemblyReference phoneAssembly;
    private IAssemblyReference phoneSystemWindowsAssembly;
    private IAssemblyReference MSPhoneControlsAssembly;
    private INamespaceTypeReference appBarIconButtonType;
    private INamespaceTypeReference appBarMenuItemType;
    private INamespaceTypeReference checkBoxType;
    private INamespaceTypeReference radioButtonType;
    private INamespaceTypeReference buttonType;
    private INamespaceTypeReference buttonBaseType;
    private INamespaceTypeReference toggleButtonType;
    private INamespaceTypeReference controlType;
    private INamespaceTypeReference uiElementType;
    private INamespaceTypeReference pivotType;
    private INamespaceTypeReference listBoxType;

    private CompileTimeConstant trueConstant;
    private CompileTimeConstant falseConstant;

    private IMethodReference isEnabledSetter;
    private IMethodReference isEnabledGetter;
    private IMethodReference isCheckedSetter;
    private IMethodReference isCheckedGetter;
    private IMethodReference visibilitySetter;
    private IMethodReference visibilityGetter;
    private IMethodReference clickHandlerAdder;
    private IMethodReference clickHandlerRemover;
    private IMethodReference checkedHandlerAdder;
    private IMethodReference checkedHandlerRemover;
    private IMethodReference uncheckedHandlerAdder;
    private IMethodReference uncheckedHandlerRemover;

    private ITypeReference getTypeForClassname(String classname) {
      if (classname == "Button") {
        return buttonType;
      } else if (classname == "RadioButton") {
        return radioButtonType;
      } else if (classname == "CheckBox") {
        return checkBoxType;
      } else if (classname == "ApplicationBarIconButton") {
        return appBarIconButtonType;
      } else if (classname == "ApplicationBarMenuItem") {
        return appBarMenuItemType;
      } else if (classname == "Pivot") {
        return pivotType;
      } else if (classname == "ListBox") {
        return listBoxType;
      } else if (classname == "DummyType") {
        // return Dummy.Type;
        return host.PlatformType.SystemObject;
      } else {
        // TODO avoid throwing exceptions, just log
        throw new NotImplementedException("Type " + classname + " is not being monitored yet for phone controls");
      }
    }

    public PhoneInitializationCodeTraverser(MetadataReaderHost host, IMethodDefinition traversedMethod) : base() {
      this.methodBeingTraversed = traversedMethod;
      this.host = host;
      InitializeTraverser();
    }

    private void InitializeTraverser() {
      Microsoft.Cci.Immutable.PlatformType platform = host.PlatformType as Microsoft.Cci.Immutable.PlatformType;
      coreAssemblyRef = platform.CoreAssemblyRef;

      // TODO obtain version, culture and signature data dynamically
      AssemblyIdentity MSPhoneAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");
      AssemblyIdentity MSPhoneControlsAssemblyId=
          new AssemblyIdentity(host.NameTable.GetNameFor("Microsoft.Phone.Controls"), "", new Version("7.0.0.0"),
                               new byte[] { 0x24, 0xEE, 0xC0, 0xD8, 0xC8, 0x6C, 0xDA, 0x1E }, "");

      AssemblyIdentity MSPhoneSystemWindowsAssemblyId =
          new AssemblyIdentity(host.NameTable.GetNameFor("System.Windows"), coreAssemblyRef.Culture, coreAssemblyRef.Version,
                               coreAssemblyRef.PublicKeyToken, "");

      phoneAssembly = host.FindAssembly(MSPhoneAssemblyId);
      phoneSystemWindowsAssembly = host.FindAssembly(MSPhoneSystemWindowsAssemblyId);
      MSPhoneControlsAssembly= host.FindAssembly(MSPhoneControlsAssemblyId);
      // TODO BUG / XAML DEPENDENCE If a control is declared in XAML, it may be one from a library *not* linked! So, assemblies could be dummy here

      // TODO determine the needed types dynamically
      if (phoneAssembly != Dummy.Assembly) {
        appBarIconButtonType = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Shell", "ApplicationBarIconButton");
        appBarMenuItemType = platform.CreateReference(phoneAssembly, "Microsoft", "Phone", "Shell", "ApplicationBarMenuItem");
      } else {
        appBarIconButtonType = host.PlatformType.SystemObject;
        appBarMenuItemType = host.PlatformType.SystemObject;
      }

      if (phoneSystemWindowsAssembly != Dummy.Assembly) {
        checkBoxType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "CheckBox");
        radioButtonType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "RadioButton");
        buttonType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "Button");
        buttonBaseType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "Primitives", "ButtonBase");
        toggleButtonType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "Primitives", "ToggleButton");
        controlType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "Control");
        uiElementType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "UIElement");
        listBoxType = platform.CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Controls", "ListBox");
      } else {
        checkBoxType = host.PlatformType.SystemObject;
        radioButtonType = host.PlatformType.SystemObject;
        buttonType = host.PlatformType.SystemObject;
        buttonBaseType = host.PlatformType.SystemObject;
        toggleButtonType = host.PlatformType.SystemObject;
        controlType = host.PlatformType.SystemObject;
        uiElementType = host.PlatformType.SystemObject;
        listBoxType = host.PlatformType.SystemObject;
      }

      if (MSPhoneControlsAssembly != Dummy.Assembly) {
        pivotType = platform.CreateReference(MSPhoneControlsAssembly, "Microsoft", "Phone", "Controls", "Pivot");
      } else {
        pivotType = host.PlatformType.SystemObject;
      }

      

      trueConstant = new CompileTimeConstant() {
        Type = platform.SystemBoolean,
        Value = true
      };
      falseConstant = new CompileTimeConstant() {
        Type = platform.SystemBoolean,
        Value = false
      };

      IEnumerable<IPropertyDefinition> controlProperties = controlType.ResolvedType.Properties;
      IEnumerable<IPropertyDefinition> toggleButtonProperties = toggleButtonType.ResolvedType.Properties;
      IEnumerable<IPropertyDefinition> uiElementProperties = uiElementType.ResolvedType.Properties;

      IPropertyDefinition prop = controlProperties.Single(p => p.Name.Value == "IsEnabled");
      isEnabledSetter = prop.Setter;
      isEnabledGetter = prop.Getter;
      prop = toggleButtonProperties.Single(p => p.Name.Value == "IsChecked");
      isCheckedSetter = prop.Setter;
      isCheckedGetter = prop.Getter;
      prop = uiElementProperties.Single(p => p.Name.Value == "Visibility");
      visibilitySetter = prop.Setter;
      visibilityGetter = prop.Getter;

      IEnumerable<IEventDefinition> buttonBaseEvents = buttonBaseType.ResolvedType.Events;
      IEnumerable<IEventDefinition> toggleButtonEvents = toggleButtonType.ResolvedType.Events;
      IEventDefinition evt = buttonBaseEvents.Single(e => e.Name.Value == "Click");
      clickHandlerAdder = evt.Adder;
      clickHandlerRemover = evt.Remover;
      evt = toggleButtonEvents.Single(e => e.Name.Value == "Checked");
      checkedHandlerAdder = evt.Adder;
      checkedHandlerRemover = evt.Remover;
      evt = toggleButtonEvents.Single(e => e.Name.Value == "Unchecked");
      uncheckedHandlerAdder = evt.Adder;
      uncheckedHandlerRemover = evt.Remover;
    }

    public void injectPhoneControlsCode(BlockStatement block) {
      this.Traverse(block);
    }

    private void injectPhoneInitializationCode(BlockStatement block, Statement statementAfter) {
      // TODO check page name against container name
      IEnumerable<ControlInfoStructure> controls = PhoneCodeHelper.instance().PhonePlugin.getControlsForPage(methodBeingTraversed.Container.ToString());
      IEnumerable<IStatement> injectedStatements = new List<IStatement>();
      if (controls != null) {
        foreach (ControlInfoStructure controlInfo in controls) {
          injectedStatements = injectedStatements.Concat(getCodeForSettingEnabledness(controlInfo));
          injectedStatements = injectedStatements.Concat(getCodeForSettingCheckedState(controlInfo));
          injectedStatements = injectedStatements.Concat(getCodeForSettingVisibility(controlInfo));
        }

        int stmtPos = block.Statements.IndexOf(statementAfter);
        block.Statements.InsertRange(stmtPos + 1, injectedStatements);
      }
    }

    private BoundExpression makeBoundControlFromControlInfo(ControlInfoStructure controlInfo) {
      return new BoundExpression() {
        Definition = new FieldDefinition() {
          ContainingTypeDefinition = methodBeingTraversed.Container,
          Name = host.NameTable.GetNameFor(controlInfo.Name),
          Type = getTypeForClassname(controlInfo.ClassName),
          IsStatic = false,
        },
        Instance = new ThisReference() { Type = methodBeingTraversed.Container },
        Type=getTypeForClassname(controlInfo.ClassName),
      };
    }

    private IEnumerable<IStatement> getCodeForSettingVisibility(ControlInfoStructure controlInfo) {
      // TODO I do not want to import System.Windows into this project...and using the underlying uint won't work for dependency properties
      /*
      IList<IStatement> code = new List<IStatement>();
      BoundExpression boundControl = makeBoundControlFromControlInfo(controlInfo);
      MethodCall setVisibilityCall= new MethodCall() {
        IsStaticCall = false,
        IsVirtualCall = true,
        IsTailCall = false,
        Type = ((Microsoft.Cci.Immutable.PlatformType) host.PlatformType).SystemVoid,
        MethodToCall = visibilitySetter,
        ThisArgument = boundControl,
      };

      ITypeReference visibilityType= ((Microsoft.Cci.Immutable.PlatformType) host.PlatformType).CreateReference(phoneSystemWindowsAssembly, "System", "Windows", "Visibility");

      switch (controlInfo.Visible) {
        case Visibility.Visible:
          setVisibilityCall.Arguments.Add(new CompileTimeConstant() {
            Type = visibilityType,
            Value = 0,
          } ); // Visible
          break;
        case Visibility.Collapsed:
          setVisibilityCall.Arguments.Add(new CompileTimeConstant() {
            Type = visibilityType,
            Value = 1,
          } ); // Collapsed
          break;
        default:
          throw new ArgumentException("Invalid visibility value for control " + controlInfo.Name + ": " + controlInfo.Visible);
      }
      
      ExpressionStatement callStmt = new ExpressionStatement() {
        Expression = setVisibilityCall,
      };
      code.Add(callStmt);
      return code;
       * */
      return new List<IStatement>();
    }

    private IEnumerable<IStatement> getCodeForSettingEnabledness(ControlInfoStructure controlInfo) {
      IList<IStatement> code = new List<IStatement>();
      BoundExpression boundControl = makeBoundControlFromControlInfo(controlInfo);
      MethodCall setEnablednessCall = new MethodCall() {
        IsStaticCall = false,
        IsVirtualCall = true,
        IsTailCall = false,
        Type = ((Microsoft.Cci.Immutable.PlatformType) host.PlatformType).SystemVoid,
        MethodToCall = isEnabledSetter,
        ThisArgument = boundControl,
      };

      setEnablednessCall.Arguments.Add(controlInfo.IsEnabled ? trueConstant : falseConstant);
      ExpressionStatement callStmt = new ExpressionStatement() {
        Expression = setEnablednessCall,
      };
      code.Add(callStmt);
      return code;
    }

    private IEnumerable<IStatement> getCodeForSettingCheckedState(ControlInfoStructure controlInfo) {
    //  IList<IStatement> code = new List<IStatement>();
    //  BoundExpression boundControl = makeBoundControlFromControlInfo(controlInfo);
    //  MethodCall setCheckStateCall= new MethodCall() {
    //    IsStaticCall = false,
    //    IsVirtualCall = true,
    //    IsTailCall = false,
    //    Type = ((Microsoft.Cci.Immutable.PlatformType) host.PlatformType).SystemVoid,
    //    MethodToCall = isCheckedSetter,
    //    ThisArgument = boundControl,
    //  };

    //  setCheckStateCall.Arguments.Add(controlInfo.IsChecked ? trueConstant : falseConstant);
    //  ExpressionStatement callStmt = new ExpressionStatement() {
    //    Expression = setCheckStateCall,
    //  };
    //  code.Add(callStmt);
    //  return code;
      return new List<IStatement>();
    }

    public override void TraverseChildren(IBlockStatement block) {
      foreach (IStatement statement in block.Statements) {
        this.Traverse(statement);
        if (initializationFound) {
          injectPhoneInitializationCode(block as BlockStatement, statement as Statement);
          initializationFound = false;
          break;
        }
      }
    }

    public override void TraverseChildren(IMethodCall methodCall) {
      if (methodCall.IsStaticCall ||
          !methodCall.MethodToCall.ContainingType.ResolvedType.Equals(methodBeingTraversed.Container) ||
          methodCall.MethodToCall.Name.Value != "InitializeComponent" ||
          methodCall.Arguments.Any())
        return;

     initializationFound= true;
    }
  }

  /// <summary>
  /// Traverse metadata looking only for PhoneApplicationPage's constructors
  /// </summary>
  public class PhoneInitializationMetadataTraverser : MetadataTraverser {
    private MetadataReaderHost host;

    public PhoneInitializationMetadataTraverser(MetadataReaderHost host)
      : base() {
        this.host = host;
    }

    public override void TraverseChildren(IModule module) {
      base.TraverseChildren(module);
    }

    public override void TraverseChildren(IAssembly assembly) {
      base.TraverseChildren(assembly);
    }

    /// <summary>
    /// Check if the type being defined is a PhoneApplicationPage, uninteresting otherwise
    /// </summary>
    /// 
    public override void TraverseChildren(ITypeDefinition typeDefinition) {
      if (typeDefinition.isPhoneApplicationClass(host)) {
        PhoneCodeHelper.instance().setMainAppTypeReference(typeDefinition);
      } else if (typeDefinition.isPhoneApplicationPageClass(host)) {
        base.TraverseChildren(typeDefinition);
      }
    }

    /// <summary>
    /// Check if it is traversing a constructor. If so, place necessary code after InitializeComponent() call
    /// </summary>
    public override void TraverseChildren(IMethodDefinition method) {
      if (!method.IsConstructor)
        return;

      PhoneInitializationCodeTraverser codeTraverser = new PhoneInitializationCodeTraverser(host, method);
      var methodBody = method.Body as SourceMethodBody;
      if (methodBody == null)
        return;
      var block = methodBody.Block as BlockStatement;
      codeTraverser.injectPhoneControlsCode(block);
    }

    public void InjectPhoneCodeAssemblies(IEnumerable<IUnit> assemblies) {
      foreach (var a in assemblies) {
        this.Traverse((IAssembly)a);
      }
    }
  }
}