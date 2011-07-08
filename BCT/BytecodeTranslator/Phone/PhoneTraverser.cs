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
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;


namespace BytecodeTranslator {

  /// <summary>
  /// Traverse code looking for phone specific points of interest, possibly injecting necessary code in-between
  /// </summary>

  public class PhoneCodeTraverser : BaseCodeTraverser {
    private readonly IMethodDefinition methodBeingTraversed;
    private static bool initializationEncountered;

    public PhoneCodeTraverser(IMethodDefinition traversedMethod) : base() {
      this.methodBeingTraversed = traversedMethod;
    }

    public void injectPhoneControlsCode(BlockStatement block) {
      this.Visit(block);
    }

    private void injectPhoneInitializationCode(IBlockStatement block, IStatement statementAfter) {
    }

    public override void Visit(IBlockStatement block) {
      initializationEncountered = false;
      foreach (IStatement statement in block.Statements) {
        this.Visit(statement);
        if (initializationEncountered) {
          injectPhoneInitializationCode(block, statement);
          break;
        }
      }
    }

    public override void Visit(IMethodCall methodCall) {
      if (methodCall.IsStaticCall ||
          !methodCall.MethodToCall.ContainingType.ResolvedType.Equals(methodBeingTraversed.Container) ||
          methodCall.MethodToCall.Name.Value != "InitializeComponent" ||
          methodCall.Arguments.Any())
        return;

      // otherwise we need to insert the desired code after this call
      // TODO make sure I am dealing with the MUTABLE code model
    }
  }

  /// <summary>
  /// Traverse metadata looking only for PhoneApplicationPage's constructors
  /// </summary>
  public class PhoneMetadataTraverser : BaseMetadataTraverser {

    public PhoneMetadataTraverser()
      : base() {
    }

    public override void Visit(IModule module) {
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      base.Visit(assembly);
    }

    /// <summary>
    /// Check if the type being defined is a PhoneApplicationPage, uninteresting otherwise
    /// </summary>
    /// 
    public override void Visit(ITypeDefinition typeDefinition) {
      if (typeDefinition.IsClass && isPhoneApplicationPage(typeDefinition)) {
        base.Visit(typeDefinition);
      }
    }

    private bool isPhoneApplicationPage(ITypeDefinition typeDefinition) {
      ITypeReference baseClass = typeDefinition.BaseClasses.FirstOrDefault();
      ITypeDefinition baseClassDef;
      while (baseClass != null) {
        baseClassDef = baseClass.ResolvedType;
        if (baseClassDef is INamespaceTypeDefinition) {
          if (((INamespaceTypeDefinition) baseClassDef).Name.Value == "PhoneApplicationPage" &&
               ((INamespaceTypeDefinition) baseClassDef).Container.ToString() == "Microsoft.Phone.Controls") {
            return true;
          }
        }
        baseClass = baseClass.ResolvedType.BaseClasses.FirstOrDefault();
      }

      return false;
    }

    /// <summary>
    /// Check if it is traversing a constructor. If so, place necessary code after InitializeComponent() call
    /// </summary>
    public override void Visit(IMethodDefinition method) {
      if (!method.IsConstructor)
        return;

      PhoneCodeTraverser codeTraverser = new PhoneCodeTraverser(method);
      var methodBody = method.Body as ISourceMethodBody;
      if (methodBody == null)
        return;
      var block = methodBody.Block as BlockStatement;
      codeTraverser.injectPhoneControlsCode(block);
    }

    public virtual void InjectPhoneCodeAssemblies(IEnumerable<IUnit> assemblies) {
      foreach (var a in assemblies) {
        a.Dispatch(this);
      }
    }
  }
}