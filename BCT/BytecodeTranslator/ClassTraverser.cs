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

namespace BytecodeTranslator {
  /// <summary>
  /// 
  /// </summary>
  public class ClassTraverser : BaseCodeAndContractTraverser {

    public readonly TraverserFactory factory;

    public readonly ToplevelTraverser ToplevelTraverser;

    private Dictionary<IFieldDefinition, Bpl.GlobalVariable> fieldVarMap = new Dictionary<IFieldDefinition, Microsoft.Boogie.GlobalVariable>();

    private Dictionary<IMethodDefinition, MethodTraverser> methodMap = new Dictionary<IMethodDefinition, MethodTraverser>();

    // TODO: (mschaef) just a stub
    public readonly Bpl.Variable ThisVariable = TranslationHelper.TempThisVar();

    public readonly Bpl.Variable HeapVariable = TranslationHelper.TempHeapVar();

    public ClassTraverser(TraverserFactory factory, IContractProvider cp, ToplevelTraverser tlTraverser)
      : base(cp) {
      this.factory = factory;
      ToplevelTraverser = tlTraverser;
    }

    public Bpl.Variable FindOrCreateFieldVariable(IFieldDefinition field) {
      Bpl.GlobalVariable v;
      if (!fieldVarMap.TryGetValue(field, out v)) {
        string fieldname = field.ContainingTypeDefinition.ToString() + "." + field.Name.Value;
        Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(field.Locations);
        Bpl.Type t = TranslationHelper.CciTypeToBoogie(field.Type.ResolvedType);
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, fieldname, t);

        v = new Bpl.GlobalVariable(tok,tident);
        fieldVarMap.Add(field, v);
        ToplevelTraverser.TranslatedProgram.TopLevelDeclarations.Add(new Bpl.Constant(tok, tident, true));
      }
      return v;
    }


    /// <summary>
    /// 
    /// </summary>
    /// <param name="method"></param>
    public override void Visit(IMethodDefinition method) {
      // check if it's static and so on
      MethodTraverser mt;
      if (!methodMap.TryGetValue(method, out mt)) {
        mt = this.factory.MakeMethodTraverser(this, this.contractProvider);
        this.methodMap.Add(method, mt);
      }
      mt.Visit(method);
    }

    public override void Visit(IFieldDefinition fieldDefinition) {
      this.FindOrCreateFieldVariable(fieldDefinition);
    }

    public override void Visit(ITypeInvariant typeInvariant) {
      // Todo: Not implemented
      base.Visit(typeInvariant);
    }

  }

}
