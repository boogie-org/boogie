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
  internal class ToplevelTraverser : BaseCodeAndContractTraverser {

    public readonly IContractProvider ContractProvider;

    public readonly Bpl.Program TranslatedProgram;

    private Dictionary<ITypeDefinition, ClassTraverser> classMap = new Dictionary<ITypeDefinition, ClassTraverser>();

    public ToplevelTraverser(IContractProvider cp)
      : base(cp) {
      ContractProvider = cp;
      TranslatedProgram = new Bpl.Program();
    }

    public Bpl.Variable FindOrCreateClassField(ITypeDefinition classtype, IFieldDefinition field) {
      ClassTraverser ct;
      if (!classMap.TryGetValue(classtype, out ct)) {
        ct = new ClassTraverser(this.ContractProvider, this);
        classMap.Add(classtype, ct);
        return ct.FindOrCreateFieldVariable(field);
      } else {
        return ct.FindOrCreateFieldVariable(field);
      }
    }


    /// <summary>
    /// 
    /// </summary>
    /// <param name="typeDefinition"></param>
    public override void Visit(ITypeDefinition typeDefinition) {
      if (typeDefinition.IsClass) {

        ClassTraverser ct;
        if (!classMap.TryGetValue(typeDefinition, out ct)) { 
          ct = new ClassTraverser(this.contractProvider, this);
          classMap.Add(typeDefinition, ct);
        }
        ct.Visit(typeDefinition);
      } else {
        Console.WriteLine("Non-Class {0} was found", typeDefinition);
        throw new NotImplementedException(String.Format("Non-Class Type {0} is not yet supported.", typeDefinition.ToString()));
      }
    }

    public override void Visit(IModule module) {
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      base.Visit(assembly);
    }

  }
}
