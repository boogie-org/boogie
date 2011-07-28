//-----------------------------------------------------------------------------
//
// Copyright (c) Microsoft. All rights reserved.
// This code is licensed under the Microsoft Public License.
// THIS CODE IS PROVIDED *AS IS* WITHOUT WARRANTY OF
// ANY KIND, EITHER EXPRESS OR IMPLIED, INCLUDING ANY
// IMPLIED WARRANTIES OF FITNESS FOR A PARTICULAR
// PURPOSE, MERCHANTABILITY, OR NON-INFRINGEMENT.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.Serialization; // needed for defining exception .ctors
using Microsoft.Cci;
using Microsoft.Cci.MutableCodeModel;

namespace AssertionInjector {

  class Program {
    readonly static int errorValue = -1;
    static int Main(string[] args) {
      if (args == null || args.Length < 4) {
        Console.WriteLine("Usage: AssertionInjector <assembly> <filename+extension> <line number> <column number> [<outputPath>]");
        return errorValue;
      }

      var fileName = args[1];

      int lineNumber;
      if (!Int32.TryParse(args[2], out lineNumber)) {
        Console.WriteLine("Error: couldn't parse '{0}' as an integer to use as a line number", args[2]);
        return errorValue;
      }
      int columnNumber;
      if (!Int32.TryParse(args[3], out columnNumber)) {
        Console.WriteLine("Error: couldn't parse '{0}' as an integer to use as a column number", args[3]);
        return errorValue;
      }

      using (var host = new PeReader.DefaultHost()) {
        IModule/*?*/ module = host.LoadUnitFrom(args[0]) as IModule;
        if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
          Console.WriteLine(args[0] + " is not a PE file containing a CLR assembly, or an error occurred when loading it.");
          return errorValue;
        }
        module = new MetadataDeepCopier(host).Copy(module);

        var pdbFile = Path.ChangeExtension(module.Location, "pdb");
        if (!File.Exists(pdbFile)) {
          Console.WriteLine("Could not load the PDB file for '" + module.Name.Value + "' . Exiting.");
          return errorValue;
        }
        using (var pdbStream = File.OpenRead(pdbFile)) {
          if (pdbStream == null) {
            Console.WriteLine("Could not load the PDB file for '" + module.Name.Value + "' . Exiting.");
            return errorValue;
          }
          using (var pdbReader = new PdbReader(pdbStream, host)) {
            var localScopeProvider = new ILGenerator.LocalScopeProvider(pdbReader);
            var mutator = new ILMutator(host, pdbReader, fileName, lineNumber, columnNumber);
            module = mutator.Rewrite(module);

            var outputPath = (args.Length == 2) ? args[1] : module.Location + ".pe";

            var outputFileName = Path.GetFileNameWithoutExtension(outputPath);

            using (var pdbWriter = new PdbWriter(outputFileName + ".pdb", pdbReader)) {
              PeWriter.WritePeToStream(module, host, File.Create(outputPath), pdbReader, localScopeProvider, pdbWriter);
            }
          }
        }
        return 0; // success
      }
    }
  }

  /// <summary>
  /// A mutator that modifies method bodies at the IL level.
  /// It injects a call to Console.WriteLine for each store
  /// to a local for which the PDB reader is able to provide a name.
  /// This is meant to distinguish programmer-defined locals from
  /// those introduced by the compiler.
  /// </summary>
  public class ILMutator : MetadataRewriter {

    PdbReader pdbReader;
    IMethodReference contractDotAssert;
    string fileName;
    int lineNumber;
    int columnNumber;

    public ILMutator(IMetadataHost host, PdbReader pdbReader, string fileName, int lineNumber, int columnNumber)
      : base(host) {
      this.pdbReader = pdbReader;
      this.fileName = fileName;
      this.lineNumber = lineNumber;
      this.columnNumber = columnNumber;

      #region Get reference to Contract.Assert
      var platformType = host.PlatformType;
      this.contractDotAssert = new Microsoft.Cci.MethodReference(
        this.host, this.host.PlatformType.SystemDiagnosticsContractsContract,
        CallingConvention.Default,
        platformType.SystemVoid,
        host.NameTable.GetNameFor("Assert"),
        0, platformType.SystemBoolean);
      #endregion Get reference to Contract.Assert
    }

    List<ILocalDefinition> currentLocals;
    ILGenerator currentGenerator;
    IEnumerator<ILocalScope>/*?*/ scopeEnumerator;
    bool scopeEnumeratorIsValid;
    Stack<ILocalScope> scopeStack = new Stack<ILocalScope>();

    public override IMethodBody Rewrite(IMethodBody methodBody) {
      try {
        this.currentGenerator = null;
        base.Rewrite(methodBody);
        if (this.currentGenerator == null) {
          //Console.WriteLine("Not rewriting '{0}'", MemberHelper.GetMethodSignature(methodBody.MethodDefinition, NameFormattingOptions.None));
          return methodBody;
        }
        var newBody = new ILGeneratorMethodBody(this.currentGenerator, methodBody.LocalsAreZeroed, (ushort)(methodBody.MaxStack + 1),
          methodBody.MethodDefinition, this.currentLocals ?? new List<ILocalDefinition>(), Enumerable<ITypeDefinition>.Empty);
        return newBody;
      } finally {
        this.currentGenerator = null;
        this.currentLocals = null;
      }
    }

    public override void RewriteChildren(MethodBody methodBody) {
      this.currentLocals = methodBody.LocalVariables;

      try {
        var operations = methodBody.Operations;
        if (operations == null || operations.Count == 0) return;

        IPrimarySourceLocation startLocation = null;
        IPrimarySourceLocation endLocation = null;
        var ys = this.pdbReader.GetClosestPrimarySourceLocationsFor(operations[0].Location);
        foreach (var y in ys) {
          //Console.WriteLine("{0}:{1}({2},{3})", y.Document.Name.Value, MemberHelper.GetMethodSignature(methodBody.MethodDefinition, NameFormattingOptions.None),
          //  y.StartLine, y.StartColumn);
          startLocation = y;
          break;
        }

        if (startLocation == null || !startLocation.Document.Name.Value.Equals(this.fileName)) return;

        ys = this.pdbReader.GetClosestPrimarySourceLocationsFor(operations[operations.Count - 1].Location);
        foreach (var y in ys) {
          //Console.WriteLine("{0}:{1}({2},{3})", y.Document.Name.Value, MemberHelper.GetMethodSignature(methodBody.MethodDefinition, NameFormattingOptions.None),
          //  y.StartLine, y.StartColumn);
          endLocation = y;
          break;
        }

        if (endLocation == null) return;
        if (startLocation.StartLine > this.lineNumber) return;

        ProcessOperations(methodBody, operations);
      } catch (AssertionInjectorException) {
        Console.WriteLine("Internal error during IL mutation for the method '{0}'.",
          MemberHelper.GetMemberSignature(methodBody.MethodDefinition, NameFormattingOptions.SmartTypeName));
      }

    }

    private void ProcessOperations(MethodBody methodBody, List<IOperation> operations) {

      var count = operations.Count;
      ILGenerator generator = new ILGenerator(this.host, methodBody.MethodDefinition);
      if (this.pdbReader != null) {
        foreach (var ns in this.pdbReader.GetNamespaceScopes(methodBody)) {
          foreach (var uns in ns.UsedNamespaces)
            generator.UseNamespace(uns.NamespaceName.Value);
        }
      }

      this.currentGenerator = generator;
      this.scopeEnumerator = this.pdbReader == null ? null : this.pdbReader.GetLocalScopes(methodBody).GetEnumerator();
      this.scopeEnumeratorIsValid = this.scopeEnumerator != null && this.scopeEnumerator.MoveNext();

      var methodName = MemberHelper.GetMemberSignature(methodBody.MethodDefinition, NameFormattingOptions.SmartTypeName);

      #region Record all offsets that appear as part of an exception handler
      Dictionary<uint, bool> offsetsUsedInExceptionInformation = new Dictionary<uint, bool>();
      foreach (var exceptionInfo in methodBody.OperationExceptionInformation ?? Enumerable<IOperationExceptionInformation>.Empty) {
        uint x = exceptionInfo.TryStartOffset;
        if (!offsetsUsedInExceptionInformation.ContainsKey(x)) offsetsUsedInExceptionInformation.Add(x, true);
        x = exceptionInfo.TryEndOffset;
        if (!offsetsUsedInExceptionInformation.ContainsKey(x)) offsetsUsedInExceptionInformation.Add(x, true);
        x = exceptionInfo.HandlerStartOffset;
        if (!offsetsUsedInExceptionInformation.ContainsKey(x)) offsetsUsedInExceptionInformation.Add(x, true);
        x = exceptionInfo.HandlerEndOffset;
        if (!offsetsUsedInExceptionInformation.ContainsKey(x)) offsetsUsedInExceptionInformation.Add(x, true);
        if (exceptionInfo.HandlerKind == HandlerKind.Filter) {
          x = exceptionInfo.FilterDecisionStartOffset;
          if (!offsetsUsedInExceptionInformation.ContainsKey(x)) offsetsUsedInExceptionInformation.Add(x, true);
        }
      }
      #endregion Record all offsets that appear as part of an exception handler

      Dictionary<uint, ILGeneratorLabel> offset2Label = new Dictionary<uint, ILGeneratorLabel>();
      #region Pass 1: Make a label for each branch target
      for (int i = 0; i < count; i++) {
        IOperation op = operations[i];
        switch (op.OperationCode) {
          case OperationCode.Beq:
          case OperationCode.Bge:
          case OperationCode.Bge_Un:
          case OperationCode.Bgt:
          case OperationCode.Bgt_Un:
          case OperationCode.Ble:
          case OperationCode.Ble_Un:
          case OperationCode.Blt:
          case OperationCode.Blt_Un:
          case OperationCode.Bne_Un:
          case OperationCode.Br:
          case OperationCode.Brfalse:
          case OperationCode.Brtrue:
          case OperationCode.Leave:
          case OperationCode.Beq_S:
          case OperationCode.Bge_S:
          case OperationCode.Bge_Un_S:
          case OperationCode.Bgt_S:
          case OperationCode.Bgt_Un_S:
          case OperationCode.Ble_S:
          case OperationCode.Ble_Un_S:
          case OperationCode.Blt_S:
          case OperationCode.Blt_Un_S:
          case OperationCode.Bne_Un_S:
          case OperationCode.Br_S:
          case OperationCode.Brfalse_S:
          case OperationCode.Brtrue_S:
          case OperationCode.Leave_S:
            uint x = (uint)op.Value;
            if (!offset2Label.ContainsKey(x))
              offset2Label.Add(x, new ILGeneratorLabel());
            break;
          case OperationCode.Switch:
            uint[] offsets = op.Value as uint[];
            foreach (var offset in offsets) {
              if (!offset2Label.ContainsKey(offset))
                offset2Label.Add(offset, new ILGeneratorLabel());
            }
            break;
          default:
            break;
        }
      }
      #endregion Pass 1: Make a label for each branch target

      #region Pass 2: Emit each operation, along with labels
      bool emittedProbe = false; // don't do it more than once
      for (int i = 0; i < count; i++) {
        IOperation op = operations[i];
        ILGeneratorLabel label;
        this.EmitDebugInformationFor(op);
        #region Mark operation if it is a label for a branch
        if (offset2Label.TryGetValue(op.Offset, out label)) {
          generator.MarkLabel(label);
        }
        #endregion Mark operation if it is a label for a branch

        #region Mark operation if it is pointed to by an exception handler
        bool ignore;
        uint offset = op.Offset;
        if (offsetsUsedInExceptionInformation.TryGetValue(offset, out ignore)) {
          foreach (var exceptionInfo in methodBody.OperationExceptionInformation) {
            if (offset == exceptionInfo.TryStartOffset)
              generator.BeginTryBody();

            // Never need to do anthing when offset == exceptionInfo.TryEndOffset because
            // we pick up an EndTryBody from the HandlerEndOffset below
            //  generator.EndTryBody();

            if (offset == exceptionInfo.HandlerStartOffset) {
              switch (exceptionInfo.HandlerKind) {
                case HandlerKind.Catch:
                  generator.BeginCatchBlock(exceptionInfo.ExceptionType);
                  break;
                case HandlerKind.Fault:
                  generator.BeginFaultBlock();
                  break;
                case HandlerKind.Filter:
                  generator.BeginFilterBody();
                  break;
                case HandlerKind.Finally:
                  generator.BeginFinallyBlock();
                  break;
              }
            }
            if (exceptionInfo.HandlerKind == HandlerKind.Filter && offset == exceptionInfo.FilterDecisionStartOffset) {
              generator.BeginFilterBlock();
            }
            if (offset == exceptionInfo.HandlerEndOffset)
              generator.EndTryBody();
          }
        }
        #endregion Mark operation if it is pointed to by an exception handler

        #region Emit operation along with any injection

        if (!emittedProbe) {
          IPrimarySourceLocation location = null;
          var locations = this.pdbReader.GetPrimarySourceLocationsFor(op.Location);
          foreach (var x in locations) {
            if (this.lineNumber <= x.StartLine) {
              location = x;
              break;
            }
          }
          if (location != null) {
            emittedProbe = true;
            generator.Emit(OperationCode.Ldc_I4_0);
            generator.Emit(OperationCode.Call, this.contractDotAssert);
          }
        }

        switch (op.OperationCode) {
          #region Branches
          case OperationCode.Beq:
          case OperationCode.Bge:
          case OperationCode.Bge_Un:
          case OperationCode.Bgt:
          case OperationCode.Bgt_Un:
          case OperationCode.Ble:
          case OperationCode.Ble_Un:
          case OperationCode.Blt:
          case OperationCode.Blt_Un:
          case OperationCode.Bne_Un:
          case OperationCode.Br:
          case OperationCode.Brfalse:
          case OperationCode.Brtrue:
          case OperationCode.Leave:
          case OperationCode.Beq_S:
          case OperationCode.Bge_S:
          case OperationCode.Bge_Un_S:
          case OperationCode.Bgt_S:
          case OperationCode.Bgt_Un_S:
          case OperationCode.Ble_S:
          case OperationCode.Ble_Un_S:
          case OperationCode.Blt_S:
          case OperationCode.Blt_Un_S:
          case OperationCode.Bne_Un_S:
          case OperationCode.Br_S:
          case OperationCode.Brfalse_S:
          case OperationCode.Brtrue_S:
          case OperationCode.Leave_S:
            generator.Emit(ILGenerator.LongVersionOf(op.OperationCode), offset2Label[(uint)op.Value]);
            break;
          case OperationCode.Switch:
            uint[] offsets = op.Value as uint[];
            ILGeneratorLabel[] labels = new ILGeneratorLabel[offsets.Length];
            for (int j = 0, n = offsets.Length; j < n; j++) {
              labels[j] = offset2Label[offsets[j]];
            }
            generator.Emit(OperationCode.Switch, labels);
            break;
          #endregion Branches
          #region Everything else
          //case OperationCode.Stloc:
          //case OperationCode.Stloc_0:
          //case OperationCode.Stloc_1:
          //case OperationCode.Stloc_2:
          //case OperationCode.Stloc_3:
          //case OperationCode.Stloc_S:
          //  EmitStoreLocal(generator, op);
          //  break;
          default:
            if (op.Value == null) {
              generator.Emit(op.OperationCode);
              break;
            }
            var typeCode = System.Convert.GetTypeCode(op.Value);
            switch (typeCode) {
              case TypeCode.Byte:
                generator.Emit(op.OperationCode, (byte)op.Value);
                break;
              case TypeCode.Double:
                generator.Emit(op.OperationCode, (double)op.Value);
                break;
              case TypeCode.Int16:
                generator.Emit(op.OperationCode, (short)op.Value);
                break;
              case TypeCode.Int32:
                generator.Emit(op.OperationCode, (int)op.Value);
                break;
              case TypeCode.Int64:
                generator.Emit(op.OperationCode, (long)op.Value);
                break;
              case TypeCode.Object:
                IFieldReference fieldReference = op.Value as IFieldReference;
                if (fieldReference != null) {
                  generator.Emit(op.OperationCode, this.Rewrite(fieldReference));
                  break;
                }
                ILocalDefinition localDefinition = op.Value as ILocalDefinition;
                if (localDefinition != null) {
                  generator.Emit(op.OperationCode, localDefinition);
                  break;
                }
                IMethodReference methodReference = op.Value as IMethodReference;
                if (methodReference != null) {
                  generator.Emit(op.OperationCode, this.Rewrite(methodReference));
                  break;
                }
                IParameterDefinition parameterDefinition = op.Value as IParameterDefinition;
                if (parameterDefinition != null) {
                  generator.Emit(op.OperationCode, parameterDefinition);
                  break;
                }
                ISignature signature = op.Value as ISignature;
                if (signature != null) {
                  generator.Emit(op.OperationCode, signature);
                  break;
                }
                ITypeReference typeReference = op.Value as ITypeReference;
                if (typeReference != null) {
                  generator.Emit(op.OperationCode, this.Rewrite(typeReference));
                  break;
                }
                throw new AssertionInjectorException("Should never get here: no other IOperation argument types should exist");
              case TypeCode.SByte:
                generator.Emit(op.OperationCode, (sbyte)op.Value);
                break;
              case TypeCode.Single:
                generator.Emit(op.OperationCode, (float)op.Value);
                break;
              case TypeCode.String:
                generator.Emit(op.OperationCode, (string)op.Value);
                break;
              default:
                // The other cases are the other enum values that TypeCode has.
                // But no other argument types should be in the Operations. ILGenerator cannot handle anything else,
                // so such IOperations should never exist.
                //case TypeCode.Boolean:
                //case TypeCode.Char:
                //case TypeCode.DateTime:
                //case TypeCode.DBNull:
                //case TypeCode.Decimal:
                //case TypeCode.Empty: // this would be the value for null, but the case when op.Value is null is handled before the switch statement
                //case TypeCode.UInt16:
                //case TypeCode.UInt32:
                //case TypeCode.UInt64:
                throw new AssertionInjectorException("Should never get here: no other IOperation argument types should exist");
            }
            break;
          #endregion Everything else
        }
        #endregion Emit operation along with any injection

      }
      while (generator.InTryBody)
        generator.EndTryBody();
      while (this.scopeStack.Count > 0) {
        this.currentGenerator.EndScope();
        this.scopeStack.Pop();
      }
      #endregion Pass 2: Emit each operation, along with labels

    }

    private void EmitDebugInformationFor(IOperation operation) {
      this.currentGenerator.MarkSequencePoint(operation.Location);
      if (this.scopeEnumerator == null) return;
      ILocalScope/*?*/ currentScope = null;
      while (this.scopeStack.Count > 0) {
        currentScope = this.scopeStack.Peek();
        if (operation.Offset < currentScope.Offset + currentScope.Length) break;
        this.scopeStack.Pop();
        this.currentGenerator.EndScope();
        currentScope = null;
      }
      while (this.scopeEnumeratorIsValid) {
        currentScope = this.scopeEnumerator.Current;
        if (currentScope.Offset <= operation.Offset && operation.Offset < currentScope.Offset + currentScope.Length) {
          this.scopeStack.Push(currentScope);
          this.currentGenerator.BeginScope();
          foreach (var local in this.pdbReader.GetVariablesInScope(currentScope))
            this.currentGenerator.AddVariableToCurrentScope(local);
          foreach (var constant in this.pdbReader.GetConstantsInScope(currentScope))
            this.currentGenerator.AddConstantToCurrentScope(constant);
          this.scopeEnumeratorIsValid = this.scopeEnumerator.MoveNext();
        } else
          break;
      }
    }

    private void EmitStoreLocal(ILGenerator generator, IOperation op) {

      #region Emit: call Console.WriteLine("foo");
      //generator.Emit(OperationCode.Ldstr, "foo");
      //generator.Emit(OperationCode.Call, this.consoleDotWriteLine);
      #endregion Emit: call Console.WriteLine("foo");

      string localName;
      switch (op.OperationCode) {
        case OperationCode.Stloc:
        case OperationCode.Stloc_S:
          ILocalDefinition loc = op.Value as ILocalDefinition;
          if (loc == null) throw new AssertionInjectorException("Stloc operation found without a valid operand");
          if (TryGetLocalName(loc, out localName)) {
            generator.Emit(OperationCode.Ldstr, localName);
            generator.Emit(OperationCode.Call, this.contractDotAssert);
          }
          generator.Emit(op.OperationCode, loc);
          break;

        case OperationCode.Stloc_0:
          if (this.currentLocals.Count < 1)
            throw new AssertionInjectorException("stloc.0 operation found but no corresponding local in method body");
          if (TryGetLocalName(this.currentLocals[0], out localName)) {
            generator.Emit(OperationCode.Ldstr, localName);
            generator.Emit(OperationCode.Call, this.contractDotAssert);
          }
          generator.Emit(op.OperationCode);
          break;

        case OperationCode.Stloc_1:
          if (this.currentLocals.Count < 2)
            throw new AssertionInjectorException("stloc.1 operation found but no corresponding local in method body");
          if (TryGetLocalName(this.currentLocals[1], out localName)) {
            generator.Emit(OperationCode.Ldstr, localName);
            generator.Emit(OperationCode.Call, this.contractDotAssert);
          }
          generator.Emit(op.OperationCode);
          break;

        case OperationCode.Stloc_2:
          if (this.currentLocals.Count < 3)
            throw new AssertionInjectorException("stloc.2 operation found but no corresponding local in method body");
          if (TryGetLocalName(this.currentLocals[2], out localName)) {
            generator.Emit(OperationCode.Ldstr, localName);
            generator.Emit(OperationCode.Call, this.contractDotAssert);
          }
          generator.Emit(op.OperationCode);
          break;

        case OperationCode.Stloc_3:
          if (this.currentLocals.Count < 4)
            throw new AssertionInjectorException("stloc.3 operation found but no corresponding local in method body");
          if (TryGetLocalName(this.currentLocals[3], out localName)) {
            generator.Emit(OperationCode.Ldstr, localName);
            generator.Emit(OperationCode.Call, this.contractDotAssert);
          }
          generator.Emit(op.OperationCode);
          break;

        default:
          throw new AssertionInjectorException("Should never get here: switch statement was meant to be exhaustive");
      }
    }

    private bool TryGetLocalName(ILocalDefinition local, out string localNameFromPDB) {
      string localName = local.Name.Value;
      localNameFromPDB = null;
      if (this.pdbReader != null) {
        foreach (IPrimarySourceLocation psloc in this.pdbReader.GetPrimarySourceLocationsForDefinitionOf(local)) {
          if (psloc.Source.Length > 0) {
            localNameFromPDB = psloc.Source;
            break;
          }
        }
      }
      return localNameFromPDB != null;
    }

    /// <summary>
    /// Exceptions thrown during extraction. Should not escape this class.
    /// </summary>
    private class AssertionInjectorException : Exception {
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public AssertionInjectorException() { }
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public AssertionInjectorException(string s) : base(s) { }
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public AssertionInjectorException(string s, Exception inner) : base(s, inner) { }
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public AssertionInjectorException(SerializationInfo info, StreamingContext context) : base(info, context) { }
    }
  }

}
