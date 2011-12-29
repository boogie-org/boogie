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
using Bpl = Microsoft.Boogie;
using System.Diagnostics;

namespace AssertionInjector {

  class Program {
    const int errorValue = -1;
    static int Main(string[] args) {
      if (args == null || args.Length < 4) {
        Console.WriteLine("Usage: AssertionInjector <assembly> <filename+extension> <line number> <column number> [<outputPath>]");
        return errorValue;
      }

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

      if (args[0].EndsWith(".bpl"))
        return InjectAssertionInBpl(args[0], args[1], lineNumber, columnNumber);
      else
        return InjectAssertionInAssembly(args[0], args[1], lineNumber, columnNumber);
    }

    static int InjectAssertionInBpl(string bplFileName, string fileName, int lineNumber, int columnNumber) {
      Bpl.CommandLineOptions.Install(new Bpl.CommandLineOptions());
      Bpl.CommandLineOptions.Clo.DoModSetAnalysis = true;
      var returnValue = errorValue; 
      Bpl.Program program;
      Bpl.Parser.Parse(bplFileName, new List<string>(), out program);
      int errorCount = program.Resolve();
      if (errorCount != 0) {
        Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, bplFileName);
        return returnValue;
      }
      errorCount = program.Typecheck();
      if (errorCount != 0) {
        Console.WriteLine("{0} type checking errors detected in {1}", errorCount, bplFileName);
        return returnValue;
      }

      GetMeHereBplInjector bplInjector = new GetMeHereBplInjector(fileName, lineNumber, columnNumber);
      bplInjector.Visit(program);
      using (Bpl.TokenTextWriter writer = new Bpl.TokenTextWriter(bplFileName)) {
        Bpl.CommandLineOptions.Clo.PrintInstrumented = true;
        program.Emit(writer);
      }
      return returnValue;
    }

    static int InjectAssertionInAssembly(string assemblyName, string fileName, int lineNumber, int columnNumber) {
      string originalAssemblyPath;
      string outputAssemblyPath;
      string outputPdbFileName;

      var returnValue = errorValue;

      using (var host = new PeReader.DefaultHost()) {
        IModule/*?*/ module = host.LoadUnitFrom(assemblyName) as IModule;
        if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
          Console.WriteLine(assemblyName + " is not a PE file containing a CLR assembly, or an error occurred when loading it.");
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
            var mutator = new GetMeHereAssemblyInjector(host, pdbReader, fileName, lineNumber, columnNumber);
            module = mutator.Rewrite(module);
            //Console.WriteLine("Emitted probe: {0}", mutator.emittedProbe);
            if (mutator.emittedProbe) returnValue = 0;

            originalAssemblyPath = module.Location;
            var tempDir = Path.GetTempPath();
            outputAssemblyPath = Path.Combine(tempDir, Path.GetFileName(originalAssemblyPath));
            outputPdbFileName = Path.ChangeExtension(outputAssemblyPath, "pdb");

            using (var outputStream = File.Create(outputAssemblyPath)) {
              using (var pdbWriter = new PdbWriter(outputPdbFileName, pdbReader)) {
                PeWriter.WritePeToStream(module, host, outputStream, pdbReader, localScopeProvider, pdbWriter);
              }
            }
          }
        }
      }

      try {
        File.Copy(outputAssemblyPath, originalAssemblyPath, true);
        File.Delete(outputAssemblyPath);
        var originalPdbPath = Path.ChangeExtension(originalAssemblyPath, "pdb");
        var outputPdbPath = Path.Combine(Path.GetDirectoryName(outputAssemblyPath), outputPdbFileName);
        File.Copy(outputPdbPath, originalPdbPath, true);
        File.Delete(outputPdbPath);
      }
      catch (Exception e) {
        Console.WriteLine("Something went wrong with replacing input assembly/pdb");
        Console.WriteLine(e.Message);
        return errorValue;
      }

      return returnValue; // success
    }
  }

  public class GetMeHereBplInjector : Bpl.StandardVisitor {
    string fileName;
    int lineNumber;
    int columnNumber;

    public GetMeHereBplInjector(string fileName, int lineNumber, int columnNumber) {
      this.fileName = fileName;
      this.lineNumber = lineNumber;
      this.columnNumber = columnNumber;
    }

    public override Bpl.CmdSeq VisitCmdSeq(Bpl.CmdSeq cmdSeq) {
      Bpl.CmdSeq newCmdSeq = new Bpl.CmdSeq();
      for (int i = 0; i < cmdSeq.Length; i++) {
        Bpl.Cmd cmd = cmdSeq[i];
        if (IsRelevant(cmd))
          newCmdSeq.Add(new Bpl.AssertCmd(cmd.tok, Bpl.Expr.False));
        newCmdSeq.Add(cmd);
      }
      return newCmdSeq;
    }

    private bool IsRelevant(Bpl.Cmd cmd) {
      Bpl.AssertCmd assertCmd = cmd as Bpl.AssertCmd;
      if (assertCmd == null)
        return false;
      string sourceFile = Bpl.QKeyValue.FindStringAttribute(assertCmd.Attributes, "sourceFile");
      if (sourceFile == null)
        return false;
      string[] ds = sourceFile.Split('\\');
      if (sourceFile != fileName && ds[ds.Length - 1] != fileName)
        return false;
      int sourceLine = Bpl.QKeyValue.FindIntAttribute(assertCmd.Attributes, "sourceLine", -1);
      Debug.Assert(sourceLine != -1);
      if (sourceLine != lineNumber)
        return false;
      return true;
    }
  }

  /// <summary>
  /// A mutator that modifies method bodies at the IL level.
  /// It injects a call to GetMeHere.GetMeHere.Assert at the
  /// specified source location.
  /// The class GetMeHere is synthesized and injected into the
  /// rewritten assembly.
  /// </summary>
  public class GetMeHereAssemblyInjector : MetadataRewriter {
    PdbReader pdbReader;
    string fileName;
    int lineNumber;
    int columnNumber;

    public GetMeHereAssemblyInjector(IMetadataHost host, PdbReader pdbReader, string fileName, int lineNumber, int columnNumber)
      : base(host) {
      this.pdbReader = pdbReader;
      this.fileName = fileName;
      this.lineNumber = lineNumber;
      this.columnNumber = columnNumber;
    }

    List<ILocalDefinition> currentLocals;
    ILGenerator currentGenerator;
    IEnumerator<ILocalScope>/*?*/ scopeEnumerator;
    bool scopeEnumeratorIsValid;
    Stack<ILocalScope> scopeStack = new Stack<ILocalScope>();
    private NamespaceTypeDefinition getMeHereClass;
    private MethodDefinition getMeHereAssert;
    public bool emittedProbe;

    public override void RewriteChildren(Module module) {
      base.RewriteChildren(module);
      module.AllTypes.Add(this.getMeHereClass);
    }

    public override void RewriteChildren(RootUnitNamespace rootUnitNamespace) {
      var ns = this.CreateGetMeHere(rootUnitNamespace); // side effect: sets fields
      rootUnitNamespace.Members.Add(ns);
      base.RewriteChildren(rootUnitNamespace);
    }

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
      //Console.WriteLine("{0}", MemberHelper.GetMethodSignature(methodBody.MethodDefinition));
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

        if (startLocation == null || startLocation.StartLine == 0x00feefee || !startLocation.Document.Name.Value.Equals(this.fileName)) return;

        var lastIndex = operations.Count;
        do {
          lastIndex--;
          ys = this.pdbReader.GetClosestPrimarySourceLocationsFor(operations[lastIndex].Location);
          foreach (var y in ys) {
            //Console.WriteLine("{0}:{1}({2},{3})", y.Document.Name.Value, MemberHelper.GetMethodSignature(methodBody.MethodDefinition, NameFormattingOptions.None),
            //  y.StartLine, y.StartColumn);
            endLocation = y;
            break;
          }
        } while (0 <= lastIndex && (endLocation == null || endLocation.StartLine == 0x00feefee));
        if (lastIndex == -1 || !(startLocation.StartLine <= this.lineNumber && this.lineNumber <= endLocation.StartLine)) return;


        ProcessOperations(methodBody, operations);
      } catch (GetMeHereInjectorException) {
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
      this.emittedProbe = false; // don't do it more than once
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

        if (!this.emittedProbe) {
          IPrimarySourceLocation location = null;
          var locations = this.pdbReader.GetPrimarySourceLocationsFor(op.Location);
          foreach (var x in locations) {
            if (x.StartLine != 0x00feefee && this.lineNumber <= x.StartLine) {
              location = x;
              break;
            }
          }
          if (location != null) {
            this.emittedProbe = true;
            generator.Emit(OperationCode.Ldc_I4_0);
            generator.Emit(OperationCode.Call, this.getMeHereAssert);
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
                throw new GetMeHereInjectorException("Should never get here: no other IOperation argument types should exist");
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
                throw new GetMeHereInjectorException("Should never get here: no other IOperation argument types should exist");
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

    private NestedUnitNamespace CreateGetMeHere(IUnitNamespace unitNamespace) {

      var voidType = this.host.PlatformType.SystemVoid;

      #region Create class

      Microsoft.Cci.MethodReference compilerGeneratedCtor =
        new Microsoft.Cci.MethodReference(
          this.host,
          this.host.PlatformType.SystemRuntimeCompilerServicesCompilerGeneratedAttribute,
          CallingConvention.HasThis,
          voidType,
          this.host.NameTable.Ctor,
          0);
      CustomAttribute compilerGeneratedAttribute = new CustomAttribute();
      compilerGeneratedAttribute.Constructor = compilerGeneratedCtor;

      var getMeHereNamespace = new NestedUnitNamespace() {
        ContainingUnitNamespace = unitNamespace,
        Name = this.host.NameTable.GetNameFor("GetMeHere"),
      };
      this.getMeHereClass = new NamespaceTypeDefinition() {
        // NB: The string name must be kept in sync with the code that recognizes GMH methods!!
        Attributes = new List<ICustomAttribute>(){compilerGeneratedAttribute},
        BaseClasses = new List<ITypeReference>(){this.host.PlatformType.SystemObject},
        ContainingUnitNamespace = getMeHereNamespace,
        InternFactory = this.host.InternFactory,
        IsBeforeFieldInit = true,
        IsClass = true,
        IsSealed = true,
        Layout = LayoutKind.Auto,
        Name = this.host.NameTable.GetNameFor("GetMeHere"),
        StringFormat = StringFormatKind.Ansi,
      };
      #endregion

      #region Create methods
      var body = new MethodBody() {
        Operations = new List<IOperation>(){new Operation() { OperationCode = OperationCode.Ret, }},
      };

      this.getMeHereAssert = new MethodDefinition() {
        Body = body,
        CallingConvention = CallingConvention.Default, // Isn't it the default for the calling convention to be the default?
        ContainingTypeDefinition = getMeHereClass,
        IsStatic = true,
        InternFactory = this.host.InternFactory,
        Name = this.host.NameTable.GetNameFor("Assert"),
        Type = voidType,
        Visibility = TypeMemberVisibility.Public,
      };
      var paramList = new List<IParameterDefinition>();
      paramList.Add(
        new ParameterDefinition() {
          ContainingSignature = getMeHereAssert,
          Name = this.host.NameTable.GetNameFor("condition"),
          Type = this.host.PlatformType.SystemBoolean,
          Index = 0,
        });
      getMeHereAssert.Parameters = paramList;
      body.MethodDefinition = getMeHereAssert;
      getMeHereClass.Methods = new List<IMethodDefinition> { getMeHereAssert };
      #endregion

      return getMeHereNamespace;
    }

    /// <summary>
    /// Exceptions thrown during extraction. Should not escape this class.
    /// </summary>
    private class GetMeHereInjectorException : Exception {
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public GetMeHereInjectorException() { }
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public GetMeHereInjectorException(string s) : base(s) { }
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public GetMeHereInjectorException(string s, Exception inner) : base(s, inner) { }
      /// <summary>
      /// Exception specific to an error occurring in the contract extractor
      /// </summary>
      public GetMeHereInjectorException(SerializationInfo info, StreamingContext context) : base(info, context) { }
    }
  }

}
