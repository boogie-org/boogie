//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.IO;
using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using System.Collections.Generic;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;
using Microsoft.Cci.MutableContracts;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;
using Microsoft.Cci.MutableCodeModel.Contracts;
using TranslationPlugins;
using BytecodeTranslator.Phone;
using System.Text.RegularExpressions;

namespace BytecodeTranslator {

  public class Options : OptionParsing {

    [OptionDescription("The names of the assemblies to use as input", ShortForm = "a")]
    public List<string> assemblies = null;

    [OptionDescription("Break into debugger", ShortForm = "break")]
    public bool breakIntoDebugger = false;

    [OptionDescription("Emit a 'capture state' directive after each statement, (default: false)", ShortForm = "c")]
    public bool captureState = false;

    [OptionDescription("Translation should be done for Get Me Here functionality, (default: false)", ShortForm = "gmh")]
    public bool getMeHere = false;

    [OptionDescription("Search paths for assembly dependencies.", ShortForm = "lib")]
    public List<string> libpaths = new List<string>();

    public enum HeapRepresentation { splitFields, twoDInt, twoDBox, general }
    [OptionDescription("Heap representation to use", ShortForm = "heap")]
    public HeapRepresentation heapRepresentation = HeapRepresentation.general;

    [OptionDescription("Translate using whole-program assumptions", ShortForm = "whole")]
    public bool wholeProgram = false;

    [OptionDescription("Stub assembly", ShortForm = "s")]
    public List<string>/*?*/ stub = null;

    [OptionDescription("Phone translation controls configuration")]
    public string phoneControls = null;

    [OptionDescription("Add phone navigation code on translation. Requires /phoneControls. Default false", ShortForm = "wpnav")]
    public bool phoneNavigationCode= false;

    [OptionDescription("Add phone feedback code on translation. Requires /phoneControls. Default false", ShortForm = "wpfb")]
    public bool phoneFeedbackCode = false;

    [OptionDescription("File containing white/black list (optionally end file name with + for white list, - for black list, default is white list", ShortForm = "exempt")]
    public string exemptionFile = "";

  }

  public class BCT {

    public static IMetadataHost Host;

    static int Main(string[] args)
    {
      int result = 0;
      int errorReturnValue = -1;

      #region Parse options and check for errors
      var options = new Options();
      options.Parse(args);
      if (options.HelpRequested) {
        options.PrintOptions("");
        return errorReturnValue;
      }
      if (options.HasErrors) {
        options.PrintErrorsAndExit(Console.Out);
      }
      if (!String.IsNullOrWhiteSpace(options.exemptionFile)) {
        string fileName = options.exemptionFile;
        var c = fileName[fileName.Length - 1];
        if (c == '+' || c == '-') fileName = options.exemptionFile.Remove(fileName.Length - 1);
        if (!File.Exists(fileName)) {
          Console.WriteLine("Specified exemption file '{0}' not found.", fileName);
        }
      }

      if (options.breakIntoDebugger) {
        System.Diagnostics.Debugger.Break();
      }

      #endregion

      var assemblyNames = options.assemblies;
      if (assemblyNames == null || assemblyNames.Count == 0) {
        assemblyNames = new List<string>();
        foreach (var g in options.GeneralArguments) {
          assemblyNames.Add(g);
        }
      }

      #region If an exclusion file has been specified, read in each line as a regular expression
      List<Regex> exemptionList = null;
      bool whiteList = false;
      if (!String.IsNullOrWhiteSpace(options.exemptionFile)) {
        int i = 0;
        exemptionList = new List<Regex>();
        string fileName = options.exemptionFile;
        var c = fileName[fileName.Length - 1];
        whiteList = true;
        if (c == '+' || c == '-') {
          fileName = options.exemptionFile.Remove(fileName.Length - 1);
          if (c == '-') whiteList = false;
        }
        try {
          // Create an instance of StreamReader to read from a file.
          // The using statement also closes the StreamReader.
          using (StreamReader sr = new StreamReader(fileName)) {
            String line;
            // Read and display lines from the file until the end of 
            // the file is reached.
            while ((line = sr.ReadLine()) != null) {
              exemptionList.Add(new Regex(line));
              i++;
            }
            //Console.WriteLine("Read {0} lines from the exclusion file '{1}'.",
            //  i, options.exemptionFile);
          }
        } catch (Exception e) {
          Console.WriteLine("Something went wrong reading the exclusion file '{0}'; read in {1} lines, continuing processing.",
            fileName, i);
          Console.WriteLine(e.Message);
        }
      }
      #endregion

      try {

        HeapFactory heap;
        switch (options.heapRepresentation) {
          case Options.HeapRepresentation.splitFields:
            heap = new SplitFieldsHeap();
            break;
          case Options.HeapRepresentation.general:
            heap = new GeneralHeap();
            break;
          default:
            Console.WriteLine("Unknown setting for /heap");
            return 1;
        }

        if ((options.phoneFeedbackCode || options.phoneNavigationCode) && (options.phoneControls == null || options.phoneControls == "")) {
          Console.WriteLine("Options /phoneNavigationCode and /phoneFeedbackCode need /phoneControls option set.");
          return 1;
        }

        result = TranslateAssembly(assemblyNames, heap, options, exemptionList, whiteList);

      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed: {0}", e.Message);
        // Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
      return result;
    }

    public static int TranslateAssembly(List<string> assemblyNames, HeapFactory heapFactory, Options options, List<Regex> exemptionList, bool whiteList) {
      Contract.Requires(assemblyNames != null);
      Contract.Requires(heapFactory != null);

      var libPaths = options.libpaths;
      var wholeProgram = options.wholeProgram;
      var/*?*/ stubAssemblies = options.stub;
      var phoneControlsConfigFile = options.phoneControls;
      var doPhoneNav = options.phoneNavigationCode;
      var doPhoneFeedback = options.phoneFeedbackCode;

      var host = new CodeContractAwareHostEnvironment(libPaths != null ? libPaths : Enumerable<string>.Empty, true, true);
      Host = host;

      var modules = new List<IModule>();
      var contractExtractors = new Dictionary<IUnit, IContractProvider>();
      var pdbReaders = new Dictionary<IUnit, PdbReader>();
      foreach (var a in assemblyNames) {
        var module = host.LoadUnitFrom(a) as IModule;
        if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
          Console.WriteLine(a + " is not a PE file containing a CLR module or assembly, or an error occurred when loading it.");
          Console.WriteLine("Skipping it, continuing with other input assemblies");
        }
        PdbReader/*?*/ pdbReader = null;
        string pdbFile = Path.ChangeExtension(module.Location, "pdb");
        if (File.Exists(pdbFile)) {
          Stream pdbStream = File.OpenRead(pdbFile);
          pdbReader = new PdbReader(pdbStream, host);
        }
        module = Decompiler.GetCodeModelFromMetadataModel(host, module, pdbReader) as IModule;
        host.RegisterAsLatest(module);
        modules.Add(module);
        contractExtractors.Add(module, host.GetContractExtractor(module.UnitIdentity));
        pdbReaders.Add(module, pdbReader);
      }
      if (stubAssemblies != null) {
        foreach (var s in stubAssemblies) {
          var module = host.LoadUnitFrom(s) as IModule;
          if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
            Console.WriteLine(s + " is not a PE file containing a CLR module or assembly, or an error occurred when loading it.");
            Console.WriteLine("Skipping it, continuing with other input assemblies");
          }
          PdbReader/*?*/ pdbReader = null;
          string pdbFile = Path.ChangeExtension(module.Location, "pdb");
          if (File.Exists(pdbFile)) {
            Stream pdbStream = File.OpenRead(pdbFile);
            pdbReader = new PdbReader(pdbStream, host);
          }
          module = Decompiler.GetCodeModelFromMetadataModel(host, module, pdbReader) as IModule;

          var copier = new CodeDeepCopier(host);
          var mutableModule = copier.Copy(module);

          var mscorlib = TypeHelper.GetDefiningUnit(host.PlatformType.SystemObject.ResolvedType);

          //var mutator = new ReparentModule(host, mscorlib, mutableModule);
          //module = mutator.Rewrite(mutableModule);
          //modules.Add(Tuple.Create(module, pdbReader));

          RewriteUnitReferences renamer = new RewriteUnitReferences(host, mutableModule);
          var mscorlibAssembly = (IAssembly)mscorlib;
          renamer.targetAssembly = mscorlibAssembly;
          renamer.originalAssemblyIdentity = mscorlibAssembly.AssemblyIdentity;
          renamer.RewriteChildren(mutableModule);
          modules.Add((IModule)mutableModule);
          contractExtractors.Add(module, host.GetContractExtractor(module.UnitIdentity));
          pdbReaders.Add(module, pdbReader);
        }
      }
      if (modules.Count == 0) {
        Console.WriteLine("No input assemblies to translate.");
        return -1;
      }

      var primaryModule = modules[0];

      TraverserFactory traverserFactory;
      if (wholeProgram)
        traverserFactory = new WholeProgram();
      else
        traverserFactory = new CLRSemantics();

      Sink sink= new Sink(host, traverserFactory, heapFactory, options, exemptionList, whiteList);
      TranslationHelper.tmpVarCounter = 0;
      MetadataTraverser translator;
      translator= traverserFactory.MakeMetadataTraverser(sink, contractExtractors, pdbReaders);

      if (phoneControlsConfigFile != null && phoneControlsConfigFile != "") {
        PhoneCodeHelper.initialize(host);
        PhoneCodeHelper.instance().PhonePlugin = new PhoneControlsPlugin(phoneControlsConfigFile);
        
        if (doPhoneNav) {
          PhoneCodeHelper.instance().PhoneNavigationToggled = true;
          PhoneInitializationMetadataTraverser initTr = new PhoneInitializationMetadataTraverser(host);
          initTr.InjectPhoneCodeAssemblies(modules);
          PhoneNavigationMetadataTraverser navTr = new PhoneNavigationMetadataTraverser(host);
          navTr.InjectPhoneCodeAssemblies(modules);
        }

        if (doPhoneFeedback) {
          PhoneCodeHelper.instance().PhoneFeedbackToggled = true;
          PhoneControlFeedbackMetadataTraverser fbMetaDataTraverser= new PhoneControlFeedbackMetadataTraverser(host);
          fbMetaDataTraverser.Visit(modules);
        }
      }

      translator.TranslateAssemblies(modules);

      foreach (var pair in sink.delegateTypeToDelegates.Values) {
        CreateDispatchMethod(sink, pair.Item1, pair.Item2);
      }

      string outputFileName = primaryModule.Name + ".bpl";
      callPostTranslationTraversers(modules, sink, phoneControlsConfigFile, outputFileName);
      Microsoft.Boogie.TokenTextWriter writer = new Microsoft.Boogie.TokenTextWriter(outputFileName);
      Prelude.Emit(writer);
      sink.TranslatedProgram.Emit(writer);
      writer.Close();
      return 0; // success
    }

    private static void callPostTranslationTraversers(List<IModule> modules, Sink sink, string phoneControlsConfigFile, string outputFileName) {
      if (PhoneCodeHelper.instance().PhoneFeedbackToggled) {
        PhoneCodeHelper.instance().CreateFeedbackCallingMethods(sink);
      }

      if (PhoneCodeHelper.instance().PhoneFeedbackToggled || PhoneCodeHelper.instance().PhoneNavigationToggled) {
        PhoneBackKeyCallbackTraverser traverser = new PhoneBackKeyCallbackTraverser(sink.host);
        traverser.Visit(modules);

        PhoneMethodInliningMetadataTraverser inlineTraverser =
          new PhoneMethodInliningMetadataTraverser(PhoneCodeHelper.instance());
        inlineTraverser.findAllMethodsToInline(modules);
        PhoneCodeHelper.updateInlinedMethods(sink, inlineTraverser.getMethodsToInline());
        System.Console.WriteLine("Total methods seen: {0}, inlined: {1}", inlineTraverser.TotalMethodsCount, inlineTraverser.InlinedMethodsCount);
      }

      if (PhoneCodeHelper.instance().PhoneNavigationToggled) {
        string outputConfigFile = Path.ChangeExtension(phoneControlsConfigFile, "bplout");
        StreamWriter outputStream = new StreamWriter(outputConfigFile);
        PhoneCodeHelper.instance().PhonePlugin.DumpControlStructure(outputStream);
        outputStream.Close();
        PhoneCodeWrapperWriter.createCodeWrapper(sink);

        // NAVIGATION TODO for now I console this out
        if (!PhoneCodeHelper.instance().OnBackKeyPressOverriden) {
          Console.Out.WriteLine("No back navigation issues, OnBackKeyPress is not overriden");
        } else if (PhoneCodeHelper.instance().BackKeyHandlerOverridenByUnknownDelegate) {
          Console.Out.WriteLine("Back navigation ISSUE: BackKeyPress is overriden by unidentified delegate and may perform illegal navigation");
          Console.Out.WriteLine("Offending pages:");
          foreach (ITypeReference type in PhoneCodeHelper.instance().BackKeyUnknownDelegateOffenders) {
            Console.WriteLine("\t" + type.ToString());
          }
        } else if (!PhoneCodeHelper.instance().BackKeyPressHandlerCancels && !PhoneCodeHelper.instance().BackKeyPressNavigates) {
          Console.Out.WriteLine("No back navigation issues, BackKeyPress overrides do not alter navigation");
        } else {
          if (PhoneCodeHelper.instance().BackKeyPressNavigates) {
            Console.Out.WriteLine("Back navigation ISSUE: back key press may navigate to pages not in backstack! From pages:");
            foreach (ITypeReference type in PhoneCodeHelper.instance().BackKeyNavigatingOffenders.Keys) {
              ICollection<string> targets = PhoneCodeHelper.instance().BackKeyNavigatingOffenders[type];
              Console.WriteLine("\t" + type.ToString() + " may navigate to ");
              foreach (string target in targets) {
                Console.WriteLine("\t\t" + target);
              }
            }
          }

          if (PhoneCodeHelper.instance().BackKeyPressHandlerCancels) {
            Console.Out.WriteLine("Back navigation ISSUE: back key press default behaviour may be cancelled! From pages:");
            foreach (ITypeReference type in PhoneCodeHelper.instance().BackKeyCancellingOffenders) {
              Console.WriteLine("\t" + type.ToString());
            }
          }
        }
      }

      if (PhoneCodeHelper.instance().PhoneNavigationToggled) {
        foreach (IMethodDefinition def in PhoneNavigationCodeTraverser.NavCallers) {
          if (!PhoneCodeHelper.instance().isKnownBackKeyOverride(def))
            PhoneCodeHelper.instance().addHandlerStubCaller(sink, def);
        }
        PhoneCodeHelper.instance().addNavigationUriHavocer(sink);
        PhoneCodeHelper.instance().createQueriesBatchFile(sink, outputFileName);
      }
    }

    private static string NameUpToFirstPeriod(string name) {
      var i = name.IndexOf('.');
      if (i == -1)
        return name;
      else
        return name.Substring(0, i);
    }

    private class ReparentModule : CodeRewriter {
      private IUnit targetUnit;
      private IUnit sourceUnit;
      public ReparentModule(IMetadataHost host, IUnit targetUnit, IUnit sourceUnit) 
        : base(host) {
        this.targetUnit = targetUnit;
        this.sourceUnit = sourceUnit;
      }

      public override void RewriteChildren(RootUnitNamespace rootUnitNamespace) {
        if (rootUnitNamespace.Unit.UnitIdentity.Equals(this.sourceUnit.UnitIdentity))
          rootUnitNamespace.Unit = this.targetUnit;
        base.RewriteChildren(rootUnitNamespace);
      }

    }

    private static Bpl.IfCmd BuildIfCmd(Bpl.Expr b, Bpl.Cmd cmd, Bpl.IfCmd ifCmd) {
      Bpl.StmtListBuilder ifStmtBuilder;
      ifStmtBuilder = new Bpl.StmtListBuilder();
      ifStmtBuilder.Add(cmd);
      return new Bpl.IfCmd(b.tok, b, ifStmtBuilder.Collect(b.tok), ifCmd, null);
    }
    private static Bpl.IfCmd BuildReturnCmd(Bpl.Expr b) {
      Bpl.StmtListBuilder ifStmtBuilder = new Bpl.StmtListBuilder();
      ifStmtBuilder.Add(new Bpl.ReturnCmd(b.tok));
      return new Bpl.IfCmd(b.tok, b, ifStmtBuilder.Collect(b.tok), null, null);
    }
    private static void WrapArguments(Sink sink, IMethodDefinition invokeMethod, IMethodDefinition delegateMethod, Bpl.ExprSeq inputExprs, Bpl.ExprSeq outputExprs, 
                                      out Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed,
                                      out Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toUnboxed) {
      IEnumerator<IParameterDefinition> penum = delegateMethod.Parameters.GetEnumerator();
      toBoxed = new Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr>();
      toUnboxed = new Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr>();
      penum.MoveNext();
      int i = 0;
      foreach (IParameterDefinition from in invokeMethod.Parameters) {
        IParameterDefinition to = penum.Current;
        bool fromIsGeneric = (from.Type is IGenericTypeParameter || from.Type is IGenericMethodParameter);
        bool toIsGeneric = (to.Type is IGenericTypeParameter || to.Type is IGenericMethodParameter);
        if (!fromIsGeneric && toIsGeneric) {
          outputExprs.Add(sink.Heap.Box(Bpl.Token.NoToken, sink.CciTypeToBoogie(from.Type), inputExprs[i]));
        }
        else if (fromIsGeneric && !toIsGeneric) {
          outputExprs.Add(sink.Heap.Unbox(Bpl.Token.NoToken, sink.CciTypeToBoogie(to.Type), inputExprs[i]));
        }
        else {
          outputExprs.Add(inputExprs[i]);
        }
        i++;
        penum.MoveNext();
      }
    }
    private static void CreateDispatchMethod(Sink sink, ITypeDefinition type, HashSet<IMethodDefinition> delegates) {
      Contract.Assert(type.IsDelegate);
      IMethodDefinition invokeMethod = null;
      foreach (IMethodDefinition m in type.Methods) {
        if (m.Name.Value == "Invoke") {
          invokeMethod = m;
          break;
        }
      }

      try {
        IMethodDefinition unspecializedInvokeMethod = Sink.Unspecialize(invokeMethod).ResolvedMethod;
        Bpl.DeclWithFormals invokeProcedure = sink.FindOrCreateProcedure(unspecializedInvokeMethod).Decl;
        var proc = invokeProcedure as Bpl.Procedure;
        var invars = proc.InParams;
        var outvars = proc.OutParams;

        Bpl.IToken token = invokeMethod.Token();

        Bpl.Formal delegateVariable = new Bpl.Formal(token, new Bpl.TypedIdent(token, "delegate", sink.Heap.DelegateType), true);
        Bpl.VariableSeq dispatchProcInvars = new Bpl.VariableSeq();
        dispatchProcInvars.Add(delegateVariable);
        for (int i = 1; i < invars.Length; i++) {
          Bpl.Variable f = invars[i];
          dispatchProcInvars.Add(new Bpl.Formal(token, new Bpl.TypedIdent(token, f.Name, f.TypedIdent.Type), true));
        }

        Bpl.VariableSeq dispatchProcOutvars = new Bpl.VariableSeq();
        foreach (Bpl.Formal f in outvars) {
          dispatchProcOutvars.Add(new Bpl.Formal(token, new Bpl.TypedIdent(token, f.Name, f.TypedIdent.Type), false));
        }

        Bpl.Procedure dispatchProc =
          new Bpl.Procedure(token,
            "DispatchOne." + proc.Name,
            new Bpl.TypeVariableSeq(),
            dispatchProcInvars,
            dispatchProcOutvars,
            new Bpl.RequiresSeq(),
            new Bpl.IdentifierExprSeq(),
            new Bpl.EnsuresSeq());
        sink.TranslatedProgram.TopLevelDeclarations.Add(dispatchProc);

        Bpl.LocalVariable method = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "method", Bpl.Type.Int));
        Bpl.LocalVariable receiver = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "receiver", sink.Heap.RefType));
        Bpl.LocalVariable typeParameter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "typeParameter", sink.Heap.TypeType));
        Bpl.IfCmd ifCmd = BuildIfCmd(Bpl.Expr.True, new Bpl.AssumeCmd(token, Bpl.Expr.False), null);
        foreach (IMethodDefinition defn in delegates) {
          Bpl.ExprSeq ins = new Bpl.ExprSeq();
          Bpl.IdentifierExprSeq outs = new Bpl.IdentifierExprSeq();
          if (!defn.IsStatic)
            ins.Add(Bpl.Expr.Ident(receiver));
          Bpl.ExprSeq args = new Bpl.ExprSeq();
          for (int i = 1; i < dispatchProcInvars.Length; i++) {
            args.Add(Bpl.Expr.Ident(dispatchProcInvars[i]));
          }
          Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toBoxed;
          Dictionary<Bpl.IdentifierExpr, Bpl.IdentifierExpr> toUnboxed;
          WrapArguments(sink, unspecializedInvokeMethod, defn, args, ins, out toBoxed, out toUnboxed);
          int numTypeParameters = Sink.GetNumberTypeParameters(defn);
          for (int i = 0; i < numTypeParameters; i++) {
            ins.Add(new Bpl.NAryExpr(Bpl.Token.NoToken, 
                                     new Bpl.FunctionCall(sink.FindOrCreateTypeParameterFunction(i)), 
                                     new Bpl.ExprSeq(Bpl.Expr.Ident(typeParameter))));
          }
          for (int i = 0; i < dispatchProcOutvars.Length; i++) {
            outs.Add(Bpl.Expr.Ident(dispatchProcOutvars[i]));
          }
          Bpl.Constant c = sink.FindOrCreateDelegateMethodConstant(defn);
          var procInfo = sink.FindOrCreateProcedure(defn);
          Bpl.Expr bexpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, Bpl.Expr.Ident(method), Bpl.Expr.Ident(c));
          Bpl.CallCmd callCmd = new Bpl.CallCmd(token, procInfo.Decl.Name, ins, outs);
          ifCmd = BuildIfCmd(bexpr, callCmd, ifCmd);
        }
        Bpl.StmtListBuilder stmtBuilder = new Bpl.StmtListBuilder();
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(method), 
                                                         sink.ReadMethod(Bpl.Expr.Ident(delegateVariable))));
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(receiver), 
                                                         sink.ReadReceiver(Bpl.Expr.Ident(delegateVariable))));
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(typeParameter), 
                                                         sink.ReadTypeParameters(Bpl.Expr.Ident(delegateVariable))));
        stmtBuilder.Add(ifCmd);
        Bpl.VariableSeq localVariables = new Bpl.VariableSeq();
        localVariables.Add(method);
        localVariables.Add(receiver);
        localVariables.Add(typeParameter);
        Bpl.Implementation dispatchImpl =
            new Bpl.Implementation(token,
                dispatchProc.Name,
                new Bpl.TypeVariableSeq(),
                dispatchProc.InParams,
                dispatchProc.OutParams,
                localVariables,
                stmtBuilder.Collect(token)
                );
        dispatchImpl.Proc = dispatchProc;
        sink.TranslatedProgram.TopLevelDeclarations.Add(dispatchImpl);

        Bpl.LocalVariable iter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "iter", sink.Heap.RefType));
        Bpl.LocalVariable niter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "niter", sink.Heap.RefType));

        Bpl.StmtListBuilder implStmtBuilder = new Bpl.StmtListBuilder();
        implStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(iter), sink.ReadHead(Bpl.Expr.Ident(invars[0]))));

        Bpl.StmtListBuilder whileStmtBuilder = new Bpl.StmtListBuilder();
        whileStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(niter), sink.ReadNext(Bpl.Expr.Ident(invars[0]), Bpl.Expr.Ident(iter))));
        whileStmtBuilder.Add(BuildReturnCmd(Bpl.Expr.Eq(Bpl.Expr.Ident(niter), sink.ReadHead(Bpl.Expr.Ident(invars[0])))));
        Bpl.ExprSeq inExprs = new Bpl.ExprSeq();
        inExprs.Add(sink.ReadDelegate(Bpl.Expr.Ident(invars[0]), Bpl.Expr.Ident(niter)));
        for (int i = 1; i < invars.Length; i++) {
          Bpl.Variable f = invars[i];
          inExprs.Add(Bpl.Expr.Ident(f));
        }
        Bpl.IdentifierExprSeq outExprs = new Bpl.IdentifierExprSeq();
        foreach (Bpl.Formal f in outvars) {
          outExprs.Add(Bpl.Expr.Ident(f));
        }
        whileStmtBuilder.Add(new Bpl.CallCmd(token, dispatchProc.Name, inExprs, outExprs));
        whileStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(iter), Bpl.Expr.Ident(niter)));
        Bpl.WhileCmd whileCmd = new Bpl.WhileCmd(token, Bpl.Expr.True, new List<Bpl.PredicateCmd>(), whileStmtBuilder.Collect(token));

        implStmtBuilder.Add(whileCmd);

        Bpl.Implementation impl =
            new Bpl.Implementation(token,
                proc.Name,
                new Bpl.TypeVariableSeq(),
                invars,
                outvars,
                new Bpl.VariableSeq(iter, niter),
                implStmtBuilder.Collect(token)
                );
        impl.Proc = proc;
        sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
      } catch (TranslationException te) {
        throw new NotImplementedException(te.ToString());
      } catch {
        throw;
      } finally {
        // Maybe this is a good place to add the procedure to the toplevel declarations
      }
    }

    private class RewriteUnitReferences : MetadataRewriter {
      private UnitIdentity sourceUnitIdentity = null;
      internal IAssembly/*?*/ targetAssembly = null;
      internal AssemblyIdentity/*?*/ originalAssemblyIdentity = null;

      Dictionary<uint, bool> internedKeys = new Dictionary<uint, bool>();

      public RewriteUnitReferences(IMetadataHost host, Module sourceUnit)
        : base(host) {
        this.sourceUnitIdentity = sourceUnit.UnitIdentity;
        }

      public override IModuleReference Rewrite(IModuleReference moduleReference) {
        if (this.sourceUnitIdentity.Equals(moduleReference.UnitIdentity)) {
          return this.targetAssembly;
        }
        return base.Rewrite(moduleReference);
      }
      public override IAssemblyReference Rewrite(IAssemblyReference assemblyReference) {
        if (this.sourceUnitIdentity.Equals(assemblyReference.UnitIdentity)) {
          return this.targetAssembly;
        }
        return base.Rewrite(assemblyReference);
      }

    }

  }

}
