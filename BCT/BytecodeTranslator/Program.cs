//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Linq;
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
using BytecodeTranslator.TranslationPlugins;
using BytecodeTranslator.TranslationPlugins.BytecodeTranslator;
using BytecodeTranslator.TranslationPlugins.PhoneTranslator;

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

    [OptionDescription("Instrument branches with unique counter values", ShortForm = "ib")]
    public bool instrumentBranches = false;

  }

  public class BCT {

    public static IMetadataHost Host;

    static int Main(string[] args)
    {
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
      if (options.stub != null) {
        Console.WriteLine("/s is no longer used to specify stub assemblies");
        return errorReturnValue;
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

        var pgm = TranslateAssembly(assemblyNames, heap, options, exemptionList, whiteList);
        var fileName = assemblyNames[0];
        fileName = Path.GetFileNameWithoutExtension(fileName);
        string outputFileName = fileName + ".bpl";
        Microsoft.Boogie.TokenTextWriter writer = new Microsoft.Boogie.TokenTextWriter(outputFileName);
        Prelude.Emit(writer);
        pgm.Emit(writer);
        writer.Close();
        return 0; // success

      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed: {0}", e.Message);
        // Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
    }

    private static List<IModule> modules;

    public static int TranslateAssemblyAndWriteOutput(List<string> assemblyNames, HeapFactory heapFactory, Options options, List<Regex> exemptionList, bool whiteList) {
      Contract.Requires(assemblyNames != null);
      Contract.Requires(heapFactory != null);
      try {
        var pgm = TranslateAssembly(assemblyNames, heapFactory, options, exemptionList, whiteList);
        var fileName = assemblyNames[0];
        fileName = Path.GetFileNameWithoutExtension(fileName);
        string outputFileName = fileName + ".bpl";
        using (var writer = new Microsoft.Boogie.TokenTextWriter(outputFileName)) {
          Prelude.Emit(writer);
          pgm.Emit(writer);
          writer.Close();
        }
        return 0; // success
      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed: {0}", e.Message);
        // Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
    }

    public static Bpl.Program/*?*/ TranslateAssembly(List<string> assemblyNames, HeapFactory heapFactory, Options options, List<Regex> exemptionList, bool whiteList) {
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

      Bpl.CommandLineOptions.Install(new Bpl.CommandLineOptions());

      #region Assemlies to translate (via cmd line)
      modules = new List<IModule>();
      var contractExtractors = new Dictionary<IUnit, IContractProvider>();
      var pdbReaders = new Dictionary<IUnit, PdbReader>();
      #region Load *all* of the assemblies before doing anything else so that they can all vote on unification matters
      foreach (var a in assemblyNames) {
        var module = host.LoadUnitFrom(a) as IModule;
        if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
          Console.WriteLine(a + " is not a PE file containing a CLR module or assembly, or an error occurred when loading it.");
          Console.WriteLine("Skipping it, continuing with other input assemblies");
        }
        modules.Add(module);
      }
      #endregion
      #region Decompile all of the assemblies
      var decompiledModules = new List<IModule>();
      foreach (var m in modules) {
        PdbReader/*?*/ pdbReader = null;
        string pdbFile = Path.ChangeExtension(m.Location, "pdb");
        if (File.Exists(pdbFile)) {
          Stream pdbStream = File.OpenRead(pdbFile);
          pdbReader = new PdbReader(pdbStream, host);
        }
        var m2 = Decompiler.GetCodeModelFromMetadataModel(host, m, pdbReader) as IModule;
        // The decompiler does not turn calls to Assert/Assume into Code Model nodes
        m2 = new Microsoft.Cci.MutableContracts.ContractExtractor.AssertAssumeExtractor(host, pdbReader).Rewrite(m2);
        decompiledModules.Add(m2);
        host.RegisterAsLatest(m2);
        contractExtractors.Add(m2, host.GetContractExtractor(m2.UnitIdentity));
        pdbReaders.Add(m2, pdbReader);
      }
      modules = decompiledModules;
      #endregion
      #endregion

      #region Assemblies to translate (stubs)
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
      #endregion

      if (modules.Count == 0) {
        throw new TranslationException("No input assemblies to translate.");
      }

      var primaryModule = modules[0];
      Sink sink= new Sink(host, heapFactory, options, exemptionList, whiteList);
      TranslationHelper.tmpVarCounter = 0;

      // TODO move away, get all plugin and translators from a config file or alike
      #region Plugged translators
      List<Translator> translatorsPlugged = new List<Translator>();      
      ITranslationPlugin bctPlugin= new BytecodeTranslatorPlugin(wholeProgram);
      Translator bcTranslator = bctPlugin.getTranslator(sink, contractExtractors, pdbReaders);
      translatorsPlugged.Add(bcTranslator);

      if (phoneControlsConfigFile != null && phoneControlsConfigFile != "") {
        // TODO this should be part of the translator initialziation
        PhoneCodeHelper.initialize(host);
        PhoneCodeHelper.instance().PhonePlugin = new PhoneControlsPlugin(phoneControlsConfigFile);

        if (doPhoneNav) {
          // TODO this should be part of the translator initialziation
          PhoneCodeHelper.instance().PhoneNavigationToggled = true;

          ITranslationPlugin phoneInitPlugin = new PhoneInitializationPlugin();
          ITranslationPlugin phoneNavPlugin = new PhoneNavigationPlugin();
          Translator phInitTranslator = phoneInitPlugin.getTranslator(sink, contractExtractors, pdbReaders);
          Translator phNavTranslator = phoneNavPlugin.getTranslator(sink, contractExtractors, pdbReaders);
          translatorsPlugged.Add(phInitTranslator);
          translatorsPlugged.Add(phNavTranslator);
        }

        if (doPhoneFeedback) {
          // TODO this should be part of the translator initialziation
          PhoneCodeHelper.instance().PhoneFeedbackToggled = true;

          ITranslationPlugin phoneFeedbackPlugin = new PhoneFeedbackPlugin();
          Translator phFeedbackTranslator = phoneFeedbackPlugin.getTranslator(sink, contractExtractors, pdbReaders);
          translatorsPlugged.Add(phFeedbackTranslator);
        }
      }
      #endregion
      sink.TranslationPlugins = translatorsPlugged;

      /*
      if (phoneControlsConfigFile != null && phoneControlsConfigFile != "") {
        // TODO send this all way to initialization of phone plugin translator
        PhoneCodeHelper.initialize(host);
        PhoneCodeHelper.instance().PhonePlugin = new PhoneControlsPlugin(phoneControlsConfigFile);
        
        // TODO these parameters will eventually form part of plugin configuration
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
      */

      // TODO replace the whole translation by a translator initialization and an orchestrator calling back for each element
      // TODO for the current BC translator it will possibly just implement onMetadataElement(IModule)
      // TODO refactor this away, handle priorities between plugged translators
      IOrderedEnumerable<Translator> prioritizedTranslators = translatorsPlugged.OrderBy(t => t.getPriority());
      foreach (Translator t in prioritizedTranslators) {
        t.initialize();
        if (t.isOneShot())
          t.TranslateAssemblies(modules);
      }

      foreach (var pair in sink.delegateTypeToDelegates.Values) {
        CreateDispatchMethod(sink, pair.Item1, pair.Item2);
      }

      string outputFileName = primaryModule.Name + ".bpl";
      callPostTranslationTraversers(modules, sink, phoneControlsConfigFile, outputFileName);
      if (PhoneCodeHelper.instance().PhoneNavigationToggled) {
        finalizeNavigationAnalysisAndBoogieCode(phoneControlsConfigFile, sink, outputFileName);
      }

      //sink.CreateIdentifierCorrespondenceTable(primaryModule.Name.Value);

      //var rc = new Bpl.ResolutionContext((Bpl.IErrorSink)null);
      //foreach (var decl in sink.TranslatedProgram.TopLevelDeclarations) {
      //  decl.Register(rc);
      //}
      //sink.TranslatedProgram.Resolve(rc);
      //var goodDecls = new List<Bpl.Declaration>();
      //var tc = new Bpl.TypecheckingContext(null);
      //foreach (var decl in sink.TranslatedProgram.TopLevelDeclarations) {
      //  var impl = decl as Bpl.Implementation;
      //  if (impl == null) {
      //    goodDecls.Add(decl);
      //    continue;
      //  }
      //  try {
      //    //var tc = new Bpl.TypecheckingContext(null);
      //    impl.Typecheck(tc);
      //    goodDecls.Add(impl);
      //  } catch {
      //    Console.WriteLine("Deleting implementation for: " + impl.Name);
      //    // nothing to do, just continue
      //  }
      //}
      //sink.TranslatedProgram.TopLevelDeclarations = goodDecls;
      return sink.TranslatedProgram;
    }


    private static void finalizeNavigationAnalysisAndBoogieCode(string phoneControlsConfigFile, Sink sink, string outputFileName) {
      outputBoogieTrackedControlConfiguration(phoneControlsConfigFile);
      checkTransitivelyCalledBackKeyNavigations(modules);
      createPhoneBoogieCallStubs(sink);
      PhoneCodeHelper.instance().createQueriesBatchFile(sink, outputFileName);
      outputBackKeyWarnings();
    }

    private static void callPostTranslationTraversers(List<IModule> modules, Sink sink, string phoneControlsConfigFile, string outputFileName) {
      if (PhoneCodeHelper.instance().PhoneFeedbackToggled) {
        PhoneCodeHelper.instance().CreateFeedbackCallingMethods(sink);
      }

      if (PhoneCodeHelper.instance().PhoneFeedbackToggled || PhoneCodeHelper.instance().PhoneNavigationToggled) {
        PhoneMethodInliningMetadataTraverser inlineTraverser =
          new PhoneMethodInliningMetadataTraverser(PhoneCodeHelper.instance());
        inlineTraverser.findAllMethodsToInline(modules);
        PhoneCodeHelper.updateInlinedMethods(sink, inlineTraverser.getMethodsToInline());
        System.Console.WriteLine("Total methods seen: {0}, inlined: {1}", inlineTraverser.TotalMethodsCount, inlineTraverser.InlinedMethodsCount);

        PhoneBackKeyCallbackTraverser traverser = new PhoneBackKeyCallbackTraverser(sink.host);
        traverser.Traverse(modules);

      }
    }

    private static void outputBoogieTrackedControlConfiguration(string phoneControlsConfigFile) {
      string outputConfigFile = Path.ChangeExtension(phoneControlsConfigFile, "bplout");
      StreamWriter outputStream = new StreamWriter(outputConfigFile);
      PhoneCodeHelper.instance().PhonePlugin.DumpControlStructure(outputStream);
      outputStream.Close();
    }

    private static void outputBackKeyWarnings() {
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
            ICollection<Tuple<IMethodReference, string>> targets = PhoneCodeHelper.instance().BackKeyNavigatingOffenders[type];
            Console.WriteLine("\t" + type.ToString() + " may navigate to ");
            foreach (Tuple<IMethodReference, string> target in targets) {
              Console.WriteLine("\t\t" + target.Item2 + " via " +
                                (target.Item1.Name == Dummy.Name ? "anonymous delegate" : target.Item1.ContainingType.ToString() + "." + target.Item1.Name.Value));
            }
          }
        }

        if (PhoneCodeHelper.instance().BackKeyPressHandlerCancels) {
          Console.Out.WriteLine("Back navigation ISSUE: back key press default behaviour may be cancelled! From pages:");
          foreach (Tuple<ITypeReference, string> cancellation in PhoneCodeHelper.instance().BackKeyCancellingOffenders) {
            Console.WriteLine("\t" + cancellation.Item1.ToString() + " via " + cancellation.Item2);
          }
        }
      }
    }

    private static void createPhoneBoogieCallStubs(Sink sink) {
      foreach (IMethodDefinition def in PhoneNavigationCodeTraverser.NavCallers) {
        if (!PhoneCodeHelper.instance().isKnownBackKeyOverride(def))
          PhoneCodeHelper.instance().addHandlerStubCaller(sink, def);
      }
      PhoneCodeHelper.instance().addNavigationUriHavocer(sink);
    }

    private static void checkTransitivelyCalledBackKeyNavigations(List<IModule> modules) {
      foreach (IMethodReference navMethod in PhoneCodeHelper.instance().KnownBackKeyHandlers) {
        // right now we traversed everything so we can see reachability
        IEnumerable<IMethodDefinition> indirects = PhoneCodeHelper.instance().getIndirectNavigators(modules, navMethod);
        if (indirects.Count() > 0) {
          ICollection<Tuple<IMethodReference, string>> targets = null;
          PhoneCodeHelper.instance().BackKeyNavigatingOffenders.TryGetValue(navMethod.ContainingType, out targets);
          if (targets == null) {
            targets = new HashSet<Tuple<IMethodReference, string>>();
          }
          string indirectTargeting = "<unknown indirect navigation> via (";
          foreach (IMethodDefinition methDef in indirects) {
            indirectTargeting += methDef.ContainingType.ToString() + "." + methDef.Name.Value + ", ";
          }
          indirectTargeting += ")";
          targets.Add(Tuple.Create<IMethodReference, string>(navMethod, indirectTargeting));
          PhoneCodeHelper.instance().BackKeyNavigatingOffenders[navMethod.ContainingType] = targets;
        }

        indirects = PhoneCodeHelper.instance().getIndirectCancellations(modules, navMethod);
        if (indirects.Count() > 0) {
          string indirectTargeting = "(";
          foreach (IMethodDefinition methDef in indirects) {
            indirectTargeting += methDef.ContainingType.ToString() + "." + methDef.Name.Value + ", ";
          }
          indirectTargeting += ")";
          PhoneCodeHelper.instance().BackKeyCancellingOffenders.Add(Tuple.Create<ITypeReference, string>(navMethod.ContainingType, indirectTargeting));
        }
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
    private static void BuildAssignment(Sink sink, Bpl.StmtListBuilder stmtBuilder, List<Bpl.Variable> lvars, List<Bpl.Variable> rvars) {
      for (int i = 0; i < lvars.Count; i++) {
        Bpl.Variable lvar = lvars[i];
        Bpl.Type ltype = lvar.TypedIdent.Type;
        Bpl.Variable rvar = rvars[i];
        Bpl.Type rtype = rvar.TypedIdent.Type;
        Bpl.IdentifierExpr lexpr = Bpl.Expr.Ident(lvar);
        Bpl.Expr rexpr = Bpl.Expr.Ident(rvar);
        if (rtype == ltype) {
          // do nothing
        } else if (ltype == sink.Heap.UnionType) {
          rexpr = sink.Heap.ToUnion(Bpl.Token.NoToken, rtype, rexpr);
        }
        else if (rtype == sink.Heap.UnionType) {
          rexpr = sink.Heap.FromUnion(Bpl.Token.NoToken, ltype, rexpr);
        }
        else {
          System.Diagnostics.Debug.Assert(false);
        }
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(lexpr, rexpr));
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
        Bpl.Procedure invokeProcedure = (Bpl.Procedure) sink.FindOrCreateProcedure(unspecializedInvokeMethod).Decl;
        invokeProcedure.AddAttribute("inline", Bpl.Expr.Literal(1));
        var invars = invokeProcedure.InParams;
        var outvars = invokeProcedure.OutParams;

        Bpl.IToken token = invokeMethod.Token();

        Bpl.Formal delegateVariable = new Bpl.Formal(token, new Bpl.TypedIdent(token, "delegate", sink.Heap.DelegateType), true);
        Bpl.VariableSeq dispatchProcInvars = new Bpl.VariableSeq();
        List<Bpl.Variable> dispatchProcInExprs = new List<Bpl.Variable>();
        dispatchProcInvars.Add(delegateVariable);
        for (int i = 1; i < invars.Length; i++) {
          Bpl.Variable v = invars[i];
          Bpl.Formal f = new Bpl.Formal(token, new Bpl.TypedIdent(token, v.Name, v.TypedIdent.Type), true);
          dispatchProcInvars.Add(f);
          dispatchProcInExprs.Add(f);
        }
        Bpl.VariableSeq dispatchProcOutvars = new Bpl.VariableSeq();
        List<Bpl.Variable> dispatchProcOutExprs = new List<Bpl.Variable>();
        foreach (Bpl.Variable v in outvars) {
          Bpl.Formal f = new Bpl.Formal(token, new Bpl.TypedIdent(token, v.Name, v.TypedIdent.Type), false);
          dispatchProcOutvars.Add(f);
          dispatchProcOutExprs.Add(f);
        }
        Bpl.Procedure dispatchProcedure =
          new Bpl.Procedure(token,
            "DispatchOne." + invokeProcedure.Name,
            new Bpl.TypeVariableSeq(),
            dispatchProcInvars,
            dispatchProcOutvars,
            new Bpl.RequiresSeq(),
            new Bpl.IdentifierExprSeq(),
            new Bpl.EnsuresSeq());
        dispatchProcedure.AddAttribute("inline", Bpl.Expr.Literal(1));
        sink.TranslatedProgram.TopLevelDeclarations.Add(dispatchProcedure);

        Bpl.LocalVariable method = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "method", Bpl.Type.Int));
        Bpl.LocalVariable receiver = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "receiver", sink.Heap.RefType));
        Bpl.LocalVariable typeParameter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "typeParameter", sink.Heap.TypeType));
        Bpl.VariableSeq localVariables = new Bpl.VariableSeq();
        localVariables.Add(method);
        localVariables.Add(receiver);
        localVariables.Add(typeParameter); 
        
        Bpl.IfCmd ifCmd = BuildIfCmd(Bpl.Expr.True, new Bpl.AssumeCmd(token, Bpl.Expr.False), null);
        int localCounter = 0;
        foreach (IMethodDefinition defn in delegates) {
          Sink.ProcedureInfo delegateProcedureInfo = sink.FindOrCreateProcedure(defn);
          Bpl.Procedure delegateProcedure = (Bpl.Procedure) delegateProcedureInfo.Decl;
          Bpl.Formal thisVariable = delegateProcedureInfo.ThisVariable;
          int numArguments = defn.ParameterCount;

          List<Bpl.Variable> tempInputs = new List<Bpl.Variable>();
          List<Bpl.Variable> tempOutputs = new List<Bpl.Variable>();

          for (int i = 0; i < defn.ParameterCount; i++) {
            Bpl.Variable v = delegateProcedure.InParams[(thisVariable == null ? 0 : 1) + i];
            Bpl.LocalVariable localVariable = new Bpl.LocalVariable(Bpl.Token.NoToken,
              new Bpl.TypedIdent(Bpl.Token.NoToken, "local" + localCounter++, v.TypedIdent.Type));
            localVariables.Add(localVariable);
            tempInputs.Add(localVariable);
          }

          for (int i = 0; i < delegateProcedure.OutParams.Length; i++) {
            Bpl.Variable v = delegateProcedure.OutParams[i];
            Bpl.LocalVariable localVariable = new Bpl.LocalVariable(Bpl.Token.NoToken,
              new Bpl.TypedIdent(Bpl.Token.NoToken, "local" + localCounter++, v.TypedIdent.Type));
            localVariables.Add(localVariable);
            tempOutputs.Add(localVariable);
          }

          Bpl.ExprSeq ins = new Bpl.ExprSeq();
          Bpl.IdentifierExprSeq outs = new Bpl.IdentifierExprSeq();
          if (!defn.IsStatic)
            ins.Add(Bpl.Expr.Ident(receiver));
          for (int i = 0; i < tempInputs.Count; i++) {
            ins.Add(Bpl.Expr.Ident(tempInputs[i]));
          }
          if (defn.IsGeneric) {
            for (int i = 0; i < defn.GenericParameterCount; i++) {
              ins.Add(new Bpl.NAryExpr(Bpl.Token.NoToken,
                                       new Bpl.FunctionCall(sink.FindOrCreateTypeParameterFunction(i)),
                                       new Bpl.ExprSeq(Bpl.Expr.Ident(typeParameter))));
            }
          }
          if (defn.IsStatic) {
            int numTypeParameters = Sink.ConsolidatedGenericParameterCount(defn.ContainingType);
            for (int i = 0; i < numTypeParameters; i++) {
              ins.Add(new Bpl.NAryExpr(Bpl.Token.NoToken,
                                       new Bpl.FunctionCall(sink.FindOrCreateTypeParameterFunction(i)),
                                       new Bpl.ExprSeq(Bpl.Expr.Ident(typeParameter))));
            }
          }
          for (int i = 0; i < tempOutputs.Count; i++) {
            outs.Add(Bpl.Expr.Ident(tempOutputs[i]));
          }
          Bpl.Constant c = sink.FindOrCreateDelegateMethodConstant(defn);
          Bpl.Expr bexpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, Bpl.Expr.Ident(method), Bpl.Expr.Ident(c));
          Bpl.StmtListBuilder ifStmtBuilder = new Bpl.StmtListBuilder();
          System.Diagnostics.Debug.Assert(tempInputs.Count == dispatchProcInExprs.Count);
          if (tempInputs.Count > 0) {
            BuildAssignment(sink, ifStmtBuilder, tempInputs, dispatchProcInExprs);
          }
          ifStmtBuilder.Add(new Bpl.CallCmd(token, delegateProcedure.Name, ins, outs));
          System.Diagnostics.Debug.Assert(tempOutputs.Count == dispatchProcOutExprs.Count);
          if (tempOutputs.Count > 0) {
            BuildAssignment(sink, ifStmtBuilder, dispatchProcOutExprs, tempOutputs);
          }
          ifCmd = new Bpl.IfCmd(bexpr.tok, bexpr, ifStmtBuilder.Collect(bexpr.tok), ifCmd, null);
        }
        Bpl.StmtListBuilder stmtBuilder = new Bpl.StmtListBuilder();
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(method), 
                                                         sink.ReadMethod(Bpl.Expr.Ident(delegateVariable))));
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(receiver), 
                                                         sink.ReadReceiver(Bpl.Expr.Ident(delegateVariable))));
        stmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(typeParameter), 
                                                         sink.ReadTypeParameters(Bpl.Expr.Ident(delegateVariable))));
        stmtBuilder.Add(ifCmd);
        
        Bpl.Implementation dispatchImpl =
            new Bpl.Implementation(token,
                dispatchProcedure.Name,
                new Bpl.TypeVariableSeq(),
                dispatchProcedure.InParams,
                dispatchProcedure.OutParams,
                localVariables,
                stmtBuilder.Collect(token)
                );
        dispatchImpl.Proc = dispatchProcedure;
        sink.TranslatedProgram.TopLevelDeclarations.Add(dispatchImpl);

        Bpl.LocalVariable iter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "iter", sink.Heap.DelegateMultisetType));
        Bpl.LocalVariable d = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "d", sink.Heap.DelegateType));
        Bpl.LocalVariable all = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "all", sink.Heap.DelegateMultisetType));

        Bpl.StmtListBuilder implStmtBuilder = new Bpl.StmtListBuilder();
        implStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(all), sink.ReadDelegate(Bpl.Expr.Ident(invars[0]))));
        implStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(iter), Bpl.Expr.Ident(sink.Heap.MultisetEmpty)));

        Bpl.StmtListBuilder whileStmtBuilder = new Bpl.StmtListBuilder();
        whileStmtBuilder.Add(BuildReturnCmd(Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, Bpl.Expr.Ident(iter), Bpl.Expr.Ident(all))));
        whileStmtBuilder.Add(new Bpl.AssumeCmd(Bpl.Token.NoToken, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Gt, Bpl.Expr.Select(new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(sink.Heap.MultisetMinus), new Bpl.ExprSeq(Bpl.Expr.Ident(all), Bpl.Expr.Ident(iter))), Bpl.Expr.Ident(d)), new Bpl.LiteralExpr(Bpl.Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(0)))));
        Bpl.ExprSeq inExprs = new Bpl.ExprSeq();
        inExprs.Add(Bpl.Expr.Ident(d));
        for (int i = 1; i < invars.Length; i++) {
          Bpl.Variable f = invars[i];
          inExprs.Add(Bpl.Expr.Ident(f));
        }
        Bpl.IdentifierExprSeq outExprs = new Bpl.IdentifierExprSeq();
        foreach (Bpl.Formal f in outvars) {
          outExprs.Add(Bpl.Expr.Ident(f));
        }
        whileStmtBuilder.Add(new Bpl.CallCmd(token, dispatchProcedure.Name, inExprs, outExprs));
        whileStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(iter), new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(sink.Heap.MultisetPlus), new Bpl.ExprSeq(Bpl.Expr.Ident(iter), new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(sink.Heap.MultisetSingleton), new Bpl.ExprSeq(Bpl.Expr.Ident(d)))))));
        whileStmtBuilder.Add(new Bpl.HavocCmd(Bpl.Token.NoToken, new Bpl.IdentifierExprSeq(Bpl.Expr.Ident(d))));
        Bpl.WhileCmd whileCmd = new Bpl.WhileCmd(token, Bpl.Expr.True, new List<Bpl.PredicateCmd>(), whileStmtBuilder.Collect(token));

        implStmtBuilder.Add(whileCmd);

        Bpl.Implementation impl =
            new Bpl.Implementation(token,
                invokeProcedure.Name,
                new Bpl.TypeVariableSeq(),
                invars,
                outvars,
                new Bpl.VariableSeq(iter, d, all),
                implStmtBuilder.Collect(token)
                );
        impl.Proc = invokeProcedure;
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
