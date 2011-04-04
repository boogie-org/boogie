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

namespace BytecodeTranslator {

  class Options : OptionParsing {

    [OptionDescription("The names of the assemblies to use as input", ShortForm = "a")]
    public List<string> assemblies = null;

    [OptionDescription("Search paths for assembly dependencies.", ShortForm = "lib")]
    public List<string> libpaths = new List<string>();

    public enum HeapRepresentation { splitFields, twoDInt, twoDBox, general }
    [OptionDescription("Heap representation to use", ShortForm = "heap")]
    public HeapRepresentation heapRepresentation = HeapRepresentation.general;

    [OptionDescription("Translate using whole-program assumptions", ShortForm = "whole")]
    public bool wholeProgram = false;

    [OptionDescription("Stub assembly", ShortForm = "s")]
    public List<string>/*?*/ stubAssemblies = null;

  }

  public class BCT {

    public static IMetadataHost Host;

    static int Main(string[] args)
    {
      int result = 0;

      #region Parse options
      var options = new Options();
      options.Parse(args);
      if (options.HasErrors) {
        if (options.HelpRequested)
          options.PrintOptions("");
        return 1;
      }
      #endregion

      var assemblyNames = options.assemblies;
      if (assemblyNames == null || assemblyNames.Count == 0) {
        assemblyNames = new List<string>();
        foreach (var g in options.GeneralArguments) {
          assemblyNames.Add(g);
        }
      }

      try {

        HeapFactory heap;
        switch (options.heapRepresentation) {
          case Options.HeapRepresentation.splitFields:
            heap = new SplitFieldsHeap();
            break;
          case Options.HeapRepresentation.twoDInt:
            heap = new TwoDIntHeap();
            break;
          case Options.HeapRepresentation.twoDBox:
            heap = new TwoDBoxHeap();
            break;
          case Options.HeapRepresentation.general:
            heap = new GeneralHeap();
            break;
          default:
            Console.WriteLine("Unknown setting for /heap");
            return 1;
        }

        result = TranslateAssembly(assemblyNames, heap, options.libpaths, options.wholeProgram, options.stubAssemblies);

      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed with uncaught exception: {0}", e.Message);
        Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
      return result;
    }

    public static int TranslateAssembly(List<string> assemblyNames, HeapFactory heapFactory, List<string>/*?*/ libPaths, bool wholeProgram, List<string>/*?*/ stubAssemblies) {
      Contract.Requires(assemblyNames != null);
      Contract.Requires(heapFactory != null);

      var host = new CodeContractAwareHostEnvironment(libPaths != null ? libPaths : IteratorHelper.GetEmptyEnumerable<string>(), true, true);
      Host = host;

      var modules = new List<Tuple<IModule,PdbReader/*?*/>>();
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
        modules.Add(Tuple.Create(module, pdbReader));
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
          var reparenter = new Reparent(host,
            TypeHelper.GetDefiningUnit(host.PlatformType.SystemObject.ResolvedType),
            module);
          module = reparenter.Visit(module);
          modules.Add(Tuple.Create(module, pdbReader));
        }
      }
      if (modules.Count == 0) {
        Console.WriteLine("No input assemblies to translate.");
        return -1;
      }

      var primaryModule = modules[0].Item1;

      TraverserFactory traverserFactory;
      if (wholeProgram)
        traverserFactory = new WholeProgram();
      else
        traverserFactory = new CLRSemantics();

      var sink = new Sink(host, traverserFactory, heapFactory);
      TranslationHelper.tmpVarCounter = 0;

      foreach (var tup in modules) {

        var module = tup.Item1;
        var pdbReader = tup.Item2;

        IAssembly/*?*/ assembly = null;
        MetadataTraverser translator = traverserFactory.MakeMetadataTraverser(sink, host.GetContractExtractor(module.ModuleIdentity), pdbReader);
        assembly = module as IAssembly;
        if (assembly != null)
          translator.Visit(assembly);
        else
          translator.Visit(module);

      }

      Microsoft.Boogie.TokenTextWriter writer = new Microsoft.Boogie.TokenTextWriter(primaryModule.Name + ".bpl");
      Prelude.Emit(writer);
      sink.TranslatedProgram.Emit(writer);
      writer.Close();
      return 0; // success
    }

    private static string NameUpToFirstPeriod(string name) {
      var i = name.IndexOf('.');
      if (i == -1)
        return name;
      else
        return name.Substring(0, i);
    }

    private class Reparent : CodeAndContractMutatingVisitor {
      private IUnit targetUnit;
      private IUnit sourceUnit;
      public Reparent(IMetadataHost host, IUnit targetUnit, IUnit sourceUnit) 
        : base(host) {
        this.targetUnit = targetUnit;
        this.sourceUnit = sourceUnit;
      }

      public override IRootUnitNamespace Visit(IRootUnitNamespace rootUnitNamespace) {
        return new RootUnitNamespace() {
          Attributes = new List<ICustomAttribute>(rootUnitNamespace.Attributes),
          Locations = new List<ILocation>(rootUnitNamespace.Locations),
          Members = new List<INamespaceMember>(rootUnitNamespace.Members),
          Name = rootUnitNamespace.Name,
          Unit = this.targetUnit,
        };
      }
    }

  }

}
