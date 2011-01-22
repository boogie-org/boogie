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

using Bpl = Microsoft.Boogie;

namespace BytecodeTranslator {

  class Options : OptionParsing {

    [OptionDescription("The name of the assembly to use as input", ShortForm = "a")]
    public string assembly = null;

    [OptionDescription("Search paths for assembly dependencies.", ShortForm = "lib")]
    public List<string> libpaths = new List<string>();

    public enum HeapRepresentation { splitFields, twoDInt, twoDBox, general }
    [OptionDescription("Heap representation to use", ShortForm = "heap")]
    public HeapRepresentation heapRepresentation = HeapRepresentation.general;

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

      var assemblyName = String.IsNullOrEmpty(options.assembly) ? options.GeneralArguments[0] : options.assembly;

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
        result = TranslateAssembly(assemblyName, heap, options.libpaths);
      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed with uncaught exception: {0}", e.Message);
        Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
      return result;
    }

    public static int TranslateAssembly(string assemblyName, HeapFactory heapFactory, List<string>/*?*/ libPaths) {

      var host = new Microsoft.Cci.MutableContracts.CodeContractAwareHostEnvironment(libPaths != null ? libPaths : IteratorHelper.GetEmptyEnumerable<string>(), true, true);
      Host = host;

      IModule/*?*/ module = host.LoadUnitFrom(assemblyName) as IModule;
      if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
        Console.WriteLine(assemblyName + " is not a PE file containing a CLR module or assembly, or an error occurred when loading it.");
        return 1;
      }

      IAssembly/*?*/ assembly = null;

      PdbReader/*?*/ pdbReader = null;
      string pdbFile = Path.ChangeExtension(module.Location, "pdb");
      if (File.Exists(pdbFile)) {
        Stream pdbStream = File.OpenRead(pdbFile);
        pdbReader = new PdbReader(pdbStream, host);
      }

      module = Decompiler.GetCodeModelFromMetadataModel(host, module, pdbReader);

      #region Pass 3: Translate the code model to BPL
      //tmp_BPLGenerator translator = new tmp_BPLGenerator(host, acp);
      var factory = new CLRSemantics();
      MetadataTraverser translator = factory.MakeMetadataTraverser(host.GetContractExtractor(module.ModuleIdentity), pdbReader, heapFactory);
      TranslationHelper.tmpVarCounter = 0;
      assembly = module as IAssembly;
      if (assembly != null)
        translator.Visit(assembly);
      else
        translator.Visit(module);
      #endregion Pass 3: Translate the code model to BPL
      Microsoft.Boogie.TokenTextWriter writer = new Microsoft.Boogie.TokenTextWriter(module.Name + ".bpl");
      Prelude.Emit(writer);
      translator.TranslatedProgram.Emit(writer);
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

  }

}
