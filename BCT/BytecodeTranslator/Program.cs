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
  public class CommandLineOptions
  {
    public static bool SplitFields = false;
  }

  public class BCT {

    public static IMetadataHost Host;

    public static bool Parse(string[] args, out string assemblyName)
    {
        assemblyName = "";
        
        foreach (string arg in args)
        {
            if (arg.StartsWith("/"))
            {
                if (arg == "/splitFields")
                {
                    CommandLineOptions.SplitFields = true;
                }
                else
                {
                    Console.WriteLine("Illegal option.");
                    return false;
                }
            }
            else if (assemblyName == "")
            {
                assemblyName = arg;
            }
            else
            {
                Console.WriteLine("Must specify only one input assembly.");
                return false;
            }
        }
        if (assemblyName == "")
        {
            Console.WriteLine("Must specify an input assembly.");
            return false;
        }
        return true;
    }

    static int Main(string[] args)
    {
      int result = 0;
      string assemblyName;
      if (!Parse(args, out assemblyName))
          return result;
      try {
        result = DoRealWork(assemblyName);
      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed with uncaught exception: {0}", e.Message);
        Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
      return result;
    }

    static int DoRealWork(string assemblyName) {

      var host = new Microsoft.Cci.MutableContracts.CodeContractAwareHostEnvironment();
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
      var heap = new Heap();
      MetadataTraverser translator = factory.MakeMetadataTraverser(host.GetContractExtractor(module.ModuleIdentity), pdbReader, heap);
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
