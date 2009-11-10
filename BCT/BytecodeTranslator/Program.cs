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

namespace BytecodeTranslator {
  class BCT {

    static int Main(string[] args) {

      int result = 0;

      if (args.Length < 1) {
        Console.WriteLine("Must specify an input file.");
        return result;
      }

      try {
        result = DoRealWork(args[0]);
      } catch (Exception e) { // swallow everything and just return an error code
        Console.WriteLine("The byte-code translator failed with uncaught exception: {0}", e.Message);
        Console.WriteLine("Stack trace: {0}", e.StackTrace);
        return -1;
      }
      return result;
    }

    static int DoRealWork(string assemblyName) {

      var host = new PeReader.DefaultHost();

      IModule/*?*/ module = host.LoadUnitFrom(assemblyName) as IModule;
      if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
        Console.WriteLine(assemblyName + " is not a PE file containing a CLR module or assembly, or an error occurred when loading it.");
        return 1;
      }

      #region Load any reference assemblies
      var fileSpec = module.Location;
      string directory;
      if (Path.IsPathRooted(fileSpec))
        directory = Path.GetDirectoryName(fileSpec);
      else
        directory = Directory.GetCurrentDirectory();
      string[] files;
      Dictionary<string, List<IAssembly>>/*?*/ referenceAssemblies = new Dictionary<string, List<IAssembly>>();
      #region Look for reference assembly dlls
      // TODO: Search a user-specified set of paths/directories, not just the one the input came from.
      files = Directory.GetFiles(directory, "*.Contracts*.dll", SearchOption.TopDirectoryOnly);
      if (files != null) {
        foreach (var file in files) {
          IAssembly/*?*/ refAssem = host.LoadUnitFrom(file) as IAssembly;
          if (refAssem == null || refAssem == Dummy.Assembly) {
            Console.WriteLine("Could not load '" + file + "' as a reference assembly.");
            continue;
          }
          var fileName = Path.GetFileNameWithoutExtension(file);
          var baseName = BCT.NameUpToFirstPeriod(fileName);
          if (referenceAssemblies.ContainsKey(baseName)) {
            referenceAssemblies[baseName].Add(refAssem);
          } else {
            List<IAssembly> a = new List<IAssembly>();
            a.Add(refAssem);
            referenceAssemblies.Add(baseName, a);
          }
        }
      }
      #endregion Look for reference assembly dlls
      #endregion Load any reference assemblies

      IAssembly/*?*/ assembly = null;

      PdbReader/*?*/ pdbReader = null;
      string pdbFile = Path.ChangeExtension(module.Location, "pdb");
      if (File.Exists(pdbFile)) {
        Stream pdbStream = File.OpenRead(pdbFile);
        pdbReader = new PdbReader(pdbStream, host);
      }

      ContractProvider contractProvider = new ContractProvider(new ContractMethods(host), module);
      module = ConvertMetadataModelToCodeModel(host, module, pdbReader, contractProvider);

      //SourceToILConverterProvider sourceToILProvider =
      //  delegate(IMetadataHost host2, ISourceLocationProvider/*?*/ sourceLocationProvider, IContractProvider/*?*/ contractProvider2)
      //  {
      //      return new CodeModelToILConverter(host2, sourceLocationProvider, contractProvider2);
      //  };


      List<IAssembly> oobUnits;
      List<KeyValuePair<IContractProvider, IMetadataHost>> oobProvidersAndHosts = new List<KeyValuePair<IContractProvider, IMetadataHost>>();
      if (referenceAssemblies.TryGetValue(module.Name.Value, out oobUnits)) {
        foreach (var oob in oobUnits) {
          LazyContractProvider ocp = new LazyContractProvider(host, oob, contractProvider.ContractMethods);
          oobProvidersAndHosts.Add(new KeyValuePair<IContractProvider, IMetadataHost>(ocp, host));
        }
      }

      AggregatingContractProvider acp = new AggregatingContractProvider(host, contractProvider, oobProvidersAndHosts);

      #region Pass 3: Translate the code model to BPL
      //tmp_BPLGenerator translator = new tmp_BPLGenerator(host, acp);
      ToplevelTraverser translator = new ToplevelTraverser(acp);
      assembly = module as IAssembly;
      if (assembly != null)
        translator.Visit(assembly);
      else
        translator.Visit(module);
      #endregion Pass 3: Translate the code model to BPL
      Microsoft.Boogie.TokenTextWriter writer = new Microsoft.Boogie.TokenTextWriter(module.Name + ".bpl");
      translator.TranslatedProgram.Emit(writer);
      writer.WriteLine(";ENDE");
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

    /// <summary>
    /// Takes a module which is presumably a metadata model (either immutable or mutable) and returns
    /// the "same" module which is now a code model module.
    /// 
    /// Currently there is no way to lazily convert a module from the metadata model to the code model.
    /// Therefore, this method works eagerly by visiting the entire <paramref name="module"/>.
    /// </summary>
    /// <param name="host">
    /// The host that was used to load the module.
    /// </param>
    /// <param name="module">
    /// The module which is to be converted.
    /// </param>
    /// <param name="pdbReader">
    /// A PDB reader that is used by ILToCodeModel during the conversion.
    /// </param>
    /// <param name="contractProvider">
    /// A contract provider that is used by ILToCodeModel during the conversion. As part of the conversion, the
    /// contract provider will become populated with any contracts found during decompilation.
    /// </param>
    /// <returns>
    /// A module that is at the code model level.
    /// </returns>
    public static IModule ConvertMetadataModelToCodeModel(IMetadataHost host, IModule module, PdbReader/*?*/ pdbReader, ContractProvider contractProvider) {

      SourceMethodBodyProvider ilToSourceProvider =
        delegate(IMethodBody methodBody) {
          return new Microsoft.Cci.ILToCodeModel.SourceMethodBody(methodBody, host, contractProvider, pdbReader);
        };

      IAssembly/*?*/ assembly;

      #region Just run the code and contract mutator which extracts all contracts to their containing methods
      CodeAndContractMutator ccm = new CodeAndContractMutator(host, true, ilToSourceProvider, null, pdbReader, contractProvider);

      assembly = module as IAssembly;
      if (assembly != null)
        module = ccm.Visit(ccm.GetMutableCopy(assembly));
      else
        module = ccm.Visit(ccm.GetMutableCopy(module));
      #endregion Just run the code and contract mutator which extracts all contracts to their containing methods

      return module;
    }

  }

}
