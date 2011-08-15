using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Contracts;

namespace BytecodeTranslator.TranslationPlugins.BytecodeTranslator {
  class BytecodeTranslatorPlugin : ITranslationPlugin {
    public ITranslator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      // TODO take whole program options into account here
      return new CLRSemantics().MakeMetadataTraverser(sink, contractProviders, pdbReaders);
      // return new WholeProgram().MakeMetadataTraverser(sink, contractProviders, pdbReaders);
    }
  }
}
