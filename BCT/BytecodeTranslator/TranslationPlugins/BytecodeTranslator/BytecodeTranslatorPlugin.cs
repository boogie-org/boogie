using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Contracts;

namespace BytecodeTranslator.TranslationPlugins.BytecodeTranslator {
  internal class BytecodeTranslatorPlugin : ITranslationPlugin {
    private bool isWholeProgram = false;

    public BytecodeTranslatorPlugin(Boolean isWholeProgram) {
      this.isWholeProgram = isWholeProgram;
    }

    public Translator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      TraverserFactory factory;
      if (isWholeProgram)
        factory= new WholeProgram();
      else
        factory= new CLRSemantics();
      // Translator translator= factory.MakeMetadataTraverser(sink, contractProviders, pdbReaders);
      Translator translator= factory.getTranslator(sink, contractProviders, pdbReaders);
      return translator;
    }
  }
}
