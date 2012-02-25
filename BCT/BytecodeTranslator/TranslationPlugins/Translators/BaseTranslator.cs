using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using BytecodeTranslator.TranslationPlugins;
using Microsoft.Cci;
using Microsoft.Cci.Contracts;

namespace BytecodeTranslator {
  class BaseTranslator : ContractAwareTranslator {
    public TraverserFactory Factory;
    private Sink sink;
    private IDictionary<IUnit, IContractProvider> contractProviders;
    private IDictionary<IUnit, PdbReader> pdbReaders;
    private BCTMetadataTraverser traverser;

    public BaseTranslator(TraverserFactory factory, Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      Factory = factory;
      this.sink = sink;
      this.contractProviders = contractProviders;
      this.pdbReaders = pdbReaders;
    }

    public override void initialize() {
      traverser = Factory.MakeMetadataTraverser(sink, contractProviders, pdbReaders);
    }

    public override bool isOneShot() {
      return true;
    }

    public override int getPriority() {
      // TODO make configurable from outside
      return 10;
    }

    public override void TranslateAssemblies(IEnumerable<Microsoft.Cci.IUnit> assemblies) {
      traverser.TranslateAssemblies(assemblies);
    }
  }
}
