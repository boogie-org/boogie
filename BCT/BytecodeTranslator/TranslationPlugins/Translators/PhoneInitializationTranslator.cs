using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using BytecodeTranslator.Phone;
using Microsoft.Cci;

namespace BytecodeTranslator.TranslationPlugins.Translators {
  class PhoneInitializationTranslator : Translator {
    private Sink sink;
    PhoneInitializationMetadataTraverser traverser;

    public PhoneInitializationTranslator(Sink sink) {
      this.sink = sink;
    }

    public override void initialize() {
      traverser = new PhoneInitializationMetadataTraverser(sink.host as MetadataReaderHost);
    }

    public override bool isOneShot() {
      return true;
    }

    public override int getPriority() {
      // TODO make configurable from outside
      return 1;
    }

    public override void TranslateAssemblies(IEnumerable<Microsoft.Cci.IUnit> assemblies) {
      traverser.InjectPhoneCodeAssemblies(assemblies);
    }
  }

  class PhoneNavigationTranslator : Translator {
    private Sink sink;
    PhoneNavigationMetadataTraverser traverser;

    public PhoneNavigationTranslator(Sink sink) {
      this.sink = sink;
    }

    public override void initialize() {
      traverser = new PhoneNavigationMetadataTraverser(sink.host as MetadataReaderHost);
    }

    public override bool isOneShot() {
      return true;
    }

    public override int getPriority() {
      // TODO make configurable from outside
      return 2;
    }

    public override void TranslateAssemblies(IEnumerable<Microsoft.Cci.IUnit> assemblies) {
      traverser.InjectPhoneCodeAssemblies(assemblies);
    }
  }
}
