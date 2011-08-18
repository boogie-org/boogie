using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using BytecodeTranslator.Phone;
using Microsoft.Cci;

namespace BytecodeTranslator.TranslationPlugins.Translators {
  class PhoneFeedbackTranslator : Translator {
    private Sink sink;
    PhoneControlFeedbackMetadataTraverser traverser;

    public PhoneFeedbackTranslator(Sink sink) {
      this.sink = sink;
    }

    public override void initialize() {
      traverser = new PhoneControlFeedbackMetadataTraverser(sink.host as MetadataReaderHost);
    }

    public override bool isOneShot() {
      return true;
    }

    public override int getPriority() {
      // TODO make configurable from outside
      return 3;
    }

    public override void TranslateAssemblies(IEnumerable<Microsoft.Cci.IUnit> assemblies) {
      traverser.Visit(assemblies);
    }
  }
}
