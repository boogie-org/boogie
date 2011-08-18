using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Contracts;
using BytecodeTranslator.TranslationPlugins.Translators;

namespace BytecodeTranslator.TranslationPlugins.PhoneTranslator {
  class PhoneFeedbackPlugin : ITranslationPlugin {
    public Translator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractProviders, IDictionary<IUnit, PdbReader> pdbReaders) {
      return new PhoneFeedbackTranslator(sink);
    }
  }
}
