using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Contracts;

namespace BytecodeTranslator.TranslationPlugins {
  interface ITranslationPlugin {
    ITranslator getTranslator(Sink sink, IDictionary<IUnit, IContractProvider> contractExtractors=null, IDictionary<IUnit, PdbReader> pdbReaders=null);
  }
}
