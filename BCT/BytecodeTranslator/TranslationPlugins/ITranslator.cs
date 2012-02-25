using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace BytecodeTranslator.TranslationPlugins {
  interface ITranslator {
    void TranslateAssemblies(IEnumerable<IUnit> assemblies);
  }
}
