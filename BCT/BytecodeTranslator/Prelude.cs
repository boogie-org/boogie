using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace BytecodeTranslator {
  public class Prelude {

    /// <summary>
    /// Prelude that is shared by all translated programs, no matter
    /// what the heap representation is.
    /// </summary>
    public static void Emit(Microsoft.Boogie.TokenTextWriter wr) {
      wr.Write(@"// Copyright (c) 2010, Microsoft Corp.
// Bytecode Translator prelude

");
    }
  }
}
