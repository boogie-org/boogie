using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace BytecodeTranslator {
  class Prelude {
    public static void Emit(Microsoft.Boogie.TokenTextWriter wr) {
      wr.WriteText(@"// Copyright (c) 2010, Microsoft Corp.
// Bytecode Translator prelude

type Ref;
const null: Ref;

type Field alpha;

type HeapType = <alpha>[Ref, Field alpha]alpha;
function IsGoodHeap(HeapType): bool;

var $Heap: HeapType where IsGoodHeap($Heap);

");
    }
  }
}
