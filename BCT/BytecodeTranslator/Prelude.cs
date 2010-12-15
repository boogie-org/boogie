using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace BytecodeTranslator {
  public class Prelude {
    public static void Emit(Microsoft.Boogie.TokenTextWriter wr) {
      wr.Write(@"// Copyright (c) 2010, Microsoft Corp.
// Bytecode Translator prelude

const null: int;
type HeapType = [int,int]int;
function IsGoodHeap(HeapType): bool;
var $Heap: HeapType where IsGoodHeap($Heap);
");
    }
  }
}
