using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace BytecodeTranslator {
  public class Prelude {
    public static void Emit(Microsoft.Boogie.TokenTextWriter wr) {
      wr.Write(@"// Copyright (c) 2010, Microsoft Corp.
// Bytecode Translator prelude

type Ref;
const null: Ref;

type Field;

type TName;

type HeapType = [Ref, Field] Ref;
function IsGoodHeap(HeapType): bool;

var $Heap: HeapType where IsGoodHeap($Heap);

// Static Fields:
//  An object for each class C is used to reference the static fields of C in the heap.
//  That object is encoded as the value of a function.
function ClassRepr(class: TName) returns (ref);
axiom (forall T: TName :: !($typeof(ClassRepr(T)) <: System.Object));
axiom (forall T: TName :: ClassRepr(T) != null);
axiom (forall h: HeapType, c: TName :: { h[ClassRepr(c), $allocated] } IsHeap(h) ==> h[ClassRepr(c), $allocated]);

");
    }
  }
}
