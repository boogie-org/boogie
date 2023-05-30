// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /typeEncoding:p "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /typeEncoding:a "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type ref;
type Field _;
type Heap = [ref]<alpha>[Field alpha]alpha;
function $IsGoodHeap(Heap) : bool;
function $IsHeapAnchor(Heap) : bool;
var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

procedure P()
{
    assert false;
}
