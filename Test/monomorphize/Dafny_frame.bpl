// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Field T;
type ref;
type HeapType = [ref]<alpha>[Field alpha]alpha;

var $Heap: HeapType;
const unique alloc: Field bool;
const null: ref;

function {:inline} read<alpha>(H: HeapType, r: ref, f: Field alpha) : alpha
{
  H[r][f]
}

procedure p($r: ref)
requires $r != null;
requires $Heap[$r][alloc];
{
  var $Frame: <beta>[ref,Field beta]bool;
  var i: int;

  $Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
    $o != null && read($Heap, $o, alloc) ==> false);

  assert $Frame[null, alloc];
  assert !$Frame[$r, alloc];
}
