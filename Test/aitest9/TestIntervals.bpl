procedure P()
{
  var a: int, b: int, c: int;

  a := 0;
  while (*) {
    a := a + 1;
  }
  // a in [0, infty]

  b := 0;
  if (*) { b := b + 1; }
  if (*) { b := b + 1; }
  if (*) { b := b + 1; }
  // b in [0, 3]

  c := a - b;
  // c in [-3, infty]
  goto Next;

  Next:
  assert -3 <= c;
  assert c <= 0;  // error (there was once an error in the Intervals which thought this assertion to be true)
}

// The following tests a triply nested array, where the innermost array is a polymorphic map.
// There was once an error in Boogie's handling of such things in the AI code.

type ref;
type teflon;

type Field a;
type HeapType = <a>[Field a]a;
var Heap: HeapType;

procedure Q(myField: Field [ref][teflon]bool, r: ref, t: teflon)
  modifies Heap;
{
  Heap[myField][r][t] := true;
}
