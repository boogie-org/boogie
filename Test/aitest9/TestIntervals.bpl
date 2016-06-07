// RUN: %boogie "%s" -infer:j > "%t"
// RUN: %diff "%s.expect" "%t"
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

// -----

procedure Neq()
{
  var n: int;
  assume 2 <= n && n <= 10;
  assume 2 != n;
  assume n != 10;
  while (*) {
    n := n;
  }
  assert 3 <= n;
  assert n < 10;
}

procedure NeqX()
{
  var n: real;
  assume 2.0 <= n && n <= 10.0;
  assume 2.0 != n;
  assume n != 10.0;
  // The following statement will cause Boogie to know about n only
  // what the abstract interpreter has inferred so far.
  while (*) { n := n; }

  assert 2.0 <= n && n <= 10.0;  // yes
  assert 2.0 < n;  // error, the abstract domain is not precise enough to figure this out
  assert n < 10.0;  // error, ditto
}
