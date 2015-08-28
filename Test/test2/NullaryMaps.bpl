// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// aren't these cool!

var m: []int;
var p: <a>[]a;

type ref;
const null: ref;

procedure P()
  requires m[] == 5;
  modifies m;
  modifies p;
  ensures m[] == 30;
  ensures p[] == null;
{
  m[] := 12;
  p[] := 12;
  p[] := true;
  assert p[] == m[];
  assert p[];
  m := m[:= 30];
  p := p[:=null];
}

procedure Q()
  modifies m;
{
  assert m[] == 5;  // error
  m[] := 30;
  assert m[] == 5;  // error
}

procedure R()
  modifies p;
{
  assert p[] < 3;  // error
}

// ----

type Field a;
type HeapType = <a>[ref, Field a]a;
const F0: Field int;
const F1: Field bool;
const alloc: Field bool;
var Heap: HeapType;
procedure FrameCondition(this: ref)
  modifies Heap;
  ensures (forall<a> o: ref, f: Field a ::
    Heap[o,f] == old(Heap)[o,f] ||
    !old(Heap)[o,alloc] ||
    (o == this && f == F0) ||
    (o == this && f == F1)
    );
{
}

