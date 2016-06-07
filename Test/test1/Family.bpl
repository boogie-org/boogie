// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type T;

var Heap: <x>[ref,Field x]x;

function IsHeap(<x>[ref,Field x]x) returns (bool);

const alloc: Field bool;
const C.x: Field int;

axiom (forall h: <x>[ref,Field x]x, f: Field ref, o: ref :: IsHeap(h) && o != null ==> h[h[o,f], alloc]);

procedure P(this: ref) returns (r: int)
  modifies Heap;
{
  start:
    r := Heap[this, C.x];
    Heap[this, C.x] := r;
    return;
}

// -----------------

procedure R(this: ref)
  modifies Heap;
{
  var field: any, refField: Field ref, yField: Field y, anyField: Field any;
  var b: bool, a: any;

  start:
    b := Heap[this, C.x];     // type error
    Heap[this, C.x] := true;  // type error
    Heap[this, refField] := this;
    Heap[this, yField] := 2;  // type error
    Heap[this, field] := a;   // type error
    Heap[this, field] := b;   // type error
    Heap[this, anyField] := a;
    Heap[this, anyField] := b;
    Heap[this, anyField] := anyField;
    Heap[this, anyField] := yField;
    Heap[this, anyField] := field;
    return;
}

type Field a;
type y;
type ref, any;
const null : ref;
