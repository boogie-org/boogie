

type Field a, Heap = <a>[ref, Field a]a;

function IsHeap(Heap) returns (bool);
const alloc : Field bool;

axiom (forall H:Heap, o:ref, f:Field ref ::
       IsHeap(H) && H[o,alloc] ==> H[H[o,f], alloc]);

procedure P() returns () {
  var h : Heap, o : ref, g : Field ref, i : Field ref, o2 : ref;
  assume IsHeap(h) && h[o, alloc];

  o2 := h[o, g];
  assert h[o2, alloc];

  o2 := h[o2, g];
  assert h[o2, alloc];

  h[o2, alloc] := false;

  o2 := h[o2, g];
  assert h[o2, alloc];      // should not be provable
}

type ref;
