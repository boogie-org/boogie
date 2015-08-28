// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type Field a;

function FieldAccessFun<b>(heap : <a>[ref, Field a]a, obj : ref, f : Field b)
         returns (res:b);

procedure FieldAccess<b>(heap : <a>[ref, Field a]a, obj : ref, f : Field b)
          returns (res:b) {
  start:
    res := heap[f, obj];    // error: wrong argument order
    res := heap[obj, f];
    assert res == FieldAccessFun(heap, obj, f);
    return;
}

procedure UseHeap(heap : <a>[ref, Field a]a) {
  var f1 : Field int; var f2 : Field bool; var obj : ref;
  var x : int; var y : bool;

  call x := FieldAccess(heap, f1, obj);  // error: wrong argument order
  call x := FieldAccess(heap, obj, f1);
  call y := FieldAccess(heap, obj, f2);

  call y := FieldAccess(heap, obj, f1);  // error: wrong result type
  call x := FieldAccess(heap, obj, obj); // error: wrong argument type
}

procedure injective<b>(heap : <a>[ref, Field a]a, obj0 : ref, obj1 : ref, f : Field b);
   requires obj0 != obj1;
   ensures heap[obj0, f] != heap[obj1, f];

type ref;
