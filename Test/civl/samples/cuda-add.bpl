// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
  Civl model of the CUDA kernel:

    int a[n];
    int b[n];
    int c[n];

    kernel add() { c[threadIdx] = a[threadIdx] + b[threadIdx]; }
    add<<<1, n>>>()

  Each thread owns a linear tid: One int identifying its slot (threadIdx).
  Distinct tids are guaranteed to be different by linear ownership, so two
  threads cannot touch the same slot.  The per-thread kernel `add` is verified
  to refine the atomic action c[tid] := a[tid] + b[tid].  The "launch" is
  implicit: any number of threads, each invoked with its own linear tid,
  compose without interference because their slot-local actions trivially
  commute (both-movers).
*/

var {:layer 0,2} a: [int]int;
var {:layer 0,2} b: [int]int;
var {:layer 0,2} c: [int]int;

////////////////////////////////////////////////////////////////////////////////
// Layer 2: kernel as a single atomic action on the owned slot.

both action {:layer 2} AtomicAdd({:linear} tid: One int)
modifies c;
{
  c[tid->val] := a[tid->val] + b[tid->val];
}

////////////////////////////////////////////////////////////////////////////////
// Layer 1 -> 2: the per-thread kernel body.  Three slot-local both-mover
// actions reduce to AtomicAdd via mover reduction.

yield procedure {:layer 1} add({:linear} tid: One int)
refines AtomicAdd;
{
  var av, bv: int;
  call av := ReadA(tid);
  call bv := ReadB(tid);
  call WriteC(tid, av + bv);
}

////////////////////////////////////////////////////////////////////////////////
// Layer 0 primitives: slot-local reads/writes with linear tid ownership.

yield procedure {:layer 0} ReadA({:linear} tid: One int) returns (v: int);
refines both action {:layer 1,2} _ {
  v := a[tid->val];
}

yield procedure {:layer 0} ReadB({:linear} tid: One int) returns (v: int);
refines both action {:layer 1,2} _ {
  v := b[tid->val];
}

yield procedure {:layer 0} WriteC({:linear} tid: One int, v: int);
refines both action {:layer 1,2} _ {
  c[tid->val] := v;
}
