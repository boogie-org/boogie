// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:sourcefile foo} T; 

function {:source bar} f(int) returns (int);

const {:description baz} unique MAXINT: int;

axiom {:naming qux} (forall i: int :: {f(ij)} f(i) == i+1);

var {:description mux} $Heap: [ref, int]bool;

var {:sort_of_like_a_trigger fux} Bla: [ref, int]bool;

procedure {:use_impl bzzt} foo(x : int) returns(n : int);

implementation {:id blt} foo(x : int) returns(n : int)
{
  block1: return;
}

// ------  and here are various correct things



const {:Correct hux0 + F(hux1)} hux0: int;

function {:Correct F(hux0) + hux1} F(int) returns (int);

axiom {:Correct F(hux0 + hux1)} true;

var {:Correct hux0*hux1} hux1: int;

procedure {:Correct hux0 - hux1} P();

implementation {:Correct hux0 + hux1} {:AlsoCorrect "hello"} P()
{
}

type ref;
