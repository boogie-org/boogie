// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:sourcefile "test.ssc"} {1} T; 

function {:source "test.scc"} {1} f(int) returns (int);

const {:description "The largest integer value"} {1} unique MAXINT: int;

axiom {:naming "MyFavoriteAxiom"} {1} (forall i: int :: {f(i)} f(i) == i+1);

var {:description "memory"} {1} $Heap: [ref, name]any;

var {(forall i: int :: true)} Bla: [ref, name]any;

procedure {1} {:use_impl 1} foo(x : int) returns(n : int);

implementation {1} {:id 1} foo(x : int) returns(n : int)
{
  block1: return;
}

implementation {:id 2} {1} foo(x : int) returns(n : int)
{
  block1: return;
}
