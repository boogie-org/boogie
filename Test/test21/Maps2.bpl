// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
// XFAIL: *

type T;

function f(x : [T][int]int) returns (int);

axiom (forall x:[T][int]int ::  {f(x)}
               (exists t:T :: x[t][13] == 42) ==> f(x) == 5);

procedure P() returns () {
  var x : [T][int]int, t : T;

  x[t] := x[t][13 := 42];

  assert f(x) == 5;
}


type name;

function Field(int) returns (name);
function Unified([name][int]int) returns ([int]int);

axiom(forall M:[name][int]int, x:int, y:int :: {Unified(M[Field(x) := M[Field(x)][x := y]])}
                     Unified(M[Field(x) := M[Field(x)][x := y]]) == Unified(M)[x := y]);
