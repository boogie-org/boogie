// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;
const {:existential true} b4:bool;
const {:existential true} b5:bool;
const {:existential true} b6:bool;
const {:existential true} b7:bool;
const {:existential true} b8:bool;

var array:[int]int;

procedure foo (i:int)
requires b6 ==> i < 0;
requires b5 ==> i == 0;
requires b2 ==> i > 0;
ensures b3 ==> array[i] > 0;
modifies array;
ensures (forall x:int :: {array[x]} x == i || array[x] == old(array)[x]);
{
    array[i] := 2 * i;
}

procedure bar (j:int) returns (result:int)
requires b8 ==> j < 0;
requires b7 ==> j == 0;
requires b4 ==> j > 0;
modifies array;
ensures (forall x:int :: {array[x]} (x == j) || array[x] == old(array)[x]);
ensures (b1 ==> array[j] == old(array)[j]);
{
    call foo(j);
    result := array[j];	
}

var p:int;

procedure main() returns (result: int) 
modifies array;
{
  call result:= bar(p);
}

// expected outcome: Correct
// expected assigment: bi->False forall i
