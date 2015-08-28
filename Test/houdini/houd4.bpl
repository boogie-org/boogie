// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;
const {:existential true} b4:bool;

var array:[int]int;

procedure foo (i:int)
requires b2 ==> i > 0;
ensures b3 ==> array[i] > 0;
modifies array;
ensures (forall x:int :: {array[x]} x == i || array[x] == old(array)[x]);
{
    array[i] := 2 * i;
}

procedure bar (j:int) returns (result:int)
requires b4 ==> j > 0;
modifies array;
ensures (forall x:int :: {array[x]} (b1 && x == j) || array[x] == old(array)[x]);
{
    call foo(j);
    result := array[j];	
}

// expected outcome: Correct
// expected assignment: b1->True,b2->True,b3->True,b4->True
