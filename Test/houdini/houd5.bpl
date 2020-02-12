// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;
const {:existential true} b4:bool;
const {:existential true} b5:bool;

var array:[int]int;

procedure foo (i:int)
requires b1 ==> i == 0;
requires b2 ==> i > 0;
requires b3 ==> i < 0;
ensures b4 ==> array[i] > 0;
modifies array;
ensures (forall x:int :: {array[x]} x == i || array[x] == old(array)[x]);
{
    array[i] := 2 * i;
}

procedure bar (j:int) returns (result:int)
requires b5 ==> j > 0;
modifies array;
{
    call foo(j);
    result := array[j];	
}

// expected outcome: Correct
// expected assigment: b1->False,b2->true,b3->False,b4->True,b5->True
