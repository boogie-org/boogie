// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} Assert() : bool;
function {:existential true} b1():bool;
function {:existential true} b2(x:bool):bool;
function {:existential true} b3(x:bool):bool;
function {:existential true} b4(x:bool):bool;

var array:[int]int;

procedure foo (i:int)
requires b2(i > 0);
ensures b3(array[i] > 0);
modifies array;
ensures Assert() || (forall x:int :: {array[x]} x == i || array[x] == old(array)[x]);
{
    array[i] := 2 * i;
}

procedure bar (j:int) returns (result:int)
requires b4(j > 0);
modifies array;
ensures Assert() || (forall x:int :: {array[x]} (!b1() && x == j) || array[x] == old(array)[x]);
{
    call foo(j);
    result := array[j];	
}

// expected assignment: Assert = false, b1(x) = false, b2(x) = false, b3(x) = false, b4(x) = false
