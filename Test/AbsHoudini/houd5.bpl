// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1(x:bool):bool;
function {:existential true} b2(x:bool):bool;
function {:existential true} b3(x:bool):bool;
function {:existential true} b4(x:bool):bool;
function {:existential true} b5():bool;
function {:existential true} Assert():bool;

var array:[int]int;

procedure foo (i:int)
requires b1(i == 0);
requires b2(i > 0);
requires b3(i < 0);
ensures b4(array[i] > 0);
modifies array;
ensures Assert() || (forall x:int :: {array[x]} x == i || array[x] == old(array)[x]);
{
    array[i] := 2 * i;
}

procedure bar (j:int) returns (result:int)
requires b5() || (j > 0);
modifies array;
{
    call foo(j);
    result := array[j];	
}

// expected assigment: assert = false, b1(x) = !x, b2(x) = x, b3(x) = !x, b4(x) = x, b5() = false
