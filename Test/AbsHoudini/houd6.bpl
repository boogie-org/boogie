// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1():bool;
function {:existential true} b2():bool;
function {:existential true} b3():bool;
function {:existential true} b4():bool;
function {:existential true} b5():bool;
function {:existential true} b6():bool;
function {:existential true} b7():bool;
function {:existential true} b8():bool;
function {:existential true} Assert(): bool;

var array:[int]int;

procedure foo (i:int)
requires b6() || i < 0;
requires b5() || i == 0;
requires b2() || i > 0;
ensures b3() || array[i] > 0;
modifies array;
ensures Assert() || (forall x:int :: {array[x]} x == i || array[x] == old(array)[x]);
{
    array[i] := 2 * i;
}

procedure bar (j:int) returns (result:int)
requires b8() || j < 0;
requires b7() || j == 0;
requires b4() || j > 0;
modifies array;
ensures Assert() || (forall x:int :: {array[x]} (x == j) || array[x] == old(array)[x]);
ensures b1() || array[j] == old(array)[j];
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

// expected assigment: Assert -> false, bi->true forall i
