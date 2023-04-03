// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} P(arr: [int]int, i: int)
requires {:layer 1} (forall x: int :: arr[x] == 1);
{
    call foo(arr, i);
}

action {:layer 1} FOO(arr: [int]int, i: int) {
    var x: int;
    x := i;
    havoc x;
    assert arr[x] == 1;
}

yield procedure {:layer 0} foo(arr: [int]int, i: int);
refines FOO;
