// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} P(arr: [int]int)
requires {:layer 1} (forall x: int :: arr[x] == 1);
{
    call foo(arr);
}

>-< action {:layer 1} FOO(arr: [int]int) {
    var x: int;
    assert arr[x] == 1;
}

yield procedure {:layer 0} foo(arr: [int]int);
refines FOO;
