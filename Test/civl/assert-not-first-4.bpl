// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Verification of P is expected to fail
procedure {:yields} {:layer 1} P(arr: [int]int, i: int)
requires {:layer 1} arr[i] == 1;
{
    call foo(arr, i);
}

procedure {:atomic} {:layer 1} FOO(arr: [int]int, i: int) {
    var x: int;
    x := i;
    havoc x;
    assert arr[x] == 1;
}

procedure {:yields} {:layer 0} {:refines "FOO"} foo(arr: [int]int, i: int);
