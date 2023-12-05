// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} X: Lset int;
var {:layer 0,1} B: [int]bool;

right action {:layer 1} Lock(i: int) returns (li: Lval int)
modifies X, B;
{
    assume !B[i];
    li := Lval(i);
    call Lval_Split(X, li);
    B[i] := true;
}

left action {:layer 1} Unlock({:linear_in} li: Lval int)
modifies X, B;
{
    var i: int;
    i := li->val;
    assert B[i];
    call Lval_Put(X, li);
    B[i] := false;
}
