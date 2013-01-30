var head: X;
var tail: X;
var {:linear "Mem"} D: [X]bool;
var Next:[X]X;
const nil: X;

procedure malloc() returns (x: X, {:linear "Mem"} M: [X]bool);
ensures M == MapConstBool(false)[x := true];

procedure Join({:linear "Mem"} A: [X]bool);
modifies D;
ensures MapOr(old(D), A) == D;

procedure one()
requires D[head] && D[tail];
requires (forall d: X :: {D[d]} D[d] ==> D[Next[d]] || d == tail);
ensures D[head] && D[tail];
ensures (forall d: X :: {D[d]} D[d] ==> D[Next[d]] || d == tail);
ensures head != tail;
{
    var x: X;
    var {:linear "Mem"} M: [X]bool;

    call x, M := malloc();
    call Join(M);
    Next[tail] := x;
    tail := x;
    Next[tail] := nil;
}

procedure two()
requires head != tail;
requires D[head] && D[tail];
requires (forall d: X :: {D[d]} D[d] ==> D[Next[d]] || d == tail);
ensures (forall d: X :: {D[d]} D[d] ==> D[Next[d]] || d == tail);
ensures D[head] && D[tail];
{
    head := Next[head];
}
