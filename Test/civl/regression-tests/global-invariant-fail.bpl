// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;

invariant {:layer 1} Inv();
preserves x > 0;


yield procedure {:layer 1} P()
preserves call Inv();
{
    call Incr();
    call Decr();
}

yield procedure {:layer 0} Incr();
refines both action {:layer 1} _
{
    x := x + 1;
}

yield procedure {:layer 0} Decr();
refines both action {:layer 1} _
{
    x := x - 1;
}