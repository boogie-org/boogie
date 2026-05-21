// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;

yield procedure {:layer 1} Thread()
requires call YieldNonNeg();
{
    var out: int;
    while (true)
    invariant {:yields} true;
    invariant {:layer 1} call YieldNonNeg();
    measure {:layer 1} x;
    {
        call out := ReadX();
        if ( out <= 0) {
            return;
        }
        call YieldDec(out) | YieldNonNeg();
        call ActionProc();
    }
}

yield procedure {:layer 0} ActionProc();
refines Action;

atomic action {:layer 1} Action()
{
    if (x > 0)
    {
        x := x - 1;
    }
}

yield procedure {:layer 0} ReadX() returns (out: int);
refines ActionReadX;

atomic action {:layer 1} ActionReadX() returns (out: int)
{
  out := x;
}

yield invariant {:layer 1} YieldDec(oldx: int);
preserves oldx >= x;

yield invariant {:layer 1} YieldNonNeg();
preserves x >= 0;
