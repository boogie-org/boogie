// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

yield procedure {:layer 1} one() 
{
    var n: int;
    n := 10;
    while (n >= 1)
    invariant {:layer 1} n >= 0;
    measure {:layer 1} n;
    measure {:layer 2} n+1;
    {
        n := n - 1;
    }
}



