// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

yield procedure {:layer 1} one() 
{
    var n: int;
    n := 10;
    while(n >= 1)
    invariant {:yields} true;
    measure {:layer 1} n;
    {
        n := n - 1;
    }
}



