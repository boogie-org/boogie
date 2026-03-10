// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: bool;

procedure one() 
{
    var n: int;
    n := 10;
    while(n >= 1)
    invariant n >= 0;
    measure n;
    {
        n := n - 1;
    }

    n := 100;
    while(n >= 1)
    invariant n >= 0;
    measure n+1;
    measure n;
    {
        n := n - 1;
    }
}
