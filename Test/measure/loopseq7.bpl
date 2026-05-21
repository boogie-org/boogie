// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: bool;

procedure one() 
modifies y;
{
    var n: int;
    n := 10;
    y := true;
    while (n >= 1)
    measure y, n;
    {
        n := n - 1;
        y := false;
    }
}
