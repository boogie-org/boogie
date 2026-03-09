// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure one() 
{
    var n: int;
    n := 0;
    while(n <= 10)
    invariant x > 0;
    invariant n >= 0;
    measure (x+1);
    measure (n);
    {
        n := n + 1;
    }
}



