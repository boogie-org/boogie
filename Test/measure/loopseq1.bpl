// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure one() 
{
    var n: int;
    n := 0;
    while (n <= 10)
    measure (n+1);
    {
        n := n + 1;
    }
}



    