// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure proc()
{
    var x: int;
    var s: int; 
    var v : int; 

    assume s > 0;

    x := -1;

    while (true)
    invariant x <= 0;
    measure (if x < 0 then 1 else 0), s;
    {
        if (x >= 0) {
            break;
        }
        if (*) {
            assume s > 0;
            x := x - 1;

            s := s - 1;
        }
        else {
            x := 0;
        }
    }
}
