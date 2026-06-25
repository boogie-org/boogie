// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure PositiveNumber() returns (n: int);
ensures n > 0;

procedure BlockingDecrement(n: int) returns (n': int);
ensures n > 0 && n' == n - 1;

procedure P()
{
    var x: int;
    var s: int;

    call s := PositiveNumber();
    x := 1;
    while (x > 0)
    invariant x >= 0;
    measure x > 0, s;
    {
        if (*) {
            // fair direction of the nondeterministic choice
            call s := PositiveNumber();
            x := 0;
        } else {
            call s := BlockingDecrement(s);
            x := x + 1;
        }
    }
}