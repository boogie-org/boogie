// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;

yield procedure {:layer 0} Incr();
refines both action {:layer 1} _ {
    x := x + 1;
}

yield right procedure {:layer 1} A()
modifies x;
ensures {:layer 1} x == old(x) + 2;
{
    call Incr() | Incr();
}

yield right procedure {:layer 1} B()
modifies x;
ensures {:layer 1} x == old(x) + 4;
{
    call A() | A();
}

yield right procedure {:layer 1} R1(i: int)
modifies x;
requires {:layer 1} 0 <= i;
ensures {:layer 1} x == old(x) + i;
{
    if (i == 0) {
        return;
    }
    call Incr() | R1(i-1);
}

yield right procedure {:layer 1} R2(i: int)
modifies x;
requires {:layer 1} 0 <= i;
ensures {:layer 1} x == old(x) + i;
{
    if (i == 0) {
        return;
    }
    call R2(i-1) | Incr();
}

yield right procedure {:layer 1} M1(i: int)
modifies x;
requires {:layer 1} 0 <= i;
ensures {:layer 1} x == old(x) + i;
{
    if (i == 0) {
        return;
    }
    call Incr() | M2(i-1);
}

yield right procedure {:layer 1} M2(i: int)
modifies x;
requires {:layer 1} 0 <= i;
ensures {:layer 1} x == old(x) + i;
{
    if (i == 0) {
        return;
    }
    call M1(i-1) | Incr();
}