// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} g: int;
yield right procedure {:layer 1} P()
{
    call A();
}

yield procedure {:layer 0} A();
refines right action {:layer 1} _ {
    g := 1;
}
