// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} Foo(x: int) returns (y: int)
refines action {:layer 1,2} _ { y := x + 1; }
{
    var z: int;
    z := x;
    if (*) { y := z + 1; }
    else { call z := Bar(z); call y := Foo(z); }
}

yield procedure {:layer 1} Bar(x: int) returns (y: int)
ensures {:layer 1} y == x;
refines action {:layer 1,2} _ { }
{
    y := x;
}