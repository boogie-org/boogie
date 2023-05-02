// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} P(b: bool, i: int) returns (o: int)
requires {:layer 1} b ==> i >= 0;
{
    call o := bar(b, i);
}

>-< action {:layer 1} BAR(b: bool, i: int) returns (o: int) {
    call o := FOO(b, i);
}

>-< action {:layer 1} FOO(b: bool, i: int) returns (o: int) {
    if (b) {
        o := i + 1;
        assert o > 0;
    }
}

yield procedure {:layer 0} bar(b: bool, i: int) returns (o: int);
refines BAR;

yield procedure {:layer 0} foo(b: bool, i: int) returns (o: int);
refines FOO;
