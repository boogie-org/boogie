// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yields} {:layer 1} P(b: bool, i: int) returns (o: int)
requires {:layer 1} b ==> i >= 0;
{
    call o := bar(b, i);
}

procedure {:atomic} {:layer 1} BAR(b: bool, i: int) returns (o: int) {
    call o := FOO(b, i);
}

procedure {:atomic} {:layer 1} FOO(b: bool, i: int) returns (o: int) {
    if (b) {
        o := i + 1;
        assert o > 0;
    }
}

procedure {:yields} {:layer 0} {:refines "BAR"} bar(b: bool, i: int) returns (o: int);
procedure {:yields} {:layer 0} {:refines "FOO"} foo(b: bool, i: int) returns (o: int);
