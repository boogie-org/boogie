// RUN: %parallel-boogie "%s" -normalizeNames:1 -enhancedErrorMessages:1 > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(i: int) returns (o: int)
requires i == 42;
ensures o < 44;
{
    assume {:print "line 22"} {:print "i = ", i} true;
    o := i;
    if (*) {
        assume {:print "line 25"} {:print "o = ", o} true;
        o := o + 1;
    }
    if (*) {
        assume {:print "line 29"} {:print "o = ", o} true;
        o := {:print "just to show off"} o + 1;
    }
    assert {:print "exit of foo"} {:print "o = ", o} true;
}

procedure bar(i: int) returns (o: int)
requires i == 42;
ensures o < 44;
{
    assume {:print "line 22"} {:print "i = ", i} true;
    o := i;
    if (*) {
        call o := FirstIncr(o);
    }
    if (*) {
        call o := SecondIncr(o);
    }
    assert {:print "exit of foo"} {:print "o = ", o} true;
}

procedure {:inline 1} FirstIncr(o: int) returns (o': int)
{
    assume {:print "line 25"} {:print "o = ", o} true;
    o' := o + 1;
}

procedure {:inline 1} SecondIncr(o: int) returns (o': int)
{
    assume {:print "line 29"} {:print "o = ", o} true;
    o' := {:print "just to show off"} o + 1;
}

