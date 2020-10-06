// RUN: %boogie "%s" -enhancedErrorMessages:1 > "%t"
// RUN: %diff "%s.expect" "%t"

var g: int;

procedure main()
requires g == 0;
ensures g == 2;
modifies g;
{
    call foo();
}

procedure {:inline 1} foo()
modifies g;
{
    assume {:print "g (before increment) = ", g} true;
    g := g + 1;
    assume {:print "g (after increment) = ", g} true;
}
