// RUN: %boogie "-proc:trivial*ZZZ" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors
procedure foo()
{
    assert false;
}

// should not be matched
procedure trivialFooZZX()
{
    assert false;
}

procedure trivialFooZZZ()
{
    assert true;
}

procedure trivialBarZZZ()
{
    assert true;
}
