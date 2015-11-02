// RUN: %boogie "-proc:bar*" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors
procedure foo()
{
    assert false;
}

procedure bar()
{
    assert true;
}

procedure barzzz()
{
    assert true;
}
