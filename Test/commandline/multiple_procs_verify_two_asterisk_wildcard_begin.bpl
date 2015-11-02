// RUN: %boogie "-proc:*Bar" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors
procedure foo()
{
    assert false;
}

procedure translucentBar()
{
    assert true;
}

procedure opaqueBar()
{
    assert true;
}
