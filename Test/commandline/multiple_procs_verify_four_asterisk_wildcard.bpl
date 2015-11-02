// RUN: %boogie "-proc:*Bar" "-proc:*Foo" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 4 verified, 0 errors

procedure foo()
{
    assert false;
}

procedure helpfulFoo()
{
    assert true;
}

procedure Foo()
{
    assert true;
}

procedure translucentBar()
{
    assert true;
}

procedure opaqueBar()
{
    assert true;
}
