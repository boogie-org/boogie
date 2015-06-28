// RUN: %boogie -proc:foo -proc:bar "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors
procedure foo()
{
    assume true;
}

procedure bar()
{
    assert true;
}

procedure barz()
{
    assert false;
}
