// RUN: %boogie -proc:foo -proc:foo "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

// Although the command line requests two verify this procedure twice we should
// only do try once.
procedure foo()
{
    assume true;
}

procedure bar()
{
    assert false;
}

procedure baz()
{
    assert false;
}
