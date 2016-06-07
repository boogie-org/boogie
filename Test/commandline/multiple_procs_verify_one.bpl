// RUN: %boogie -proc:foo "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

// Only this procedure should be verified, the others should be ignored
procedure foo()
{
    assume true;
}

// An old version of Boogie just checked if the name passed to ``-proc:``
// occurs somewhere in procedure name which would cause it to try and also
// verify the procedures below.
procedure foo2()
{
    assert false;
}

procedure function_foo()
{
    assert false;
}
