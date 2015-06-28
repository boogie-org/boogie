// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Test()
{
  var i: int;

  entry:
    i := 0;
    goto block850;

  block850:
    assert i == 0;
    havoc i;
    goto block850;

}

// The following procedure once exhibited a bug in Boogie's DAG manipulations
procedure TightLoop0()
{
  L:
    assert !true;  // error
    goto L;
}
procedure TightLoop1()
{
  L:
    assert false;  // error
    goto L;
}
procedure TightLoop2()
{
  L:
    assert true;  // cool
    goto L;
}
procedure TightLoop3(b: bool)
{
  L:
    assert b;  // error
    goto L;
}
