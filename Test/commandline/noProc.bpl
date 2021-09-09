// RUN: %parallel-boogie -noProc:b* "%s" > "%t1"
// RUN: %parallel-boogie -proc:a* -noProc:ab "%s" > "%t2"
// RUN: %parallel-boogie -noProc:ba -proc:aa -proc:ab -proc:ba "%s" > "%t3"
// RUN: %diff "%s.1.expect" "%t1"
// RUN: %diff "%s.2.expect" "%t2"
// RUN: %diff "%s.3.expect" "%t3"

procedure aa ()
{
  assert false;
}

procedure ab ()
{
  assert false;
}

procedure ba ()
{
  assert false;
}

procedure bb ()
{
  assert false;
}
