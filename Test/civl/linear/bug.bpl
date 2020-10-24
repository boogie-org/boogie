// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear ""} X = int;

var {:linear ""} g:int;

procedure A()
{
}

procedure B()
{
  call A();
  assert false;
}
