// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear} g:int;

procedure A()
{
}

procedure B()
{
  call A();
  assert false;
}
