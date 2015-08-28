// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function foo(x:int) : int
  { if x <= 0 then 1 else foo(x - 1) + 2 }

procedure bar()
{
  assert foo(0) == 1;
  assert foo(1) == 3;
  assert foo(2) == 5;
}
