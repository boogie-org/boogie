// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:yields} {:layer 0,1} Set(v: int);
ensures {:atomic}
|{A:
  x := v; return true;
}|;

procedure {:yields} {:layer 1} B()
{
  yield;
  call Set(5);
  yield;
  assert {:layer 1} x == 5;
}

