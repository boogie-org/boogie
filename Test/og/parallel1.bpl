// RUN: %boogie -noinfer %s > %t
// RUN: %diff %s.expect %t
var {:phase 1} g:int;

procedure {:yields} {:phase 1} PB()
{
  yield;
  call Incr();
  yield;
}

procedure {:yields} {:phase 0,1} Incr();
ensures {:atomic}
|{A:
  g := g + 1; return true;
}|;

procedure {:yields} {:phase 0,1} Set(v: int);
ensures {:atomic}
|{A:
  g := v; return true;
}|;

procedure {:yields} {:phase 1} PC()
ensures {:phase 1} g == 3;
{
  yield;
  call Set(3);
  yield;
  assert {:phase 1} g == 3;
}

procedure {:yields} {:phase 1} PD()
{
  call PC();
  assert {:phase 1} g == 3;
  yield;
}

procedure {:yields} {:phase 1} Main()
{
  yield;
  while (*)
  {
    par PB() | PC() | PD();
  }
}
