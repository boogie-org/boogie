var {:phase 1} x:int;

procedure {:yields} {:phase 0,1} Set(v: int);
ensures {:atomic}
|{A:
  x := v; return true;
}|;

procedure A()
modifies x;
{
  x := x;
}

procedure {:yields} {:phase 1} B()
{
  yield;
  call Set(5);
  yield;
  assert {:phase 1} x == 5;
}

