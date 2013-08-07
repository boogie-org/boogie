var x:int;

procedure A()
modifies x;
{
  x := x;
}

procedure {:yields} B()
{
  x := 5;
  yield;
  assert x == 5;
}

