var x:int;

procedure A()
{
  x := x;
}

procedure B()
{
  x := 5;
  yield;
  assert x == 5;
}

