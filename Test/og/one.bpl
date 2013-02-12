var x:int;

procedure A()
{
  x := x;
}

procedure B()
{
  x := 5;
  assert{:yield} x == 5;
}

