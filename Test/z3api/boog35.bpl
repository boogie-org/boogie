procedure foo1(x: int, y: int)
{
  var a: [int][int]int;

  a[x][y] := 42;

  assert a[x][y] == 42;
}

procedure foo2(x: int, y: int)
{
  var a: [int][int]int;

  a[x][y] := 42;

  assert a[x][y] == 43;
}