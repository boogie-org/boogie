var g:int;

procedure {:yields} {:stable} PB()
modifies g;
{
  g := g + 1;
}

procedure {:yields} {:stable} PC()
ensures g == 3;
{
  g := 3;
  yield;
  assert g == 3;
}

procedure {:yields} {:stable} PD()
{
  call PC();
  assert g == 3;
  yield;
}

procedure {:entrypoint} {:yields} Main()
{
  while (true)
  {
    par PB() | PC() | PD();
  }
}
