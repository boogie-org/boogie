var g:int;

procedure {:yields} {:stable} PB()
modifies g;
{
  g := g + 1;
}

procedure {:yields} PC()
ensures g == old(g);
{
  yield;
  assert g == old(g);
}

procedure {:yields} {:stable} PE()
{
  call PC();
}

procedure {:yields} {:stable} PD()
{
  g := 3;
  call PC();
  assert g == 3;
}

procedure{:entrypoint} {:yields} Main2()
{
  while (*)
  {
    async call PB();
    async call PE();
    async call PD();
  }
}
