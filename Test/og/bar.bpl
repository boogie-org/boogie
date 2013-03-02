var g:int;

procedure PB()
{
  g := g + 1;
}

procedure PC()
  ensures g == old(g);
{
  yield;
  assert g == old(g);
}

procedure PD()
{
  g := 3;
  call PC();
  assert g == 3;
}

procedure{:entrypoint} Main2()
{
  while (true)
  {
    async call PB();
    async call PC();
    async call PD();
  }
}
