var g:int;

procedure PB()
{
  g := g + 1;
}

procedure PC()
  ensures g == old(g);
{
  assert{:yield} g == old(g);
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
    call{:async} PB();
    call{:async} PC();
    call{:async} PD();
  }
}
