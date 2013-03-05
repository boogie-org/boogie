var g:int;

procedure PB()
{
  g := g + 1;
}

procedure PC()
  ensures g == 3;
{
  g := 3;
  yield;
  assert g == 3;
}

procedure PD()
{
  call PC();
  assert g == 3;
  yield;
}

procedure{:entrypoint} Main()
{
  while (true)
  {
    call PB() | PC() | PD();
  }
}
