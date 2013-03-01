var g:int;

procedure PB()
{
  g := g + 1;
}

procedure PC()
  ensures g == 3;
{
  g := 3;
  assert{:yield} g == 3;
}

procedure PD()
{
  call PC();
  assert g == 3;
  assert{:yield} true;
}

procedure{:entrypoint} Main()
{
  while (true)
  {
    call{:async} PB();
    call{:async} PC();
    call{:async} PD();
  }
}
