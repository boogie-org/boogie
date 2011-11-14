var g: int;

procedure main() 
modifies g;
{
  g := 0;
  call foo();
  assert g == 1;
}

procedure foo() 
modifies g;
{
  g := g + 1;
}