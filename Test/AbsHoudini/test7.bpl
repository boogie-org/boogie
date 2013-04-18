function {:existential true} Assert() : bool;

var g: int;

procedure main() 
modifies g;
{
  g := 0;
  call foo();
  assert Assert() || g == 1;
}

procedure foo() 
modifies g;
{
  g := g + 1;
}

// Expected: Assert = false
