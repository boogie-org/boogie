function {:existential true} b0(x:int): bool;
function {:existential true} b1(x:int): bool;

var g: int;

procedure foo() 
modifies g;
requires b0(g);
ensures b1(g);
{
  if(*) {
    g := g + 1;
    call foo();
  }
}

procedure main()
modifies g;
{
  g := 0;
  if(*) { g := 5; }
  call foo();
}


// Expected: b0(x) = [0,\infty], b1(x) = [0, \infty]
