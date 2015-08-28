var y: int;
var x: int;

procedure {:inline 1} bar(b: bool)
modifies y;
{
  if (b) {
    y := y + 1;
  } else {
    y := y - 1;
  }
}

procedure {:inline 1} foo() 
modifies x, y;
{
  var b: bool;
  if (b) {
    x := x + 1;
    call bar(true);
    call bar(true);
    x := x + 1;
  } else {
    x := x - 1;
    call bar(false);
    call bar(false);
    x := x - 1;  
  }
}


procedure main()
requires x == y;
ensures x == y;
modifies x, y;
modifies y;
{
  call foo();
  assert x == y;
  call bar(false);
}
