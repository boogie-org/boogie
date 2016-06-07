// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var y: int;
var x: int;

procedure bar(b: bool)
modifies y;
{
  if (b) {
    y := y + 1;
  } else {
    y := y - 1;
  }
}

procedure foo() 
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


procedure {:entrypoint} main()
modifies x, y;
{
  assume x == y;
  call foo();
  call bar(false);
  assume x != y;
}
