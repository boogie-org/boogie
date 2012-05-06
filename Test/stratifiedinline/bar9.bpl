var i: int;
var m: int;

procedure {:inline 1} foo(x: int)
modifies i;
{
  if (i < x) {
      i := i + 1;
      call foo(x);
  }
}

procedure {:inline 1} bar1(j: int) 
modifies i;
{
  if (j < 2*m) 
  {
    i := i + 1;
    call bar1(j+1);
  }
}

procedure {:inline 1} bar2(j: int) 
modifies i;
{
  if (j < m) {
    i := i - 1;
    call bar2(j+1);
  }
}

procedure main() 
modifies i;
{
  i := 0;
  if (*) {
    call foo(20);
    i := 0;
    call foo(4);
  } else {
    call bar1(0);
    call bar2(0);
  }
  assert i < 10;
}