// RUN: %boogie -stratifiedInline:1 -vc:i -nonUniformUnfolding "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var i: int;
var m: int;

procedure foo(x: int)
modifies i;
{
  if (i < x) {
      i := i + 1;
      call foo(x);
  }
}

procedure bar1(j: int) 
modifies i;
{
  if (j < 2*m) 
  {
    i := i + 1;
    call bar1(j+1);
  }
}

procedure bar2(j: int) 
modifies i;
{
  if (j < m) {
    i := i - 1;
    call bar2(j+1);
  }
}

procedure {:entrypoint} main() 
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
  assume !(i < 10);
}
