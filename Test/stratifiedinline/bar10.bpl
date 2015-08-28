// RUN: %boogie -stratifiedInline:1 -vc:i -nonUniformUnfolding "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var i: int;
var m: int;

procedure foo()
modifies i;
{
  if (i < 20) {
      i := i + 1;
      call foo();
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
  call bar1(0);
  call bar2(0);
  i := 0;
  call foo();
  assume !(i < 10);
}
