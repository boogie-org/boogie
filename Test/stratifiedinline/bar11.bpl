// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var x: int;
var y: int;
procedure boogie_si_record_int(x:int);

procedure bar()
modifies y;
{
  y := y + 1;
  call boogie_si_record_int(y);
}

procedure foo() 
modifies x, y;
{
  call boogie_si_record_int(x);
  x := x + 1;
  call bar();
  call bar();
  x := x + 1;
  call boogie_si_record_int(x);
}

procedure {:entrypoint} main()
modifies x, y;
{
  assume x == 0;
  assume x == y;
  call foo();
  assume x == y;
}

