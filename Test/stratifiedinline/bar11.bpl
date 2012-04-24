var x: int;
var y: int;
procedure boogie_si_record_int(x:int);

procedure {:inline 1} bar()
modifies y;
{
  y := y + 1;
  call boogie_si_record_int(y);
}

procedure {:inline 1} foo() 
modifies x, y;
{
  call boogie_si_record_int(x);
  x := x + 1;
  call bar();
  call bar();
  x := x + 1;
  call boogie_si_record_int(x);
}

procedure main()
requires x == 0;
requires x == y;
ensures x != y;
modifies x, y;
{

  call foo();
}

