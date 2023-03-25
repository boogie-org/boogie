// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x : int;

action {:layer 2} MAIN ()
modifies x;
{
  havoc x;
  assume x > old(x) && (x - old(x)) mod 6 == 0;
}


yield procedure {:layer 1} main () refines MAIN
{
  async call {:sync} a();
}

yield <- procedure {:layer 1} a ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 0;
{
  call add(1);
  async call {:sync} b();
}

yield <- procedure {:layer 1} b ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 5;
{
  call add(2);
  async call {:sync} c();
}

yield <- procedure {:layer 1} c ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 3;
{
  call add(3);
  if (*) {
    async call {:sync} a();
  }
}

// ###########################################################################
// Low level atomic actions

<- action {:layer 1} ADD (n:int)
modifies x;
{ x := x + n; }

yield procedure {:layer 0} add (n:int) refines ADD;
