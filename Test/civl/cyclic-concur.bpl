// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x : int;

procedure {:atomic} {:layer 2} MAIN ()
modifies x;
{
  havoc x;
  assume x > old(x) && (x - old(x)) mod 6 == 0;
}


procedure {:yields} {:layer 1} {:refines "MAIN"} main ()
{
  async call {:sync} a();
}

procedure {:yields} {:layer 1} {:left} {:cooperates} a ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 0;
{
  call add(1);
  async call {:sync} b();
}

procedure {:yields} {:layer 1} {:left} {:cooperates} b ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 5;
{
  call add(2);
  async call {:sync} c();
}

procedure {:yields} {:layer 1} {:left} {:cooperates} c ()
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

procedure {:left} {:layer 1} ADD (n:int)
modifies x;
{ x := x + n; }

procedure {:yields} {:layer 0} {:refines "ADD"} add (n:int);
