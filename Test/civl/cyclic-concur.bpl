// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x : int;

procedure {:atomic} {:layer 2} MAIN ()
modifies x;
{
  var x':int;
  assume x' > x && (x' - x) mod 6 == 0;
  x := x';
}


procedure {:yields} {:layer 1} {:refines "MAIN"} main ()
{
  yield;
  async call a();
  yield;
}

procedure {:yields} {:layer 1} {:left} {:terminates} a ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 0;
{
  call dummy();
  call add(1);
  async call b();
  call dummy();
}

procedure {:yields} {:layer 1} {:left} {:terminates} b ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 5;
{
  call dummy();
  call add(2);
  async call c();
  call dummy();
}

procedure {:yields} {:layer 1} {:left} {:terminates} c ()
modifies x;
ensures {:layer 1} x > old(x) && (x - old(x)) mod 6 == 3;
{
  call dummy();
  call add(3);
  if (*) {
    async call a();
  }
  call dummy();
}

procedure {:yields} {:layer 0} dummy ();

// ###########################################################################
// Low level atomic actions

procedure {:left} {:layer 1} ADD (n:int)
modifies x;
{ x := x + n; }

procedure {:yields} {:layer 0} {:refines "ADD"} add (n:int);
