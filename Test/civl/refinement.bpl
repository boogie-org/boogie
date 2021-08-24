// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

procedure {:yields}{:layer 1}{:refines "INCR"} p ()
{
  call incr(); // Refined action INCR occurred
  yield;
  call incr(); // Error: State changed again
}

procedure {:yields}{:layer 1}{:refines "INCR"} q ()
{
  call decr(); // Error: State changed, but not according to INCR
  yield;
  call incr(); // Error: State changed again
}

procedure {:yields}{:layer 1}{:refines "INCR"} r ()
{
  call incr();
  call decr(); // SKIP
  yield;
  call incr(); // INCR
  yield;
  call incr();
  call incr();
  call decr();
  call decr(); // SKIP
}

procedure {:yields}{:layer 1}{:refines "INCR"} s ()
{
  // Error: Refined action INCR never occurs
}

procedure {:yields}{:layer 1}{:refines "INCR"} t ()
{
  call incr();
  yield;
  while (*)
  invariant {:layer 1}{:yields} true;
  {
    call incr(); // Error: State change inside yielding loop
  }
}

procedure {:both} {:layer 1,2} INCR ()
modifies x;
{
  x := x + 1;
}

procedure {:both} {:layer 1,2} DECR ()
modifies x;
{
  x := x - 1;
}

procedure {:yields} {:layer 0} {:refines "INCR"} incr ();
procedure {:yields} {:layer 0} {:refines "DECR"} decr ();
