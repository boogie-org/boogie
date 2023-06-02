// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: batch_mode

var {:layer 0,2} x:int;

yield procedure {:layer 1} p ()
refines INCR;
{
  call incr(); // Refined action INCR occurred
  call Yield();
  call incr(); // Error: State changed again
}

yield procedure {:layer 1} q ()
refines INCR;
{
  call decr(); // Error: State changed, but not according to INCR
  call Yield();
  call incr(); // Error: State changed again
}

yield procedure {:layer 1} r ()
refines INCR;
{
  call incr();
  call decr(); // SKIP
  call Yield();
  call incr(); // INCR
  call Yield();
  call incr();
  call incr();
  call decr();
  call decr(); // SKIP
}

yield procedure {:layer 1} s ()
refines INCR;
{
  // Error: Refined action INCR never occurs
}

yield procedure {:layer 1} t ()
refines INCR;
{
  call incr();
  call Yield();
  while (*)
  invariant {:yields} true;
  {
    call incr(); // Error: State change inside yielding loop
  }
}

both action {:layer 1,2} INCR ()
modifies x;
{
  x := x + 1;
}

both action {:layer 1,2} DECR ()
modifies x;
{
  x := x - 1;
}

yield procedure {:layer 0} incr ();
refines INCR;

yield procedure {:layer 0} decr ();
refines DECR;

yield invariant {:layer 1} Yield();
