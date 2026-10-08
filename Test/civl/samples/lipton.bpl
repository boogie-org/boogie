// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The semaphor operations P and V used in [Lipton 1975]

var {:layer 0,1} c : int;

yield procedure {:layer 1} Thread ()
{
  call p();
  call p();
  call v();
  call v();
}

yield procedure {:layer 0} p ();
refines right action {:layer 1} P
{ assume c > 0; c := c - 1; }

yield procedure {:layer 0} v ();
refines left action {:layer 1} V
{ c := c + 1; }
