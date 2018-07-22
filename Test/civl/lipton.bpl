// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The semaphor operations P and V used in [Lipton 1975]

var {:layer 0,1} c : int;

procedure {:yields}{:layer 1} Thread ()
{
  yield;
  call p();
  call p();
  call v();
  call v();
  yield;
}

procedure {:right} {:layer 1} P ()
modifies c;
{ assume c > 0; c := c - 1; }

procedure {:left} {:layer 1} V ()
modifies c;
{ c := c + 1; }

procedure {:yields}{:layer 0}{:refines "P"} p ();
procedure {:yields}{:layer 0}{:refines "V"} v ();
