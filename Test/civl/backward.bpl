// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Demonstration of backward assignments in atomic actions.
// * For the refinement check of nondet, NONDET is translated into the
//   quantifier-free transition relation "x > 0".
// * For the call to NONDET in foo (at layer 2), NONDET is translated
//   into standard "forward" code.

var {:layer 0,2} x:int;

procedure {:yields }{:layer 2} foo ()
{
  call nondet();
  assert {:layer 2} x > 0;
}

procedure {:atomic} {:layer 2} NONDET ()
modifies x;
{
  var p:int;
  x := p;
  assume x > 0;
  p  := {:backward} x;
}

procedure {:yields} {:layer 1} {:refines "NONDET"} nondet ()
{
  call set(1);
}

procedure {:atomic} {:layer 1} SET (v:int)
modifies x;
{
  x := v;
}

procedure {:yields} {:layer 0} {:refines "SET"} set (v:int);
