// RUN: %parallel-boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The interval domain (-infer:j) described a variable by a pair of integer bounds. A float has no such
// value to bound: arithmetic rounds, overflows to an infinity and produces NaN; -0.0 and +0.0 share the
// value 0 while Boogie's == on floats is bit identity; and NaN has no value at all. So the domain
// describes no float, and the other Interval*.bpl files here pin consequences of that -- each is a false
// assertion it used to prove.
//
// This file pins the property itself, by printing what is inferred. Every route by which a float could
// acquire bounds is exercised below, and no {:inferred} element mentions one. Re-admitting float tracking
// changes this file even where the re-admission happens to be sound, which no consequence test would
// catch.

// The loop guard is a bool rather than a comparison on purpose: how a negated comparison prints is a
// separate question from what gets inferred, and this file should only pin the latter.
procedure Routes(w: float24e8, more: bool) returns (r: int)
{
  var x: float24e8;
  var y: float24e8;
  var z: float24e8;
  var i: int;

  x := 0x1.8e0f24e8;                        // a literal assignment
  y := x;                                   // a copy from another float
  z := if (x <= y) then x else y;           // an if-then-else, and a comparison
  assume 0x1.0e0f24e8 <= w;                 // a bound from an assume
  assume w != 0x2.0e0f24e8;                 // a disequality
  i := 0;
  while (more)
  {
    z := x + y;                             // arithmetic
    i := i + 1;
  }
  r := if (z == 0NaN24e8) then 1 else 0;    // a NaN
}
