// RUN: %parallel-boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Prints what -infer:j infers for a program that assigns, compares and assumes floats: no {:inferred}
// element mentions a float, and what is known about the ints i and r survives every float statement.
// Unlike the other Interval*.bpl files, this also catches a re-admission of float tracking that is sound.

// A bool loop guard keeps the output independent of how a negated comparison prints.
procedure Routes(w: float24e8, more: bool) returns (r: int)
{
  var x: float24e8;
  var y: float24e8;
  var z: float24e8;
  var i: int;

  i := 0;
  x := 0x1.8e0f24e8;                        // a literal assignment
  y := x;                                   // a copy from another float
  z := if (x <= y) then x else y;           // an if-then-else, and a comparison
  assume 0x1.0e0f24e8 <= w;                 // a bound from an assume
  assume w != 0x2.0e0f24e8;                 // a disequality
  while (more)
  {
    z := x + y;                             // arithmetic
    i := i + 1;
  }
  r := if (z == 0NaN24e8) then 1 else 0;    // a NaN
}
