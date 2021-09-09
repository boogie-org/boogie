// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Contrived example to illustrate the injection of lemmas into commutativity checks

var {:layer 0,1} x : int;

function f(x: int, i: int) : int;

function {:inline}
{:lemma}
{:commutativity "inc", "inc"}
lemma (x: int, first_i: int, second_i: int) : bool
{
  f(x, first_i) == x + first_i &&
  f(x + first_i, second_i) == x + first_i + second_i &&
  f(x, second_i) == x + second_i &&
  f(x + second_i, first_i) == x + second_i + first_i
}

procedure {:right} {:layer 1} inc (i: int)
modifies x;
{ x := f(x, i); }
