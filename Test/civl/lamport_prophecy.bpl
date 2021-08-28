// This is a specification of a simple concurrent algorithm from the paper
// "Teaching Concurrency" by Leslie Lamport. In there are N processes and
// two arrays of length N, x and y. Each process i executes the following
// sequence of statements:
//
//     x[i] := 1;
//     y[i] := x[(i-1) mod N];
//
// The reads and writes of each x[j] are assumed to be atomic. This
// algorithm has the property that once all processes have finished, at
// least one y[j] == 1.

// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

// Number of processes in the algorithm. There needs to be at least one.
const N : int;
axiom N > 0;

function {:inline} IsProcId(i: int) : bool { 0 <= i && i < N }

var {:layer 0, 1} x : [int]int;
var {:layer 0, 3} y : [int]int;

// Prophecy variable p and associated constant c.
// For soundness, p must be havoced in the backward assignment that introduces it.
// We capture the prophecy p in a constant c to make the prophecy available
// even after the havoc of p.
// Initial condition IsProcId(p) && p == c implies the precondition of Main.
var {:layer 1, 1} p : int;
const c: int;

function {:inline} Invariant(i: int, p: int, c: int, x: [int]int) : bool {
  IsProcId(i) &&
  IsProcId(p) &&
  IsProcId(c) &&
  (p == c || x[c] == 1)
}
procedure {:yield_invariant} {:layer 1} Yield(i: int);
requires Invariant(i, p, c, x);

// #############################################################################

// Main procedures that spawns all processes
procedure {:layer 2}{:yields}{:refines "atomic_main_abs"}
{:yield_requires "Yield", 0}
Main()
{
  var i: int;
  i := 0;
  call Yield(i);
  while (i < N)
  invariant {:cooperates} {:layer 1,2} true;
  invariant {:layer 1} (IsProcId(i) || i == N) && IsProcId(p) && IsProcId(c) && (p == c || x[c] == 1);
  invariant {:layer 2} (IsProcId(i) || i == N) && IsProcId(c) && (i <= (c+1) mod N || y[(c+1) mod N] == 1);
  {
    async call {:sync} Proc(i);
    i := i + 1;
  }
}

procedure {:layer 3}{:atomic} atomic_main_abs()
modifies y;
{
  var y': [int]int;
  assert IsProcId(c);
  assume y'[(c+1) mod N] == 1;
  y := y';
}

// #############################################################################

// The specification of a process
procedure {:layer 1}{:yields}{:refines "atomic_update_y_abs"}
{:yield_requires "Yield", i}
Proc(i: int)
{
  call update_x(i);
  call backward_assign_p(i);
  yield;
  assert {:layer 1} x[c] == 1;
  call update_y(i);
}

procedure {:intro} {:layer 1} backward_assign_p(i: int)
modifies p;
{
  assume p == i;
  havoc p;
  assume IsProcId(p);
}

procedure {:layer 2}{:left} atomic_update_y_abs(i: int)
modifies y;
{
  if (i == (c+1) mod N) {
    y[i] := 1;
  } else {
    havoc y;
    assume y == old(y)[i := y[i]];
  }
}

// #############################################################################

// Low-level atomic actions

procedure {:layer 1}{:atomic} atomic_update_x(i: int)
modifies x;
{
  x[i] := 1;
}

procedure {:layer 1}{:atomic} atomic_update_y(i: int)
modifies y;
{
  y[i] := x[(i-1) mod N];
}

procedure {:layer 0}{:yields}{:refines "atomic_update_x"} update_x(i: int);
procedure {:layer 0}{:yields}{:refines "atomic_update_y"} update_y(i: int);

// #############################################################################
