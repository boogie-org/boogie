// Example from the paper "Teaching Concurrency" by Leslie Lamport
// http://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf
//
// There are N processes (numbered from 0 to N-1) and two arrays x and y. Each
// process i executes the following sequence of statements:
//
//     x[i] := 1;
//     y[i] := x[(i-1) mod N];
//
// Both lines are assumed to be atomic. This algorithm has the property that
// once all processes have finished, at least one y[j] == 1.

// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Number of processes in the algorithm. There needs to be at least one.
const N : int;
axiom N >= 1;

var {:layer 0,1} x : [int]int;
var {:layer 0,1} y : [int]int;
// Records whether or not a process has finished
var {:layer 1} done : [int]bool;

// #############################################################################

// Main procedures that spawns all processes
yield procedure {:layer 1} Main()
preserves call yield_ind_inv();
{
  var i: int;
  i := 0;
  while (i < N)
  invariant {:layer 1} ind_inv(done, y, x);
  {
    async call Proc(i);
    i := i + 1;
  }
}

// Code of process i
yield procedure {:layer 1}
Proc(i: int)
preserves call yield_ind_inv();
{
  call update_x(i);
  call Yield(i);
  call update_y(i);
  call mark_done(i);
}

// Introduction action that gives meaning to the introduced variable done
link action {:layer 1} mark_done(i: int)
modifies done;
{
  done := done[i:=true];
}

// #############################################################################

// Low-level atomic actions

action {:layer 1} atomic_update_x(i: int)
modifies x;
{
  x[i] := 1;
}

action {:layer 1} atomic_update_y(i: int)
modifies y;
{
  y[i] := x[(i-1) mod N];
}

yield procedure {:layer 0} update_x(i: int);
refines atomic_update_x;

yield procedure {:layer 0} update_y(i: int);
refines atomic_update_y;

// #############################################################################

// Process IDs range from 0 to N-1
function {:inline} in_range(i: int): bool
{
  0 <= i && i < N
}

// The core correctness property of the system. If all the processes
// have finished, there's at least one element of y equal to 1.
function {:inline} safety(done: [int]bool, y: [int]int): bool
{
  (forall i : int :: in_range(i) ==> done[i])
  ==>
  (exists i : int :: in_range(i) && y[i] == 1)
}

// Records that all completed processes have their x equal to 1.
// This is weaker than the corresponding inductive invariant
// conjunct in other tools for the same algorithm.
function {:inline} x_inv(done: [int]bool, x: [int]int): bool
{
  (forall i : int :: in_range(i) && done[i] ==> x[i] == 1)
}

// Inductive invariant. Given the discussion at the top of this file,
// this should probably be considered part of the global inductive
// invariant. I think the assert x[i] == 1 in Proc is also, in some sense,
// part of the global inductive invariant.
function {:inline} ind_inv(done: [int]bool, y: [int]int, x: [int]int): bool
{
  safety(done, y) && x_inv(done, x)
}

yield invariant {:layer 1} yield_ind_inv();
invariant ind_inv(done, y, x);

yield invariant {:layer 1} Yield(i: int);
invariant x[i] == 1;
invariant ind_inv(done, y, x);
