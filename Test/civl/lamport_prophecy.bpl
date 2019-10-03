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

// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Number of processes in the algorithm. There needs to be at least one.
const N : int;
axiom N > 0;

function {:inline} IsProcId(i: int) : bool { 0 <= i && i < N }

var {:layer 0, 1} x : [int]int;
var {:layer 0, 3} y : [int]int;

// Prophecy variable and associated constant
var {:layer 1, 1} p : int;
const c: int;

function {:inline} Invariant(i: int, p: int, c: int, x: [int]int) : bool {
  IsProcId(i) && 
  IsProcId(p) && 
  IsProcId(c) &&
  (p == c || x[c] == 1)
}

// #############################################################################

// Main procedures that spawns all processes
procedure {:layer 2}{:yields}{:refines "atomic_main_abs"} Main()
requires {:layer 1} IsProcId(p) && IsProcId(c) && p == c;
{
  var i: int;
  i := 0;
  yield;
  assert {:layer 1} Invariant(i, p, c, x);
  while (i < N)
  invariant {:terminates} {:layer 0,1,2} true;
  invariant {:layer 1} (IsProcId(i) || i == N) && IsProcId(p) && IsProcId(c) && (p == c || x[c] == 1);
  invariant {:layer 2} (IsProcId(i) || i == N) && IsProcId(c) && (i <= (c+1) mod N || y[(c+1) mod N] == 1);
  {
    async call Proc(i);
    i := i + 1;
  }
  yield;
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
procedure {:layer 1}{:yields}{:refines "atomic_update_y_abs"} Proc(i: int)
requires {:layer 1} Invariant(i, p, c, x);
{
	yield;
	assert {:layer 1} Invariant(i, p, c, x);
	call update_x(i);
	call backward_assign_p(i);
  yield;
	assert {:layer 1} x[c] == 1;	
  call update_y(i);
  yield;
}

procedure {:layer 1}{:inline 1} backward_assign_p(i: int)
modifies p;
{
	assume p == i;
	havoc p;
  assume IsProcId(p);
}

procedure {:layer 2}{:left} atomic_update_y_abs(i: int)
modifies y;
{
  var v: int;
  if (i == (c+1) mod N) { 
	  y[i] := 1; 
  } else {
    y[i] := v;
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
