// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "Perm"} X = int;
var {:layer 0,1} x: int;

procedure {:yields} {:layer 1}  {:yield_requires "Yield", permVar_in, 0}
mainE({:linear_in "Perm"} permVar_in: [int]bool)
{
    var {:linear "Perm"} permVar_out: [int]bool;

    permVar_out := permVar_in;

    async call foo(permVar_out);
}

procedure {:yields} {:layer 1} {:yield_requires "Yield", permVar_in, 0}
foo({:linear_in "Perm"} permVar_in: [int]bool)
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;
  call Incr();
  call Yield(permVar_out, 1);
}

procedure {:atomic} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:yield_invariant} {:layer 1} Yield({:linear "Perm"} p: [int]bool, v: int);
requires p[1];
requires x == v;