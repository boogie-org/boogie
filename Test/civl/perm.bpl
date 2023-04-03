// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "Perm"} X = int;
var {:layer 0,1} x: int;

yield procedure {:layer 1}
mainE({:linear_in "Perm"} permVar_in: [int]bool)
requires call Yield(permVar_in, 0);
{
    var {:linear "Perm"} permVar_out: [int]bool;

    permVar_out := permVar_in;

    async call foo(permVar_out);
}

yield procedure {:layer 1}
foo({:linear_in "Perm"} permVar_in: [int]bool)
requires call Yield(permVar_in, 0);
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;
  call Incr();
  call Yield(permVar_out, 1);
}

action {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

yield invariant {:layer 1} Yield({:linear "Perm"} p: [int]bool, v: int);
invariant p[1];
invariant x == v;
