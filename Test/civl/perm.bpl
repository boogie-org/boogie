// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "Perm"} X = int;
var {:layer 0,1} x: int;

procedure {:yields} {:layer 1} mainE({:linear_in "Perm"} permVar_in: [int]bool)
   requires {:layer 1} permVar_in == MapConst(true);
   requires {:layer 1} x == 0;
{
    var {:linear "Perm"} permVar_out: [int]bool;

    permVar_out := permVar_in;

    async call foo(permVar_out);
}

procedure {:yields} {:layer 1} foo({:linear_in "Perm"} permVar_in: [int]bool)
  requires {:layer 1} permVar_in != MapConst(false);
  requires {:layer 1} permVar_in[1];
  requires {:layer 1} x == 0;
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;

  call Incr();

  yield;
  assert {:layer 1} permVar_out[1];
  assert {:layer 1} x == 1;
}

procedure {:atomic} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();
