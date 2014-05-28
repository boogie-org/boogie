// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} mapconstbool(x:bool): [int]bool;

var {:phase 1} g:int;

function {:inline} {:linear "Perm"} SetCollectorPerm(x: [int]bool) : [int]bool
{
  x
}

procedure Allocate_Perm({:linear "Perm"} Permissions: [int]bool) returns ({:linear "Perm"} xls: [int]bool);
requires Permissions == mapconstbool(true);
ensures xls == mapconstbool(true);

procedure {:yields} {:phase 1} PB({:linear "Perm"} permVar_in:[int]bool)
requires {:phase 1} permVar_in[0] && g == 0;
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;

  yield;
  assert {:phase 1} permVar_out[0];
  assert {:phase 1} g == 0;

  call IncrG();

  yield;
  assert {:phase 1} permVar_out[0];
  assert {:phase 1} g == 1;
}

procedure {:yields} {:phase 1} Main({:linear "Perm"} Permissions: [int]bool)
requires {:phase 0,1} Permissions == mapconstbool(true);
{
  var {:linear "Perm"} permVar_out: [int]bool;

  call permVar_out := Allocate_Perm(Permissions);
  yield;
  call SetG(0);
  async call PB(permVar_out);
  yield;
}

procedure {:yields} {:phase 0,1} SetG(val:int);
ensures {:atomic} |{A: g := val; return true; }|;

procedure {:yields} {:phase 0,1} IncrG();
ensures {:atomic} |{A: g := g + 1; return true; }|;
