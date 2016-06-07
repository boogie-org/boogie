// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} mapconstbool(x:bool): [int]bool;

var {:layer 0,1} g:int;

function {:inline} {:linear "Perm"} SetCollectorPerm(x: [int]bool) : [int]bool
{
  x
}

procedure {:yields} {:layer 1} PB({:linear_in "Perm"} permVar_in:[int]bool)
requires {:layer 1} permVar_in[0] && g == 0;
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;

  yield;
  assert {:layer 1} permVar_out[0];
  assert {:layer 1} g == 0;

  call IncrG();

  yield;
  assert {:layer 1} permVar_out[0];
  assert {:layer 1} g == 1;
}

procedure {:yields} {:layer 1} Main({:linear_in "Perm"} Permissions: [int]bool)
requires {:layer 1} Permissions == mapconstbool(true);
{
  yield;
  call SetG(0);
  async call PB(Permissions);
  yield;
}

procedure {:yields} {:layer 0,1} SetG(val:int);
ensures {:atomic} |{A: g := val; return true; }|;

procedure {:yields} {:layer 0,1} IncrG();
ensures {:atomic} |{A: g := g + 1; return true; }|;
