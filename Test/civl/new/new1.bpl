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

procedure {:atomic} {:layer 1} AtomicSetG(val:int)
modifies g;
{ g := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSetG"} SetG(val:int);

procedure {:atomic} {:layer 1} AtomicIncrG()
modifies g;
{ g := g + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncrG"} IncrG();