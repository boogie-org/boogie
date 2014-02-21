function {:builtin "MapConst"} mapconstbool(x:bool): [int]bool;

var g:int;

function {:inline} {:linear "Perm"} SetCollectorPerm(x: [int]bool) : [int]bool
{
  x
}

procedure Allocate_Perm({:linear "Perm"} Permissions: [int]bool) returns ({:linear "Perm"} xls: [int]bool);
requires Permissions == mapconstbool(true);
ensures xls == mapconstbool(true);

procedure {:yields} {:stable} PB({:linear "Perm"} permVar_in:[int]bool)
requires permVar_in[0] && g == 0;
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;

  yield;
  assert permVar_out[0];
  assert g == 0;

  g := g + 1;

  yield;
  assert permVar_out[0];
  assert g == 1;
}

procedure{:entrypoint} {:yields} Main({:linear "Perm"} Permissions: [int]bool)
requires Permissions == mapconstbool(true);
{
  var {:linear "Perm"} permVar_out: [int]bool;

  call permVar_out := Allocate_Perm(Permissions);

  g := 0;
  async call PB(permVar_out);
}
