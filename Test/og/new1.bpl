function {:builtin "MapConst"} mapconstbool(x:bool): [int]bool;

var g:int;

var {:linear "Perm"} Permissions: [int]bool;

procedure Allocate_Perm() returns ({:linear "Perm"} xls: [int]bool);
modifies Permissions;
requires Permissions == mapconstbool(true);
ensures xls == mapconstbool(true) && Permissions == mapconstbool(false);

procedure PB({:linear "Perm"} permVar_in:[int]bool)
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

procedure{:entrypoint} Main()
requires Permissions == mapconstbool(true);
{
  var {:linear "Perm"} permVar_out: [int]bool;

  call permVar_out := Allocate_Perm();

  g := 0;
  async call PB(permVar_out);
}
