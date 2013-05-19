var x: int;
function {:builtin "MapConst"} ch_mapconstbool(x: bool) : [int]bool;

function {:builtin "MapOr"} ch_mapunion(x: [int]bool, y: [int]bool) : [int]bool;

procedure Split({:linear "Perm"} xls: [int]bool) returns ({:linear "Perm"} xls1: [int]bool, {:linear "Perm"} xls2: [int]bool);
  ensures xls == ch_mapunion(xls1, xls2) && xls1 != ch_mapconstbool(false) && xls2 != ch_mapconstbool(false);


procedure {:entrypoint} mainE({:linear "Perm"} permVar_in: [int]bool)
   free requires permVar_in == ch_mapconstbool(true);
   free requires permVar_in[0];
  modifies x;
{
    var {:linear "Perm"} permVar_out: [int]bool;
    var {:linear "Perm"} permVarOut2: [int]bool;

    permVar_out := permVar_in;

    assume x == 0;

    yield;
    assert x == 0;
    assert permVar_out[0];
    assert permVar_out == ch_mapconstbool(true);

    call permVar_out, permVarOut2 := Split(permVar_out);
    async call foo(permVarOut2);
}

procedure foo({:linear "Perm"} permVar_in: [int]bool) 
  free requires permVar_in != ch_mapconstbool(false);
  free requires permVar_in[1];
  requires x == 0;
  modifies x;
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;
  
  yield;
  assert permVar_out[1];
  assert x == 0;

  x := x + 1;

  yield;
  assert permVar_out[1];
  assert x == 1;
}

