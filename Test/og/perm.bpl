// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x: int;
function {:builtin "MapConst"} ch_mapconstbool(x: bool) : [int]bool;

function {:builtin "MapOr"} ch_mapunion(x: [int]bool, y: [int]bool) : [int]bool;

function {:inline} {:linear "Perm"} SetCollectorPerm(x: [int]bool) : [int]bool
{
  x
}

procedure Split({:linear_in "Perm"} xls: [int]bool) returns ({:linear "Perm"} xls1: [int]bool, {:linear "Perm"} xls2: [int]bool);
  ensures xls == ch_mapunion(xls1, xls2) && xls1 != ch_mapconstbool(false) && xls2 != ch_mapconstbool(false);


procedure {:yields} {:layer 1} mainE({:linear_in "Perm"} permVar_in: [int]bool)
   free requires {:layer 1} permVar_in == ch_mapconstbool(true);
   free requires {:layer 1} permVar_in[0];
   free requires {:layer 1} x == 0;
{
    var {:linear "Perm"} permVar_out: [int]bool;
    var {:linear "Perm"} permVarOut2: [int]bool;

    permVar_out := permVar_in;

    yield;
    assert {:layer 1} x == 0;
    assert {:layer 1} permVar_out[0];
    assert {:layer 1} permVar_out == ch_mapconstbool(true);

    call permVar_out, permVarOut2 := Split(permVar_out);
    async call foo(permVarOut2);
    yield;
}

procedure {:yields} {:layer 1} foo({:linear_in "Perm"} permVar_in: [int]bool) 
  free requires {:layer 1} permVar_in != ch_mapconstbool(false);
  free requires {:layer 1} permVar_in[1];
  requires {:layer 1} x == 0;
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;
  
  yield;
  assert {:layer 1} permVar_out[1];
  assert {:layer 1} x == 0;

  call Incr();

  yield;
  assert {:layer 1} permVar_out[1];
  assert {:layer 1} x == 1;
}

procedure {:yields} {:layer 0,1} Incr();
ensures {:atomic} |{A: x := x + 1; return true; }|;