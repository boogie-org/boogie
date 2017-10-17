// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x: int;
function {:builtin "MapConst"} ch_mapconstbool(x: bool) : [int]bool;

function {:builtin "MapOr"} ch_mapunion(x: [int]bool, y: [int]bool) : [int]bool;

function {:inline} {:linear "Perm"} SetCollectorPerm(x: [int]bool) : [int]bool
{
  x
}

procedure {:yields} {:layer 1} mainE({:linear_in "Perm"} permVar_in: [int]bool)
   requires {:layer 1} permVar_in == ch_mapconstbool(true);
   requires {:layer 1} x == 0;
{
    var {:linear "Perm"} permVar_out: [int]bool;

    permVar_out := permVar_in;

    yield;
    assert {:layer 1} x == 0;
    assert {:layer 1} permVar_out == ch_mapconstbool(true);

    async call foo(permVar_out);
    yield;
}

procedure {:yields} {:layer 1} foo({:linear_in "Perm"} permVar_in: [int]bool)
  requires {:layer 1} permVar_in != ch_mapconstbool(false);
  requires {:layer 1} permVar_in[1];
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

procedure {:atomic} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();