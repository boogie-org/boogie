function {:existential true} {:absdomain "ImplicationDomain"} b1(x1: bool, x2: bool) : bool;
function {:existential true} {:absdomain "ImplicationDomain"} b2(x1: bool, x2: bool) : bool;
function {:existential true} {:absdomain "PowDomain"} b3(x1: int) : bool;
function {:existential true} {:absdomain "PowDomain"} b4(x1: bv32) : bool;
function {:existential true} {:absdomain "EqualitiesDomain"} b5(x: int, y: int, z: int, w:int) : bool;

function {:builtin "bvslt"} BV_SLT(x: bv32, y: bv32) : bool;

var x: int;
var flag: bool;

// Test implication domain
procedure foo ()
  modifies x, flag;
{
   flag := true;
   x := 0;
   assert b1(flag, x == 0);
   flag := false;
   assert b2(flag, x == 0);
}

// Test for PowDomain(int)
procedure bar1 ()
  modifies x, flag;
{
   x := 2;
   if(*) { x := 16; }
   assert b3(x);
}

// Test for PowDomain(bv32)
procedure bar2 ()
  modifies x, flag;
{
  var s: bv32;

  s := 2bv32;
  if(*) { s := 16bv32; }
  assert b4(s);
}

// Test for EqualitiesDomain
procedure baz ()
  modifies x, flag;
{
  var y: int;
  var z: int;
  var w: int;

  assume x == y;
  assume x == z;

  if(*) {
    x := x + 1;
    y := y + 1;
  } else {
    x := x + 2;
    y := y + 2;
  }

  assume x == w;

  assert b5(x,y,z,w);
}


