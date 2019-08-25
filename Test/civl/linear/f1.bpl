// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory -doModSetAnalysis "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;
const {:existential true} b0: bool;
const {:existential true} b1: bool;
const {:existential true} b2: bool;
const {:existential true} b3: bool;
const {:existential true} b4: bool;
const {:existential true} b5: bool;
const {:existential true} b6: bool;
const {:existential true} b7: bool;
const {:existential true} b8: bool;

axiom(b0);
axiom(b1);
axiom(b2);
axiom(b3);
axiom(b4);
axiom(b5);
axiom(!b6);
axiom(!b7);
axiom(b8);

function {:inline} {:linear "1"} SetCollector1(x: [int]bool) : [int]bool
{
  x
}

procedure main({:linear_in "1"} x_in: [int]bool) 
  requires b0 ==> x_in == mapconstbool(true);
  requires b1 ==> x_in != mapconstbool(false);
{
   var {:linear "1"} x: [int] bool;
   x := x_in;

   call foo(x);
   
   assert b6 ==> x == mapconstbool(true);
   assert b7 ==> x != mapconstbool(false);
   assert b8 ==> x == mapconstbool(false);
}

procedure foo({:linear_in "1"} x_in: [int]bool)
  requires b2 ==> x_in == mapconstbool(true);
  requires b3 ==> x_in != mapconstbool(false);
{
   var {:linear "1"} x: [int] bool;
   x := x_in;

   assert b4 ==> x == mapconstbool(true);
   assert b5 ==> x != mapconstbool(false);

}
