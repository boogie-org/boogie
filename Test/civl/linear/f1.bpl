// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "1"} X = int;
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
  requires b0 ==> x_in == MapConst(true);
  requires b1 ==> x_in != MapConst(false);
{
   var {:linear "1"} x: [int] bool;
   x := x_in;

   call foo(x);

   assert b6 ==> x == MapConst(true);
   assert b7 ==> x != MapConst(false);
   assert b8 ==> x == MapConst(false);
}

procedure foo({:linear_in "1"} x_in: [int]bool)
  requires b2 ==> x_in == MapConst(true);
  requires b3 ==> x_in != MapConst(false);
{
   var {:linear "1"} x: [int] bool;
   x := x_in;

   assert b4 ==> x == MapConst(true);
   assert b5 ==> x != MapConst(false);

}
