// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

procedure main({:linear_in} x_in: [int]bool)
  requires b0 ==> x_in == MapConst(true);
  requires b1 ==> x_in != MapConst(false);
{
   var x: [int] bool;
   x := x_in;

   call foo(x);

   assert b6 ==> x == MapConst(true);
   assert b7 ==> x != MapConst(false);
   assert b8 ==> x == MapConst(false);
}

procedure foo({:linear_in} x_in: [int]bool)
  requires b2 ==> x_in == MapConst(true);
  requires b3 ==> x_in != MapConst(false);
{
   var x: [int] bool;
   x := x_in;

   assert b4 ==> x == MapConst(true);
   assert b5 ==> x != MapConst(false);

}
