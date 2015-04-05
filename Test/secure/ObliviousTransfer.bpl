type T = bv2;
function {:inline} xor(a: bool, b: bool) returns (bool)  { (!a && b) || (a && !b) }
function {:bvbuiltin "bvxor"} xorT(p1: T, p2: T) : T;

// Oblivious Transfer
procedure ObliviousTransfer_A(
    {:visible} m0: T, {:visible} m1: T,
    {:hidden} c: bool)
returns ({:hidden} m: T, 
    {:visible} m0p: T, {:visible} m1p: T,
    {:visible} x: bool, 
    {:visible} y: T, {:visible} z: T
    )
// spec
ensures (m == if c then m1 else m0);
// Implementation
{
   var {:hidden} mp: T; 
   var {:hidden} cp: bool; 

   havoc cp;
   havoc m0p, m1p;
   mp := if cp then m0p else m1p;

   x := xor(c, cp);
   y := xorT(m0, if x then m0p else m1p);
   z := xorT(m1, if x then m1p else m0p);
  
   m := xorT(if c then z else y, mp);
}


// Oblivious Transfer
procedure ObliviousTransfer_B(
    {:hidden} m0: T, {:hidden} m1: T,
    {:visible} c: bool)
returns ({:visible} m: T, 
    {:visible} mp: T, {:visible} cp: bool,
    {:visible} x: bool, 
    {:visible} y: T, {:visible} z: T
    )
// spec
ensures (m == if c then m1 else m0);
// Implementation
{
   var {:hidden} m0p, m1p: T; 

   havoc cp;
   havoc m0p, m1p;
   mp := if cp then m0p else m1p;

   x := xor(c, cp);
   y := xorT(m0, if x then m0p else m1p);
   z := xorT(m1, if x then m1p else m0p);
  
   m := xorT(if c then z else y, mp);
   //y := m0;
}

// Oblivious Transfer
procedure ObliviousTransfer_X(
    {:hidden} m0: T, {:hidden} m1: T,
    {:hidden} c: bool)
returns ({:hidden "B"} m: T)
// spec
ensures (m == if c then m1 else m0);
// Implementation
{
   var {:hidden} m0p, m1p: T; 
   var {:hidden} mp: T; 
   var {:hidden} cp: bool; 

   var {:hidden} x: bool; 
   var {:hidden} y, z: T; 

   havoc cp;
   havoc m0p, m1p;
   mp := if cp then m0p else m1p;

   x := xor(c, cp);
   y := xorT(m0, if x then m0p else m1p);
   z := xorT(m1, if x then m1p else m0p);
  
   m := xorT(if c then z else y, mp);
}


