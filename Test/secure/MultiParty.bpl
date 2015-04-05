// Type for data
type T = bv4;
const N: int; axiom N == 4;
const one: T; axiom one == 1bv4;

// helper operations
function {:inline} xor(a: bool, b: bool) returns (bool)  { (!a && b) || (a && !b) }
function {:bvbuiltin "bvxor"} xorT(p1: T, p2: T) : T;
function {:bvbuiltin "bvult"} bv2lt(p1: bv2, p2: bv2) : bool;
function {:bvbuiltin "bvult"} bvlt(p1: T, p2: T) : bool; // unsigned less than
function {:bvbuiltin "bvlshr"} shiftrightAny(p1: T, n: T) : T; // shift right
function {:inline} shiftright(p1: T) : T { shiftrightAny(p1, one) }
function bv2bool(x: bv1) : bool { if (x == 0bv1) then false else true }

// Oblivious Transfer
procedure ObliviousTransfer(
    {:visible "A"} m0: T, {:visible "A"} m1: T,
    {:visible "B"} c: bool)
returns ({:visible "B"} m: T)
// spec
ensures (m == if c then m1 else m0);
// Implementation
{
   var {:visible "A"} m0p, m1p: T; 
   var {:visible "B"} mp: T; 
   var {:visible "B"} cp: bool; 

   var x: bool; 
   var y, z: T; 

   havoc cp;
   havoc m0p, m1p;
   mp := if cp then m0p else m1p;

   x := xor(c, cp);
   y := xorT(m0, if x then m0p else m1p);
   z := xorT(m1, if x then m1p else m0p);
  
   m := xorT(if c then z else y, mp);
}

// Oblivious Transfer for Bools
procedure ObliviousTransferBool(
    {:visible "A"} m0: bool, {:visible "A"} m1: bool,
    {:visible "B"} c: bool)
returns ({:visible "B"} m: bool);
// spec
free ensures (m == if c then m1 else m0);


// Lover's Protocol 1
procedure LoversProtocol1(
    {:visible "A"} a: bool, {:visible "B"} b: bool)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
// spec
ensures xor(ap, bp) == (a && b);
{
  havoc ap;
  call bp := ObliviousTransferBool(ap, xor(a, ap), b);
}

// Lover's Protocol 1 Modified
procedure LoversProtocol1Modified(
    {:visible "A"} a: bool, {:visible "B"} b: bool)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
// spec
ensures xor(ap, bp) == xor(a, b);
{
  var {:visible "B"} bpp: bool;

  havoc ap;
  bpp := xor(ap, a);
  bp := xor(bpp, b);
}

// Lover's Protocol 2
procedure LoversProtocol2(
    {:visible "A"} aA: bool, {:visible "A"} bA: bool,
    {:visible "B"} aB: bool, {:visible "B"} bB: bool)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
// spec
ensures xor(ap, bp) == (xor(aA, aB) && xor(bA, bB));
{
   var {:visible "A"} rA, wA: bool;
   var {:visible "B"} rB, wB: bool;

   call rA, wA := LoversProtocol1(aA, bB);
   call rB, wB := LoversProtocol1(aB, bA);

   ap := xor(xor(aA && bA, rA), wA);
   bp := xor(xor(wB, rB), aB && bB);
}

// While functionally correct, this isn't secure
procedure Incorrect(
    {:visible "A"} a: bool, {:visible "B"} b: bool)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
// spec
ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure TwoBitMillionaires(
    {:visible "A"} a: bv2, {:visible "B"} b: bv2)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
ensures xor(ap, bp) == bv2lt(a, b);
{
   var {:visible "A"} a0, a1: bool;
   var {:visible "B"} b0, b1: bool;

   // Extract bits
   a0 := bv2bool(a[1:0]);
   a1 := bv2bool(a[2:1]);
   b0 := bv2bool(b[1:0]);
   b1 := bv2bool(b[2:1]);

   call ap, bp := TwoBitMillionairesExplicit(a0, a1, b0, b1);
}

procedure TwoBitMillionairesExplicit(
    {:visible "A"} a0: bool, {:visible "A"} a1: bool, 
    {:visible "B"} b0: bool, {:visible "B"} b1: bool)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
ensures xor(ap, bp) == xor(!a1 && b1, (a1 == b1) && (!a0 && b0));
{
   var {:visible "A"} aA, bA, wA: bool;
   var {:visible "B"} aB, bB, wB: bool;


   call aA, aB := LoversProtocol1(!a1, b1);
   call wA, wB := LoversProtocol1(!a0, b0);
   call bA, bB := LoversProtocol2(!a1, wA, b1, wB);

   ap := xor(aA, bA);
   bp := xor(aB, bB);
}

procedure TwoBitMillionairesExplicitModified(
    {:visible "A"} a0: bool, {:visible "A"} a1: bool, 
    {:visible "B"} b0: bool, {:visible "B"} b1: bool)
returns ({:visible "A"} ap: bool, {:visible "B"} bp: bool)
ensures xor(ap, bp) == xor(!a1 && b1, (a1 == b1) && xor(a0, b0));
{
   var {:visible "A"} aA, bA, wA: bool;
   var {:visible "B"} aB, bB, wB: bool;


   call aA, aB := LoversProtocol1(!a1, b1);
   call wA, wB := LoversProtocol1Modified(a0, b0);
   call bA, bB := LoversProtocol2(!a1, wA, b1, wB);

   ap := xor(aA, bA);
   bp := xor(aB, bB);
}

procedure NBitMillionaires(
    {:visible "A"} a: T, {:visible "B"} b: T)
returns ({:visible "A"} la: bool, {:visible "B"} lb: bool)
ensures xor(la, lb) == bvlt(a, b);
{
   var n: int;

   var {:visible "A"} aleft: T;
   var {:visible "B"} bleft: T;
   var {:visible "A"} an: bool;
   var {:visible "B"} bn: bool;

   n := 0;
   aleft := a;
   bleft := b;

   havoc la, lb; assume xor(la, lb) == false;
   while (n < N)
     invariant true;
   {
      an := bv2bool(aleft[1:0]);
      bn := bv2bool(bleft[1:0]);
      aleft := shiftright(aleft);
      bleft := shiftright(bleft);

      call la, lb := TwoBitMillionairesExplicitModified(la, an, lb, bn);
      n := n + 1;
   }
}

