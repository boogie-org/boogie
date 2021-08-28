// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Permission types
type {:datatype} AB;
function {:constructor} AB (x:int) : AB;
type {:datatype} A;
function {:constructor} A (x:int) : A;
type {:datatype} B;
function {:constructor} B (x:int) : B;

// Linear collectors
type {:linear "perm"} Perm = int;

function {:inline} {:linear "perm"} ABCollector(ab: AB) : [int]bool
{ MapConst(false)[x#AB(ab) := true][-x#AB(ab) := true] }
function {:inline} {:linear "perm"} ABSetCollector(abs: [AB]bool) : [int]bool
{ (lambda i:int :: abs[AB(i)] || abs[AB(-i)]) }

function {:inline} {:linear "perm"} ACollector(a: A) : [int]bool
{ MapConst(false)[x#A(a) := true] }
function {:inline} {:linear "perm"} ASetCollector(as: [A]bool) : [int]bool
{ (lambda i:int :: as[A(i)]) }

function {:inline} {:linear "perm"} BCollector(b: B) : [int]bool
{ MapConst(false)[-x#B(b) := true] }
function {:inline} {:linear "perm"} BSetCollector(bs: [B]bool) : [int]bool
{ (lambda i:int :: bs[B(-i)]) }

function {:inline} bToA (b:B) : A { A(x#B(b)) }

// Global variables
var {:layer 0,1} x:int;
var {:layer 0,1}{:linear "perm"} As:[A]bool;
var {:layer 0,1}{:linear "perm"} Bs:[B]bool;

// Invariant
procedure {:yield_invariant}{:layer 1} Inv ();
requires x >= cardAs(As) - cardBs(Bs);
requires (forall b:B :: Bs[b] ==> As[bToA(b)]);

procedure {:yield_invariant}{:layer 1} Inv_incdec (b:B);
requires As[bToA(b)];

// Definitions and facts about cardinality
function cardAs (As:[A]bool) : int;
axiom (forall As:[A]bool :: cardAs(As) >= 0);

function cardBs (Bs:[B]bool) : int;
axiom (forall Bs:[B]bool :: cardBs(Bs) >= 0);

procedure {:lemma} Lemma_add_to_A (a: A, As: [A]bool);
requires !As[a];
ensures  cardAs(As[a := true]) == cardAs(As) + 1;

procedure {:lemma} Lemma_add_to_B (b: B, Bs: [B]bool);
requires !Bs[b];
ensures cardBs(Bs[b := true]) == cardBs(Bs) + 1;

procedure {:lemma} Lemma_card_geq (As: [A]bool, Bs: [B]bool);
requires (forall b: B :: Bs[b] ==> As[bToA(b)]);
ensures cardAs(As) >= cardBs(Bs);

procedure {:lemma} Lemma_card_greater (_b: B, As: [A]bool, Bs: [B]bool);
requires (forall b: B :: Bs[b] ==> As[bToA(b)]);
requires !Bs[_b];
requires As[bToA(_b)];
ensures cardAs(As) > cardBs(Bs);

// Acutal program
procedure {:yields}{:layer 1}
{:yield_requires "Inv"}
main ({:linear_in "perm"} all_abs: [AB]bool)
requires {:layer 1} all_abs == (lambda v:AB :: 1 <= x#AB(v));
{
  var i:int;
  var {:linear "perm"} abs: [AB]bool;
  var {:linear "perm"} ab:AB;
  abs := all_abs;
  i := 1;
  while (*)
  invariant {:yields}{:layer 1}{:yield_loop "Inv"} true;
  invariant {:layer 1} 1 <= i;
  invariant {:layer 1} abs == (lambda v:AB :: i <= x#AB(v));
  {
    call ab, abs := transfer_ab(i, abs);
    async call incdec(ab);
    i := i + 1;
  }
}

procedure {:both}{:layer 1} TRANSFER_AB (x:int, {:linear_in "perm"} abs:[AB]bool) returns ({:linear "perm"} ab:AB, {:linear "perm"} abs':[AB]bool)
{
  assert !abs[AB(-x)];
  assert abs[AB(x)];
  abs' := abs[AB(x) := false];
  ab := AB(x);
}

procedure {:both}{:layer 1} SPLIT_AB ({:linear_in "perm"} ab:AB) returns ({:linear "perm"} a:A, {:linear "perm"} b:B)
{
  assert x#AB(ab) != 0;
  a := A(x#AB(ab));
  b := B(x#AB(ab));
}

procedure {:yields}{:layer 1}
{:yield_preserves "Inv"}
incdec({:linear_in "perm"} ab:AB)
requires {:layer 1} x#AB(ab) != 0;
{
  var {:linear "perm"} a:A;
  var {:linear "perm"} b:B;
  call a,b := split_ab(ab);
  call {:layer 1} Lemma_card_geq(As, Bs);
  call {:layer 1} Lemma_add_to_A(a, As);
  call geq0_inc(a, b);
  par Inv() | Inv_incdec(b);
  call {:layer 1} Lemma_card_greater(b, As, Bs);
  call {:layer 1} Lemma_add_to_B(b, Bs);
  call geq0_dec(b);
}

procedure {:atomic}{:layer 1} GEQ0_INC ({:linear_in "perm"} a:A, {:linear "perm"} b:B)
modifies x, As;
{
  assert x >= 0;
  assert !As[a];
  x := x + 1;
  As[a] := true;
}

procedure {:atomic}{:layer 1} GEQ0_DEC ({:linear_in "perm"} b:B)
modifies x, Bs;
{
  assert x >= 0;
  assert !Bs[b];
  x := x - 1;
  Bs[b] := true;
}

procedure {:yields}{:layer 0}{:refines "GEQ0_INC"} geq0_inc ({:linear_in "perm"} a:A, {:linear "perm"} b:B);
procedure {:yields}{:layer 0}{:refines "GEQ0_DEC"} geq0_dec ({:linear_in "perm"} b:B);

procedure {:yields}{:layer 0}{:refines "TRANSFER_AB"} transfer_ab (x:int, {:linear_in "perm"} abs:[AB]bool) returns ({:linear "perm"} ab:AB, {:linear "perm"} abs':[AB]bool);
procedure {:yields}{:layer 0}{:refines "SPLIT_AB"} split_ab ({:linear_in "perm"} ab:AB) returns ({:linear "perm"} a:A, {:linear "perm"} b:B);
