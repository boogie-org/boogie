// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Permission types
type {:datatype} AB;
function {:constructor} AB (x:int) : AB;
type {:datatype} A;
function {:constructor} A (x:int) : A;
type {:datatype} B;
function {:constructor} B (x:int) : B;

// Linear collectors
function {:builtin "MapConst"} MapConstBool(bool): [int]bool;

function {:inline} {:linear "perm"} ABCollector(ab: AB) : [int]bool
{ MapConstBool(false)[x#AB(ab) := true][-x#AB(ab) := true] }
function {:inline} {:linear "perm"} ABSetCollector(abs: [AB]bool) : [int]bool
{ (lambda i:int :: (exists ab:AB :: abs[ab] && (i == x#AB(ab) || i == -x#AB(ab)))) }

function {:inline} {:linear "perm"} ACollector(a: A) : [int]bool
{ MapConstBool(false)[x#A(a) := true] }
function {:inline} {:linear "perm"} ASetCollector(as: [A]bool) : [int]bool
{ (lambda i:int :: (exists a:A :: as[a] && (i == x#A(a)))) }

function {:inline} {:linear "perm"} BCollector(b: B) : [int]bool
{ MapConstBool(false)[-x#B(b) := true] }
function {:inline} {:linear "perm"} BSetCollector(bs: [B]bool) : [int]bool
{ (lambda i:int :: (exists b:B :: bs[b] && (i == -x#B(b)))) }

function {:inline} bToA (b:B) : A { A(x#B(b)) }

// Global variables
var {:layer 0,1} x:int;
var {:layer 0,1}{:linear "perm"} As:[A]bool;
var {:layer 0,1}{:linear "perm"} Bs:[B]bool;

// Invariant
function {:inline} Inv (x:int, As:[A]bool, Bs: [B]bool) : bool
{
     x >= cardAs(As) - cardBs(Bs)
  && (forall b:B :: Bs[b] ==> As[bToA(b)])
}

// Definitions and facts about cardinality
function {:inline} cardAs (As:[A]bool) : int;
axiom (forall As:[A]bool :: cardAs(As) >= 0);

function {:inline} cardBs (Bs:[B]bool) : int;
axiom (forall Bs:[B]bool :: cardBs(Bs) >= 0);

procedure {:layer 1} Lemma_add_to_A (a:A);
requires {:layer 1} !As[a];
ensures  {:layer 1} cardAs(As[a := true]) == cardAs(As) + 1;

procedure {:layer 1} Lemma_add_to_B (b:B);
requires {:layer 1} !Bs[b];
ensures  {:layer 1} cardBs(Bs[b := true]) == cardBs(Bs) + 1;

procedure {:layer 1} Lemma_card_geq ();
requires {:layer 1} (forall b:B :: Bs[b] ==> As[bToA(b)]);
ensures  {:layer 1} cardAs(As) >= cardBs(Bs);

procedure {:layer 1} Lemma_card_greater (_b:B);
requires {:layer 1} (forall b:B :: Bs[b] ==> As[bToA(b)]);
requires {:layer 1} !Bs[_b];
requires {:layer 1} As[bToA(_b)];
ensures  {:layer 1} cardAs(As) > cardBs(Bs);

// Acutal program
procedure {:yields}{:layer 2} main ()
requires {:layer 1} Inv(x, As, Bs);
{
  var i:int;
  var {:linear "perm"} ab:AB;
  yield; assert {:layer 1} Inv(x, As, Bs);
  while (*)
  invariant {:layer 1} Inv(x, As, Bs);
  {
    call ab := alloc_ab();
    async call incdec(ab);
    yield; assert {:layer 1} Inv(x, As, Bs);
  }
  yield;
}

procedure {:yields}{:layer 1} alloc_ab () returns ({:linear "perm"} ab:AB);
ensures {:layer 1} As == old(As);
ensures {:layer 1} Bs == old(Bs);
ensures {:layer 1} x == old(x);

procedure {:yields}{:layer 1} split_ab ({:linear_in "perm"} ab:AB) returns ({:linear "perm"} a:A, {:linear "perm"} b:B);
ensures {:layer 1} x#A(a) == x#AB(ab);
ensures {:layer 1} x#B(b) == x#AB(ab);
ensures {:layer 1} As == old(As);
ensures {:layer 1} Bs == old(Bs);
ensures {:layer 1} x == old(x);

procedure {:yields}{:layer 1} incdec({:linear_in "perm"} ab:AB)
requires {:layer 1} Inv(x, As, Bs);
ensures  {:layer 1} Inv(x, As, Bs);
{
  var {:linear "perm"} a:A;
  var {:linear "perm"} b:B;
  yield; assert {:layer 1} Inv(x, As, Bs);
  call a,b := split_ab(ab);
  call Lemma_card_geq();
  call Lemma_add_to_A(a);
  call geq0_inc(a, b);
  yield;
  assert {:layer 1} Inv(x, As, Bs) && As[bToA(b)];
  call Lemma_card_greater(b);
  call Lemma_add_to_B(b);
  call geq0_dec(b);
  yield; assert {:layer 1}{:expand} Inv(x, As, Bs);
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
