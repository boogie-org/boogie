// RUN: %boogie /typeEncoding:predicates /logPrefix:p "%s" > "%t"
// RUN: %boogie /typeEncoding:arguments /logPrefix:a "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

const C:int;
const D:bool;

function empty<alpha>() returns (alpha);

function eqC<alpha>(x:alpha) returns (bool) { x == C }
function giveEmpty<alpha>() returns (alpha) { empty() }

function {:inline true} eqC2<alpha>(x:alpha) returns (bool) { x == C }
function {:inline true} giveEmpty2<alpha>() returns (alpha) { empty() }

function eqC3<alpha>(x:alpha) returns (bool);
axiom {:inline true} (forall<alpha> x:alpha :: eqC3(x) == (x == C));

function giveEmpty3<alpha>() returns (alpha);
axiom {:inline true} (forall<alpha> :: giveEmpty3():alpha == empty());

procedure P() {
  assert eqC(C);
  assert eqC2(C);
  assert eqC3(C);
  assert eqC2(D);  // should not be provable
}

procedure Q() {
  assert giveEmpty() == empty();
  assert giveEmpty() == empty():int;
  assert giveEmpty():bool == empty();

  assert giveEmpty2() == empty();
  assert giveEmpty2() == empty():int;
  assert giveEmpty2():bool == empty();

  assert giveEmpty3() == empty();
  assert giveEmpty3() == empty():int;
  assert giveEmpty3():bool == empty();

  assert giveEmpty3() == C;     // should not be provable
}
