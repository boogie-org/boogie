// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// defined functions

function Twice(x: int) returns (int)
{
  x + x
}

function {:define} Double(x: int) returns (int)
{
  3 * x - x
}

function f(int) returns (int);
function g(int) returns (int);
function h(int) returns (int);
function k(int) returns (int);
axiom (forall x: int :: Twice(x) == f(x));  // here, Twice(x) and f(x) are both triggers
axiom (forall x: int :: Double(x) == g(x));  // if Double was inlined, the trigger would be just g(x); what is trigger when Double is defined?
axiom (forall x: int :: { f(x) } f(x) < h(x) );
axiom (forall x: int :: { g(x) } g(x) < k(x) );

procedure P(a: int, b: int, c: int)
{
  // The following is provable, because Twice triggers its definition and the resulting f(a)
  // triggers the relation to h(a).
  assert Twice(a) < h(a);
  if (*) {
    // The following is NOT provable, it seems because Double is defined and thus no g(b) term is ever
    // created; double-check this
    assert Double(b) < k(b);  // error
  } else {
    // The following IS provable, because the explicit g(c) will cause both of the necessary
    // quantifiers to trigger
    assert g(c) == 2*c;
    assert Double(c) < k(c);
  }
}

// nullary functions

function Five() returns (int) { 5 }

function {:define} Eight() returns (e: int) { 8 }

procedure Q()
{
  assert 8 * Five() == 5 * Eight();
}
