// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// inlined functions

function Twice(x: int) returns (int)
{
  x + x
}

function {:inline} Double(x: int) returns (int)
{
  3 * x - x
}

function f(int) returns (int);
function g(int) returns (int);
function h(int) returns (int);
function k(int) returns (int);
axiom (forall x: int :: Twice(x) == f(x));  // here, Twice(x) and f(x) are both triggers
axiom (forall x: int :: Double(x) == g(x));  // since Double is inlined, the trigger here is just g(x)
axiom (forall x: int :: { f(x) } f(x) < h(x) );
axiom (forall x: int :: { g(x) } g(x) < k(x) );

procedure P(a: int, b: int, c: int)
{
  // The following is provable, because Twice triggers its definition and the resulting f(a)
  // triggers the relation to h(a).
  assert Twice(a) < h(a);
  if (*) {
    // The following is NOT provable, because Double is inlined and thus no g(b) term is ever
    // created
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

function {:inline} Eight() returns (e: int) { 8 }

procedure Q()
{
  assert 8 * Five() == 5 * Eight();
}
