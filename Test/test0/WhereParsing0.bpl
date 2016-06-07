// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const x: int;

function R(int) returns (bool);
function Even(int) returns (bool);

var y: int where R(y);
var g: int where g == 12;

procedure P(x: int where x > 0) returns (y: int where y < 0);
  requires x < 100;
  modifies g;
  ensures -100 < y;

procedure Q(x: int where x > 0) returns (y: int where y < 0)
  requires x < 100;
  modifies g;
  ensures (forall t: int where Even(t) :: -100 < y + t) ||  // error: where not allowed in quant
          (exists t: int where Even(t) :: -100 < y + t);    // error: where not allowed in quant
{
  var a: int;
  var b: int;

  start:
    a := x;
    call b := P(a);
    y := b;
    return;
}

axiom (forall yu: bool, {:myAttr} x: int :: x < 100);
axiom (forall {:myAttr} x: int :: x < 100);
axiom (forall <T> {:myAttr} x: T :: x == x);
