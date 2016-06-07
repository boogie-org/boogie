// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type double;

function R(int) returns (bool);
function K(double, bool) returns (bool);

var y: int where R(y);
var g: int where h ==> g == 12;
var h: bool where g < 100;
var k: double where K(k, h);

procedure P(x: int where x > 0) returns (y: int where y < 0);
  requires x < 100;
  modifies g;
  ensures -100 < y;

implementation P(xx: int) returns (yy: int)
{
  var a: int where a == 10;
  var b: int where a == b && b < g;

  start:
    a := xx;
    call b := P(a);
    yy := b;
    return;
}

procedure Q(w: int where x < w || x > alpha/*error: out-parameter alpha is not in scope*/, x: int where x + w > 0)
    returns (v: bool where v,
             y: int where x + y + z < 0,
             z: int where g == 12,
             alpha: ref where old(alpha) != null,  // error: cannot use old in where clause
             beta: ref where (forall r: ref :: r == beta ==> beta == null))
  requires x < 100;
  modifies g;
  ensures -100 < y;
{
  var a: int;
  var b: int;

  start:
    a := x;
    call b := P(a);
    y := b;
    return;
}

const SomeConstant: ref;

procedure Cnst(n: ref where n != SomeConstant) returns (SomeConstant: int)
{
  var m: ref where m != SomeConstant;
  var k: int where k != SomeConstant;
  var r: ref where (forall abc: ref :: abc == SomeConstant);
  var b: bool;
  start:
    b := (forall l: ref :: l == SomeConstant);
    return;
}

type ref;
const null : ref;
