// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: int where g == 12;

procedure P(x: int where x > 0) returns (y: int where y < 0);
  requires x < 100;
  modifies g;
  ensures -100 < y;

implementation P(xx: int) returns (yy: int)
{
  var a: int;
  var b: int;

  start:
    a := xx;
    call b := P(a);
    yy := b;
    return;
}

type double;
function F(double) returns (double);
function G(double) returns (bool);

procedure Q(omega: double where omega == F(omega),
            psi: double where psi + 1 == 0,  // error: psi doesn't have right type for +
            pi: double where F(pi),          // error: F has wrong return type
            sigma: double where G(sigma));


const SomeConstant: name;
function fgh(int) returns (int);

procedure Cnst(n: name where n <: SomeConstant /*this SomeConstant refers to the const*/) returns (SomeConstant: int)
{
  var k: int where k != SomeConstant;  // fine, since SomeConstants refers to the out parameter
  var m: name where m != SomeConstant;  // error: types don't match up
  var r: ref where (forall abc: int :: abc == SomeConstant);
  var b: bool;
  start:
    b := (forall x: int :: fgh(x) < SomeConstant);
    b := (forall l: name :: l == SomeConstant);  // error: SomeConstant here refers to the out parameter
    return;
}

type ref, name;
