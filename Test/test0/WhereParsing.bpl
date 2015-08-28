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

implementation P(xx: int where xx > 0)  // error: where not allowed in implementation decl
    returns (yy: int where yy < 0)      // error: where not allowed in implementation decl
{
  var a: int where a == b;  // b is not allowed to be mentioned here, but this test is only
  var b: int;               // for parsing, so no complaint will be issued

  start:
    a := xx;
    call b := P(a);
    yy := b;
    return;
}

procedure {:myProcAttr} Attr(x: int, {:myParamAttr x, y} y: bool) returns (z: int, {:retAttr x} w: bool)
{
}

procedure BadAttrs(x: int);
implementation BadAttrs({:myParamAttr} x: int)  // error: attributes not allowed in implementation decl
{
}
