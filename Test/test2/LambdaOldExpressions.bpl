// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var b: bool;


procedure p0();
  requires b;
  modifies b;
  ensures (lambda x: bool :: {:MyAttr "put an attr here", !b} old(b))[true];
  ensures !(lambda x: bool :: {:AnotherAttr "yes, why not", b} {:ABC b, b, old(b)} b)[true];

implementation p0()
{
    b := !b;
    assert (lambda x: bool :: old(b))[true];
    assert !(lambda x: bool :: b)[true];
}


procedure p1();
  requires !b;
  modifies b;
  ensures (lambda x: bool :: old(b))[true];  // error

implementation p1()
{
    b := !b;
    assert !(lambda x: bool :: old(b))[true];
}


procedure p2();
  requires b;
  modifies b;
  ensures (lambda x: bool :: old(b) != b)[true];

implementation p2()
{
    b := !b;
    assert (lambda x: bool :: old(b) != b)[true];
}


procedure p3();
  requires b;
  modifies b;
  ensures (lambda x: int :: old(old(b)) != b)[15];

implementation p3()
{
    b := !b;
    assert (lambda x: int :: old(old(b)) != b)[15];
}

// Note that variables (inside and outside old expressions) mentioned
// in attributes (even if they are not mentioned in the body of the
// lambda) are also picked up by the auto-generated lambda functions,
// so that the attributes can be copied to the function and axiom.
var h: int;
procedure TestAttributeParameters()
  ensures (lambda x: int :: {:MyAttribute old(h), h} x < 100)[23];
{
}
