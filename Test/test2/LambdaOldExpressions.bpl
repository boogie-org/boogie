var b: bool;


procedure p0();
  requires b;
  modifies b;
  ensures (lambda x: bool :: old(b))[true];
  ensures !(lambda x: bool :: b)[true];

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
