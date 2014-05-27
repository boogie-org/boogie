// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Test0()
{
    var {:assumption} a0: bool;

    assert a0;
}


procedure Test1(n: int)
{
    var {:assumption} a0: bool;

    a0 := a0 && (0 <= n);

    assert a0;  // error
}


procedure Test2()
{
    var {:assumption} a0: bool;

    havoc a0;

    assert a0;  // error
}


var {:assumption} a0: bool;


procedure Test3()
  modifies a0;
{
    a0 := a0 && true;

    assert a0;  // error
}
