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


var {:assumption} ga0: bool;


procedure Test3()
  modifies ga0;
{
    ga0 := ga0 && true;

    assert ga0;  // error
}


procedure Test4()
{
    var {:assumption} a0: bool;
    var tmp: bool;

    tmp := a0;

    havoc a0;

    assert a0 ==> tmp;
}


procedure Test5(A: bool)
{
    var {:assumption} a0: bool;
    var tmp0, tmp1: bool;

    a0 := a0 && A;
    tmp0 := a0;

    havoc a0;

    assert a0 ==> tmp0;

    tmp1 := a0;

    havoc a0;

    assert a0 ==> tmp1;
}
