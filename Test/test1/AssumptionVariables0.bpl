// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Test0()
{
    var {:assumption} a0: bool where a0;  // error
}


procedure Test1()
{
    var {:assumption} a0: bool;

    a0 := a0 && true;
}


procedure Test2()
{
    var {:assumption} a0: bool;

    a0 := true;  // error
}


procedure Test3()
{
    var {:assumption} a0: bool;
    var {:assumption} a1: bool;

    a0 := a1 && true;  // error
}


procedure Test4()
{
    var {:assumption} a0: bool;

    a0 := a0 && true;
    a0 := a0 && true;  // error
}


procedure Test5()
  modifies a0;
{
    a0 := a0 && true;
}


var {:assumption} a0: bool;


procedure Test6()
  modifies a0;
{
    a0 := a0 && true;  // error
}
