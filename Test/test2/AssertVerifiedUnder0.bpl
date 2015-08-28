// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Test0()
{
    assert {:verified_under false} false;  // error
}


procedure Test1()
{
    assert {:verified_under true} false;
}


procedure Test2(P: bool, A: bool)
{
    assert {:verified_under A} P;  // error
}


procedure Test3(P: bool, A: bool)
  requires !A ==> P;
{
    assert {:verified_under A} P;
}


procedure Test4(P: bool, A: bool)
{
    assert {:verified_under A} {:verified_under true} P;  // error
}


procedure Test5(P: bool, A: bool)
  requires !A ==> P;
{
    assert {:verified_under A} {:verified_under true} P;
}
