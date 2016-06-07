// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure A(P: bool);
  requires P;

procedure Test0()
{
    call {:verified_under false} A(false);  // error
}


procedure Test1()
{
    call {:verified_under true} A(false);
}


procedure Test2(P: bool, A: bool)
{
    call {:verified_under A} A(P);  // error
}


procedure Test3(P: bool, A: bool)
  requires !A ==> P;
{
    call {:verified_under A} A(P);
}


procedure Test4(P: bool, A: bool)
{
    call {:verified_under A} {:verified_under true} A(P);  // error
}


procedure Test5(P: bool, A: bool)
  requires !A ==> P;
{
    call {:verified_under A} {:verified_under true} A(P);
}
