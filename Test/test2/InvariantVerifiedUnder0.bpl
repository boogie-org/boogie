// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Test0()
{
    while (*)
      invariant {:verified_under false} false;  // error
    {}
}


procedure Test1()
{
    while (*)
      invariant {:verified_under true} false;
    {}
}


procedure Test2(P: bool, Q: bool, A: bool)
{
    while (*)
      invariant {:verified_under A} P;  // error
      invariant {:verified_under A} Q;  // error
    {}
}


procedure Test3(P: bool, Q: bool, A: bool)
  requires !A ==> P;
{
    while (*)
      invariant {:verified_under A} P;
      invariant {:verified_under A} Q;  // error
    {}
}

procedure Test4(P: bool, Q: bool, A: bool)
{
    while (*)
      invariant {:verified_under A} {:verified_under true} P;  // error
      invariant {:verified_under A} {:verified_under true} Q;  // error
    {}
}


procedure Test5(P: bool, Q: bool, A: bool)
  requires !A ==> Q;
{
    while (*)
      invariant {:verified_under A} {:verified_under true} P;  // error
      invariant {:verified_under A} {:verified_under true} Q;
    {}
}
