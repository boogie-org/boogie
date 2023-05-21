// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of cycle of increasing types

procedure A<T>(i: T)
{
    call A(Some(i));
}
