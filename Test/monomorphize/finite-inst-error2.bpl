// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of cycle of increasing types

function B<T>(i: T) : bool
{
    B(Some(i))
}
