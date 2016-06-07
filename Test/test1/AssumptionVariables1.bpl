// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Test0()
{
    var {:assumption} a0: int;  // error
}
