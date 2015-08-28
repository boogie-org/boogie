// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo2(x : bv32) returns(r : bv32)
{
  block1:
    r := x[x:1];  // Error
    r := x[(1:13)];  // Error
    return;
}


