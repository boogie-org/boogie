// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo2(x : bv32) returns(r : bv32)
{
  block1:
    r := x[-1:1];  // Error
//    r := x[x:1];  // Error
    r := x[1:x];  // Error
    r := x[1+1:3];  // Error
    return;
}


