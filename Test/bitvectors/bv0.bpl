// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo2(x : bv32) returns(r : bv32)
{
  block1:
  	r := 17bv31; // Error
  	r := 17; // Error
    r := x[1:0]; // Error
    r := x[0:1]; // Error
    r := x[55:54]; // Error
    r := x[33:32]; // Error
    r := 17bv10 ++ 17bv42 ++ 13bv22; // Error
    return;
}

