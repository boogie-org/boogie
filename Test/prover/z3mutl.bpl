// RUN: %boogie -typeEncoding:m -z3multipleErrors "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var x:int;

procedure Foo(){

start:

    goto L1, L2, L3, L4;
L1: assume x == 1;
    goto L5;

L2: assume x == 2;
    goto L5;

L3: assume x == 3;
    goto L5;

L4: assume x > 10;
    goto L5;

L5: assert (x > 4);

}