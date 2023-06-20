// RUN: %parallel-boogie -inline:spec -print:- -env:0 -printInlined "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure a(i:int where i > 2) returns (r:int) {
    call r := b(i);
    return;
}

procedure {:inline 1} b(i:int where i > 2) returns (r:int) {
    var d:int where d > 3;
    d := i + i;
    r := d;
    return;
}