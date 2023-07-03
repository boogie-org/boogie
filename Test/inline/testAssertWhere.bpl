// RUN: %parallel-boogie -inline:spec -print:- -env:0 -printInlined "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure a() returns () {
    call b();
}

procedure {:inline 1} b() returns () {
    var v:int where v > 3;
    assert v > 3;
}