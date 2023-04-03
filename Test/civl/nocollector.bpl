// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:linear "L"} x:int;

yield procedure {:layer 1} P()
{
}
