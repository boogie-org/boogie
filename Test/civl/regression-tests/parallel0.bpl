// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} P()
{
  var x, y: int;
  call x := A(y) | y := B(x);
}

left action {:layer 1} AtomicA(a: int) returns (b: int)
{ }

yield procedure {:layer 0} A(a: int) returns (b: int);
refines AtomicA;

left action {:layer 1} AtomicB(v: int) returns (w: int)
{ }

yield procedure {:layer 0} B(v: int) returns (w: int);
refines AtomicB;
