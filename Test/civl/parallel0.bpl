// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yields} {:layer 1} P()
{
  var x, y: int;
  par x := A(y) | y := B(x);
}

procedure {:left} {:layer 1} AtomicA(a: int) returns (b: int)
{ }

procedure {:yields} {:layer 0} {:refines "AtomicA"} A(a: int) returns (b: int);

procedure {:left} {:layer 1} AtomicB(v: int) returns (w: int)
{ }

procedure {:yields} {:layer 0} {:refines "AtomicB"} B(v: int) returns (w: int);
