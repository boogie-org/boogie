// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yields} {:layer 1} PA()
{
  var x, y: int;
  yield;
  par x := Incr(y) | y := Set(x);
  yield;
}

procedure {:left} {:layer 1} AtomicIncr(a: int) returns (b: int)
{ }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(a: int) returns (b: int);

procedure {:left} {:layer 1} AtomicSet(v: int) returns (w: int)
{ }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int) returns (w: int);



