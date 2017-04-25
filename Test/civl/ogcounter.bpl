// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0} x: int;

procedure {:yields} {:layer 0,1} Incr();
ensures {:left} |{ L: x := x + 1; return true; }|;

procedure {:yields} {:layer 1} IncrBy2()
ensures {:left} |{ L: x := x + 2; return true; }|;
{
  yield;
  par Incr() | Incr();
  yield;
}