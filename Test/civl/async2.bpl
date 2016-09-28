// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0} x: int;

procedure {:yields} {:layer 0,1} Incr();
ensures {:left} |{ L: x := x + 1; return true; }|;

procedure {:yields} {:layer 1,2} AsyncIncr()
ensures {:left} |{ L: x := x + 1; return true; }|;
{
  yield;
  async call Incr();
  yield;
}

procedure {:yields} {:layer 0,1} Decr();
ensures {:left} |{ L: x := x - 1; return true; }|;

procedure {:yields} {:layer 1,2} AsyncDecr()
ensures {:left} |{ L: x := x - 1; return true; }|;
{
  yield;
  async call Decr();
  yield;
}

procedure {:yields} {:layer 1,2} AsyncIncrDecr()
ensures {:left} |{ L: return true; }|;
{
  yield;
  async call Incr();
  async call Decr();
  yield;
}

