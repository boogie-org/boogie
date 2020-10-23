// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

procedure {:left} {:layer 1,2} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:left} {:layer 1,2} AtomicDecr()
modifies x;
{ x := x - 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();
procedure {:yields} {:layer 0} {:refines "AtomicDecr"} Decr();

procedure {:yields} {:layer 1} {:refines "AtomicIncr"} AsyncIncr()
{
  async call {:sync} Incr();
}

procedure {:yields} {:layer 1} {:refines "AtomicDecr"} AsyncDecr()
{
  async call {:sync} Decr();
}

procedure {:yields} {:layer 1} AsyncIncrDecr()
{
  async call {:sync} Incr();
  async call {:sync} Decr();
}
