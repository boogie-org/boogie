// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

<- action {:layer 1,2} AtomicIncr()
modifies x;
{ x := x + 1; }

<- action {:layer 1,2} AtomicDecr()
modifies x;
{ x := x - 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

yield procedure {:layer 0} Decr();
refines AtomicDecr;

yield procedure {:layer 1} AsyncIncr()
refines AtomicIncr;
{
  async call {:sync} Incr();
}

yield procedure {:layer 1} AsyncDecr()
refines AtomicDecr;
{
  async call {:sync} Decr();
}

yield procedure {:layer 1} AsyncIncrDecr()
{
  async call {:sync} Incr();
  async call {:sync} Decr();
}
