// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

right action {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

pure procedure {:inline 1} ghost(y: int) returns (z: int)
{
  z := y + 1;
}

right action {:layer 2} AtomicIncr2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 1} Incr2()
refines AtomicIncr2;
{
  var {:layer 1} a: int;

  call {:layer 1} a := ghost(1);
  assert {:layer 1} a == 2;
  par Incr() | Incr();
}

yield procedure {:layer 1} Incr2'()
refines AtomicIncr2;
{
  var {:layer 1} a: int;
  var {:layer 1} b: int;

  call {:layer 1} a := Copy(x);
  par Incr() | Incr();
  call {:layer 1} b := Copy(x);
  assert {:layer 1} b == a + 2;
}
