// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

-> action {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

action {:layer 1} ghost(y: int) returns (z: int)
{
  z := y + 1;
}

-> action {:layer 2} AtomicIncr2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 1} Incr2()
refines AtomicIncr2;
{
  var {:layer 1} a: int;

  call a := ghost(1);
  assert {:layer 1} a == 2;
  par Incr() | Incr();
}

action {:layer 1} ghost'() returns (z: int)
{
  z := x;
}

yield procedure {:layer 1} Incr2'()
refines AtomicIncr2;
{
  var {:layer 1} a: int;
  var {:layer 1} b: int;

  call a := ghost'();
  par Incr() | Incr();
  call b := ghost'();
  assert {:layer 1} b == a + 2;
}
