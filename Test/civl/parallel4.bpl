// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"




type {:linear "tid"} X = int;

var {:layer 0,1} a:int;

yield procedure {:layer 1} Allocate() returns ({:linear "tid"} tid: int);

yield procedure {:layer 1} main()
{
  var {:linear "tid"} i: int;
  var {:linear "tid"} j: int;
  call i := Allocate();
  call j := Allocate();
  par i := t(i) | j := t(j);
}

yield procedure {:layer 1} t({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
  i := i';
  call Yield();
  assert {:layer 1} a == old(a);
  call Incr();
}

>-< action {:layer 1} AtomicIncr()
modifies a;
{ a := a + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

yield invariant {:layer 1} Yield();
