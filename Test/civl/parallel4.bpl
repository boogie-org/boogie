// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"




type {:linear "tid"} X = int;

var {:layer 0,1} a:int;

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} tid: int);

procedure {:yields} {:layer 1} main()
{
  var {:linear "tid"} i: int;
  var {:linear "tid"} j: int;
  call i := Allocate();
  call j := Allocate();
  par i := t(i) | j := t(j);
}

procedure {:yields} {:layer 1} t({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
  i := i';
  call Yield();
  assert {:layer 1} a == old(a);
  call Incr();
}

procedure {:atomic} {:layer 1} AtomicIncr()
modifies a;
{ a := a + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:yield_invariant} {:layer 1} Yield();
