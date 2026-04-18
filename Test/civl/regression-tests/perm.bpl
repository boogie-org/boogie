// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;

yield procedure {:layer 1}
mainE({:linear_in} permVar_in: UnitMap (One int))
requires call Yield(permVar_in, 0);
{
    var permVar_out: UnitMap (One int);

    permVar_out := permVar_in;

    async call foo(permVar_out);
}

yield procedure {:layer 1}
foo({:linear_in} permVar_in: UnitMap (One int))
requires call Yield(permVar_in, 0);
{
  var permVar_out: UnitMap (One int);
  permVar_out := permVar_in;
  call Incr();
  call Yield(permVar_out, 1);
}

atomic action {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

yield invariant {:layer 1} Yield({:linear} p: UnitMap (One int), v: int);
preserves Map_Contains(p, One(1));
preserves x == v;
