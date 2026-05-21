// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} g:int;

yield procedure {:layer 1} PB({:linear_in} permVar_in: UnitMap (One int))
requires call Yield(permVar_in, 0);
{
  var permVar_out: UnitMap (One int);
  permVar_out := permVar_in;
  call IncrG();
  call Yield(permVar_out, 1);
}

yield procedure {:layer 1} Main({:linear_in} Permissions: UnitMap (One int))
requires {:layer 1} Permissions->dom == Set_Add(Set_Add(Set_Empty(), One(0)), One(1));
{
  call SetG(0);
  async call PB(Permissions);
}

atomic action {:layer 1} AtomicSetG(val:int)
modifies g;
{ g := val; }

yield procedure {:layer 0} SetG(val:int);
refines AtomicSetG;

atomic action {:layer 1} AtomicIncrG()
modifies g;
{ g := g + 1; }

yield procedure {:layer 0} IncrG();
refines AtomicIncrG;

yield invariant {:layer 1} Yield({:linear} p: UnitMap (One int), v: int);
preserves Map_Contains(p, One(0));
preserves g == v;
