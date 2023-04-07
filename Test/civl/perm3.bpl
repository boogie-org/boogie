// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "Perm"} X = int;
var {:layer 0,1} g:int;

yield procedure {:layer 1} PB({:linear_in "Perm"} permVar_in:[int]bool)
requires call Yield(permVar_in, 0);
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;
  call IncrG();
  call Yield(permVar_out, 1);
}

yield procedure {:layer 1} Main({:linear_in "Perm"} Permissions: [int]bool)
requires {:layer 1} Permissions == MapConst(true);
{
  call SetG(0);
  async call PB(Permissions);
}

action {:layer 1} AtomicSetG(val:int)
modifies g;
{ g := val; }

yield procedure {:layer 0} SetG(val:int);
refines AtomicSetG;

action {:layer 1} AtomicIncrG()
modifies g;
{ g := g + 1; }

yield procedure {:layer 0} IncrG();
refines AtomicIncrG;

yield invariant {:layer 1} Yield({:linear "Perm"} p: [int]bool, v: int);
invariant p[0];
invariant g == v;
