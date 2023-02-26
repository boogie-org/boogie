// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "Perm"} X = int;
var {:layer 0,1} g:int;

procedure {:yields} {:layer 1}  
{:yield_requires "Yield", permVar_in, 0}
PB({:linear_in "Perm"} permVar_in:[int]bool)
{
  var {:linear "Perm"} permVar_out: [int]bool;
  permVar_out := permVar_in;
  call IncrG();
  call Yield(permVar_out, 1);
}

procedure {:yields} {:layer 1} Main({:linear_in "Perm"} Permissions: [int]bool)
requires {:layer 1} Permissions == MapConst(true);
{
  call SetG(0);
  async call PB(Permissions);
}

procedure {:atomic} {:layer 1} AtomicSetG(val:int)
modifies g;
{ g := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSetG"} SetG(val:int);

procedure {:atomic} {:layer 1} AtomicIncrG()
modifies g;
{ g := g + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncrG"} IncrG();

procedure {:yield_invariant} {:layer 1} Yield({:linear "Perm"} p: [int]bool, v: int);
requires p[0];
requires g == v;