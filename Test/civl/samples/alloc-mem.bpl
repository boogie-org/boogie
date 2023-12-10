// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} PoolInv(unallocated:[int]bool, pool:Lset int) : (bool)
{
  (forall x:int :: unallocated[x] ==> Lset_Contains(pool, x))
}

yield procedure {:layer 2} Main ()
preserves call Yield();
{
  var {:layer 1,2} l:Lmap int int;
  var i:int;
  while (*)
    invariant {:yields} true;
    invariant call Yield();
  {
    call  l, i := Alloc();
    async call Thread(l, i);
  }
}

yield procedure {:layer 2} Thread ({:layer 1,2} {:linear_in} local_in:Lmap int int, i:int)
preserves call Yield();
requires {:layer 1,2} Lmap_Contains(local_in, i);
{
  var y, o:int;
  var {:layer 1,2} local:Lmap int int;
  var {:layer 1,2} l:Lmap int int;

  call local := Write(local_in, i, 42);
  call o := Read(local, i);
  assert {:layer 2} o == 42;
  while (*)
  invariant {:yields} true;
  invariant call Yield();
  {
    call l, y := Alloc();
    call l := Write(l, y, 42);
    call o := Read(l, y);
    assert {:layer 2} o == 42;
    call Free(l, y);
  }
}

right action {:layer 2} atomic_Alloc() returns (l:Lmap int int, i:int)
modifies pool;
{
  assume Lset_Contains(pool, i);
  call l, pool := AllocLinear(i, pool);
}

yield procedure {:layer 1}
Alloc() returns ({:layer 1} l:Lmap int int, i:int)
refines atomic_Alloc;
preserves call Yield();
ensures {:layer 1} Lmap_Contains(l, i);
{
  call i := PickAddr();
  call {:layer 1} l, pool := AllocLinear(i, pool);
}

left action {:layer 2} atomic_Free({:linear_in} l:Lmap int int, i:int)
modifies pool;
{
  var t:Lset int;
  assert Lmap_Contains(l, i);
  call t := Lmap_Free(l);
  call Lset_Put(pool, t);
}

yield procedure {:layer 1} Free({:layer 1} {:linear_in} l:Lmap int int, i:int)
refines atomic_Free;
requires {:layer 1} Lmap_Contains(l, i);
preserves call Yield();
{
  call {:layer 1} pool := FreeLinear(l, i, pool);
  call ReturnAddr(i);
}

both action {:layer 2} atomic_Read (l:Lmap int int, i:int) returns (o:int)
{
  assert Lmap_Contains(l, i);
  o := l->val[i];
}

both action {:layer 2} atomic_Write ({:linear_in} l:Lmap int int, i:int, o:int) returns (l':Lmap int int)
{
  assert Lmap_Contains(l, i);
  l' := l;
  l'->val[i] := o;
}

yield procedure {:layer 1}
Read ({:layer 1} l:Lmap int int, i:int) returns (o:int)
refines atomic_Read;
requires call YieldMem(l, i);
ensures call Yield();
{
  call o := ReadLow(i);
}

yield procedure {:layer 1}
Write ({:layer 1} {:linear_in} l:Lmap int int, i:int, o:int) returns ({:layer 1} l':Lmap int int)
refines atomic_Write;
requires call Yield();
requires {:layer 1} Lmap_Contains(l, i);
ensures call YieldMem(l', i);
{
  call WriteLow(i, o);
  call {:layer 1} l' := WriteLinear(l, i, o);
}

pure action AllocLinear (i:int, {:linear_in} pool:Lset int) returns (l:Lmap int int, pool':Lset int)
{
  var m:[int]int;
  var t:Lset int;
  assert Lset_Contains(pool, i);
  pool' := pool;
  call t := Lset_Get(pool', MapOne(i));
  call l := Lmap_Alloc(t, m);
}

pure action FreeLinear ({:linear_in} l:Lmap int int, i:int, {:linear_in} pool:Lset int) returns (pool':Lset int)
{
  var t: Lset int;
  assert Lmap_Contains(l, i);
  call t := Lmap_Free(l);
  pool' := pool;
  call Lset_Put(pool', t);
}

pure action WriteLinear ({:layer 1} {:linear_in} l:Lmap int int, i:int, o:int) returns ({:layer 1} l':Lmap int int)
{
  assert Lmap_Contains(l, i);
  l' := l;
  l'->val[i] := o;
}

yield invariant {:layer 1} Yield ();
invariant PoolInv(unallocated, pool);

yield invariant {:layer 1} YieldMem ({:layer 1} l:Lmap int int, i:int);
invariant PoolInv(unallocated, pool);
invariant Lmap_Contains(l, i) && Lmap_Deref(l, i) == mem[i];

var {:layer 1, 2} pool:Lset int;
var {:layer 0, 1} mem:[int]int;
var {:layer 0, 1} unallocated:[int]bool;

atomic action {:layer 1} atomic_ReadLow (i:int) returns (o:int)
{ o := mem[i]; }

atomic action {:layer 1} atomic_WriteLow (i:int, o:int)
modifies mem;
{ mem[i] := o; }

atomic action {:layer 1} atomic_PickAddr () returns (i:int)
modifies unallocated;
{
  assume unallocated[i];
  unallocated[i] := false;
}

atomic action {:layer 1} atomic_ReturnAddr (i:int)
modifies unallocated;
{ unallocated[i] := true; }

yield procedure {:layer 0} ReadLow (i:int) returns (o:int);
refines atomic_ReadLow;

yield procedure {:layer 0} WriteLow (i:int, o:int);
refines atomic_WriteLow;

yield procedure {:layer 0} PickAddr () returns (i:int);
refines atomic_PickAddr;

yield procedure {:layer 0} ReturnAddr (i:int);
refines atomic_ReturnAddr;
