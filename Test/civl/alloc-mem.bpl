// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "mem"} ref = int;

type lmap;
function {:linear "mem"} dom(lmap) : [int]bool;
function map(lmap) : [int]int;
function cons([int]bool, [int]int) : lmap;
axiom (forall x:[int]bool, y:[int]int :: {cons(x,y)} dom(cons(x, y)) == x && map(cons(x,y)) == y);
axiom (forall x: lmap :: {dom(x)} {map(x)} cons(dom(x), map(x)) == x);

function Empty(m:[int]int) : lmap;
axiom (forall m: [int]int :: Empty(m) == cons(MapConst(false), m));

function Add(x:lmap, i:int): lmap;
axiom (forall x:lmap, i:int :: dom(Add(x, i)) == dom(x)[i:=true] && map(Add(x, i)) == map(x));

function Remove(x:lmap, i:int): lmap;
axiom (forall x:lmap, i:int :: dom(Remove(x, i)) == dom(x)[i:=false] && map(Remove(x, i)) == map(x));

function {:inline} PoolInv(unallocated:[int]bool, pool:lmap) : (bool)
{
  (forall x:int :: unallocated[x] ==> dom(pool)[x])
}

yield procedure {:layer 2} Main ()
preserves call Yield();
{
  var {:layer 1,2} {:linear "mem"} l:lmap;
  var i:int;
  while (*)
    invariant {:yields} true;
    invariant call Yield();
  {
    call  l, i := Alloc();
    async call Thread(l, i);
  }
}

yield procedure {:layer 2} Thread ({:layer 1,2} {:linear_in "mem"} local_in:lmap, i:int)
requires call YieldMem(local_in, i);
ensures call Yield();
requires {:layer 2} dom(local_in)[i];
{
  var y, o:int;
  var {:layer 1,2} {:linear "mem"} local:lmap;
  var {:layer 1,2} {:linear "mem"} l:lmap;

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

-> action {:layer 2} atomic_Alloc() returns ({:linear "mem"} l:lmap, i:int)
modifies pool;
{
  var m:[int]int;
  assume dom(pool)[i];
  pool := Remove(pool, i);
  l := Add(Empty(m), i);
}

yield procedure {:layer 1}
Alloc() returns ({:layer 1} {:linear "mem"} l:lmap, i:int) refines atomic_Alloc
requires call Yield();
ensures call YieldMem(l, i);
{
  call i := PickAddr();
  call l := AllocLinear(i);
}

<- action {:layer 2} atomic_Free({:linear_in "mem"} l:lmap, i:int)
modifies pool;
{
  assert dom(l)[i];
  pool := Add(pool, i);
}

yield procedure {:layer 1} Free({:layer 1} {:linear_in "mem"} l:lmap, i:int) refines atomic_Free
requires {:layer 1} dom(l)[i];
preserves call Yield();
{
  call FreeLinear(l, i);
  call ReturnAddr(i);
}

<-> action {:layer 2} atomic_Read ({:linear "mem"} l:lmap, i:int) returns (o:int)
{
  assert dom(l)[i];
  o := map(l)[i];
}

<-> action {:layer 2} atomic_Write ({:linear_in "mem"} l:lmap, i:int, o:int) returns ({:linear "mem"} l':lmap)
{
  assert dom(l)[i];
  l' := cons(dom(l), map(l)[i := o]);
}

yield procedure {:layer 1}
Read ({:layer 1} {:linear "mem"} l:lmap, i:int) returns (o:int) refines atomic_Read
requires call YieldMem(l, i);
ensures call Yield();
{
  call o := ReadLow(i);
}

yield procedure {:layer 1}
Write ({:layer 1} {:linear_in "mem"} l:lmap, i:int, o:int) returns ({:layer 1} {:linear "mem"} l':lmap) refines atomic_Write
requires call YieldMem(l, i);
ensures call YieldMem(l', i);
{
  call WriteLow(i, o);
  call l' := WriteLinear(l, i, o);
}

link action {:layer 1} AllocLinear (i:int) returns ({:linear "mem"} l:lmap)
modifies pool;
{
  assert dom(pool)[i];
  pool := Remove(pool, i);
  l := Add(Empty(mem), i);
}

link action {:layer 1} FreeLinear ({:linear_in "mem"} l:lmap, i:int)
modifies pool;
{
  assert dom(l)[i];
  pool := Add(pool, i);
}

link action {:layer 1} WriteLinear ({:layer 1} {:linear_in "mem"} l:lmap, i:int, o:int) returns ({:layer 1} {:linear "mem"} l':lmap)
{
  assert dom(l)[i];
  l' := cons(dom(l), map(l)[i := o]);
}

yield invariant {:layer 1} Yield ();
invariant PoolInv(unallocated, pool);

yield invariant {:layer 1} YieldMem ({:layer 1} {:linear "mem"} l:lmap, i:int);
invariant PoolInv(unallocated, pool);
invariant dom(l)[i] && map(l)[i] == mem[i];

var {:layer 1, 2} {:linear "mem"} pool:lmap;
var {:layer 0, 1} mem:[int]int;
var {:layer 0, 1} unallocated:[int]bool;

action {:layer 1} atomic_ReadLow (i:int) returns (o:int)
{ o := mem[i]; }

action {:layer 1} atomic_WriteLow (i:int, o:int)
modifies mem;
{ mem[i] := o; }

action {:layer 1} atomic_PickAddr () returns (i:int)
modifies unallocated;
{
  assume unallocated[i];
  unallocated[i] := false;
}

action {:layer 1} atomic_ReturnAddr (i:int)
modifies unallocated;
{ unallocated[i] := true; }

yield procedure {:layer 0} ReadLow (i:int) returns (o:int) refines atomic_ReadLow;
yield procedure {:layer 0} WriteLow (i:int, o:int) refines atomic_WriteLow;
yield procedure {:layer 0} PickAddr () returns (i:int) refines atomic_PickAddr;
yield procedure {:layer 0} ReturnAddr (i:int) refines atomic_ReturnAddr;
