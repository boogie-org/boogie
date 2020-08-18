// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

type lmap;
function {:linear "mem"} dom(lmap) : [int]bool;
function map(lmap) : [int]int;
function cons([int]bool, [int]int) : lmap;
axiom (forall x:[int]bool, y:[int]int :: {cons(x,y)} dom(cons(x, y)) == x && map(cons(x,y)) == y);
axiom (forall x: lmap :: {dom(x)} {map(x)} cons(dom(x), map(x)) == x);

function Empty(m:[int]int) : lmap;
axiom (forall m: [int]int :: Empty(m) == cons(MapConstBool(false), m));

function Add(x:lmap, i:int): lmap;
axiom (forall x:lmap, i:int :: dom(Add(x, i)) == dom(x)[i:=true] && map(Add(x, i)) == map(x));

function Remove(x:lmap, i:int): lmap;
axiom (forall x:lmap, i:int :: dom(Remove(x, i)) == dom(x)[i:=false] && map(Remove(x, i)) == map(x));

function {:inline} PoolInv(unallocated:[int]bool, pool:lmap) : (bool)
{
  (forall x:int :: unallocated[x] ==> dom(pool)[x])
}

procedure {:yields} {:layer 2}
{:yield_preserves "Yield"}
Main ()
{
  var {:layer 1,2} {:linear "mem"} l:lmap;
  var i:int;
  while (*)
  invariant {:yields} {:layer 1,2} {:yield_loop "Yield"} true;
  {
    call  l, i := Alloc();
    async call Thread(l, i);
  }
}

procedure {:yields} {:layer 2}
{:yield_requires "YieldMem", local_in, i}
{:yield_ensures "Yield"}
Thread ({:layer 1,2} {:linear_in "mem"} local_in:lmap, i:int)
requires {:layer 2} dom(local_in)[i];
{
  var y, o:int;
  var {:layer 1,2} {:linear "mem"} local:lmap;
  var {:layer 1,2} {:linear "mem"} l:lmap;

  call local := Write(local_in, i, 42);
  call o := Read(local, i);
  assert {:layer 2} o == 42;
  while (*)
  invariant {:yields} {:layer 1,2} {:yield_loop "Yield"} true;
  {
    call l, y := Alloc();
    call l := Write(l, y, 42);
    call o := Read(l, y);
    assert {:layer 2} o == 42;
    call Free(l, y);
  }
}

procedure {:right} {:layer 2} atomic_Alloc() returns ({:linear "mem"} l:lmap, i:int)
modifies pool;
{
  var m:[int]int;
  assume dom(pool)[i];
  pool := Remove(pool, i);
  l := Add(Empty(m), i);
}

procedure {:yields} {:layer 1} {:refines "atomic_Alloc"}
{:yield_requires "Yield"}
{:yield_ensures "YieldMem", l, i}
Alloc() returns ({:layer 1} {:linear "mem"} l:lmap, i:int)
{
  call i := PickAddr();
  call l := AllocLinear(i);
}

procedure {:left} {:layer 2} atomic_Free({:linear_in "mem"} l:lmap, i:int)
modifies pool;
{
  assert dom(l)[i];
  pool := Add(pool, i);
}

procedure {:yields} {:layer 1} {:refines "atomic_Free"}
{:yield_preserves "Yield"}
Free({:layer 1} {:linear_in "mem"} l:lmap, i:int)
requires {:layer 1} dom(l)[i];
{
  call FreeLinear(l, i);
  call ReturnAddr(i);
}

procedure {:both} {:layer 2} atomic_Read ({:linear "mem"} l:lmap, i:int) returns (o:int)
{
  assert dom(l)[i];
  o := map(l)[i];
}

procedure {:both} {:layer 2} atomic_Write ({:linear_in "mem"} l:lmap, i:int, o:int) returns ({:linear "mem"} l':lmap)
{
  assert dom(l)[i];
  l' := cons(dom(l), map(l)[i := o]);
}

procedure {:yields} {:layer 1} {:refines "atomic_Read"}
{:yield_requires "YieldMem", l, i}
{:yield_ensures "Yield"}
Read ({:layer 1} {:linear "mem"} l:lmap, i:int) returns (o:int)
{
  call o := ReadLow(i);
}

procedure {:yields} {:layer 1} {:refines "atomic_Write"}
{:yield_requires "YieldMem", l, i}
{:yield_ensures "YieldMem", l', i}
Write ({:layer 1} {:linear_in "mem"} l:lmap, i:int, o:int) returns ({:layer 1} {:linear "mem"} l':lmap)
{
  call WriteLow(i, o);
  call l' := WriteLinear(l, i, o);
}

procedure {:intro} {:layer 1} AllocLinear (i:int) returns ({:linear "mem"} l:lmap)
modifies pool;
{
  assert dom(pool)[i];
  pool := Remove(pool, i);
  l := Add(Empty(mem), i);
}

procedure {:intro} {:layer 1} FreeLinear ({:linear_in "mem"} l:lmap, i:int)
modifies pool;
{
  assert dom(l)[i];
  pool := Add(pool, i);
}

procedure {:intro} {:layer 1} WriteLinear ({:layer 1} {:linear_in "mem"} l:lmap, i:int, o:int) returns ({:layer 1} {:linear "mem"} l':lmap)
{
  assert dom(l)[i];
  l' := cons(dom(l), map(l)[i := o]);
}

procedure {:yield_invariant} {:layer 1} Yield ();
requires PoolInv(unallocated, pool);

procedure {:yield_invariant} {:layer 1} YieldMem ({:layer 1} {:linear "mem"} l:lmap, i:int);
requires PoolInv(unallocated, pool);
requires dom(l)[i] && map(l)[i] == mem[i];

var {:layer 1, 2} {:linear "mem"} pool:lmap;
var {:layer 0, 1} mem:[int]int;
var {:layer 0, 1} unallocated:[int]bool;

procedure {:atomic} {:layer 1} atomic_ReadLow (i:int) returns (o:int)
{ o := mem[i]; }

procedure {:atomic} {:layer 1} atomic_WriteLow (i:int, o:int)
modifies mem;
{ mem[i] := o; }

procedure {:atomic} {:layer 1} atomic_PickAddr () returns (i:int)
modifies unallocated;
{
  assume unallocated[i];
  unallocated[i] := false;
}

procedure {:atomic} {:layer 1} atomic_ReturnAddr (i:int)
modifies unallocated;
{ unallocated[i] := true; }

procedure {:yields} {:layer 0} {:refines "atomic_ReadLow"} ReadLow (i:int) returns (o:int);
procedure {:yields} {:layer 0} {:refines "atomic_WriteLow"} WriteLow (i:int, o:int);
procedure {:yields} {:layer 0} {:refines "atomic_PickAddr"} PickAddr () returns (i:int);
procedure {:yields} {:layer 0} {:refines "atomic_ReturnAddr"} ReturnAddr (i:int);
