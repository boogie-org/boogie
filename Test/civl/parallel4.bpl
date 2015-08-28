// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} a:int;

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} tid: int)
{
    yield;
    call tid := AllocateLow();
    yield;
}

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

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
  yield;
}

procedure {:yields} {:layer 0,1} Incr();
ensures {:atomic} |{A: a := a + 1; return true; }|;

procedure {:yields} {:layer 1} Yield()
{
  yield;
}

procedure {:yields} {:layer 0,1} AllocateLow() returns ({:linear "tid"} tid: int);
ensures {:atomic} |{ A: return true; }|;
