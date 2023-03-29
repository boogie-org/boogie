// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

////////////////////////////////////////////////////////////////////////////////

action {:layer 1} SUM (n: int)
refines MAIN' using INV
creates ADD;
modifies x;
{
  assert n >= 0;

  assume {:add_to_pool "A", 0} true;
  call create_asyncs((lambda pa: ADD :: 1 <= pa->i && pa->i <= n));
}

action {:layer 2} MAIN' (n: int)
modifies x;
{
  assert n >= 0;
  x := x + (n * (n+1)) div 2;
}

invariant action {:layer 1} INV (n: int)
creates ADD;
modifies x;
{
  var {:pool "A"} i: int;

  assert n >= 0;

  assume
    {:add_to_pool "A", i, i+1}
    {:add_to_pool "B", ADD(n)}
    0 <= i && i <= n;
  x := x + (i * (i+1)) div 2;
  call create_asyncs((lambda {:pool "B"} pa: ADD :: i < pa->i && pa->i <= n));
  call set_choice(ADD(i+1));
}

////////////////////////////////////////////////////////////////////////////////

async <- action {:layer 1} ADD (i: int)
modifies x;
{
  x := x + i;
}
