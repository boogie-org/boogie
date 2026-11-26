// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Pool terms need fresh let binders to avoid rebinding the same variable object.

function P(int, int): bool;

procedure Test(x: int)
{
  assume (var v := x;
    (exists j: int :: {:add_to_pool "A", v} true) &&
    (forall {:pool "A"} i: int :: P(v, i)));
  assert P(x, x);
}

function {:inline} Make(v: int): [int]int
{
  (lambda {:pool "A"} i: int :: i + v)
}

procedure WithLet(x: int)
{
  var f: [int]int;
  f := Make((var y := x; y));
  assert {:add_to_pool "A", 0} f[0] == x;
}

procedure WithoutLet(x: int)
{
  var f: [int]int;
  f := Make(x);
  assert {:add_to_pool "A", 0} f[0] == x;
}
