// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Pair { Pair(a: int, b: int) }


procedure P0(p: Pair) returns (q: Pair)
  requires p->a == 0;
  ensures  q->a == 1;
{
  q := p;
  q->b := 1;
}

procedure P1(p: [int]Pair, x: int) returns (q: [int]Pair)
  requires p[x]->a == 0;
  ensures  q[x]->a == 1;
{
  q[x] := p[x];
  q[x]->b := 1;
}

datatype PairOfMaps { PairOfMaps(amap: [int]Pair, bmap: [int]Pair) }


procedure P2(p: PairOfMaps, x: int) returns (q: PairOfMaps)
  requires p->amap[x]->a == 0;
  ensures  q->bmap[x]->a == 0;
{
  var t: [int]Pair;
  q := p;
  call t := P1(p->amap, x);
  q->bmap := t;
}

datatype Perm {
  Left(i: int), Right(i: int)
}

procedure P3(a: int) {
  var left: Perm;
  left->i := a;
  assert left == Left(a);
}

procedure P4(s: Perm) returns (i: int)
ensures i == s->i;
{
  var s': Perm;
  Left(i) := s;
  s' := Left(i);
  assert s == s';
}

procedure P5(p: Pair) returns (q: Pair)
  requires p->a == 0;
  ensures  q->a == 1;
{
  q := p->(a := 1);
  assert q == Pair(1, 1);
}
