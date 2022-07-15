// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type{:datatype} Pair;
function{:constructor} Pair(a: int, b: int): Pair;

procedure P0(p: Pair) returns (q: Pair)
  requires p->a#Pair == 0;
  ensures  q->a#Pair == 1;
{
  assert p->a == p->a#Pair;
  q := p;
  q->a#Pair := 1;
  assert q->b == p->b#Pair;
  q->b#Pair := 1;
  assert q == Pair(1, 1);
}

procedure P1(p: [int]Pair, x: int) returns (q: [int]Pair)
  requires p[x]->a#Pair == 0;
  ensures  q[x]->a#Pair == 1;
{
  assert p[x]->a == p[x]->a#Pair;
  q[x] := p[x];
  q[x]->a#Pair := 1;
  assert q[x]->b == p[x]->b#Pair;
  q[x]->b#Pair := 1;
  assert q[x] == Pair(1, 1);
}

type{:datatype} PairOfMaps;
function{:constructor} PairOfMaps(amap: [int]Pair, bmap: [int]Pair): PairOfMaps;

procedure P2(p: PairOfMaps, x: int) returns (q: PairOfMaps)
  requires p->amap[x]->a == 0;
  ensures  q->bmap[x]->a == 1;
{
  var t: [int]Pair;
  q := p;
  call t := P1(p->amap, x);
  q->bmap := t;
}
