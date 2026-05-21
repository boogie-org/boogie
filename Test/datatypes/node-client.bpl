// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<V> { Treiber(top: Option Loc, nodes: Map (One Loc) (Node V)) }

type X;
var ts: Map Loc (Treiber X);

function {:inline} SubsetInv(ts: Map Loc (Treiber X), ref_t: Loc): bool
{
  (var t := Map_At(ts, ref_t); InDomain(t->nodes, t->top))
}

procedure YieldInv(ref_t: Loc)
requires Map_Contains(ts, ref_t);
requires SubsetInv(ts, ref_t);
ensures Map_Contains(ts, ref_t);
ensures SubsetInv(ts, ref_t);
modifies ts;
{
  var x: X;
  call x := AtomicPopIntermediate(ref_t);
  call AtomicPushIntermediate(ref_t, x);
}

procedure {:inline 1} AtomicPopIntermediate(loc_t: Loc) returns (x: X)
modifies ts;
{
  var treiber: Treiber X;
  var loc_n_opt: Option (Loc);
  assert Map_Contains(ts, loc_t);
  treiber := Map_At(ts, loc_t);
  assume treiber->top is Some && Map_Contains(treiber->nodes, One(treiber->top->t));
  Node(loc_n_opt, x) := Map_At(treiber->nodes, One(treiber->top->t));
  treiber->top := loc_n_opt;
  ts := Map_Update(ts, loc_t, treiber);
}

procedure {:inline 1} AtomicPushIntermediate(loc_t: Loc, x: X)
modifies ts;
{
  var treiber: Treiber X;
  var loc_n: Loc;
  assert Map_Contains(ts, loc_t);
  treiber := Map_At(ts, loc_t);
  assume !Map_Contains(treiber->nodes, One(loc_n));
  treiber->nodes := Map_Update(treiber->nodes, One(loc_n), Node(treiber->top, x));
  treiber->top := Some(loc_n);
  ts := Map_Update(ts, loc_t, treiber);
}
