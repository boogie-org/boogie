// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type TaggedLocNode V = TaggedLoc (Node V) Unit;

datatype Treiber<V> { Treiber(top: Option (LocNode V), {:linear} nodes: Map (LocNode V) (Node V)) }
type LocTreiber V = Loc (Treiber V);
type TaggedLocTreiber V = TaggedLoc (Treiber V) Unit;

type X;
var ts: Map (LocTreiber X) (Treiber X);

procedure YieldInv(ref_t: LocTreiber X)
requires Map_Contains(ts, ref_t);
requires (var t := Map_At(ts, ref_t); Between(t->nodes->val, t->top, None(), None()));
requires (var t := Map_At(ts, ref_t); (var m := t->nodes; IsSubset(BetweenSet(m->val, t->top, None()), m->dom->val)));
ensures Map_Contains(ts, ref_t);
ensures (var t := Map_At(ts, ref_t); Between(t->nodes->val, t->top, None(), None()));
ensures (var t := Map_At(ts, ref_t); (var m := t->nodes; IsSubset(BetweenSet(m->val, t->top, None()), m->dom->val)));
modifies ts;
{
  var x: X;
  call x := AtomicPopIntermediate(ref_t);
  call AtomicPushIntermediate(ref_t, x);
}

procedure {:inline 1} AtomicPopIntermediate(loc_t: LocTreiber X) returns (x: X)
modifies ts;
{
  var treiber: Treiber X;
  var loc_n_opt: Option (LocNode X);
  assert Map_Contains(ts, loc_t);
  treiber := Map_At(ts, loc_t);
  assume treiber->top is Some && Map_Contains(treiber->nodes, treiber->top->t);
  Node(loc_n_opt, x) := Map_At(treiber->nodes, treiber->top->t);
  treiber->top := loc_n_opt;
  ts := Map_Update(ts, loc_t, treiber);
}

procedure {:inline 1} AtomicPushIntermediate(loc_t: LocTreiber X, x: X)
modifies ts;
{
  var treiber: Treiber X;
  var loc_n: LocNode X;
  assert Map_Contains(ts, loc_t);
  treiber := Map_At(ts, loc_t);
  assume !Map_Contains(treiber->nodes, loc_n);
  treiber->nodes := Map_Update(treiber->nodes, loc_n, Node(treiber->top, x));
  treiber->top := Some(loc_n);
  ts := Map_Update(ts, loc_t, treiber);
}
