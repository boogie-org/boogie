// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type TaggedLocNode V = TaggedLoc (Node V) Unit;

datatype Treiber<V> { Treiber(top: Option (LocNode V), nodes: Map (One (LocNode V)) (Node V)) }
type LocTreiber V = Loc (Treiber V);
type TaggedLocTreiber V = TaggedLoc (Treiber V) Unit;

type X;
var ts: Map (LocTreiber X) (Treiber X);

function {:inline} SubsetInv(ts: Map (LocTreiber X) (Treiber X), ref_t: LocTreiber X): bool
{
  (var t := Map_At(ts, ref_t);
    (var m := t->nodes; 
      (forall x: LocNode X:: BetweenSet(m->val, t->top, None())[x] ==> Set_Contains(m->dom, One(x)))))
}

procedure YieldInv(ref_t: LocTreiber X)
requires Map_Contains(ts, ref_t);
requires (var t := Map_At(ts, ref_t); Between(t->nodes->val, t->top, None(), None()));
requires SubsetInv(ts, ref_t);
ensures Map_Contains(ts, ref_t);
ensures (var t := Map_At(ts, ref_t); Between(t->nodes->val, t->top, None(), None()));
ensures SubsetInv(ts, ref_t);
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
  assume treiber->top is Some && Map_Contains(treiber->nodes, One(treiber->top->t));
  Node(loc_n_opt, x) := Map_At(treiber->nodes, One(treiber->top->t));
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
  assume !Map_Contains(treiber->nodes, One(loc_n));
  treiber->nodes := Map_Update(treiber->nodes, One(loc_n), Node(treiber->top, x));
  treiber->top := Some(loc_n);
  ts := Map_Update(ts, loc_t, treiber);
}
