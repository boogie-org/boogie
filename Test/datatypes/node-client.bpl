// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<T> { Treiber(top: RefNode T, stack: Lmap (RefNode T) (Node T)) }
type RefTreiber T = Ref (Treiber T);

type X;
var ts: Lmap (RefTreiber X) (Treiber X);

procedure YieldInv(ref_t: RefTreiber X)
requires Map_Contains(ts->val, ref_t);
requires (var t := Map_At(ts->val, ref_t); BetweenSet(t->stack->val->val, t->top, Nil())[t->top]);
requires (var t := Map_At(ts->val, ref_t); (var m := t->stack->val; Subset(BetweenSet(m->val, t->top, Nil()), m->dom->val[Nil() := true])));
ensures Map_Contains(ts->val, ref_t);
ensures (var t := Map_At(ts->val, ref_t); BetweenSet(t->stack->val->val, t->top, Nil())[t->top]);
ensures (var t := Map_At(ts->val, ref_t); (var m := t->stack->val; Subset(BetweenSet(m->val, t->top, Nil()), m->dom->val[Nil() := true])));
modifies ts;
{
  var x: X;
  call x := AtomicPopIntermediate(ref_t);
  call AtomicPushIntermediate(ref_t, x);
}

procedure {:inline 1} AtomicPopIntermediate(ref_t: RefTreiber X) returns (x: X)
modifies ts;
{
  var ref_n: RefNode X;
  assert Map_Contains(ts->val, ref_t);
  assume ts->val->val[ref_t]->top != Nil() && Map_Contains(ts->val->val[ref_t]->stack->val, ts->val->val[ref_t]->top);
  Node(ref_n, x) := Map_At(ts->val->val[ref_t]->stack->val, ts->val->val[ref_t]->top);
  ts->val->val[ref_t]->top := ref_n;
}

procedure {:inline 1} AtomicPushIntermediate(ref_t: RefTreiber X, x: X)
modifies ts;
{
  var t: RefNode X;
  var ref_n: RefNode X;
  var loc_n: Lval (Loc (Node X));
  var lmap_n: Lmap (RefNode X) (Node X);
  var lmap_n': Lmap (RefNode X) (Node X);
  assert Map_Contains(ts->val, ref_t);
  t := ts->val->val[ref_t]->top;
  call loc_n, lmap_n := Lmap_Alloc(Node(t, x));
  call Lmap_Assume(lmap_n, ts->val->val[ref_t]->stack);
  ref_n := Ref(loc_n->val);
  call lmap_n, lmap_n' := Lmap_Move(lmap_n, ts->val->val[ref_t]->stack, ref_n);
  ts->val->val[ref_t]->stack := lmap_n';
  ts->val->val[ref_t]->top := ref_n;
}
