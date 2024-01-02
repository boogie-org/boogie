// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<T> { Treiber(top: RefNode T, stack: Lmap (RefNode T) (Node T)) }
type RefTreiber T = Ref (Treiber T);

type X;
var ts: Lmap (RefTreiber X) (Treiber X);

procedure YieldInv(ref_t: RefTreiber X)
requires ts->dom[ref_t];
requires BetweenSet(ts->val[ref_t]->stack->val, ts->val[ref_t]->top, Nil())[ts->val[ref_t]->top];
requires Subset(BetweenSet(ts->val[ref_t]->stack->val, ts->val[ref_t]->top, Nil()), Union(Singleton(Nil()), ts->val[ref_t]->stack->dom));
ensures ts->dom[ref_t];
ensures BetweenSet(ts->val[ref_t]->stack->val, ts->val[ref_t]->top, Nil())[ts->val[ref_t]->top];
ensures Subset(BetweenSet(ts->val[ref_t]->stack->val, ts->val[ref_t]->top, Nil()), Union(Singleton(Nil()), ts->val[ref_t]->stack->dom));
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
  assert ts->dom[ref_t];
  assume ts->val[ref_t]->top != Nil() && ts->val[ref_t]->stack->dom[ts->val[ref_t]->top];
  Node(ref_n, x) := ts->val[ref_t]->stack->val[ts->val[ref_t]->top];
  ts->val[ref_t]->top := ref_n;
}

procedure {:inline 1} AtomicPushIntermediate(ref_t: RefTreiber X, x: X)
modifies ts;
{
  var t: RefNode X;
  var ref_n: RefNode X;
  var loc_n: Lval (Loc (Node X));
  var lmap_n: Lmap (RefNode X) (Node X);
  var lmap_n': Lmap (RefNode X) (Node X);
  assert ts->dom[ref_t];
  t := ts->val[ref_t]->top;
  call loc_n, lmap_n := Lmap_Alloc(Node(t, x));
  call Lmap_Assume(lmap_n, ts->val[ref_t]->stack);
  ref_n := Ref(loc_n->val);
  call lmap_n, lmap_n' := Lmap_Move(lmap_n, ts->val[ref_t]->stack, ref_n);
  ts->val[ref_t]->stack := lmap_n';
  ts->val[ref_t]->top := ref_n;
}
