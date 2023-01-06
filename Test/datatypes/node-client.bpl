// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Treiber T;
function {:constructor} Treiber<T>(top: RefNode T, stack: Lmap (Node T)): Treiber T;
type RefTreiber T = Ref (Treiber T);

type X; 
var ts: Lmap (Treiber X);

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
  call Lmap_Write(ts->val[ref_t]->top, ref_n);
}

procedure {:inline 1} AtomicPushIntermediate(ref_t: RefTreiber X, x: X)
modifies ts;
{
  var ref_n: RefNode X;
  assert ts->dom[ref_t];
  call ref_n := Lmap_Add(ts->val[ref_t]->stack, Node(ts->val[ref_t]->top, x));
  call Lmap_Write(ts->val[ref_t]->top, ref_n);
}
