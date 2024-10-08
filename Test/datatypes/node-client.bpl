// RUN: %parallel-boogie /lib:base /lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type TreiberNode _;
type StackElem T = Node Loc T;
type StackMap T = Map Loc (StackElem T);
datatype Treiber<T> { Treiber(top: Option Loc, {:linear} stack: StackMap T) }

type X;
var ts: Map Loc (Treiber X);

procedure YieldInv(ref_t: Loc)
requires Map_Contains(ts, ref_t);
requires (var t := Map_At(ts, ref_t); Between(t->stack->val, t->top, None(), None()));
requires (var t := Map_At(ts, ref_t); (var m := t->stack; IsSubset(BetweenSet(m->val, t->top, None()), m->dom->val)));
ensures Map_Contains(ts, ref_t);
ensures (var t := Map_At(ts, ref_t); Between(t->stack->val, t->top, None(), None()));
ensures (var t := Map_At(ts, ref_t); (var m := t->stack; IsSubset(BetweenSet(m->val, t->top, None()), m->dom->val)));
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
  var loc_n_opt: Option Loc;
  assert Map_Contains(ts, loc_t);
  treiber := Map_At(ts, loc_t);
  assume treiber->top is Some && Map_Contains(treiber->stack, treiber->top->t);
  Node(loc_n_opt, x) := Map_At(treiber->stack, treiber->top->t);
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
  assume !Map_Contains(treiber->stack, loc_n);
  treiber->stack := Map_Update(treiber->stack, loc_n, Node(treiber->top, x));
  treiber->top := Some(loc_n);
  ts := Map_Update(ts, loc_t, treiber);
}
