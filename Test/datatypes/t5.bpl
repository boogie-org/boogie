// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type{:datatype} GenericPair U;
function{:constructor} GenericPair<U>(a: U, b: U): GenericPair U;

procedure P0<T>(p: GenericPair T) returns (q: GenericPair T)
  requires p->a == p->b;
  ensures  q->a == q->b;
{
  q->a := p->b;
  q->b := p->a;
}
