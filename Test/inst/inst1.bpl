// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} PA;
function {:constructor} ADD(i: int) : PA;

procedure INV0(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:pool "A0"} pa: PA :: PAs[pa] == if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:pool "A0"} pa: PA :: PAs[pa] == 0);
  assert {:add_to_pool "A0", ADD(n)} i == n;
}

procedure INV1(n: int)
{
  var m: int;
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:pool "A1"} pa: PA :: PAs[pa] == if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:pool "A1"} pa: PA :: PAs[pa] == 0);
  m := n + 1;
  m := m + 1;
  assert {:add_to_pool "A1", ADD(m-2)} i == n;
}

procedure INV2(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  // add all labels used in :pool attributes on bound variables to the body of the lambda
  // to avoid the lambda getting unified with the logically identical lambda on line 64
  PAs := (lambda {:pool "A2"} pa: PA :: {:pool "A2"} if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall pa: PA :: PAs[pa] == 0);
  assert {:add_to_pool "A2", ADD(n)} i == n;
}

procedure INV3(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;

  call PAs := CreateLambda(i, n);
  call LookupLambda(i, n, PAs);
}

procedure {:inline 1} CreateLambda(i: int, n: int) returns (PAs: [PA]int)
{
  // add all labels used in :pool attributes on bound variables to the body of the lambda
  // to avoid the lambda getting unified with the logically identical lambda on line 43
  PAs := (lambda {:pool "A3"} pa: PA :: {:pool "A3"} if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
}

procedure {:inline 1} LookupLambda(i: int, n: int, PAs: [PA]int)
{
  assume (forall pa: PA :: PAs[pa] == 0);
  assert {:add_to_pool "A3", ADD(n)} i == n;
}
