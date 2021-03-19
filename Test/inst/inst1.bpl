// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} PA;
function {:constructor} ADD(i: int) : PA;

procedure INV0(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:inst_at "A0"} pa: PA :: PAs[pa] == if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:inst_at "A0"} pa: PA :: PAs[pa] == 0);
  assert {:inst_add "A0", ADD(n)} i == n;
}

procedure INV1(n: int)
{
  var m: int;
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:inst_at "A1"} pa: PA :: PAs[pa] == if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:inst_at "A1"} pa: PA :: PAs[pa] == 0);
  m := n + 1;
  m := m + 1;
  assert {:inst_add "A1", ADD(m-2)} i == n;
}

procedure INV2(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  PAs := (lambda {:inst_at "A2"} pa: PA :: {:labels "A2"} if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall pa: PA :: PAs[pa] == 0);
  assert {:inst_add "A2", ADD(n)} i == n;
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
  PAs := (lambda {:inst_at "A3"} pa: PA :: {:labels "A3"} if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
}

procedure {:inline 1} LookupLambda(i: int, n: int, PAs: [PA]int)
{
  assume (forall pa: PA :: PAs[pa] == 0);
  assert {:inst_add "A3", ADD(n)} i == n;
}
