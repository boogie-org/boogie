type {:datatype} PA;
function {:constructor} ADD(i: int) : PA;

procedure INV0(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:inst_label "A"} pa: PA :: PAs[pa] == if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:inst_label "A"} pa: PA :: PAs[pa] == 0);
  assert {:inst "A", ADD(n)} i == n;
}

procedure INV1(n: int)
{
  var m: int;
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:inst_label "A"} pa: PA :: PAs[pa] == if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:inst_label "A"} pa: PA :: PAs[pa] == 0);
  m := n + 1;
  m := m + 1;
  assert {:inst "A", ADD(m-2)} i == n;
}

procedure INV2(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  PAs := (lambda {:inst_label "A"} pa: PA :: if is#ADD(pa) && i < i#ADD(pa) && i#ADD(pa) <= n then 1 else 0);
  assume (forall {:inst_label "A"} pa: PA :: PAs[pa] == 0);
  assert {:inst "A", ADD(n)} i == n;
}
