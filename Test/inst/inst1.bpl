// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype PA { ADD(i: int) }

procedure INV0(n: int)
{
  var i: int;
  var PAs: [PA]int;

  assume 0 <= i;
  assume i <= n;
  assume (forall {:pool "A0"} pa: PA :: PAs[pa] == if pa is ADD && i < pa->i && pa->i <= n then 1 else 0);
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
  assume (forall {:pool "A1"} pa: PA :: PAs[pa] == if pa is ADD && i < pa->i && pa->i <= n then 1 else 0);
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
  PAs := (lambda {:pool "A2"} pa: PA :: if pa is ADD && i < pa->i && pa->i <= n then 1 else 0);
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
  PAs := (lambda {:pool "A3"} pa: PA :: if pa is ADD && i < pa->i && pa->i <= n then 1 else 0);
}

procedure {:inline 1} LookupLambda(i: int, n: int, PAs: [PA]int)
{
  assume (forall pa: PA :: PAs[pa] == 0);
  assert {:add_to_pool "A3", ADD(n)} i == n;
}

procedure INV4()
{
  var members: [int]bool;

  members := (lambda {:pool "A4"} x: int ::
    (exists {:pool "B4"} y: int :: x == y - 1));
  assert {:add_to_pool "A4", 0} {:add_to_pool "B4", 1} members[0];
}

function SkolemPredicate(x: int, y: int): bool;

procedure NestedSkolemization()
{
  var members: [int]bool;

  members := (lambda {:pool "NestedAddress"} x: int ::
    (exists {:pool "NestedIndex"} j: int :: SkolemPredicate(x, j + 1)));
  assert (forall x: int ::
    {:add_to_pool "NestedAddress", x}
    (var at := x;
      (exists i: int ::
        {:add_to_pool "NestedIndex", i - 1}
        SkolemPredicate(at, i))) ==> members[x]);
}
