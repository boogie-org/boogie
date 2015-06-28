// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type T;
const zero: T;

function IsProperIndex(i: int, size: int): bool;

procedure P(a: [int]T, n: int)
  requires (forall i : int :: IsProperIndex(i, n) ==> a[i] == zero);
{
  call Q(a, n);
}

procedure Q(a: [int]T, n: int)
  requires (forall i : int :: IsProperIndex(i, n) ==> |{ B: return a[i] == zero; }|);
{
  call P(a, n);
}

procedure A(a: [int]T, n: int)
{
  assert
    (forall i : int :: IsProperIndex(i, n) ==> a[i] == zero)
    ==>
    (forall i : int :: IsProperIndex(i, n) ==> |{ B: return a[i] == zero; }|);
}

procedure B(a: [int]T, n: int)
{
  assert
    (forall i : int :: IsProperIndex(i, n) ==> |{ B: return a[i] == zero; }|)
    ==>
    (forall i : int :: IsProperIndex(i, n) ==> a[i] == zero);
}

procedure C(a: [int]T, n: int)
{
  Start:
    assume (forall i : int :: IsProperIndex(i, n) ==> a[i] == zero);
    goto Next;
  Next:
    assert (forall i : int :: IsProperIndex(i, n) ==> |{ B: return a[i] == zero; }|);
}

procedure D(a: [int]T, n: int)
{
  Start:
    assume (forall i : int :: IsProperIndex(i, n) ==> |{ B: return a[i] == zero; }|);
    goto Next;
  Next:
    assert (forall i : int :: IsProperIndex(i, n) ==> a[i] == zero);
}
