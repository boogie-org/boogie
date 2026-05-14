var {:layer 0, 1} A: [int]int;
// length of array
const N: int;
axiom N > 0;

yield left procedure {:layer 1} Reduce({:linear} ps: UnitMap (One int))
{
  var n: int;
  var stride: int;

  n := N;
  while (n > 1)
  {
    stride := n div 2;
    n := n - stride;
    call Add(ps, 0, stride);
  }
  // A[0] contains the sum A[0] + ... + A[N-1]
}

yield left procedure {:layer 1} Add({:linear} ps: UnitMap (One int), i: int, stride: int)
{
  var ps': UnitMap (One int);
  var tps: UnitMap (One int);

  if (i == stride) { return; }
  ps' := ps;
  call tps := Map_Split(ps', Set_Add(Set_Singleton(One(i)), One(i + stride)));
  call T(tps, i, stride) | Add(ps', i + 1, stride);
  call Map_Join(ps', tps);
  call Move(ps', ps);
}

yield left procedure {:layer 1} T({:linear} ps: UnitMap (One int), i: int, stride: int)
{
  var v, v': int;

  call v := Read(ps, i);
  call v' := Read(ps, i + stride);
  call Write(ps, i, v + v');
}

yield procedure {:layer 0} Read({:linear} ps: UnitMap (One int), i: int) returns (v: int);
refines both action {:layer 1} _ {
  assert Map_Contains(ps, One(i));
  v := A[i];
}

yield procedure {:layer 0} Write({:linear} ps: UnitMap (One int), i: int, v: int);
refines both action {:layer 1} _ {
  assert Map_Contains(ps, One(i));
  A[i] := v;
}

