// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function PowerOfTwo(i: int): int;
axiom (forall i: int:: PowerOfTwo(i) > 0);
axiom PowerOfTwo(0) == 1;
axiom (forall i: int:: i > 0 ==> PowerOfTwo(i) == 2 * PowerOfTwo(i-1));
axiom (forall i, j: int:: i < j ==> PowerOfTwo(i) < PowerOfTwo(j));

yield left procedure {:layer 1} UpSweep({:linear_in} A: Map (One int) int, N: int)
returns ({:linear} A': Map (One int) int)
requires {:layer 1} 0 < N;
requires {:layer 1} (forall j: int:: 0 <= j && j < PowerOfTwo(N) ==> Map_Contains(A, One(j)));
ensures {:layer 1} A->dom == A'->dom;
{
  var n: int;

  A' := A;
  n := 0;
  while (n < N)
  invariant {:layer 1} 0 <= n;
  invariant {:layer 1} A->dom == A'->dom;
  {
    call A' := UpSweepAtLevel(A', PowerOfTwo(n) - 1, n, N);
    n := n + 1;
  }
}

yield left procedure {:layer 1} UpSweepAtLevel({:linear_in} A: Map (One int) int, i: int, level: int, N: int)
returns ({:linear} A': Map (One int) int)
requires {:layer 1} 0 <= i;
requires {:layer 1} ((i + 1 - PowerOfTwo(level)) mod (2 * PowerOfTwo(level))) == 0;
requires {:layer 1} 0 <= level && level < N;
requires {:layer 1} (forall j: int:: i <= j && j < PowerOfTwo(N) ==> Map_Contains(A, One(j)));
ensures {:layer 1} A->dom == A'->dom;
{
  var B: Map (One int) int;
  var stride: int;

  A' := A;
  if (i == PowerOfTwo(N)) { return; }
  stride := PowerOfTwo(level);
  call B := Map_Split(A', Set_Add(Set_Singleton(One(i)), One(i + stride)));
  call B := AddOne(B, i, stride) | A' := UpSweepAtLevel(A', i + 2 * stride, level, N);
  call Map_Join(A', B);
}

yield left procedure {:layer 1} AddOne({:linear_in} B: Map (One int) int, i: int, stride: int)
returns ({:linear} B': Map (One int) int)
requires {:layer 1} Map_Contains(B, One(i)) && Map_Contains(B, One(i + stride));
ensures {:layer 1} B->dom == B'->dom;
{
  var v, v': int;

  B' := B;
  call v := Path_Load(B'->val[One(i)]);
  call v' := Path_Load(B'->val[One(i + stride)]);
  call Path_Store(B'->val[One(i + stride)], v + v');
}
