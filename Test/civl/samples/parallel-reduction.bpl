yield left procedure {:layer 1} Reduce({:linear_in} A: Map (One int) int, N: int)
returns ({:linear} A': Map (One int) int)
requires {:layer 1} 0 < N;
requires {:layer 1} (forall j: int:: 0 <= j && j < N ==> Map_Contains(A, One(j)));
ensures {:layer 1} A->dom == A'->dom;
{
  var n: int;
  var stride: int;

  A' := A;
  n := N;
  while (n > 1)
  invariant {:layer 1} 0 <= n && n <= N;
  invariant {:layer 1} A->dom == A'->dom;
  {
    stride := n div 2;
    n := n - stride;
    call A' := Add(A', 0, stride);
  }
  // A'[0] contains the sum A[0] + ... + A[N-1]
}

yield left procedure {:layer 1} Add({:linear_in} A: Map (One int) int, i: int, stride: int)
returns ({:linear} A': Map (One int) int)
requires {:layer 1} 0 <= i && i <= stride;
requires {:layer 1} (forall j: int:: i <= j && j < stride ==> Map_Contains(A, One(j)) && Map_Contains(A, One(j + stride)));
ensures {:layer 1} A->dom == A'->dom;
{
  var B: Map (One int) int;

  A' := A;
  if (i == stride) { return; }
  call B := Map_Split(A', Set_Add(Set_Singleton(One(i)), One(i + stride)));
  call B := AddOne(B, i, stride) | A' := Add(A', i + 1, stride);
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
  call Path_Store(B'->val[One(i)], v + v');
}
