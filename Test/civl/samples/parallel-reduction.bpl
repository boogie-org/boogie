yield left procedure {:layer 1} Reduce({:linear_in} A: Map (One int) int, N: int)
returns ({:linear} A': Map (One int) int)
{
  var n: int;
  var stride: int;

  A' := A;
  n := N;
  while (n > 1)
  {
    stride := n div 2;
    n := n - stride;
    call A' := Add(A', 0, stride);
  }
  // A'[0] contains the sum A[0] + ... + A[N-1]
}

yield left procedure {:layer 1} Add({:linear_in} A: Map (One int) int, i: int, stride: int)
returns ({:linear} A': Map (One int) int)
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
{
  var v, v': int;

  B' := B;
  call v := Path_Load(B'->val[One(i)]);
  call v' := Path_Load(B'->val[One(i + stride)]);
  call Path_Store(B'->val[One(i)], v + v');
}
