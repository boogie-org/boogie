// Bubble sort, where specification says the output is a permutation of its input
// Rustan Leino, 30 April 2009

const N: int;
axiom 0 <= N;

var a: [int]int;

procedure BubbleSort() returns (perm: [int]int)
  modifies a;
  // array is sorted
  ensures (forall i, j: int :: 0 <= i && i <= j && j < N ==> a[i] <= a[j]);
  // perm is a permutation
  ensures (forall i: int :: 0 <= i && i < N ==> 0 <= perm[i] && perm[i] < N);
  ensures (forall i, j: int :: 0 <= i && i < j && j < N ==> perm[i] != perm[j]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: 0 <= i && i < N ==> a[i] == old(a)[perm[i]]);
{
  var n, p, tmp: int;

  n := 0;
  while (n < N)
    invariant n <= N;
    invariant (forall i: int :: 0 <= i && i < n ==> perm[i] == i);
  {
    perm[n] := n;
    n := n + 1;
  }

  while (true)
    invariant 0 <= n && n <= N;
    // array is sorted from n onwards
    invariant (forall i, k: int :: n <= i && i < N && 0 <= k && k < i ==> a[k] <= a[i]);
    // perm is a permutation
    invariant (forall i: int :: 0 <= i && i < N ==> 0 <= perm[i] && perm[i] < N);
    invariant (forall i, j: int :: 0 <= i && i < j && j < N ==> perm[i] != perm[j]);
    // the current array is that permutation of the input array
    invariant (forall i: int :: 0 <= i && i < N ==> a[i] == old(a)[perm[i]]);
  {
    n := n - 1;
    if (n < 0) {
      break;
    }

    p := 0;
    while (p < n)
      invariant p <= n;
      // array is sorted from n+1 onwards
      invariant (forall i, k: int :: n+1 <= i && i < N && 0 <= k && k < i ==> a[k] <= a[i]);
      // perm is a permutation
      invariant (forall i: int :: 0 <= i && i < N ==> 0 <= perm[i] && perm[i] < N);
      invariant (forall i, j: int :: 0 <= i && i < j && j < N ==> perm[i] != perm[j]);
      // the current array is that permutation of the input array
      invariant (forall i: int :: 0 <= i && i < N ==> a[i] == old(a)[perm[i]]);
      // a[p] is at least as large as any of the first p elements
      invariant (forall k: int :: 0 <= k && k < p ==> a[k] <= a[p]);
    {
      if (a[p+1] < a[p]) {
        tmp := a[p];  a[p] := a[p+1];  a[p+1] := tmp;
        tmp := perm[p];  perm[p] := perm[p+1];  perm[p+1] := tmp;
      }

      p := p + 1;
    }
  }
}
