// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} InOrder(x: int, y: int, z: int): bool {
    x <= y && y < z
}

function {:inline} Permutation<E>(A: Vec E, B: Vec E): bool {
    Vec_Len(A) == Vec_Len(B) &&
    (forall {:pool "A"} k: int :: {:add_to_pool "A", k} InOrder(0, k, Vec_Len(A)) ==>
            (exists {:pool "B"} k': int :: {:add_to_pool "B", k'} InOrder(0, k', Vec_Len(B)) ==> Vec_Nth(A, k) == Vec_Nth(B, k')))
}

procedure verify_sort(A: Vec int) returns (B: Vec int)
ensures (forall k: int :: InOrder(0, k, Vec_Len(B) - 1) ==> Vec_Nth(B, k) <= Vec_Nth(B, k + 1));
ensures Permutation(A, B);
{
    var i, j, vlen: int;

    B := A;
	vlen := Vec_Len(B);
    if (vlen <= 1) {
        return;
    }

	i := 0;
	j := 1;
    while (true)
	invariant vlen == Vec_Len(B);
    invariant i < j && j < vlen;
	invariant (forall k: int :: InOrder(0, k, i) ==> Vec_Nth(B, k) <= Vec_Nth(B, k + 1));
    invariant i > 0 ==> (forall k: int :: InOrder(i, k, vlen) ==> Vec_Nth(B, i - 1) <= Vec_Nth(B, k));
    invariant (forall k: int :: InOrder(i, k, j) ==> Vec_Nth(B, i) <= Vec_Nth(B, k));
    invariant Permutation(A, B);
	{
		if (Vec_Nth(B, i) > Vec_Nth(B, j)) {
			B := Vec_Swap(B, i, j);
		}
        assume {:add_to_pool "A", i, j} true;
        assume {:add_to_pool "B", i, j} true;
        if (j < vlen - 1 ) {
			j := j + 1;
		} else {
			i := i + 1;
		}
        if (i == vlen - 1) {
            break;
        }
        j := i + 1;
	}
}
