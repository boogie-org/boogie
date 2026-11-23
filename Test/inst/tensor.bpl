// RUN: %parallel-boogie -lib:base -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Tensor1D {
    Tensor1D(start: int, dim0: int, stride0: int)
}

datatype Tensor2D {
    Tensor2D(start: int, dim0: int, dim1: int, stride0: int, stride1: int)
}

function {:inline} Slice1D(tensor: Tensor1D, pos0: int, dim0: int): Tensor1D {
    Tensor1D(tensor->start + pos0 * tensor->stride0, dim0, tensor->stride0)
}

function {:inline} Slice2D(tensor: Tensor2D, pos0: int, pos1: int, dim0: int, dim1: int): Tensor2D {
    Tensor2D(tensor->start + pos0 * tensor->stride0 + pos1 * tensor->stride1,
             dim0, dim1, tensor->stride0, tensor->stride1)
}

function {:inline} Tensor1DAddrs(tensor: Tensor1D): [int]bool {
    (lambda x: int ::
        (exists {:pool "Tensor1DIndex"} i: int :: {:add_to_pool "A", i}
        0 <= i && i < tensor->dim0 && x == tensor->start + i * tensor->stride0))
}

procedure Tensor1DSliceSubset(tensor: Tensor1D, k: int)
requires 0 <= k && k <= tensor->dim0;
requires tensor->stride0 > 0;
{
    var piece: Tensor1D;

    piece := Slice1D(tensor, k, tensor->dim0 - k);
    assume (forall {:pool "A"} x: int :: (exists y: int:: {:add_to_pool "Tensor1DIndex", x + k} true));
    assert Set_IsSubset(Tensor1DAddrs(piece), Tensor1DAddrs(tensor));
}

pure procedure Tensor1DSliceRemove(tensor: Tensor1D, k: int, {:linear_in} addresses: UnitMap (One int))
returns ({:linear} remaining: UnitMap (One int), {:linear} removed: UnitMap (One int))
requires 0 <= k && k <= tensor->dim0;
requires tensor->stride0 > 0;
requires Vals(addresses->dom) == Tensor1DAddrs(tensor);
{
    var piece: Tensor1D;

    piece := Slice1D(tensor, k, tensor->dim0 - k);
    remaining := addresses;
    assume (forall {:pool "A"} x: int :: (exists y: int :: {:add_to_pool "Tensor1DIndex", x + k} true));
    call remaining, removed := Map_Split_Wrapper(remaining, Tensor1DAddrs(tensor), Tensor1DAddrs(piece));
    assert Vals(removed->dom) == Tensor1DAddrs(piece);
    assert Vals(remaining->dom) == Set_Difference(Tensor1DAddrs(tensor), Tensor1DAddrs(piece));
}

pure procedure Map_Split_Wrapper<K,V>({:linear_in} m: Map (One K) V, m_dom_vals: [K]bool, k: [K]bool)
    returns ({:linear} m': Map (One K) V, {:linear} l: Map (One K) V);
requires m->dom == Ones(m_dom_vals);
requires Set_IsSubset(k, m_dom_vals);
ensures m'->dom == Ones(Set_Difference(m_dom_vals, k));
ensures l->dom == Ones(k);

procedure Tensor1DRepeatedSlices(tensor: Tensor1D)
requires 0 <= tensor->dim0;
requires tensor->stride0 > 0;
{
    var processed, remaining, piece: Tensor1D;
    var consumed, size: int;

    consumed := 0;
    processed := Slice1D(tensor, 0, consumed);
    remaining := tensor;
    while (0 < remaining->dim0)
    invariant 0 <= consumed && consumed <= tensor->dim0;
    invariant remaining == Slice1D(tensor, consumed, tensor->dim0 - consumed);
    invariant processed == Slice1D(tensor, 0, consumed);
    {
        havoc size;
        assume 0 < size && size <= remaining->dim0;

        // Supply index translations without adding mathematical assumptions.
        assume (forall {:pool "A"} x: int :: (exists y: int :: {:add_to_pool "Tensor1DIndex", x,  x + consumed} true));

        piece := Slice1D(remaining, 0, size);
        assert Set_IsSubset(Tensor1DAddrs(piece), Tensor1DAddrs(remaining));
        assert Set_IsDisjoint(Tensor1DAddrs(processed), Tensor1DAddrs(piece));
        
        remaining := Slice1D(remaining, size, remaining->dim0 - size);
        consumed := consumed + size;
        processed := Slice1D(tensor, 0, consumed);
        assert Set_IsSubset(Tensor1DAddrs(piece), Tensor1DAddrs(processed));
    }
    assert consumed == tensor->dim0;
    assert processed == tensor;
}

procedure Tensor1DSplitDisjoint(tensor: Tensor1D, k: int)
requires 0 <= k && k <= tensor->dim0;
requires tensor->stride0 != 0;
{
    assert (forall x: int ::
        !(Tensor1DAddrs(Slice1D(tensor, 0, k))[x] &&
          Tensor1DAddrs(Slice1D(tensor, k, tensor->dim0 - k))[x]));
}

function {:inline} Tensor2DAddrs(tensor: Tensor2D): [int]bool {
    (lambda x: int :: (exists i, j: int ::
        0 <= i && i < tensor->dim0 && 0 <= j && j < tensor->dim1 &&
        x == tensor->start + i * tensor->stride0 + j * tensor->stride1))
}

procedure Tensor2DSplitDisjoint(tensor: Tensor2D, k: int)
requires 0 <= k && k <= tensor->dim0;
requires 0 <= tensor->dim1;
requires tensor->stride0 == tensor->dim1 * tensor->stride1;
requires tensor->stride1 != 0;
{
    assert (forall x: int ::
        !(Tensor2DAddrs(Slice2D(tensor, 0, 0, k, tensor->dim1))[x] &&
          Tensor2DAddrs(Slice2D(tensor, k, 0, tensor->dim0 - k, tensor->dim1))[x]));
}

function {:inline} Ones<T>(set: [T]bool): [One T]bool {
    (lambda x: One T:: set[x->val])
}

function {:inline} Vals<T>(one_set: [One T]bool): [T]bool {
    (lambda x: T:: one_set[One(x)])
}
