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
    (lambda {:pool "Tensor1DAddress"} x: int ::
        (exists {:pool "Tensor1DIndex"} i: int ::
        0 <= i && i < tensor->dim0 && x == tensor->start + i * tensor->stride0))
}

procedure Tensor1DSliceSubset(tensor: Tensor1D, k: int)
requires 0 <= k && k <= tensor->dim0;
requires tensor->stride0 == 1;
{
    var slice: Tensor1D;

    slice := Slice1D(tensor, k, tensor->dim0 - k);
    assert (forall x: int ::
        {:add_to_pool "Tensor1DAddress", x}
        (exists {:pool "Tensor1DIndex"} i: int :: 
        {:add_to_pool "Tensor1DIndex", k + i}
        0 <= i && i < slice->dim0 && x == slice->start + i * slice->stride0)
        /*Tensor1DAddrs(slice)[x]*/ ==> Tensor1DAddrs(tensor)[x]);
    assert Set_IsSubset((lambda {:pool "Tensor1DAddress"} x: int ::
        (exists {:pool "Tensor1DIndex"} i: int ::
        {:add_to_pool "Tensor1DIndex", k + i}
        0 <= i && i < slice->dim0 && x == slice->start + i * slice->stride0)), 
        (lambda {:pool "Tensor1DAddress"} x: int ::
        (exists {:pool "Tensor1DIndex"} i: int ::
        {:add_to_pool "Tensor1DIndex", k + i}
        0 <= i && i < tensor->dim0 && x == tensor->start + i * tensor->stride0)));
    //assert Set_IsSubset(Tensor1DAddrs(slice), Tensor1DAddrs(tensor));
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
