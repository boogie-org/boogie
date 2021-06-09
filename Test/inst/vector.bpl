// RUN: %boogie -lib "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} Vec_Concat<T>(v1: Vec T, v2: Vec T): Vec T {
    Vec(
        (lambda {:pool "A"} i: int ::
            if (i < 0) then Default()
            else if (0 <= i && i < Vec_Len(v1)) then Vec_Nth(v1, i)
            else if (Vec_Len(v1) <= i && i < Vec_Len(v1) + Vec_Len(v2)) then Vec_Nth(v2, i - Vec_Len(v1))
            else Default()),
        Vec_Len(v1) + Vec_Len(v2)
        )
}

function {:inline} Vec_Slice<T>(v: Vec T, i: int, j: int): Vec T {
    if (0 <= i && i < j && j <= len#Vec(v)) then
        Vec(
            (lambda {:pool "A"} k: int ::
                if (k < 0) then Default()
                else if (0 <= k && k < j - i) then Vec_Nth(v, k + i)
                else Default()),
            j - i
            )
    else Vec_Empty()
}

function {:inline} Vec_Swap<T>(v: Vec T, i: int, j: int): Vec T {
    if (0 <= i && i < len#Vec(v) && 0 <= j && j < len#Vec(v) && i != j)
    then Vec(contents#Vec(v)[i := contents#Vec(v)[j]][j := contents#Vec(v)[i]], len#Vec(v))
    else v
}

function {:inline} Vec_Remove<T>(v: Vec T): Vec T {
    if (0 < len#Vec(v))
    then Vec(contents#Vec(v)[len#Vec(v)-1 := Default()], len#Vec(v) - 1)
    else Vec_Empty()
}

procedure Vec_Ext(A: Vec int, B: Vec int) returns (i: int);
ensures A == B || Vec_Len(A) != Vec_Len(B) || Vec_Nth(A, i) != Vec_Nth(B, i);

procedure Ex0(A: Vec int, i: int)
requires 0 <= i && i < Vec_Len(A);
{
    assert Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i, Vec_Len(A))) == A;
}

procedure Ex1(A: Vec int, i: int)
requires 0 <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(A, i) == Vec_Nth(A, i + 1);
{
    assert
    Vec_Concat(Vec_Slice(A, 0, i + 1), Vec_Slice(A, i + 2, Vec_Len(A)))
    ==
    Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A)));

    assert Vec_Swap(A, i, i+1) == A;
}

procedure Ex2(A: Vec int, i: int, j: int)
requires 0 <= i && i < Vec_Len(A);
requires 0 <= j && j < Vec_Len(A);
requires Vec_Nth(A, i) == Vec_Nth(A, j);
{
    assert Vec_Swap(A, i, j) == A;
}

procedure Ex3(A: Vec int, i: int, j: int)
requires 0 <= i && i < Vec_Len(A);
requires 0 <= j && j < Vec_Len(A);
{
    assert
    Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i, Vec_Len(A)))
    ==
    Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j, Vec_Len(A)));
}

procedure Ex4(A: Vec int, B: Vec int, i: int, e: int)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == B;
{
    var A', B': Vec int;

    A' := Vec_Append(A, e);
    B' := Vec_Append(B, e);

    assert Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))) == B';
}

procedure Ex5(A: Vec int, B: Vec int, i: int, e: int)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Nth(A, i) == Vec_Nth(B, Vec_Len(B) - 1);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == Vec_Slice(B, 0, Vec_Len(B) - 1);
{
    var A', B': Vec int;
    var x: int;

    A' := Vec_Append(A, e);
    B' := Vec_Swap(Vec_Append(B, e), Vec_Len(B) - 1, Vec_Len(B));

    assume {:add_to_pool "A", x}
    Vec_Nth(Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))), x) != Vec_Nth(Vec_Slice(B', 0, Vec_Len(B') - 1), x);
    assert false;
}

procedure Ex6a(A: Vec int, B: Vec int, i: int, e: int)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Nth(A, i) == Vec_Nth(B, Vec_Len(B) - 1);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == Vec_Slice(B, 0, Vec_Len(B) - 1);
{
    var A', B': Vec int;

    A' := Vec_Append(A, e);
    B' := Vec_Swap(Vec_Append(B, e), Vec_Len(B) - 1, Vec_Len(B));

    assert Vec_Nth(A', i) == Vec_Nth(B', Vec_Len(B') - 1);
}

procedure Ex6b(A: Vec int, B: Vec int, i: int, e: int)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Nth(A, i) == Vec_Nth(B, Vec_Len(B) - 1);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == Vec_Slice(B, 0, Vec_Len(B) - 1);
{
    var A', B': Vec int;
    var x: int;

    A' := Vec_Append(A, e);
    B' := Vec_Swap(Vec_Append(B, e), Vec_Len(B) - 1, Vec_Len(B));

    call x := Vec_Ext(Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))), Vec_Slice(B', 0, Vec_Len(B') - 1));
    assert {:add_to_pool "A", x} Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))) == Vec_Slice(B', 0, Vec_Len(B') - 1);
}

procedure Ex7a(A: Vec int, j: int, B: Vec int, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec int;
    var i': int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    assert Vec_Nth(B', i') == Vec_Nth(A, j);
}

procedure Ex7b(A: Vec int, j: int, B: Vec int, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec int;
    var i': int;
    var x: int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    call x := Vec_Ext(Vec_Slice(B', 0, i'), Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1)));
    assert {:add_to_pool "A", 0, x + j, x - j, x, x + 1, x - 1} Vec_Slice(B', 0, i') == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1));
}

procedure Ex7c(A: Vec int, j: int, B: Vec int, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec int;
    var i': int;
    var x: int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    call x := Vec_Ext(Vec_Slice(B', i' + 1, Vec_Len(B')), Vec_Slice(A, i' + 1, Vec_Len(A)));
    assert {:add_to_pool "A", x, x + 1} Vec_Slice(B', i' + 1, Vec_Len(B')) == Vec_Slice(A, i' + 1, Vec_Len(A));
}

procedure Ex7(A: Vec int, j: int, B: Vec int, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec int;
    var i': int;
    var x, y: int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    assert Vec_Nth(B', i') == Vec_Nth(A, j);
    call x := Vec_Ext(Vec_Slice(B', 0, i'), Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1)));
    assert {:add_to_pool "A", 0, x + j, x - j, x, x + 1, x - 1} Vec_Slice(B', 0, i') == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1));
    call y := Vec_Ext(Vec_Slice(B', i' + 1, Vec_Len(B')), Vec_Slice(A, i' + 1, Vec_Len(A)));
    assert {:add_to_pool "A", y, y + 1} Vec_Slice(B', i' + 1, Vec_Len(B')) == Vec_Slice(A, i' + 1, Vec_Len(A));
}

procedure remove(A: Vec int, j: int) returns (B: Vec int, e: int)
requires 0 <= j && j < Vec_Len(A);
ensures e == Vec_Nth(A, j);
ensures B == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, Vec_Len(A)));
{
    var i: int;
    var x, y, z: int;

    B := A;
    i := j;
    while (i < Vec_Len(A) - 1)
    invariant j <= i && i <= Vec_Len(A) - 1;
    invariant Vec_Nth(B, i) == Vec_Nth(A, j);
    invariant Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
    invariant Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
    {
        assume {:add_to_pool "A", i, j} true;

        B := Vec_Swap(B, i, i + 1);
        i := i + 1;

        assume {:add_to_pool "A", i} true;
        call x := Vec_Ext(Vec_Slice(B, 0, i), Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1)));
        assume {:add_to_pool "A", 0, x + j, x - j, x, x + 1, x - 1} true;
        call y := Vec_Ext(Vec_Slice(B, i + 1, Vec_Len(B)), Vec_Slice(A, i + 1, Vec_Len(A)));
        assume {:add_to_pool "A", y, y + 1} true;
        assume {:add_to_pool "A", i} true;
    }
    e := Vec_Nth(B, Vec_Len(A) - 1);
    B := Vec_Remove(B);
    call z := Vec_Ext(B, Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, Vec_Len(A))));
    assume {:add_to_pool "A", z, j, j + 1, j - 1} true;
}
