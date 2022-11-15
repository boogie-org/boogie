// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// procedures Ex0 to Ex9 are exercises to ramp up to the "real" vector procedures
procedure Ex0<Element>(A: Vec Element, i: int)
requires 0 <= i && i < Vec_Len(A);
{
    assert Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i, Vec_Len(A))) == A;
}

procedure Ex1<Element>(A: Vec Element, i: int)
requires 0 <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(A, i) == Vec_Nth(A, i + 1);
{
    assert
    Vec_Concat(Vec_Slice(A, 0, i + 1), Vec_Slice(A, i + 2, Vec_Len(A)))
    ==
    Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A)));

    assert Vec_Swap(A, i, i+1) == A;
}

procedure Ex2<Element>(A: Vec Element, i: int, j: int)
requires 0 <= i && i < Vec_Len(A);
requires 0 <= j && j < Vec_Len(A);
requires Vec_Nth(A, i) == Vec_Nth(A, j);
{
    assert Vec_Swap(A, i, j) == A;
}

procedure Ex3<Element>(A: Vec Element, i: int, j: int)
requires 0 <= i && i < Vec_Len(A);
requires 0 <= j && j < Vec_Len(A);
{
    assert
    Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i, Vec_Len(A)))
    ==
    Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j, Vec_Len(A)));
}

procedure Ex4<Element>(A: Vec Element, B: Vec Element, i: int, e: Element)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == B;
{
    var A', B': Vec Element;

    A' := Vec_Append(A, e);
    B' := Vec_Append(B, e);

    assert Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))) == B';
}

procedure Ex5<Element>(A: Vec Element, B: Vec Element, i: int, e: Element)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Len(A) == Vec_Len(B);
requires Vec_Nth(A, i) == Vec_Nth(B, Vec_Len(B) - 1);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == Vec_Slice(B, 0, Vec_Len(B) - 1);
{
    var A', B': Vec Element;

    A' := Vec_Append(A, e);
    B' := Vec_Swap(Vec_Append(B, e), Vec_Len(B) - 1, Vec_Len(B));

    assert (forall x: int :: {:add_to_pool "Slice", x}
    Vec_Nth(Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))), x) == Vec_Nth(Vec_Slice(B', 0, Vec_Len(B') - 1), x));
}

procedure Ex6a<Element>(A: Vec Element, B: Vec Element, i: int, e: Element)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Len(A) == Vec_Len(B);
requires Vec_Nth(A, i) == Vec_Nth(B, Vec_Len(B) - 1);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == Vec_Slice(B, 0, Vec_Len(B) - 1);
{
    var A', B': Vec Element;

    A' := Vec_Append(A, e);
    B' := Vec_Swap(Vec_Append(B, e), Vec_Len(B) - 1, Vec_Len(B));

    assert Vec_Nth(A', i) == Vec_Nth(B', Vec_Len(B') - 1);
}

procedure Ex6b<Element>(A: Vec Element, B: Vec Element, i: int, e: Element)
requires 0 <= i && i < Vec_Len(A);
requires Vec_Len(A) == Vec_Len(B);
requires Vec_Nth(A, i) == Vec_Nth(B, Vec_Len(B) - 1);
requires Vec_Concat(Vec_Slice(A, 0, i), Vec_Slice(A, i + 1, Vec_Len(A))) == Vec_Slice(B, 0, Vec_Len(B) - 1);
{
    var A', B': Vec Element;
    var x: int;

    A' := Vec_Append(A, e);
    B' := Vec_Swap(Vec_Append(B, e), Vec_Len(B) - 1, Vec_Len(B));

    call x := Vec_Ext(Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))), Vec_Slice(B', 0, Vec_Len(B') - 1));
    assert {:add_to_pool "Slice", x}
    Vec_Concat(Vec_Slice(A', 0, i), Vec_Slice(A', i + 1, Vec_Len(A'))) == Vec_Slice(B', 0, Vec_Len(B') - 1);
}

procedure Ex7a<Element>(A: Vec Element, j: int, B: Vec Element, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec Element;
    var i': int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    assert Vec_Nth(B', i') == Vec_Nth(A, j);
}

procedure Ex7b<Element>(A: Vec Element, j: int, B: Vec Element, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec Element;
    var i': int;
    var x: int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    call x := Vec_Ext(Vec_Slice(B', 0, i'), Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1)));
    assert {:add_to_pool "Slice", 0, x + j, x - j, x, x + 1, x - 1}
    Vec_Slice(B', 0, i') == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1));
}

procedure Ex7c<Element>(A: Vec Element, j: int, B: Vec Element, i: int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
{
    var B': Vec Element;
    var i': int;
    var x: int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    call x := Vec_Ext(Vec_Slice(B', i' + 1, Vec_Len(B')), Vec_Slice(A, i' + 1, Vec_Len(A)));
    assert {:add_to_pool "Slice", x, x + 1}
    Vec_Slice(B', i' + 1, Vec_Len(B')) == Vec_Slice(A, i' + 1, Vec_Len(A));
}

procedure Ex8<Element>(A: Vec Element, j: int, B: Vec Element, i: int)
returns (B': Vec Element, i': int)
requires 0 <= j && j <= i && i < Vec_Len(A) - 1;
requires Vec_Nth(B, i) == Vec_Nth(A, j);
requires Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
requires Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
ensures i' == i + 1;
ensures Vec_Nth(B', i') == Vec_Nth(A, j);
ensures Vec_Slice(B', 0, i') == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1));
ensures Vec_Slice(B', i' + 1, Vec_Len(B')) == Vec_Slice(A, i' + 1, Vec_Len(A));
ensures Vec_Len(B) == Vec_Len(B');
{
    var x, y: int;

    B' := Vec_Swap(B, i, i + 1);
    i' := i + 1;

    assert Vec_Nth(B', i') == Vec_Nth(A, j);
    call x := Vec_Ext(Vec_Slice(B', 0, i'), Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1)));
    assert {:add_to_pool "Slice", 0, x + j, x - j, x, x + 1, x - 1}
    Vec_Slice(B', 0, i') == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i' + 1));
    call y := Vec_Ext(Vec_Slice(B', i' + 1, Vec_Len(B')), Vec_Slice(A, i' + 1, Vec_Len(A)));
    assert {:add_to_pool "Slice", y, y + 1}
    Vec_Slice(B', i' + 1, Vec_Len(B')) == Vec_Slice(A, i' + 1, Vec_Len(A));
}

procedure Ex9<Element>(A: Vec Element, j: int) returns (B: Vec Element, e: Element)
requires 0 <= j && j < Vec_Len(A);
ensures e == Vec_Nth(A, j);
ensures B == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, Vec_Len(A)));
{
    var i: int;
    var x, y, z: int;

    B := A;
    i := j;
    assert {:split_here} true;
    while (i < Vec_Len(A) - 1)
    invariant j <= i && i <= Vec_Len(A) - 1;
    invariant Vec_Len(A) == Vec_Len(B);
    invariant Vec_Nth(B, i) == Vec_Nth(A, j);
    invariant Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
    invariant Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
    {
        call B, i := Ex8(A, j, B, i);
        assert {:split_here} true;
    }
    assert {:split_here} true;
    e := Vec_Nth(B, Vec_Len(A) - 1);
    B := Vec_Remove(B);
    call z := Vec_Ext(B, Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, Vec_Len(A))));
    assume {:add_to_pool "Slice", z, j, j + 1, j - 1} true;
}

// "real" vector procedures start here
procedure remove<Element>(A: Vec Element, j: int) returns (B: Vec Element, e: Element)
requires 0 <= j && j < Vec_Len(A);
ensures e == Vec_Nth(A, j);
ensures B == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, Vec_Len(A)));
{
    var i: int;
    var x, y, z: int;

    B := A;
    i := j;
    assert {:split_here} true;
    while (i < Vec_Len(A) - 1)
    invariant j <= i && i <= Vec_Len(A) - 1;
    invariant Vec_Len(A) == Vec_Len(B);
    invariant Vec_Nth(B, i) == Vec_Nth(A, j);
    invariant Vec_Slice(B, 0, i) == Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1));
    invariant Vec_Slice(B, i + 1, Vec_Len(B)) == Vec_Slice(A, i + 1, Vec_Len(A));
    {
        B := Vec_Swap(B, i, i + 1);
        i := i + 1;
        call x := Vec_Ext(Vec_Slice(B, 0, i), Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, i + 1)));
        assume {:add_to_pool "Concat", x} {:add_to_pool "Slice", 0, x, x - j} true;
        call y := Vec_Ext(Vec_Slice(B, i + 1, Vec_Len(B)), Vec_Slice(A, i + 1, Vec_Len(A)));
        assume {:add_to_pool "Slice", y, y + 1} true;
        assert {:split_here} true;
    }
    assert {:split_here} true;
    e := Vec_Nth(B, Vec_Len(A) - 1);
    B := Vec_Remove(B);
    call z := Vec_Ext(B, Vec_Concat(Vec_Slice(A, 0, j), Vec_Slice(A, j + 1, Vec_Len(A))));
    assume {:add_to_pool "Concat", z} {:add_to_pool "Slice", z, z - j} true;
}

procedure swap_remove<Element>(A: Vec Element, j: int) returns (B: Vec Element)
requires 0 <= j && j < Vec_Len(A);
ensures Vec_Slice(B, 0, j) == Vec_Slice(A, 0, j);
ensures Vec_Slice(B, j+1, Vec_Len(B)) == Vec_Slice(A, j+1, Vec_Len(B));
ensures Vec_Len(B) == Vec_Len(A) - 1;
ensures j < Vec_Len(B) ==> Vec_Nth(B, j) == Vec_Nth(A, Vec_Len(A) - 1);
{
    var last_idx: int;

    last_idx := Vec_Len(A) - 1;
    B := Vec_Swap(A, j, last_idx);
    B := Vec_Remove(B);
    assume {:add_to_pool "Slice", j, j + 1} true;
}

procedure reverse<Element>(A: Vec Element) returns (B: Vec Element)
ensures Vec_Len(A) == Vec_Len(B);
ensures (forall x: int :: 0 <= x && x < Vec_Len(A) ==> Vec_Nth(A, x) == Vec_Nth(B, Vec_Len(A) - 1 - x));
{
    var len: int;
    var front_index: int;
    var back_index: int;

    B := A;
    len := Vec_Len(A);
    if (len == 0) {
        return;
    }

    front_index := 0;
    back_index := len - 1;
    while (front_index < back_index)
    invariant front_index + back_index == len - 1;
    invariant Vec_Len(A) == Vec_Len(B);
    invariant (forall x: int :: 0 <= x && x < front_index ==> Vec_Nth(A, x) == Vec_Nth(B, Vec_Len(A) - 1 - x));
    invariant (forall x: int :: back_index < x && x < Vec_Len(A) ==> Vec_Nth(A, x) == Vec_Nth(B, Vec_Len(A) - 1 - x));
    invariant (forall x: int :: front_index <= x && x <= back_index ==> Vec_Nth(A, x) == Vec_Nth(B, x));
    {
        B := Vec_Swap(B, front_index, back_index);
        front_index := front_index + 1;
        back_index := back_index - 1;
    }
}

procedure append<Element>(A: Vec Element, B: Vec Element) returns (C: Vec Element)
ensures C == Vec_Concat(A, B);
{
    var R: Vec Element;
    var e: Element;
    var y: int;

    C := A;
    call R := reverse(B);
    assert {:split_here} true;
    while (0 < Vec_Len(R))
    invariant Vec_Len(R) <= Vec_Len(B);
    invariant (forall {:pool "L"} x: int :: {:add_to_pool "L", 0, x + 1}
    0 <= x && x < Vec_Len(R) ==> Vec_Nth(B, x + Vec_Len(B) - Vec_Len(R)) == Vec_Nth(R, Vec_Len(R) - 1 - x));
    invariant C == Vec_Concat(A, Vec_Slice(B, 0, Vec_Len(B) - Vec_Len(R)));
    {
        e := Vec_Nth(R, Vec_Len(R) - 1);
        C := Vec_Append(C, e);
        R := Vec_Remove(R);
        call y := Vec_Ext(C, Vec_Concat(A, Vec_Slice(B, 0, Vec_Len(B) - Vec_Len(R))));
        assume {:add_to_pool "Concat", y} {:add_to_pool "Slice", y - Vec_Len(A)} true;
        assert {:split_here} true;
    }
    assert {:split_here} true;
}

procedure contains<Element>(A: Vec Element, e: Element) returns (found: bool)
ensures !found <==> (forall x: int :: 0 <= x && x < Vec_Len(A) ==> Vec_Nth(A, x) != e);
{
    var i: int;
    var len: int;

    found := false;
    i := 0;
    len := Vec_Len(A);
    while (i < len)
    invariant 0 <= i;
    invariant (forall x: int :: 0 <= x && x < i ==> Vec_Nth(A, x) != e);
    {
        if (Vec_Nth(A, i) == e) {
            found := true;
            return;
        }
        i := i + 1;
    }
}

procedure index_of<Element>(A: Vec Element, e: Element) returns (found: bool, pos: int)
ensures found ==> Vec_Nth(A, pos) == e;
ensures !found ==> pos == 0 && (forall x: int :: 0 <= x && x < Vec_Len(A) ==> Vec_Nth(A, x) != e);
{
    var i: int;
    var len: int;

    found, pos := false, 0;
    i := 0;
    len := Vec_Len(A);
    while (i < len)
    invariant (forall x: int :: 0 <= x && x < i ==> Vec_Nth(A, x) != e);
    {
        if (Vec_Nth(A, i) == e) {
            found, pos := true, i;
            return;
        }
        i := i + 1;
    }
}
