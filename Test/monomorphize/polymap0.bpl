// RUN: %parallel-boogie /monomorphize /useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType = <A, B> [Ref, Field A B]B;
const $b: Field NormalField bool;
const $i: Field NormalField int;
const $R: Field NormalField Ref;

procedure A(h: HeapType)
returns (h': HeapType)
ensures h' == h;
{
    var r, s: Ref;
    h' := h;
    h'[r, $R] := r;
    assert h' == h[r, $R := r];
    s := h[r, $R];
    assert h == h'[r, $R := s];
    h'[r, $R] := s;
}

procedure B(h: HeapType)
returns (h': HeapType)
ensures h' == h;
{
    var r: Ref;
    var b, c: bool;
    call h' := A(h);
    h'[r, $b] := b;
    assert h' == h[r, $b := b];
    c := h[r, $b];
    assert h == h'[r, $b := c];
    h'[r, $b] := c;
}

procedure C<X>(m: <B>[Ref]B, r: Ref, f: Field NormalField X, h: HeapType) returns (h': HeapType)
ensures h' == h[r, f := m[r]];
{
    var x: X;
    h' := h;
    h'[r, f] := m[r];
    assert h' == h[r, f := m[r]];
    x := h'[r, f];
    assert x == m[r];
}

type {:datatype} Pair _;
function {:constructor} Pair<T>(first: T, second: T): Pair T;

procedure D<T>(m: <B>[Ref]B, r: Ref, f: Field NormalField (Pair T), h: HeapType, t: T) returns (h': HeapType)
requires m[r] == Pair(t, t);
ensures h'[r, f] == Pair(t, t);
{
    call h' := C(m, r, f, h);
}

procedure E(m: <B>[Ref]B, r: Ref, f: Field NormalField (Pair int), h: HeapType, t: int) returns (h': HeapType)
requires m[r] == Pair(t, t);
ensures h'[r,f] is Pair;
ensures h'[r, f]->first + h'[r, f]->second == 2*t;
{
    call h' := C(m, r, f, h);
}
