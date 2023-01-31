// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #356

type Vec _;

datatype VecRep<T> { VecRep(v: [int]T, l: int) }


function VecToRep<T>(v: Vec T): VecRep T;
function VecFromRep<T>(v: VecRep T): Vec T;

axiom {:ctor "VecRep"} (forall<T> v: Vec T :: {VecToRep(v)} VecFromRep(VecToRep(v)) == v);

axiom {:ctor "VecRep"} (forall<T> r1, r2: VecRep T :: {VecFromRep(r1), VecFromRep(r2)}
    VecRepIsEqual(r1, r2) <==> VecFromRep(r1) == VecFromRep(r2));

function {:inline} VecRepIsEqual<T>(r1: VecRep T, r2: VecRep T): bool {
    r1 == r2 ||
    (var l := r1->l;
     l == r2->l &&
     (forall i: int :: {r1->v[i], r2->v[i]}
         i >=0 && i < l ==> r1->v[i] == r2->v[i]))
}

function DefaultVecMap<T>(): [int]T;
function {:inline} EmptyVecRep<T>(): VecRep T {
    VecRep(DefaultVecMap(), 0)
}

function {:inline} EmptyVec<T>(): Vec T {
    VecFromRep(EmptyVecRep())
}

function {:inline} SingleVec<T>(v: T): Vec T {
    VecFromRep(VecRep(DefaultVecMap()[0 := v], 1))
}

function {:inline} ReadVec<T>(a: Vec T, i: int): T {
    VecToRep(a)->v[i]
}

function {:inline} LenVec<T>(a: Vec T): int {
    VecToRep(a)->l
}

function {:inline} RemoveVec<T>(a: Vec T): Vec T {
    (var r := VecToRep(a);
    (var l := r->l - 1;
     VecFromRep(VecRep(r->v, l))))
}

function {:inline} RemoveAtVec<T>(a: Vec T, i: int): Vec T {
    (var r := VecToRep(a);
    (var l := r->l - 1;
    VecFromRep(VecRep(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then r->v[j] else r->v[j+1]
           else DefaultVecMap()[0]),
        l))))
}

function {:inline} ConcatVec<T>(a1: Vec T, a2: Vec T): Vec T {
    (var r1, r2 := VecToRep(a1), VecToRep(a2);
    (var l1, m1, l2, m2 := r1->l, r1->v, r2->l, r2->v;
    VecFromRep(VecRep(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecMap()[0]),
        l1 + l2))))
}

procedure test() {
    var v1: Vec int;
    var v2: Vec int;
    v1 := RemoveAtVec(ConcatVec(SingleVec(1), SingleVec(2)), 0);
    v2 := SingleVec(2);
    assert v1 == v2;
}
