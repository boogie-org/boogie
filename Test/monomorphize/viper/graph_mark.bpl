// RUN: %parallel-boogie /noVerify "%s" > "%t"

// ==================================================
// Preamble of State module.
// ==================================================

function  state(Heap: HeapType, Mask: MaskType): bool;

// ==================================================
// Preamble of Heap module.
// ==================================================

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType = <A, B> [Ref, Field A B]B;
const unique $allocated: Field NormalField bool;
axiom (forall o: Ref, f: (Field NormalField Ref), Heap: HeapType ::
  { Heap[o, f] }
  Heap[o, $allocated] ==> Heap[Heap[o, f], $allocated]
);
function  succHeap(Heap0: HeapType, Heap1: HeapType): bool;
function  succHeapTrans(Heap0: HeapType, Heap1: HeapType): bool;
function  IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function  IsPredicateField<A, B>(f_1: (Field A B)): bool;
function  IsWandField<A, B>(f_1: (Field A B)): bool;
function  getPredicateId<A, B>(f_1: (Field A B)): int;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o_1: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o_1, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o_1, f_2) ==> Heap[o_1, f_2] == ExhaleHeap[o_1, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// Frame all wand mask locations of wands with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsWandField(pm_f), ExhaleHeap[null, WandMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsWandField(pm_f) ==> Heap[null, WandMaskField(pm_f)] == ExhaleHeap[null, WandMaskField(pm_f)]
);
// Frame all locations in the footprint of magic wands
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsWandField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsWandField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, WandMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o_1: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o_1, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o_1, $allocated] ==> ExhaleHeap[o_1, $allocated]
);
// Updated Heaps are Successor Heaps
axiom (forall <A, B> Heap: HeapType, o: Ref, f_3: (Field A B), v: B ::
  { Heap[o, f_3:=v] }
  succHeap(Heap, Heap[o, f_3:=v])
);
// IdenticalOnKnownLocations Heaps are Successor Heaps
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> succHeap(Heap, ExhaleHeap)
);
// Successor Heaps are Transitive Successor Heaps
axiom (forall Heap0: HeapType, Heap1: HeapType ::
  { succHeap(Heap0, Heap1) }
  succHeap(Heap0, Heap1) ==> succHeapTrans(Heap0, Heap1)
);
// Transitivity of Transitive Successor Heaps
axiom (forall Heap0: HeapType, Heap1: HeapType, Heap2: HeapType ::
  { succHeapTrans(Heap0, Heap1), succHeap(Heap1, Heap2) }
  succHeapTrans(Heap0, Heap1) && succHeap(Heap1, Heap2) ==> succHeapTrans(Heap0, Heap2)
);

// ==================================================
// Preamble of Permission module.
// ==================================================

type Perm = real;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_2: Ref, f_4: (Field A B) ::
  { ZeroMask[o_2, f_4] }
  ZeroMask[o_2, f_4] == NoPerm
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_2: Ref, f_4: (Field A B) ::
  { ZeroPMask[o_2, f_4] }
  !ZeroPMask[o_2, f_4]
);
function  PredicateMaskField<A>(f_5: (Field A FrameType)): Field A PMaskType;
function  WandMaskField<A>(f_5: (Field A FrameType)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function  Perm(a: real, b: real): Perm;
function  GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_2: Ref, f_4: (Field A B) ::
  { GoodMask(Mask), Mask[o_2, f_4] }
  GoodMask(Mask) ==> Mask[o_2, f_4] >= NoPerm && ((GoodMask(Mask) && !IsPredicateField(f_4)) && !IsWandField(f_4) ==> Mask[o_2, f_4] <= FullPerm)
);
function  HasDirectPerm<A, B>(Mask: MaskType, o_2: Ref, f_4: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_2: Ref, f_4: (Field A B) ::
  { HasDirectPerm(Mask, o_2, f_4) }
  HasDirectPerm(Mask, o_2, f_4) <==> Mask[o_2, f_4] > NoPerm
);
function  sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_2: Ref, f_4: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_2, f_4] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_2, f_4] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_2, f_4] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_2, f_4] == SummandMask1[o_2, f_4] + SummandMask2[o_2, f_4]
);
// ==================================================
// Function for trigger used in checks which are never triggered
// ==================================================

function  neverTriggered1(n_3: Ref): bool;
function  neverTriggered2(n$0_3: Ref): bool;
function  neverTriggered3(n$2_1: Ref): bool;
function  neverTriggered4(n$3_1: Ref): bool;
function  neverTriggered5(n$6_1: Ref): bool;
function  neverTriggered6(n$7_1: Ref): bool;
function  neverTriggered7(n: Ref): bool;
function  neverTriggered8(n$0_2: Ref): bool;
function  neverTriggered9(n_1: Ref): bool;
function  neverTriggered10(n$0_3: Ref): bool;
function  neverTriggered11(n$6_2: Ref): bool;
function  neverTriggered12(n$7_2: Ref): bool;
function  neverTriggered13(n$10: Ref): bool;
function  neverTriggered14(n$11: Ref): bool;
function  neverTriggered15(n$10_2: Ref): bool;
function  neverTriggered16(n$11_2: Ref): bool;
function  neverTriggered17(n_7: Ref): bool;
function  neverTriggered18(n$0_4: Ref): bool;
function  neverTriggered19(n_8: Ref): bool;
function  neverTriggered20(n$0_5: Ref): bool;
function  neverTriggered21(n_9: Ref): bool;
function  neverTriggered22(n$0_6: Ref): bool;
function  neverTriggered23(n_10: Ref): bool;
function  neverTriggered24(n$0_7: Ref): bool;
function  neverTriggered25(n_11: Ref): bool;
function  neverTriggered26(n$0_8: Ref): bool;
function  neverTriggered27(n_12: Ref): bool;
function  neverTriggered28(n$0_9: Ref): bool;
function  neverTriggered29(n_13: Ref): bool;
function  neverTriggered30(n$0_10: Ref): bool;
function  neverTriggered31(n$0_11: Ref): bool;
function  neverTriggered32(n$0_12: Ref): bool;
function  neverTriggered33(n_25: Ref): bool;
function  neverTriggered34(n$0_13: Ref): bool;
function  neverTriggered35(n$10_3: Ref): bool;
function  neverTriggered36(n$11_3: Ref): bool;
function  neverTriggered37(n$10_4: Ref): bool;
function  neverTriggered38(n$11_4: Ref): bool;
function  neverTriggered39(n$10_5: Ref): bool;
function  neverTriggered40(n$11_5: Ref): bool;
function  neverTriggered41(n_46: Ref): bool;
function  neverTriggered42(n$0_14: Ref): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function  invRecv1(recv: Ref): Ref;
function  invRecv2(recv: Ref): Ref;
function  invRecv3(recv: Ref): Ref;
function  invRecv4(recv: Ref): Ref;
function  invRecv5(recv: Ref): Ref;
function  invRecv6(recv: Ref): Ref;
function  invRecv7(recv: Ref): Ref;
function  invRecv8(recv: Ref): Ref;
function  invRecv9(recv: Ref): Ref;
function  invRecv10(recv: Ref): Ref;
function  invRecv11(recv: Ref): Ref;
function  invRecv12(recv: Ref): Ref;
function  invRecv13(recv: Ref): Ref;
function  invRecv14(recv: Ref): Ref;
function  invRecv15(recv: Ref): Ref;
function  invRecv16(recv: Ref): Ref;
function  invRecv17(recv: Ref): Ref;
function  invRecv18(recv: Ref): Ref;
function  invRecv19(recv: Ref): Ref;
function  invRecv20(recv: Ref): Ref;
function  invRecv21(recv: Ref): Ref;
function  invRecv22(recv: Ref): Ref;
function  invRecv23(recv: Ref): Ref;
function  invRecv24(recv: Ref): Ref;
function  invRecv25(recv: Ref): Ref;
function  invRecv26(recv: Ref): Ref;
function  invRecv27(recv: Ref): Ref;
function  invRecv28(recv: Ref): Ref;
function  invRecv29(recv: Ref): Ref;
function  invRecv30(recv: Ref): Ref;
function  invRecv31(recv: Ref): Ref;
function  invRecv32(recv: Ref): Ref;
function  invRecv33(recv: Ref): Ref;
function  invRecv34(recv: Ref): Ref;
function  invRecv35(recv: Ref): Ref;
function  invRecv36(recv: Ref): Ref;
function  invRecv37(recv: Ref): Ref;
function  invRecv38(recv: Ref): Ref;
function  invRecv39(recv: Ref): Ref;
function  invRecv40(recv: Ref): Ref;
function  invRecv41(recv: Ref): Ref;
function  invRecv42(recv: Ref): Ref;
// ==================================================
// Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale
// ==================================================

function  qpRange1(recv: Ref): bool;
function  qpRange2(recv: Ref): bool;
function  qpRange3(recv: Ref): bool;
function  qpRange4(recv: Ref): bool;
function  qpRange5(recv: Ref): bool;
function  qpRange6(recv: Ref): bool;
function  qpRange7(recv: Ref): bool;
function  qpRange8(recv: Ref): bool;
function  qpRange9(recv: Ref): bool;
function  qpRange10(recv: Ref): bool;
function  qpRange11(recv: Ref): bool;
function  qpRange12(recv: Ref): bool;
function  qpRange13(recv: Ref): bool;
function  qpRange14(recv: Ref): bool;
function  qpRange15(recv: Ref): bool;
function  qpRange16(recv: Ref): bool;
function  qpRange17(recv: Ref): bool;
function  qpRange18(recv: Ref): bool;
function  qpRange19(recv: Ref): bool;
function  qpRange20(recv: Ref): bool;
function  qpRange21(recv: Ref): bool;
function  qpRange22(recv: Ref): bool;
function  qpRange23(recv: Ref): bool;
function  qpRange24(recv: Ref): bool;
function  qpRange25(recv: Ref): bool;
function  qpRange26(recv: Ref): bool;
function  qpRange27(recv: Ref): bool;
function  qpRange28(recv: Ref): bool;
function  qpRange29(recv: Ref): bool;
function  qpRange30(recv: Ref): bool;
function  qpRange31(recv: Ref): bool;
function  qpRange32(recv: Ref): bool;
function  qpRange33(recv: Ref): bool;
function  qpRange34(recv: Ref): bool;
function  qpRange35(recv: Ref): bool;
function  qpRange36(recv: Ref): bool;
function  qpRange37(recv: Ref): bool;
function  qpRange38(recv: Ref): bool;
function  qpRange39(recv: Ref): bool;
function  qpRange40(recv: Ref): bool;
function  qpRange41(recv: Ref): bool;
function  qpRange42(recv: Ref): bool;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 1: $$
// - height 0: get
const AssumeFunctionsAbove: int;
// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function  FrameFragment<T>(t: T): FrameType;
function  ConditionalFrame(p: Perm, f_6: FrameType): FrameType;
function  dummyFunction<T>(t: T): bool;
function  CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p: Perm, f_6: FrameType ::
  { ConditionalFrame(p, f_6) }
  ConditionalFrame(p, f_6) == (if p > 0.000000000 then f_6 else EmptyFrame)
);
// Function for recording enclosure of one predicate instance in another
function  InsidePredicate<A, B>(p: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType): bool;
// Transitivity of InsidePredicate
axiom (forall <A, B, C> p: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType, r: (Field C FrameType), u: FrameType ::
  { InsidePredicate(p, v_1, q, w), InsidePredicate(q, w, r, u) }
  InsidePredicate(p, v_1, q, w) && InsidePredicate(q, w, r, u) ==> InsidePredicate(p, v_1, r, u)
);
// Knowledge that two identical instances of the same predicate cannot be inside each other
axiom (forall <A> p: (Field A FrameType), v_1: FrameType, w: FrameType ::
  { InsidePredicate(p, v_1, p, w) }
  !InsidePredicate(p, v_1, p, w)
);

// ==================================================
// Preamble of Set module.
// ==================================================


type Set T = [T]bool;

function Set#Card<T>(Set T): int;
axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>(): Set T;
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall<T> s: Set T :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

function Set#Singleton<T>(T): Set T;
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
  Set#UnionOne(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);
//axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
//  Set#Disjoint(a, b) ==>
//    Set#Difference(Set#Union(a, b), a) == b &&
//    Set#Difference(Set#Union(a, b), b) == a);

function Set#Intersection<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] } {Set#Intersection(a,b), a[o]} {Set#Intersection(a,b), b[o]} // AS: added alternative triggers 20/06/19
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] } { Set#Difference(a,b), a[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );
axiom (forall<T> a, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  + Set#Card(Set#Intersection(a, b))
    == Set#Card(Set#Union(a, b)) &&
  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall<T> a: Set T, b: Set T ::
//   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
//   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


function Set#Equal<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

//function Set#Disjoint<T>(Set T, Set T): bool;
//axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
//  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of multisets --------------------------------
// ---------------------------------------------------------------

function Math#min(a: int, b: int): int;
axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

type MultiSet T; // = [T]int;

function MultiSet#Select<T>(ms: MultiSet T, x:T): int;

//function $IsGoodMultiSet<T>(ms: MultiSet T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
//axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
//  $IsGoodMultiSet(ms) <==>
//  (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

axiom (forall<T> ms: MultiSet T, x: T :: {MultiSet#Select(ms,x)} MultiSet#Select(ms,x) >= 0); // NEW

function MultiSet#Card<T>(MultiSet T): int;
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
//axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
//  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);
//
function MultiSet#Empty<T>(): MultiSet T;
axiom (forall<T> o: T :: { MultiSet#Select(MultiSet#Empty(),o) } MultiSet#Select(MultiSet#Empty(),o) == 0);
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < MultiSet#Select(s,x))));

function MultiSet#Singleton<T>(T): MultiSet T;
axiom (forall<T> r: T, o: T :: { MultiSet#Select(MultiSet#Singleton(r),o) } (MultiSet#Select(MultiSet#Singleton(r),o) == 1 <==> r == o) &&
                                                            (MultiSet#Select(MultiSet#Singleton(r),o) == 0 <==> r != o));
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Card(MultiSet#Singleton(r)) == 1 && MultiSet#Select(MultiSet#Singleton(r),r) == 1); // AS: added
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r)); // AS: remove this?

function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
// union-ing increases count by one for x, not for others
axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#Select(MultiSet#UnionOne(a,x),o) } { MultiSet#UnionOne(a, x), MultiSet#Select(a,o) } // AS: added back this trigger (used on a similar axiom before)
  MultiSet#Select(MultiSet#UnionOne(a, x),o) == (if x==o then MultiSet#Select(a,o) + 1 else MultiSet#Select(a,o)));
// non-decreasing
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) } {MultiSet#UnionOne(a, x), MultiSet#Card(a)} // AS: added alternative trigger
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);
// AS: added - concrete knowledge of element added
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a,x)}
  MultiSet#Select(MultiSet#UnionOne(a, x),x) > 0 && MultiSet#Card(MultiSet#UnionOne(a, x)) > 0);

function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
// union-ing is the sum of the contents
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Select(MultiSet#Union(a,b),o) } {MultiSet#Union(a,b), MultiSet#Select(a,o), MultiSet#Select(b,o)}// AS: added triggers
  MultiSet#Select(MultiSet#Union(a,b),o) == MultiSet#Select(a,o) + MultiSet#Select(b,o));
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) } {MultiSet#Card(a), MultiSet#Union(a,b)} {MultiSet#Card(b), MultiSet#Union(a,b)}
  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Select(MultiSet#Intersection(a,b),o) }
  MultiSet#Select(MultiSet#Intersection(a,b),o) == Math#min(MultiSet#Select(a,o),  MultiSet#Select(b,o)));

// left and right pseudo-idempotence
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));

// multiset difference, a - b. clip() makes it positive.
function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Select(MultiSet#Difference(a,b),o) }
  MultiSet#Select(MultiSet#Difference(a,b),o) == Math#clip(MultiSet#Select(a,o) - MultiSet#Select(b,o)));
axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), MultiSet#Select(b,y), MultiSet#Select(a,y) }
  MultiSet#Select(a,y) <= MultiSet#Select(b,y) ==> MultiSet#Select(MultiSet#Difference(a, b),y) == 0 );
axiom (forall<T> a, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
    == MultiSet#Card(MultiSet#Union(a, b)) &&
  MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

// multiset subset means a must have at most as many of each element as b
function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
  MultiSet#Subset(a,b) <==> (forall o: T :: {MultiSet#Select(a,o)} {MultiSet#Select(b,o)} MultiSet#Select(a,o) <= MultiSet#Select(b,o)));

function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) <==> (forall o: T :: {MultiSet#Select(a,o)} {MultiSet#Select(b,o)} MultiSet#Select(a,o) == MultiSet#Select(b,o)));
// extensionality axiom for multisets
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
  MultiSet#Disjoint(a,b) <==> (forall o: T :: {MultiSet#Select(a,o)} {MultiSet#Select(b,o)} MultiSet#Select(a,o) == 0 || MultiSet#Select(b,o) == 0));



// ==================================================
// Translation of domain Edge
// ==================================================

// The type for domain Edge
type EdgeDomainType;

// Translation of domain function edge_pred
function  edge_pred(e: EdgeDomainType): Ref;

// Translation of domain function edge_succ
function  edge_succ(e: EdgeDomainType): Ref;

// Translation of domain function create_edge
function  create_edge(p_1: Ref, s: Ref): EdgeDomainType;

// Translation of domain axiom edge_injectivity
axiom (forall p_2: Ref, s_1: Ref ::
  { (create_edge(p_2, s_1): EdgeDomainType) }
  (edge_pred((create_edge(p_2, s_1): EdgeDomainType)): Ref) == p_2 && (edge_succ((create_edge(p_2, s_1): EdgeDomainType)): Ref) == s_1
);

// ==================================================
// Translation of domain TrClo
// ==================================================

// The type for domain TrClo
type TrCloDomainType;

// Translation of domain function exists_path
function  exists_path(EG: (Set EdgeDomainType), start: Ref, end: Ref): bool;

// Translation of domain function exists_path_
function  exists_path_(EG: (Set EdgeDomainType), start: Ref, end: Ref): bool;

// Translation of domain function exists_spath
function  exists_spath(EG: (Set EdgeDomainType), from: (Set Ref), to: Ref): bool;

// Translation of domain function is_on_path
function  is_on_path(EG: (Set EdgeDomainType), start: Ref, w_1: Ref, end: Ref): bool;

// Translation of domain function apply_IND
function  apply_IND(EG: (Set EdgeDomainType), Z: (Set Ref), P: (Set Ref)): bool;

// Translation of domain function apply_noExit
function  apply_noExit(EG: (Set EdgeDomainType), U: (Set Ref), M: (Set Ref)): bool;

// Translation of domain function apply_goOut
function  apply_goOut(EG: (Set EdgeDomainType), U: (Set Ref), A: (Set Ref), B: (Set Ref)): bool;

// Translation of domain function apply_newStart
function  apply_newStart(U: (Set Ref), A: (Set Ref), EG1: (Set EdgeDomainType), EG2: (Set EdgeDomainType)): bool;

// Translation of domain function inst_uReach
function  inst_uReach(EG: (Set EdgeDomainType), x: Ref): Set Ref;

// Translation of domain function acyclic_graph
function  acyclic_graph(EG: (Set EdgeDomainType)): bool;

// Translation of domain function unshared_graph
function  unshared_graph(EG: (Set EdgeDomainType)): bool;

// Translation of domain function func_graph
function  func_graph(EG: (Set EdgeDomainType)): bool;

// Translation of domain axiom ax_NoExit
axiom (forall EG_1: (Set EdgeDomainType), U_1: (Set Ref), M_1: (Set Ref) ::
  { (apply_noExit(EG_1, U_1, M_1): bool) }
  (apply_noExit(EG_1, U_1, M_1): bool) ==> (forall u_1: Ref, v_2: Ref ::
    { EG_1[(create_edge(u_1, v_2): EdgeDomainType)] } { M_1[u_1], M_1[v_2] }
    M_1[u_1] && (U_1[v_2] && !M_1[v_2]) ==> !EG_1[(create_edge(u_1, v_2): EdgeDomainType)]
  ) ==> (forall u_1_1: Ref, v_1_1: Ref ::
    { (exists_path(EG_1, u_1_1, v_1_1): bool) } { M_1[u_1_1], M_1[v_1_1] }
    M_1[u_1_1] && (U_1[v_1_1] && !M_1[v_1_1]) ==> !(exists_path(EG_1, u_1_1, v_1_1): bool)
  )
);

// Translation of domain axiom ax_instantiation_uReach
axiom (forall EG_1: (Set EdgeDomainType), x_1: Ref, v_2: Ref ::
  { (inst_uReach(EG_1, x_1): Set Ref)[v_2] } { (exists_path(EG_1, x_1, v_2): bool) }
  (inst_uReach(EG_1, x_1): Set Ref)[v_2] == (exists_path(EG_1, x_1, v_2): bool)
);

// Translation of domain axiom ax_Alias
axiom (forall EG_1: (Set EdgeDomainType), start_1: Ref, end_1: Ref ::
  { (exists_path(EG_1, start_1, end_1): bool) }
  (exists_path(EG_1, start_1, end_1): bool) == (exists_path_(EG_1, start_1, end_1): bool)
);

// Translation of domain axiom ax_IsOnPath
axiom (forall EG_1: (Set EdgeDomainType), start_1: Ref, mid: Ref, end_1: Ref ::
  { (is_on_path(EG_1, start_1, mid, end_1): bool) } { EG_1[(create_edge(start_1, mid): EdgeDomainType)], (exists_path_(EG_1, mid, end_1): bool) }
  (is_on_path(EG_1, start_1, mid, end_1): bool) == (EG_1[(create_edge(start_1, mid): EdgeDomainType)] && (exists_path_(EG_1, mid, end_1): bool))
);

// Translation of domain axiom ax_ExistsPath
axiom (forall EG_1: (Set EdgeDomainType), start_1: Ref, end_1: Ref ::
  { (exists_path(EG_1, start_1, end_1): bool) } { EG_1[(create_edge(start_1, end_1): EdgeDomainType)] }
  (exists_path_(EG_1, start_1, end_1): bool) == (start_1 == end_1 || (exists w_2: Ref ::
    { EG_1[(create_edge(start_1, w_2): EdgeDomainType)] } { (exists_path_(EG_1, w_2, end_1): bool) }
    EG_1[(create_edge(start_1, w_2): EdgeDomainType)] && (exists_path_(EG_1, w_2, end_1): bool)
  ))
);

// Translation of domain axiom ax_ExistsPathTrans
axiom (forall EG_1: (Set EdgeDomainType), u_1: Ref, v_2: Ref, w_2: Ref ::
  { (exists_path(EG_1, u_1, w_2): bool), (exists_path(EG_1, w_2, v_2): bool) }
  (exists_path_(EG_1, u_1, w_2): bool) && (exists_path_(EG_1, w_2, v_2): bool) ==> (exists_path_(EG_1, u_1, v_2): bool)
);

// Translation of domain axiom ax_ExistsSetPath
axiom (forall EG_1: (Set EdgeDomainType), from_1: (Set Ref), to_1: Ref ::
  { (exists_spath(EG_1, from_1, to_1): bool) }
  (exists_spath(EG_1, from_1, to_1): bool) == (exists f_7: Ref ::
    { from_1[f_7] } { (exists_path(EG_1, f_7, to_1): bool) }
    from_1[f_7] && (exists_path(EG_1, f_7, to_1): bool)
  )
);

// ==================================================
// Translation of all fields
// ==================================================

const unique car: Field NormalField Ref;
axiom !IsPredicateField(car);
axiom !IsWandField(car);
const unique cdr: Field NormalField Ref;
axiom !IsPredicateField(cdr);
axiom !IsWandField(cdr);

// ==================================================
// Translation of function $$
// ==================================================

// Uninterpreted function definitions
function  $$(Heap: HeapType, refs: (Set Ref)): Set EdgeDomainType;
function  $$'(Heap: HeapType, refs: (Set Ref)): Set EdgeDomainType;
axiom (forall Heap: HeapType, refs: (Set Ref) ::
  { $$(Heap, refs) }
  $$(Heap, refs) == $$'(Heap, refs) && dummyFunction($$#triggerStateless(refs))
);
axiom (forall Heap: HeapType, refs: (Set Ref) ::
  { $$'(Heap, refs) }
  dummyFunction($$#triggerStateless(refs))
);

// Framing axioms
function  $$#frame(frame: FrameType, refs: (Set Ref)): Set EdgeDomainType;
axiom (forall Heap: HeapType, Mask: MaskType, refs: (Set Ref) ::
  { state(Heap, Mask), $$'(Heap, refs) }
  state(Heap, Mask) ==> $$'(Heap, refs) == $$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, refs)), FrameFragment($$#condqp2(Heap, refs))), refs)
);
// ==================================================
// Function used for framing of quantified permission (forall n: Ref :: { n.car } (n in refs) ==> acc(n.car, write)) in function $$
// ==================================================

function  $$#condqp1(Heap: HeapType, refs_1_1: (Set Ref)): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, refs: (Set Ref) ::
  { $$#condqp1(Heap2Heap, refs), $$#condqp1(Heap1Heap, refs), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall n: Ref ::

    (refs[n] && NoPerm < FullPerm <==> refs[n] && NoPerm < FullPerm) && (refs[n] && NoPerm < FullPerm ==> Heap2Heap[n, car] == Heap1Heap[n, car])
  ) ==> $$#condqp1(Heap2Heap, refs) == $$#condqp1(Heap1Heap, refs)
);
// ==================================================
// Function used for framing of quantified permission (forall n$0: Ref :: { n$0.cdr } (n$0 in refs) ==> acc(n$0.cdr, write)) in function $$
// ==================================================

function  $$#condqp2(Heap: HeapType, refs_1_1: (Set Ref)): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, refs: (Set Ref) ::
  { $$#condqp2(Heap2Heap, refs), $$#condqp2(Heap1Heap, refs), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall n$0: Ref ::

    (refs[n$0] && NoPerm < FullPerm <==> refs[n$0] && NoPerm < FullPerm) && (refs[n$0] && NoPerm < FullPerm ==> Heap2Heap[n$0, cdr] == Heap1Heap[n$0, cdr])
  ) ==> $$#condqp2(Heap2Heap, refs) == $$#condqp2(Heap1Heap, refs)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, refs: (Set Ref) ::
  { state(Heap, Mask), $$'(Heap, refs) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 1 || $$#trigger(CombineFrames(FrameFragment($$#condqp1(Heap, refs)), FrameFragment($$#condqp2(Heap, refs))), refs)) ==> (forall p_2: Ref, s_1: Ref ::
    { $$'(Heap, refs)[(create_edge(p_2, s_1): EdgeDomainType)] }
    (refs[p_2] && (refs[s_1] && (Heap[p_2, car] == s_1 || Heap[p_2, cdr] == s_1))) == $$'(Heap, refs)[(create_edge(p_2, s_1): EdgeDomainType)]
  )
);

// Trigger function (controlling recursive postconditions)
function  $$#trigger(frame: FrameType, refs: (Set Ref)): bool;

// State-independent trigger function
function  $$#triggerStateless(refs: (Set Ref)): Set EdgeDomainType;

// Check contract well-formedness and postcondition
procedure $$#definedness(refs: (Set Ref)) returns (Result: (Set EdgeDomainType))
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var p_3: Ref;
  var s_2: Ref;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 1;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)

    // -- Check definedness of (forall n: Ref :: { n.car } (n in refs) ==> acc(n.car, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource n.car might not be injective. (graph_mark.vpr@158.14--158.25) [544]"}
      (forall n_3: Ref, n_3_1: Ref ::

      (((n_3 != n_3_1 && refs[n_3]) && refs[n_3_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_3 != n_3_1
    );

    // -- Define Inverse Function
      assume (forall n_3: Ref ::
        { Heap[n_3, car] } { QPMask[n_3, car] } { Heap[n_3, car] }
        refs[n_3] && NoPerm < FullPerm ==> qpRange1(n_3) && invRecv1(n_3) == n_3
      );
      assume (forall o_3: Ref ::
        { invRecv1(o_3) }
        (refs[invRecv1(o_3)] && NoPerm < FullPerm) && qpRange1(o_3) ==> invRecv1(o_3) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall n_3: Ref ::
        { Heap[n_3, car] } { QPMask[n_3, car] } { Heap[n_3, car] }
        refs[n_3] ==> n_3 != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, car] }
        ((refs[invRecv1(o_3)] && NoPerm < FullPerm) && qpRange1(o_3) ==> (NoPerm < FullPerm ==> invRecv1(o_3) == o_3) && QPMask[o_3, car] == Mask[o_3, car] + FullPerm) && (!((refs[invRecv1(o_3)] && NoPerm < FullPerm) && qpRange1(o_3)) ==> QPMask[o_3, car] == Mask[o_3, car])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);

    // -- Check definedness of (forall n$0: Ref :: { n$0.cdr } (n$0 in refs) ==> acc(n$0.cdr, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@158.14--158.25) [545]"}
      (forall n$0_3: Ref, n$0_3_1: Ref ::

      (((n$0_3 != n$0_3_1 && refs[n$0_3]) && refs[n$0_3_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_3 != n$0_3_1
    );

    // -- Define Inverse Function
      assume (forall n$0_3: Ref ::
        { Heap[n$0_3, cdr] } { QPMask[n$0_3, cdr] } { Heap[n$0_3, cdr] }
        refs[n$0_3] && NoPerm < FullPerm ==> qpRange2(n$0_3) && invRecv2(n$0_3) == n$0_3
      );
      assume (forall o_3: Ref ::
        { invRecv2(o_3) }
        (refs[invRecv2(o_3)] && NoPerm < FullPerm) && qpRange2(o_3) ==> invRecv2(o_3) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall n$0_3: Ref ::
        { Heap[n$0_3, cdr] } { QPMask[n$0_3, cdr] } { Heap[n$0_3, cdr] }
        refs[n$0_3] ==> n$0_3 != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, cdr] }
        ((refs[invRecv2(o_3)] && NoPerm < FullPerm) && qpRange2(o_3) ==> (NoPerm < FullPerm ==> invRecv2(o_3) == o_3) && QPMask[o_3, cdr] == Mask[o_3, cdr] + FullPerm) && (!((refs[invRecv2(o_3)] && NoPerm < FullPerm) && qpRange2(o_3)) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Checking definedness of postcondition (no body)

    // -- Check definedness of (forall p: Ref, s: Ref :: { (create_edge(p, s) in result) } ((p in refs) && ((s in refs) && (p.car == s || p.cdr == s))) == (create_edge(p, s) in result))
      if (*) {
        if (refs[p_3]) {
          if (refs[s_2]) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access p.car (graph_mark.vpr@159.13--163.34) [546]"}
              HasDirectPerm(Mask, p_3, car);
            if (!(Heap[p_3, car] == s_2)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access p.cdr (graph_mark.vpr@159.13--163.34) [547]"}
                HasDirectPerm(Mask, p_3, cdr);
            }
          }
        }
        assume false;
      }
    assume (forall p_2_1: Ref, s_2_1: Ref ::
      { Result[(create_edge(p_2_1, s_2_1): EdgeDomainType)] }
      (refs[p_2_1] && (refs[s_2_1] && (Heap[p_2_1, car] == s_2_1 || Heap[p_2_1, cdr] == s_2_1))) == Result[(create_edge(p_2_1, s_2_1): EdgeDomainType)]
    );
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function get
// ==================================================

// Uninterpreted function definitions
function  get(Heap: HeapType, s_1: (Set Ref)): Ref;
function  get'(Heap: HeapType, s_1: (Set Ref)): Ref;
axiom (forall Heap: HeapType, s_1: (Set Ref) ::
  { get(Heap, s_1) }
  get(Heap, s_1) == get'(Heap, s_1) && dummyFunction(get#triggerStateless(s_1))
);
axiom (forall Heap: HeapType, s_1: (Set Ref) ::
  { get'(Heap, s_1) }
  dummyFunction(get#triggerStateless(s_1))
);

// Framing axioms
function  get#frame(frame: FrameType, s_1: (Set Ref)): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, s_1: (Set Ref) ::
  { state(Heap, Mask), get'(Heap, s_1) }
  state(Heap, Mask) ==> get'(Heap, s_1) == get#frame(EmptyFrame, s_1)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, s_1: (Set Ref) ::
  { state(Heap, Mask), get'(Heap, s_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 0 || get#trigger(EmptyFrame, s_1)) ==> Set#Card(s_1) > 0 ==> s_1[get'(Heap, s_1)]
);

// Trigger function (controlling recursive postconditions)
function  get#trigger(frame: FrameType, s_1: (Set Ref)): bool;

// State-independent trigger function
function  get#triggerStateless(s_1: (Set Ref)): Ref;

// Check contract well-formedness and postcondition
procedure get#definedness(s_1: (Set Ref)) returns (Result: Ref)
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 0;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume Set#Card(s_1) > 0;
    assume state(Heap, Mask);

  // -- Checking definedness of postcondition (no body)
    assume s_1[Result];
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method mark
// ==================================================

procedure mark(g: (Set Ref), roots: (Set Ref)) returns (marked: (Set Ref))
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var n$0_1: Ref;
  var n$1: Ref;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var n$4: Ref;
  var n$5: Ref;
  var v_3: Ref;
  var ExhaleHeap: HeapType;
  var v_4: Ref;
  var x_1: Ref;
  var pending: (Set Ref);
  var n$8: Ref;
  var n$9: Ref;
  var n$8_1: Ref;
  var n$9_1: Ref;
  var n_14: Ref;
  var n1_1: Ref;
  var n2_1: Ref;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var n$8_5: Ref;
  var n$9_5: Ref;
  var n$4_2: Ref;
  var n$5_2: Ref;
  var v_4_1: Ref;
  var v_6: Ref;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Checked inhaling of precondition
    assume Set#Card(roots) > 0;
    assume state(Heap, Mask);
    assume !g[null];

    // -- Check definedness of (forall n$2: Ref :: { n$2.car } (n$2 in g) ==> acc(n$2.car, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource n$2.car might not be injective. (graph_mark.vpr@191.14--191.22) [548]"}
      (forall n$2_1: Ref, n$2_1_1: Ref ::

      (((n$2_1 != n$2_1_1 && g[n$2_1]) && g[n$2_1_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$2_1 != n$2_1_1
    );

    // -- Define Inverse Function
      assume (forall n$2_1: Ref ::
        { Heap[n$2_1, car] } { QPMask[n$2_1, car] } { Heap[n$2_1, car] }
        g[n$2_1] && NoPerm < FullPerm ==> qpRange3(n$2_1) && invRecv3(n$2_1) == n$2_1
      );
      assume (forall o_3: Ref ::
        { invRecv3(o_3) }
        (g[invRecv3(o_3)] && NoPerm < FullPerm) && qpRange3(o_3) ==> invRecv3(o_3) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall n$2_1: Ref ::
        { Heap[n$2_1, car] } { QPMask[n$2_1, car] } { Heap[n$2_1, car] }
        g[n$2_1] ==> n$2_1 != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, car] }
        ((g[invRecv3(o_3)] && NoPerm < FullPerm) && qpRange3(o_3) ==> (NoPerm < FullPerm ==> invRecv3(o_3) == o_3) && QPMask[o_3, car] == Mask[o_3, car] + FullPerm) && (!((g[invRecv3(o_3)] && NoPerm < FullPerm) && qpRange3(o_3)) ==> QPMask[o_3, car] == Mask[o_3, car])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);

    // -- Check definedness of (forall n$3: Ref :: { n$3.cdr } (n$3 in g) ==> acc(n$3.cdr, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource n$3.cdr might not be injective. (graph_mark.vpr@191.14--191.22) [549]"}
      (forall n$3_1: Ref, n$3_1_1: Ref ::

      (((n$3_1 != n$3_1_1 && g[n$3_1]) && g[n$3_1_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$3_1 != n$3_1_1
    );

    // -- Define Inverse Function
      assume (forall n$3_1: Ref ::
        { Heap[n$3_1, cdr] } { QPMask[n$3_1, cdr] } { Heap[n$3_1, cdr] }
        g[n$3_1] && NoPerm < FullPerm ==> qpRange4(n$3_1) && invRecv4(n$3_1) == n$3_1
      );
      assume (forall o_3: Ref ::
        { invRecv4(o_3) }
        (g[invRecv4(o_3)] && NoPerm < FullPerm) && qpRange4(o_3) ==> invRecv4(o_3) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall n$3_1: Ref ::
        { Heap[n$3_1, cdr] } { QPMask[n$3_1, cdr] } { Heap[n$3_1, cdr] }
        g[n$3_1] ==> n$3_1 != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, cdr] }
        ((g[invRecv4(o_3)] && NoPerm < FullPerm) && qpRange4(o_3) ==> (NoPerm < FullPerm ==> invRecv4(o_3) == o_3) && QPMask[o_3, cdr] == Mask[o_3, cdr] + FullPerm) && (!((g[invRecv4(o_3)] && NoPerm < FullPerm) && qpRange4(o_3)) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);

    // -- Check definedness of (forall n$0: Ref :: { (n$0.car in g) } { (n$0 in g), n$0.car } (n$0 in g) ==> (n$0.car in g))
      if (*) {
        if (g[n$0_1]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access n$0.car (graph_mark.vpr@191.14--191.22) [550]"}
            HasDirectPerm(Mask, n$0_1, car);
        }
        assume false;
      }
    assume (forall n$0_1_1: Ref ::
      { g[Heap[n$0_1_1, car]] } { g[n$0_1_1], Heap[n$0_1_1, car] }
      g[n$0_1_1] ==> g[Heap[n$0_1_1, car]]
    );

    // -- Check definedness of (forall n$1: Ref :: { (n$1.cdr in g) } { (n$1 in g), n$1.cdr } (n$1 in g) ==> (n$1.cdr in g))
      if (*) {
        if (g[n$1]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access n$1.cdr (graph_mark.vpr@191.14--191.22) [551]"}
            HasDirectPerm(Mask, n$1, cdr);
        }
        assume false;
      }
    assume (forall n$1_1: Ref ::
      { g[Heap[n$1_1, cdr]] } { g[n$1_1], Heap[n$1_1, cdr] }
      g[n$1_1] ==> g[Heap[n$1_1, cdr]]
    );
    assume state(Heap, Mask);
    assume Set#Subset(roots, g);
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  PostHeap := Heap;
  PostMask := Mask;
  havoc PostHeap;
  PostMask := ZeroMask;
  assume state(PostHeap, PostMask);
  if (*) {
    // Checked inhaling of postcondition to check definedness
    assume Set#Subset(roots, marked);
    assume state(PostHeap, PostMask);
    assume Set#Subset(marked, g);
    assume state(PostHeap, PostMask);
    assume !g[null];

    // -- Check definedness of (forall n$6: Ref :: { n$6.car } (n$6 in g) ==> acc(n$6.car, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource n$6.car might not be injective. (graph_mark.vpr@195.13--195.21) [552]"}
      (forall n$6_1: Ref, n$6_1_1: Ref ::

      (((n$6_1 != n$6_1_1 && g[n$6_1]) && g[n$6_1_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$6_1 != n$6_1_1
    );

    // -- Define Inverse Function
      assume (forall n$6_1: Ref ::
        { PostHeap[n$6_1, car] } { QPMask[n$6_1, car] } { PostHeap[n$6_1, car] }
        g[n$6_1] && NoPerm < FullPerm ==> qpRange5(n$6_1) && invRecv5(n$6_1) == n$6_1
      );
      assume (forall o_3: Ref ::
        { invRecv5(o_3) }
        (g[invRecv5(o_3)] && NoPerm < FullPerm) && qpRange5(o_3) ==> invRecv5(o_3) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall n$6_1: Ref ::
        { PostHeap[n$6_1, car] } { QPMask[n$6_1, car] } { PostHeap[n$6_1, car] }
        g[n$6_1] ==> n$6_1 != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, car] }
        ((g[invRecv5(o_3)] && NoPerm < FullPerm) && qpRange5(o_3) ==> (NoPerm < FullPerm ==> invRecv5(o_3) == o_3) && QPMask[o_3, car] == PostMask[o_3, car] + FullPerm) && (!((g[invRecv5(o_3)] && NoPerm < FullPerm) && qpRange5(o_3)) ==> QPMask[o_3, car] == PostMask[o_3, car])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != car ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall n$7: Ref :: { n$7.cdr } (n$7 in g) ==> acc(n$7.cdr, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource n$7.cdr might not be injective. (graph_mark.vpr@195.13--195.21) [553]"}
      (forall n$7_1: Ref, n$7_1_1: Ref ::

      (((n$7_1 != n$7_1_1 && g[n$7_1]) && g[n$7_1_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$7_1 != n$7_1_1
    );

    // -- Define Inverse Function
      assume (forall n$7_1: Ref ::
        { PostHeap[n$7_1, cdr] } { QPMask[n$7_1, cdr] } { PostHeap[n$7_1, cdr] }
        g[n$7_1] && NoPerm < FullPerm ==> qpRange6(n$7_1) && invRecv6(n$7_1) == n$7_1
      );
      assume (forall o_3: Ref ::
        { invRecv6(o_3) }
        (g[invRecv6(o_3)] && NoPerm < FullPerm) && qpRange6(o_3) ==> invRecv6(o_3) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall n$7_1: Ref ::
        { PostHeap[n$7_1, cdr] } { QPMask[n$7_1, cdr] } { PostHeap[n$7_1, cdr] }
        g[n$7_1] ==> n$7_1 != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, cdr] }
        ((g[invRecv6(o_3)] && NoPerm < FullPerm) && qpRange6(o_3) ==> (NoPerm < FullPerm ==> invRecv6(o_3) == o_3) && QPMask[o_3, cdr] == PostMask[o_3, cdr] + FullPerm) && (!((g[invRecv6(o_3)] && NoPerm < FullPerm) && qpRange6(o_3)) ==> QPMask[o_3, cdr] == PostMask[o_3, cdr])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != cdr ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall n$4: Ref :: { (n$4.car in g) } { (n$4 in g), n$4.car } (n$4 in g) ==> (n$4.car in g))
      if (*) {
        if (g[n$4]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access n$4.car (graph_mark.vpr@195.13--195.21) [554]"}
            HasDirectPerm(PostMask, n$4, car);
        }
        assume false;
      }
    assume (forall n$4_1: Ref ::
      { g[PostHeap[n$4_1, car]] } { g[n$4_1], PostHeap[n$4_1, car] }
      g[n$4_1] ==> g[PostHeap[n$4_1, car]]
    );

    // -- Check definedness of (forall n$5: Ref :: { (n$5.cdr in g) } { (n$5 in g), n$5.cdr } (n$5 in g) ==> (n$5.cdr in g))
      if (*) {
        if (g[n$5]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access n$5.cdr (graph_mark.vpr@195.13--195.21) [555]"}
            HasDirectPerm(PostMask, n$5, cdr);
        }
        assume false;
      }
    assume (forall n$5_1: Ref ::
      { g[PostHeap[n$5_1, cdr]] } { g[n$5_1], PostHeap[n$5_1, cdr] }
      g[n$5_1] ==> g[PostHeap[n$5_1, cdr]]
    );
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall v: Ref :: { (v in marked) } { exists_spath($$(g), roots, v) } (v in g) ==> (v in marked) ==> exists_spath($$(g), roots, v))
      if (*) {
        if (g[v_3]) {
          if (marked[v_3]) {
            if (*) {
              // Exhale precondition of function application
              havoc QPMask;

              // -- check that the permission amount is positive


              // -- check if receiver n is injective
                assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@196.114--196.119) [556]"}
                  (forall n: Ref, n_2: Ref ::
                  { neverTriggered7(n), neverTriggered7(n_2) }
                  (((n != n_2 && g[n]) && g[n_2]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n != n_2
                );

              // -- check if sufficient permission is held
                assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@196.114--196.119) [557]"}
                  (forall n: Ref ::
                  { PostHeap[n, car] } { QPMask[n, car] } { PostHeap[n, car] }
                  g[n] ==> PostMask[n, car] >= FullPerm
                );

              // -- assumptions for inverse of receiver n
                assume (forall n: Ref ::
                  { PostHeap[n, car] } { QPMask[n, car] } { PostHeap[n, car] }
                  g[n] && NoPerm < FullPerm ==> qpRange7(n) && invRecv7(n) == n
                );
                assume (forall o_3: Ref ::
                  { invRecv7(o_3) }
                  g[invRecv7(o_3)] && (NoPerm < FullPerm && qpRange7(o_3)) ==> invRecv7(o_3) == o_3
                );

              // -- assume permission updates for field car
                assume (forall o_3: Ref ::
                  { QPMask[o_3, car] }
                  (g[invRecv7(o_3)] && (NoPerm < FullPerm && qpRange7(o_3)) ==> invRecv7(o_3) == o_3 && QPMask[o_3, car] == PostMask[o_3, car] - FullPerm) && (!(g[invRecv7(o_3)] && (NoPerm < FullPerm && qpRange7(o_3))) ==> QPMask[o_3, car] == PostMask[o_3, car])
                );

              // -- assume permission updates for independent locations
                assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                  { QPMask[o_3, f_5] }
                  f_5 != car ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
                );
              PostMask := QPMask;
              havoc QPMask;

              // -- check that the permission amount is positive


              // -- check if receiver n$0 is injective
                assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@196.114--196.119) [558]"}
                  (forall n$0_2: Ref, n$0_2_1: Ref ::
                  { neverTriggered8(n$0_2), neverTriggered8(n$0_2_1) }
                  (((n$0_2 != n$0_2_1 && g[n$0_2]) && g[n$0_2_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_2 != n$0_2_1
                );

              // -- check if sufficient permission is held
                assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@196.114--196.119) [559]"}
                  (forall n$0_2: Ref ::
                  { PostHeap[n$0_2, cdr] } { QPMask[n$0_2, cdr] } { PostHeap[n$0_2, cdr] }
                  g[n$0_2] ==> PostMask[n$0_2, cdr] >= FullPerm
                );

              // -- assumptions for inverse of receiver n$0
                assume (forall n$0_2: Ref ::
                  { PostHeap[n$0_2, cdr] } { QPMask[n$0_2, cdr] } { PostHeap[n$0_2, cdr] }
                  g[n$0_2] && NoPerm < FullPerm ==> qpRange8(n$0_2) && invRecv8(n$0_2) == n$0_2
                );
                assume (forall o_3: Ref ::
                  { invRecv8(o_3) }
                  g[invRecv8(o_3)] && (NoPerm < FullPerm && qpRange8(o_3)) ==> invRecv8(o_3) == o_3
                );

              // -- assume permission updates for field cdr
                assume (forall o_3: Ref ::
                  { QPMask[o_3, cdr] }
                  (g[invRecv8(o_3)] && (NoPerm < FullPerm && qpRange8(o_3)) ==> invRecv8(o_3) == o_3 && QPMask[o_3, cdr] == PostMask[o_3, cdr] - FullPerm) && (!(g[invRecv8(o_3)] && (NoPerm < FullPerm && qpRange8(o_3))) ==> QPMask[o_3, cdr] == PostMask[o_3, cdr])
                );

              // -- assume permission updates for independent locations
                assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                  { QPMask[o_3, f_5] }
                  f_5 != cdr ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
                );
              PostMask := QPMask;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
              PostHeap := ExhaleHeap;
              // Stop execution
              assume false;
            }
          }
        }
        assume false;
      }
    assume (forall v_1_1: Ref ::
      { marked[v_1_1] } { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(PostHeap, g)), FrameFragment($$#condqp2(PostHeap, g))), g), roots, v_1_1): bool) }
      g[v_1_1] ==> marked[v_1_1] ==> (exists_spath($$(PostHeap, g), roots, v_1_1): bool)
    );
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall v: Ref :: { (v in marked) } { exists_spath($$(g), roots, v) } (v in g) ==> exists_spath($$(g), roots, v) ==> (v in marked))
      if (*) {
        if (g[v_4]) {
          if (*) {
            // Exhale precondition of function application
            havoc QPMask;

            // -- check that the permission amount is positive


            // -- check if receiver n is injective
              assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@197.98--197.103) [560]"}
                (forall n_1: Ref, n_1_1: Ref ::
                { neverTriggered9(n_1), neverTriggered9(n_1_1) }
                (((n_1 != n_1_1 && g[n_1]) && g[n_1_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_1 != n_1_1
              );

            // -- check if sufficient permission is held
              assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@197.98--197.103) [561]"}
                (forall n_1: Ref ::
                { PostHeap[n_1, car] } { QPMask[n_1, car] } { PostHeap[n_1, car] }
                g[n_1] ==> PostMask[n_1, car] >= FullPerm
              );

            // -- assumptions for inverse of receiver n
              assume (forall n_1: Ref ::
                { PostHeap[n_1, car] } { QPMask[n_1, car] } { PostHeap[n_1, car] }
                g[n_1] && NoPerm < FullPerm ==> qpRange9(n_1) && invRecv9(n_1) == n_1
              );
              assume (forall o_3: Ref ::
                { invRecv9(o_3) }
                g[invRecv9(o_3)] && (NoPerm < FullPerm && qpRange9(o_3)) ==> invRecv9(o_3) == o_3
              );

            // -- assume permission updates for field car
              assume (forall o_3: Ref ::
                { QPMask[o_3, car] }
                (g[invRecv9(o_3)] && (NoPerm < FullPerm && qpRange9(o_3)) ==> invRecv9(o_3) == o_3 && QPMask[o_3, car] == PostMask[o_3, car] - FullPerm) && (!(g[invRecv9(o_3)] && (NoPerm < FullPerm && qpRange9(o_3))) ==> QPMask[o_3, car] == PostMask[o_3, car])
              );

            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != car ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
              );
            PostMask := QPMask;
            havoc QPMask;

            // -- check that the permission amount is positive


            // -- check if receiver n$0 is injective
              assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@197.98--197.103) [562]"}
                (forall n$0_3: Ref, n$0_3_1: Ref ::
                { neverTriggered10(n$0_3), neverTriggered10(n$0_3_1) }
                (((n$0_3 != n$0_3_1 && g[n$0_3]) && g[n$0_3_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_3 != n$0_3_1
              );

            // -- check if sufficient permission is held
              assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@197.98--197.103) [563]"}
                (forall n$0_3: Ref ::
                { PostHeap[n$0_3, cdr] } { QPMask[n$0_3, cdr] } { PostHeap[n$0_3, cdr] }
                g[n$0_3] ==> PostMask[n$0_3, cdr] >= FullPerm
              );

            // -- assumptions for inverse of receiver n$0
              assume (forall n$0_3: Ref ::
                { PostHeap[n$0_3, cdr] } { QPMask[n$0_3, cdr] } { PostHeap[n$0_3, cdr] }
                g[n$0_3] && NoPerm < FullPerm ==> qpRange10(n$0_3) && invRecv10(n$0_3) == n$0_3
              );
              assume (forall o_3: Ref ::
                { invRecv10(o_3) }
                g[invRecv10(o_3)] && (NoPerm < FullPerm && qpRange10(o_3)) ==> invRecv10(o_3) == o_3
              );

            // -- assume permission updates for field cdr
              assume (forall o_3: Ref ::
                { QPMask[o_3, cdr] }
                (g[invRecv10(o_3)] && (NoPerm < FullPerm && qpRange10(o_3)) ==> invRecv10(o_3) == o_3 && QPMask[o_3, cdr] == PostMask[o_3, cdr] - FullPerm) && (!(g[invRecv10(o_3)] && (NoPerm < FullPerm && qpRange10(o_3))) ==> QPMask[o_3, cdr] == PostMask[o_3, cdr])
              );

            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != cdr ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
              );
            PostMask := QPMask;
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
            PostHeap := ExhaleHeap;
            // Stop execution
            assume false;
          }
        }
        assume false;
      }
    assume (forall v_3_1: Ref ::
      { marked[v_3_1] } { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(PostHeap, g)), FrameFragment($$#condqp2(PostHeap, g))), g), roots, v_3_1): bool) }
      g[v_3_1] ==> (exists_spath($$(PostHeap, g), roots, v_3_1): bool) ==> marked[v_3_1]
    );
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Assumptions about local variables
    assume Heap[x_1, $allocated];

  // -- Translating statement: x := get(roots) -- graph_mark.vpr@199.5--199.28

    // -- Check definedness of get(roots)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function get might not hold. Assertion |roots| > 0 might not hold. (graph_mark.vpr@199.18--199.28) [564]"}
          Set#Card(roots) > 0;
        // Stop execution
        assume false;
      }
    x_1 := get(Heap, roots);
    assume state(Heap, Mask);

  // -- Translating statement: pending := roots -- graph_mark.vpr@200.5--200.34
    pending := roots;
    assume state(Heap, Mask);

  // -- Translating statement: marked := Set[Ref]() -- graph_mark.vpr@201.5--201.20
    marked := (Set#Empty(): Set Ref);
    assume state(Heap, Mask);

  // -- Translating statement: while (|pending| > 0) -- graph_mark.vpr@203.5--238.6

    // -- Before loop head

      // -- Exhale loop invariant before loop
        assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. Assertion !((null in g)) might not hold. (graph_mark.vpr@205.19--205.27) [565]"}
          !g[null];
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver n$10 is injective
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. Quantified resource n$10.car might not be injective. (graph_mark.vpr@205.19--205.27) [566]"}
            (forall n$10: Ref, n$10_1: Ref ::
            { neverTriggered13(n$10), neverTriggered13(n$10_1) }
            (((n$10 != n$10_1 && g[n$10]) && g[n$10_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$10 != n$10_1
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. There might be insufficient permission to access n$10.car (graph_mark.vpr@205.19--205.27) [567]"}
            (forall n$10: Ref ::
            { Heap[n$10, car] } { QPMask[n$10, car] } { Heap[n$10, car] }
            g[n$10] ==> Mask[n$10, car] >= FullPerm
          );

        // -- assumptions for inverse of receiver n$10
          assume (forall n$10: Ref ::
            { Heap[n$10, car] } { QPMask[n$10, car] } { Heap[n$10, car] }
            g[n$10] && NoPerm < FullPerm ==> qpRange13(n$10) && invRecv13(n$10) == n$10
          );
          assume (forall o_3: Ref ::
            { invRecv13(o_3) }
            g[invRecv13(o_3)] && (NoPerm < FullPerm && qpRange13(o_3)) ==> invRecv13(o_3) == o_3
          );

        // -- assume permission updates for field car
          assume (forall o_3: Ref ::
            { QPMask[o_3, car] }
            (g[invRecv13(o_3)] && (NoPerm < FullPerm && qpRange13(o_3)) ==> invRecv13(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv13(o_3)] && (NoPerm < FullPerm && qpRange13(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver n$11 is injective
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. Quantified resource n$11.cdr might not be injective. (graph_mark.vpr@205.19--205.27) [568]"}
            (forall n$11: Ref, n$11_1: Ref ::
            { neverTriggered14(n$11), neverTriggered14(n$11_1) }
            (((n$11 != n$11_1 && g[n$11]) && g[n$11_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$11 != n$11_1
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. There might be insufficient permission to access n$11.cdr (graph_mark.vpr@205.19--205.27) [569]"}
            (forall n$11: Ref ::
            { Heap[n$11, cdr] } { QPMask[n$11, cdr] } { Heap[n$11, cdr] }
            g[n$11] ==> Mask[n$11, cdr] >= FullPerm
          );

        // -- assumptions for inverse of receiver n$11
          assume (forall n$11: Ref ::
            { Heap[n$11, cdr] } { QPMask[n$11, cdr] } { Heap[n$11, cdr] }
            g[n$11] && NoPerm < FullPerm ==> qpRange14(n$11) && invRecv14(n$11) == n$11
          );
          assume (forall o_3: Ref ::
            { invRecv14(o_3) }
            g[invRecv14(o_3)] && (NoPerm < FullPerm && qpRange14(o_3)) ==> invRecv14(o_3) == o_3
          );

        // -- assume permission updates for field cdr
          assume (forall o_3: Ref ::
            { QPMask[o_3, cdr] }
            (g[invRecv14(o_3)] && (NoPerm < FullPerm && qpRange14(o_3)) ==> invRecv14(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv14(o_3)] && (NoPerm < FullPerm && qpRange14(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        if (*) {
          if (g[n$8]) {
            assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. Assertion (n$8.car in g) might not hold. (graph_mark.vpr@205.19--205.27) [570]"}
              g[Heap[n$8, car]];
          }
          assume false;
        }
        assume (forall n$8_1_1: Ref ::
          { g[Heap[n$8_1_1, car]] } { g[n$8_1_1], Heap[n$8_1_1, car] }
          g[n$8_1_1] ==> g[Heap[n$8_1_1, car]]
        );
        if (*) {
          if (g[n$9]) {
            assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not hold on entry. Assertion (n$9.cdr in g) might not hold. (graph_mark.vpr@205.19--205.27) [571]"}
              g[Heap[n$9, cdr]];
          }
          assume false;
        }
        assume (forall n$9_1_1: Ref ::
          { g[Heap[n$9_1_1, cdr]] } { g[n$9_1_1], Heap[n$9_1_1, cdr] }
          g[n$9_1_1] ==> g[Heap[n$9_1_1, cdr]]
        );
        assert {:msg "  Loop invariant (x in g) might not hold on entry. Assertion (x in g) might not hold. (graph_mark.vpr@208.19--208.25) [572]"}
          g[x_1];
        assert {:msg "  Loop invariant (pending subset g) might not hold on entry. Assertion (pending subset g) might not hold. (graph_mark.vpr@209.27--209.35) [573]"}
          Set#Subset(pending, g);
        assert {:msg "  Loop invariant (marked subset g) might not hold on entry. Assertion (marked subset g) might not hold. (graph_mark.vpr@210.26--210.34) [574]"}
          Set#Subset(marked, g);
        assert {:msg "  Loop invariant exists_spath($$(g), roots, x) && ((x.cdr != null ==> (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr) ==> exists_path($$(g), x, x.cdr)) && (x.car != null ==> (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car) ==> exists_path($$(g), x, x.car))) might not hold on entry. Assertion exists_spath($$(g), roots, x) might not hold. (graph_mark.vpr@212.19--214.118) [575]"}
          (exists_spath($$(Heap, g), roots, x_1): bool);
        if (Heap[x_1, cdr] != null) {
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, cdr]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, cdr], Heap[x_1, cdr]): bool)) {
            assert {:msg "  Loop invariant exists_spath($$(g), roots, x) && ((x.cdr != null ==> (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr) ==> exists_path($$(g), x, x.cdr)) && (x.car != null ==> (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car) ==> exists_path($$(g), x, x.car))) might not hold on entry. Assertion exists_path($$(g), x, x.cdr) might not hold. (graph_mark.vpr@212.19--214.118) [576]"}
              (exists_path($$(Heap, g), x_1, Heap[x_1, cdr]): bool);
          }
        }
        if (Heap[x_1, car] != null) {
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, car]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, car], Heap[x_1, car]): bool)) {
            assert {:msg "  Loop invariant exists_spath($$(g), roots, x) && ((x.cdr != null ==> (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr) ==> exists_path($$(g), x, x.cdr)) && (x.car != null ==> (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car) ==> exists_path($$(g), x, x.car))) might not hold on entry. Assertion exists_path($$(g), x, x.car) might not hold. (graph_mark.vpr@212.19--214.118) [577]"}
              (exists_path($$(Heap, g), x_1, Heap[x_1, car]): bool);
          }
        }
        assert {:msg "  Loop invariant (forall n: Ref :: { (n in pending) } { (n in roots) } (n in roots) == (n in pending)) && (forall n: Ref :: { (n in marked) } (n in g) ==> !((n in marked))) || (forall n: Ref :: { (n in pending) } { (n in marked) } (n in roots) ==> (n in marked) || (n in pending)) && ((forall n: Ref :: { (n in pending) } (n in g) ==> !((n in marked) && (n in pending))) && ((forall n: Ref :: { exists_spath($$(g), roots, n) } (n in pending) || (n in marked) ==> exists_spath($$(g), roots, n)) && (forall n1: Ref, n2: Ref :: { (n1 in marked), (n2 in marked) } (n1 in marked) && ((n2 in g) && (!((n2 in marked)) && !((n2 in pending)))) ==> !((create_edge(n1, n2) in $$(g)))))) might not hold on entry. Assertion (forall n: Ref :: { (n in pending) } { (n in roots) } (n in roots) == (n in pending)) && (forall n: Ref :: { (n in marked) } (n in g) ==> !((n in marked))) || (forall n: Ref :: { (n in pending) } { (n in marked) } (n in roots) ==> (n in marked) || (n in pending)) && ((forall n: Ref :: { (n in pending) } (n in g) ==> !((n in marked) && (n in pending))) && ((forall n: Ref :: { exists_spath($$(g), roots, n) } (n in pending) || (n in marked) ==> exists_spath($$(g), roots, n)) && (forall n1: Ref, n2: Ref :: { (n1 in marked), (n2 in marked) } (n1 in marked) && ((n2 in g) && (!((n2 in marked)) && !((n2 in pending)))) ==> !((create_edge(n1, n2) in $$(g)))))) might not hold. (graph_mark.vpr@217.9--223.152) [578]"}
          ((forall n_2_1: Ref ::
          { pending[n_2_1] } { roots[n_2_1] }
          roots[n_2_1] == pending[n_2_1]
        ) && (forall n_3: Ref ::
          { marked[n_3] }
          g[n_3] ==> !marked[n_3]
        )) || ((forall n_4: Ref ::
          { pending[n_4] } { marked[n_4] }
          roots[n_4] ==> marked[n_4] || pending[n_4]
        ) && ((forall n_5: Ref ::
          { pending[n_5] }
          g[n_5] ==> !(marked[n_5] && pending[n_5])
        ) && ((forall n_6: Ref ::
          { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, n_6): bool) }
          pending[n_6] || marked[n_6] ==> (exists_spath($$(Heap, g), roots, n_6): bool)
        ) && (forall n1: Ref, n2: Ref ::
          { marked[n1], marked[n2] }
          marked[n1] && (g[n2] && (!marked[n2] && !pending[n2])) ==> !$$(Heap, g)[(create_edge(n1, n2): EdgeDomainType)]
        ))));
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;

    // -- Havoc loop written variables (except locals)
      havoc pending, marked, x_1;
      assume Heap[x_1, $allocated];

    // -- Check definedness of invariant
      if (*) {
        assume !g[null];

        // -- Check definedness of (forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write))
          if (*) {
            assume false;
          }
        havoc QPMask;
        assert {:msg "  Contract might not be well-formed. Quantified resource n$10.car might not be injective. (graph_mark.vpr@205.19--205.27) [579]"}
          (forall n$10_2: Ref, n$10_2_1: Ref ::

          (((n$10_2 != n$10_2_1 && g[n$10_2]) && g[n$10_2_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$10_2 != n$10_2_1
        );

        // -- Define Inverse Function
          assume (forall n$10_2: Ref ::
            { Heap[n$10_2, car] } { QPMask[n$10_2, car] } { Heap[n$10_2, car] }
            g[n$10_2] && NoPerm < FullPerm ==> qpRange15(n$10_2) && invRecv15(n$10_2) == n$10_2
          );
          assume (forall o_3: Ref ::
            { invRecv15(o_3) }
            (g[invRecv15(o_3)] && NoPerm < FullPerm) && qpRange15(o_3) ==> invRecv15(o_3) == o_3
          );

        // -- Assume set of fields is nonNull
          assume (forall n$10_2: Ref ::
            { Heap[n$10_2, car] } { QPMask[n$10_2, car] } { Heap[n$10_2, car] }
            g[n$10_2] ==> n$10_2 != null
          );

        // -- Define permissions
          assume (forall o_3: Ref ::
            { QPMask[o_3, car] }
            ((g[invRecv15(o_3)] && NoPerm < FullPerm) && qpRange15(o_3) ==> (NoPerm < FullPerm ==> invRecv15(o_3) == o_3) && QPMask[o_3, car] == Mask[o_3, car] + FullPerm) && (!((g[invRecv15(o_3)] && NoPerm < FullPerm) && qpRange15(o_3)) ==> QPMask[o_3, car] == Mask[o_3, car])
          );
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
            f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assume state(Heap, Mask);

        // -- Check definedness of (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))
          if (*) {
            assume false;
          }
        havoc QPMask;
        assert {:msg "  Contract might not be well-formed. Quantified resource n$11.cdr might not be injective. (graph_mark.vpr@205.19--205.27) [580]"}
          (forall n$11_2: Ref, n$11_2_1: Ref ::

          (((n$11_2 != n$11_2_1 && g[n$11_2]) && g[n$11_2_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$11_2 != n$11_2_1
        );

        // -- Define Inverse Function
          assume (forall n$11_2: Ref ::
            { Heap[n$11_2, cdr] } { QPMask[n$11_2, cdr] } { Heap[n$11_2, cdr] }
            g[n$11_2] && NoPerm < FullPerm ==> qpRange16(n$11_2) && invRecv16(n$11_2) == n$11_2
          );
          assume (forall o_3: Ref ::
            { invRecv16(o_3) }
            (g[invRecv16(o_3)] && NoPerm < FullPerm) && qpRange16(o_3) ==> invRecv16(o_3) == o_3
          );

        // -- Assume set of fields is nonNull
          assume (forall n$11_2: Ref ::
            { Heap[n$11_2, cdr] } { QPMask[n$11_2, cdr] } { Heap[n$11_2, cdr] }
            g[n$11_2] ==> n$11_2 != null
          );

        // -- Define permissions
          assume (forall o_3: Ref ::
            { QPMask[o_3, cdr] }
            ((g[invRecv16(o_3)] && NoPerm < FullPerm) && qpRange16(o_3) ==> (NoPerm < FullPerm ==> invRecv16(o_3) == o_3) && QPMask[o_3, cdr] == Mask[o_3, cdr] + FullPerm) && (!((g[invRecv16(o_3)] && NoPerm < FullPerm) && qpRange16(o_3)) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
          );
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
            f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assume state(Heap, Mask);

        // -- Check definedness of (forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g))
          if (*) {
            if (g[n$8_1]) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access n$8.car (graph_mark.vpr@205.19--205.27) [581]"}
                HasDirectPerm(Mask, n$8_1, car);
            }
            assume false;
          }
        assume (forall n$8_3: Ref ::
          { g[Heap[n$8_3, car]] } { g[n$8_3], Heap[n$8_3, car] }
          g[n$8_3] ==> g[Heap[n$8_3, car]]
        );

        // -- Check definedness of (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g))
          if (*) {
            if (g[n$9_1]) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access n$9.cdr (graph_mark.vpr@205.19--205.27) [582]"}
                HasDirectPerm(Mask, n$9_1, cdr);
            }
            assume false;
          }
        assume (forall n$9_3: Ref ::
          { g[Heap[n$9_3, cdr]] } { g[n$9_3], Heap[n$9_3, cdr] }
          g[n$9_3] ==> g[Heap[n$9_3, cdr]]
        );
        assume state(Heap, Mask);
        assume g[x_1];
        assume state(Heap, Mask);
        assume Set#Subset(pending, g);
        assume state(Heap, Mask);
        assume Set#Subset(marked, g);
        assume state(Heap, Mask);
        assume state(Heap, Mask);

        // -- Check definedness of exists_spath($$(g), roots, x)
          if (*) {
            // Exhale precondition of function application
            havoc QPMask;

            // -- check that the permission amount is positive


            // -- check if receiver n is injective
              assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@212.32--212.37) [583]"}
                (forall n_7: Ref, n_7_1: Ref ::
                { neverTriggered17(n_7), neverTriggered17(n_7_1) }
                (((n_7 != n_7_1 && g[n_7]) && g[n_7_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_7 != n_7_1
              );

            // -- check if sufficient permission is held
              assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@212.32--212.37) [584]"}
                (forall n_7: Ref ::
                { Heap[n_7, car] } { QPMask[n_7, car] } { Heap[n_7, car] }
                g[n_7] ==> Mask[n_7, car] >= FullPerm
              );

            // -- assumptions for inverse of receiver n
              assume (forall n_7: Ref ::
                { Heap[n_7, car] } { QPMask[n_7, car] } { Heap[n_7, car] }
                g[n_7] && NoPerm < FullPerm ==> qpRange17(n_7) && invRecv17(n_7) == n_7
              );
              assume (forall o_3: Ref ::
                { invRecv17(o_3) }
                g[invRecv17(o_3)] && (NoPerm < FullPerm && qpRange17(o_3)) ==> invRecv17(o_3) == o_3
              );

            // -- assume permission updates for field car
              assume (forall o_3: Ref ::
                { QPMask[o_3, car] }
                (g[invRecv17(o_3)] && (NoPerm < FullPerm && qpRange17(o_3)) ==> invRecv17(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv17(o_3)] && (NoPerm < FullPerm && qpRange17(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
              );

            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            havoc QPMask;

            // -- check that the permission amount is positive


            // -- check if receiver n$0 is injective
              assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@212.32--212.37) [585]"}
                (forall n$0_4: Ref, n$0_4_1: Ref ::
                { neverTriggered18(n$0_4), neverTriggered18(n$0_4_1) }
                (((n$0_4 != n$0_4_1 && g[n$0_4]) && g[n$0_4_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_4 != n$0_4_1
              );

            // -- check if sufficient permission is held
              assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@212.32--212.37) [586]"}
                (forall n$0_4: Ref ::
                { Heap[n$0_4, cdr] } { QPMask[n$0_4, cdr] } { Heap[n$0_4, cdr] }
                g[n$0_4] ==> Mask[n$0_4, cdr] >= FullPerm
              );

            // -- assumptions for inverse of receiver n$0
              assume (forall n$0_4: Ref ::
                { Heap[n$0_4, cdr] } { QPMask[n$0_4, cdr] } { Heap[n$0_4, cdr] }
                g[n$0_4] && NoPerm < FullPerm ==> qpRange18(n$0_4) && invRecv18(n$0_4) == n$0_4
              );
              assume (forall o_3: Ref ::
                { invRecv18(o_3) }
                g[invRecv18(o_3)] && (NoPerm < FullPerm && qpRange18(o_3)) ==> invRecv18(o_3) == o_3
              );

            // -- assume permission updates for field cdr
              assume (forall o_3: Ref ::
                { QPMask[o_3, cdr] }
                (g[invRecv18(o_3)] && (NoPerm < FullPerm && qpRange18(o_3)) ==> invRecv18(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv18(o_3)] && (NoPerm < FullPerm && qpRange18(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
              );

            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
            // Stop execution
            assume false;
          }
        assume (exists_spath($$(Heap, g), roots, x_1): bool);

        // -- Check definedness of x.cdr != null
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.cdr (graph_mark.vpr@212.19--214.118) [587]"}
            HasDirectPerm(Mask, x_1, cdr);
        if (Heap[x_1, cdr] != null) {

          // -- Check definedness of (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.cdr (graph_mark.vpr@212.19--214.118) [588]"}
              HasDirectPerm(Mask, x_1, cdr);
            if (*) {
              // Exhale precondition of function application
              havoc QPMask;

              // -- check that the permission amount is positive


              // -- check if receiver n is injective
                assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@213.32--213.51) [589]"}
                  (forall n_8: Ref, n_8_1: Ref ::
                  { neverTriggered19(n_8), neverTriggered19(n_8_1) }
                  (((n_8 != n_8_1 && g[n_8]) && g[n_8_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_8 != n_8_1
                );

              // -- check if sufficient permission is held
                assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@213.32--213.51) [590]"}
                  (forall n_8: Ref ::
                  { Heap[n_8, car] } { QPMask[n_8, car] } { Heap[n_8, car] }
                  g[n_8] ==> Mask[n_8, car] >= FullPerm
                );

              // -- assumptions for inverse of receiver n
                assume (forall n_8: Ref ::
                  { Heap[n_8, car] } { QPMask[n_8, car] } { Heap[n_8, car] }
                  g[n_8] && NoPerm < FullPerm ==> qpRange19(n_8) && invRecv19(n_8) == n_8
                );
                assume (forall o_3: Ref ::
                  { invRecv19(o_3) }
                  g[invRecv19(o_3)] && (NoPerm < FullPerm && qpRange19(o_3)) ==> invRecv19(o_3) == o_3
                );

              // -- assume permission updates for field car
                assume (forall o_3: Ref ::
                  { QPMask[o_3, car] }
                  (g[invRecv19(o_3)] && (NoPerm < FullPerm && qpRange19(o_3)) ==> invRecv19(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv19(o_3)] && (NoPerm < FullPerm && qpRange19(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                );

              // -- assume permission updates for independent locations
                assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                  { QPMask[o_3, f_5] }
                  f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                );
              Mask := QPMask;
              havoc QPMask;

              // -- check that the permission amount is positive


              // -- check if receiver n$0 is injective
                assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@213.32--213.51) [591]"}
                  (forall n$0_5: Ref, n$0_5_1: Ref ::
                  { neverTriggered20(n$0_5), neverTriggered20(n$0_5_1) }
                  (((n$0_5 != n$0_5_1 && g[n$0_5]) && g[n$0_5_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_5 != n$0_5_1
                );

              // -- check if sufficient permission is held
                assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@213.32--213.51) [592]"}
                  (forall n$0_5: Ref ::
                  { Heap[n$0_5, cdr] } { QPMask[n$0_5, cdr] } { Heap[n$0_5, cdr] }
                  g[n$0_5] ==> Mask[n$0_5, cdr] >= FullPerm
                );

              // -- assumptions for inverse of receiver n$0
                assume (forall n$0_5: Ref ::
                  { Heap[n$0_5, cdr] } { QPMask[n$0_5, cdr] } { Heap[n$0_5, cdr] }
                  g[n$0_5] && NoPerm < FullPerm ==> qpRange20(n$0_5) && invRecv20(n$0_5) == n$0_5
                );
                assume (forall o_3: Ref ::
                  { invRecv20(o_3) }
                  g[invRecv20(o_3)] && (NoPerm < FullPerm && qpRange20(o_3)) ==> invRecv20(o_3) == o_3
                );

              // -- assume permission updates for field cdr
                assume (forall o_3: Ref ::
                  { QPMask[o_3, cdr] }
                  (g[invRecv20(o_3)] && (NoPerm < FullPerm && qpRange20(o_3)) ==> invRecv20(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv20(o_3)] && (NoPerm < FullPerm && qpRange20(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                );

              // -- assume permission updates for independent locations
                assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                  { QPMask[o_3, f_5] }
                  f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                );
              Mask := QPMask;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
              // Stop execution
              assume false;
            }
            if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, cdr]): EdgeDomainType)]) {
              if (*) {
                // Exhale precondition of function application
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@213.67--213.72) [593]"}
                    (forall n_9: Ref, n_9_1: Ref ::
                    { neverTriggered21(n_9), neverTriggered21(n_9_1) }
                    (((n_9 != n_9_1 && g[n_9]) && g[n_9_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_9 != n_9_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@213.67--213.72) [594]"}
                    (forall n_9: Ref ::
                    { Heap[n_9, car] } { QPMask[n_9, car] } { Heap[n_9, car] }
                    g[n_9] ==> Mask[n_9, car] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n
                  assume (forall n_9: Ref ::
                    { Heap[n_9, car] } { QPMask[n_9, car] } { Heap[n_9, car] }
                    g[n_9] && NoPerm < FullPerm ==> qpRange21(n_9) && invRecv21(n_9) == n_9
                  );
                  assume (forall o_3: Ref ::
                    { invRecv21(o_3) }
                    g[invRecv21(o_3)] && (NoPerm < FullPerm && qpRange21(o_3)) ==> invRecv21(o_3) == o_3
                  );

                // -- assume permission updates for field car
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, car] }
                    (g[invRecv21(o_3)] && (NoPerm < FullPerm && qpRange21(o_3)) ==> invRecv21(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv21(o_3)] && (NoPerm < FullPerm && qpRange21(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n$0 is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@213.67--213.72) [595]"}
                    (forall n$0_6: Ref, n$0_6_1: Ref ::
                    { neverTriggered22(n$0_6), neverTriggered22(n$0_6_1) }
                    (((n$0_6 != n$0_6_1 && g[n$0_6]) && g[n$0_6_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_6 != n$0_6_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@213.67--213.72) [596]"}
                    (forall n$0_6: Ref ::
                    { Heap[n$0_6, cdr] } { QPMask[n$0_6, cdr] } { Heap[n$0_6, cdr] }
                    g[n$0_6] ==> Mask[n$0_6, cdr] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n$0
                  assume (forall n$0_6: Ref ::
                    { Heap[n$0_6, cdr] } { QPMask[n$0_6, cdr] } { Heap[n$0_6, cdr] }
                    g[n$0_6] && NoPerm < FullPerm ==> qpRange22(n$0_6) && invRecv22(n$0_6) == n$0_6
                  );
                  assume (forall o_3: Ref ::
                    { invRecv22(o_3) }
                    g[invRecv22(o_3)] && (NoPerm < FullPerm && qpRange22(o_3)) ==> invRecv22(o_3) == o_3
                  );

                // -- assume permission updates for field cdr
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, cdr] }
                    (g[invRecv22(o_3)] && (NoPerm < FullPerm && qpRange22(o_3)) ==> invRecv22(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv22(o_3)] && (NoPerm < FullPerm && qpRange22(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.cdr (graph_mark.vpr@212.19--214.118) [597]"}
                HasDirectPerm(Mask, x_1, cdr);
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.cdr (graph_mark.vpr@212.19--214.118) [598]"}
                HasDirectPerm(Mask, x_1, cdr);
            }
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, cdr]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, cdr], Heap[x_1, cdr]): bool)) {
            assume state(Heap, Mask);

            // -- Check definedness of exists_path($$(g), x, x.cdr)
              if (*) {
                // Exhale precondition of function application
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@213.102--213.107) [599]"}
                    (forall n_10: Ref, n_10_1: Ref ::
                    { neverTriggered23(n_10), neverTriggered23(n_10_1) }
                    (((n_10 != n_10_1 && g[n_10]) && g[n_10_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_10 != n_10_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@213.102--213.107) [600]"}
                    (forall n_10: Ref ::
                    { Heap[n_10, car] } { QPMask[n_10, car] } { Heap[n_10, car] }
                    g[n_10] ==> Mask[n_10, car] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n
                  assume (forall n_10: Ref ::
                    { Heap[n_10, car] } { QPMask[n_10, car] } { Heap[n_10, car] }
                    g[n_10] && NoPerm < FullPerm ==> qpRange23(n_10) && invRecv23(n_10) == n_10
                  );
                  assume (forall o_3: Ref ::
                    { invRecv23(o_3) }
                    g[invRecv23(o_3)] && (NoPerm < FullPerm && qpRange23(o_3)) ==> invRecv23(o_3) == o_3
                  );

                // -- assume permission updates for field car
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, car] }
                    (g[invRecv23(o_3)] && (NoPerm < FullPerm && qpRange23(o_3)) ==> invRecv23(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv23(o_3)] && (NoPerm < FullPerm && qpRange23(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n$0 is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@213.102--213.107) [601]"}
                    (forall n$0_7: Ref, n$0_7_1: Ref ::
                    { neverTriggered24(n$0_7), neverTriggered24(n$0_7_1) }
                    (((n$0_7 != n$0_7_1 && g[n$0_7]) && g[n$0_7_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_7 != n$0_7_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@213.102--213.107) [602]"}
                    (forall n$0_7: Ref ::
                    { Heap[n$0_7, cdr] } { QPMask[n$0_7, cdr] } { Heap[n$0_7, cdr] }
                    g[n$0_7] ==> Mask[n$0_7, cdr] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n$0
                  assume (forall n$0_7: Ref ::
                    { Heap[n$0_7, cdr] } { QPMask[n$0_7, cdr] } { Heap[n$0_7, cdr] }
                    g[n$0_7] && NoPerm < FullPerm ==> qpRange24(n$0_7) && invRecv24(n$0_7) == n$0_7
                  );
                  assume (forall o_3: Ref ::
                    { invRecv24(o_3) }
                    g[invRecv24(o_3)] && (NoPerm < FullPerm && qpRange24(o_3)) ==> invRecv24(o_3) == o_3
                  );

                // -- assume permission updates for field cdr
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, cdr] }
                    (g[invRecv24(o_3)] && (NoPerm < FullPerm && qpRange24(o_3)) ==> invRecv24(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv24(o_3)] && (NoPerm < FullPerm && qpRange24(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.cdr (graph_mark.vpr@212.19--214.118) [603]"}
                HasDirectPerm(Mask, x_1, cdr);
            assume (exists_path($$(Heap, g), x_1, Heap[x_1, cdr]): bool);
          }
        }

        // -- Check definedness of x.car != null
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.car (graph_mark.vpr@212.19--214.118) [604]"}
            HasDirectPerm(Mask, x_1, car);
        if (Heap[x_1, car] != null) {

          // -- Check definedness of (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.car (graph_mark.vpr@212.19--214.118) [605]"}
              HasDirectPerm(Mask, x_1, car);
            if (*) {
              // Exhale precondition of function application
              havoc QPMask;

              // -- check that the permission amount is positive


              // -- check if receiver n is injective
                assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@214.32--214.51) [606]"}
                  (forall n_11: Ref, n_11_1: Ref ::
                  { neverTriggered25(n_11), neverTriggered25(n_11_1) }
                  (((n_11 != n_11_1 && g[n_11]) && g[n_11_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_11 != n_11_1
                );

              // -- check if sufficient permission is held
                assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@214.32--214.51) [607]"}
                  (forall n_11: Ref ::
                  { Heap[n_11, car] } { QPMask[n_11, car] } { Heap[n_11, car] }
                  g[n_11] ==> Mask[n_11, car] >= FullPerm
                );

              // -- assumptions for inverse of receiver n
                assume (forall n_11: Ref ::
                  { Heap[n_11, car] } { QPMask[n_11, car] } { Heap[n_11, car] }
                  g[n_11] && NoPerm < FullPerm ==> qpRange25(n_11) && invRecv25(n_11) == n_11
                );
                assume (forall o_3: Ref ::
                  { invRecv25(o_3) }
                  g[invRecv25(o_3)] && (NoPerm < FullPerm && qpRange25(o_3)) ==> invRecv25(o_3) == o_3
                );

              // -- assume permission updates for field car
                assume (forall o_3: Ref ::
                  { QPMask[o_3, car] }
                  (g[invRecv25(o_3)] && (NoPerm < FullPerm && qpRange25(o_3)) ==> invRecv25(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv25(o_3)] && (NoPerm < FullPerm && qpRange25(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                );

              // -- assume permission updates for independent locations
                assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                  { QPMask[o_3, f_5] }
                  f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                );
              Mask := QPMask;
              havoc QPMask;

              // -- check that the permission amount is positive


              // -- check if receiver n$0 is injective
                assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@214.32--214.51) [608]"}
                  (forall n$0_8: Ref, n$0_8_1: Ref ::
                  { neverTriggered26(n$0_8), neverTriggered26(n$0_8_1) }
                  (((n$0_8 != n$0_8_1 && g[n$0_8]) && g[n$0_8_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_8 != n$0_8_1
                );

              // -- check if sufficient permission is held
                assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@214.32--214.51) [609]"}
                  (forall n$0_8: Ref ::
                  { Heap[n$0_8, cdr] } { QPMask[n$0_8, cdr] } { Heap[n$0_8, cdr] }
                  g[n$0_8] ==> Mask[n$0_8, cdr] >= FullPerm
                );

              // -- assumptions for inverse of receiver n$0
                assume (forall n$0_8: Ref ::
                  { Heap[n$0_8, cdr] } { QPMask[n$0_8, cdr] } { Heap[n$0_8, cdr] }
                  g[n$0_8] && NoPerm < FullPerm ==> qpRange26(n$0_8) && invRecv26(n$0_8) == n$0_8
                );
                assume (forall o_3: Ref ::
                  { invRecv26(o_3) }
                  g[invRecv26(o_3)] && (NoPerm < FullPerm && qpRange26(o_3)) ==> invRecv26(o_3) == o_3
                );

              // -- assume permission updates for field cdr
                assume (forall o_3: Ref ::
                  { QPMask[o_3, cdr] }
                  (g[invRecv26(o_3)] && (NoPerm < FullPerm && qpRange26(o_3)) ==> invRecv26(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv26(o_3)] && (NoPerm < FullPerm && qpRange26(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                );

              // -- assume permission updates for independent locations
                assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                  { QPMask[o_3, f_5] }
                  f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                );
              Mask := QPMask;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
              // Stop execution
              assume false;
            }
            if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, car]): EdgeDomainType)]) {
              if (*) {
                // Exhale precondition of function application
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@214.67--214.72) [610]"}
                    (forall n_12: Ref, n_12_1: Ref ::
                    { neverTriggered27(n_12), neverTriggered27(n_12_1) }
                    (((n_12 != n_12_1 && g[n_12]) && g[n_12_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_12 != n_12_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@214.67--214.72) [611]"}
                    (forall n_12: Ref ::
                    { Heap[n_12, car] } { QPMask[n_12, car] } { Heap[n_12, car] }
                    g[n_12] ==> Mask[n_12, car] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n
                  assume (forall n_12: Ref ::
                    { Heap[n_12, car] } { QPMask[n_12, car] } { Heap[n_12, car] }
                    g[n_12] && NoPerm < FullPerm ==> qpRange27(n_12) && invRecv27(n_12) == n_12
                  );
                  assume (forall o_3: Ref ::
                    { invRecv27(o_3) }
                    g[invRecv27(o_3)] && (NoPerm < FullPerm && qpRange27(o_3)) ==> invRecv27(o_3) == o_3
                  );

                // -- assume permission updates for field car
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, car] }
                    (g[invRecv27(o_3)] && (NoPerm < FullPerm && qpRange27(o_3)) ==> invRecv27(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv27(o_3)] && (NoPerm < FullPerm && qpRange27(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n$0 is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@214.67--214.72) [612]"}
                    (forall n$0_9: Ref, n$0_9_1: Ref ::
                    { neverTriggered28(n$0_9), neverTriggered28(n$0_9_1) }
                    (((n$0_9 != n$0_9_1 && g[n$0_9]) && g[n$0_9_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_9 != n$0_9_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@214.67--214.72) [613]"}
                    (forall n$0_9: Ref ::
                    { Heap[n$0_9, cdr] } { QPMask[n$0_9, cdr] } { Heap[n$0_9, cdr] }
                    g[n$0_9] ==> Mask[n$0_9, cdr] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n$0
                  assume (forall n$0_9: Ref ::
                    { Heap[n$0_9, cdr] } { QPMask[n$0_9, cdr] } { Heap[n$0_9, cdr] }
                    g[n$0_9] && NoPerm < FullPerm ==> qpRange28(n$0_9) && invRecv28(n$0_9) == n$0_9
                  );
                  assume (forall o_3: Ref ::
                    { invRecv28(o_3) }
                    g[invRecv28(o_3)] && (NoPerm < FullPerm && qpRange28(o_3)) ==> invRecv28(o_3) == o_3
                  );

                // -- assume permission updates for field cdr
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, cdr] }
                    (g[invRecv28(o_3)] && (NoPerm < FullPerm && qpRange28(o_3)) ==> invRecv28(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv28(o_3)] && (NoPerm < FullPerm && qpRange28(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.car (graph_mark.vpr@212.19--214.118) [614]"}
                HasDirectPerm(Mask, x_1, car);
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.car (graph_mark.vpr@212.19--214.118) [615]"}
                HasDirectPerm(Mask, x_1, car);
            }
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, car]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, car], Heap[x_1, car]): bool)) {
            assume state(Heap, Mask);

            // -- Check definedness of exists_path($$(g), x, x.car)
              if (*) {
                // Exhale precondition of function application
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@214.102--214.107) [616]"}
                    (forall n_13: Ref, n_13_1: Ref ::
                    { neverTriggered29(n_13), neverTriggered29(n_13_1) }
                    (((n_13 != n_13_1 && g[n_13]) && g[n_13_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_13 != n_13_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@214.102--214.107) [617]"}
                    (forall n_13: Ref ::
                    { Heap[n_13, car] } { QPMask[n_13, car] } { Heap[n_13, car] }
                    g[n_13] ==> Mask[n_13, car] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n
                  assume (forall n_13: Ref ::
                    { Heap[n_13, car] } { QPMask[n_13, car] } { Heap[n_13, car] }
                    g[n_13] && NoPerm < FullPerm ==> qpRange29(n_13) && invRecv29(n_13) == n_13
                  );
                  assume (forall o_3: Ref ::
                    { invRecv29(o_3) }
                    g[invRecv29(o_3)] && (NoPerm < FullPerm && qpRange29(o_3)) ==> invRecv29(o_3) == o_3
                  );

                // -- assume permission updates for field car
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, car] }
                    (g[invRecv29(o_3)] && (NoPerm < FullPerm && qpRange29(o_3)) ==> invRecv29(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv29(o_3)] && (NoPerm < FullPerm && qpRange29(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                havoc QPMask;

                // -- check that the permission amount is positive


                // -- check if receiver n$0 is injective
                  assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@214.102--214.107) [618]"}
                    (forall n$0_10: Ref, n$0_10_1: Ref ::
                    { neverTriggered30(n$0_10), neverTriggered30(n$0_10_1) }
                    (((n$0_10 != n$0_10_1 && g[n$0_10]) && g[n$0_10_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_10 != n$0_10_1
                  );

                // -- check if sufficient permission is held
                  assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@214.102--214.107) [619]"}
                    (forall n$0_10: Ref ::
                    { Heap[n$0_10, cdr] } { QPMask[n$0_10, cdr] } { Heap[n$0_10, cdr] }
                    g[n$0_10] ==> Mask[n$0_10, cdr] >= FullPerm
                  );

                // -- assumptions for inverse of receiver n$0
                  assume (forall n$0_10: Ref ::
                    { Heap[n$0_10, cdr] } { QPMask[n$0_10, cdr] } { Heap[n$0_10, cdr] }
                    g[n$0_10] && NoPerm < FullPerm ==> qpRange30(n$0_10) && invRecv30(n$0_10) == n$0_10
                  );
                  assume (forall o_3: Ref ::
                    { invRecv30(o_3) }
                    g[invRecv30(o_3)] && (NoPerm < FullPerm && qpRange30(o_3)) ==> invRecv30(o_3) == o_3
                  );

                // -- assume permission updates for field cdr
                  assume (forall o_3: Ref ::
                    { QPMask[o_3, cdr] }
                    (g[invRecv30(o_3)] && (NoPerm < FullPerm && qpRange30(o_3)) ==> invRecv30(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv30(o_3)] && (NoPerm < FullPerm && qpRange30(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                  );

                // -- assume permission updates for independent locations
                  assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                    { QPMask[o_3, f_5] }
                    f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                  );
                Mask := QPMask;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.car (graph_mark.vpr@212.19--214.118) [620]"}
                HasDirectPerm(Mask, x_1, car);
            assume (exists_path($$(Heap, g), x_1, Heap[x_1, car]): bool);
          }
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);

        // -- Check definedness of (forall n: Ref :: { (n in pending) } { (n in roots) } (n in roots) == (n in pending)) && (forall n: Ref :: { (n in marked) } (n in g) ==> !((n in marked))) || (forall n: Ref :: { (n in pending) } { (n in marked) } (n in roots) ==> (n in marked) || (n in pending)) && ((forall n: Ref :: { (n in pending) } (n in g) ==> !((n in marked) && (n in pending))) && ((forall n: Ref :: { exists_spath($$(g), roots, n) } (n in pending) || (n in marked) ==> exists_spath($$(g), roots, n)) && (forall n1: Ref, n2: Ref :: { (n1 in marked), (n2 in marked) } (n1 in marked) && ((n2 in g) && (!((n2 in marked)) && !((n2 in pending)))) ==> !((create_edge(n1, n2) in $$(g))))))
          if (*) {
            assume false;
          }
          if ((forall n_15: Ref ::
            { pending[n_15] } { roots[n_15] }
            roots[n_15] == pending[n_15]
          )) {
            if (*) {
              assume false;
            }
          }
          if (!((forall n_17: Ref ::
            { pending[n_17] } { roots[n_17] }
            roots[n_17] == pending[n_17]
          ) && (forall n_18: Ref ::
            { marked[n_18] }
            g[n_18] ==> !marked[n_18]
          ))) {
            if (*) {
              assume false;
            }
            if ((forall n_20: Ref ::
              { pending[n_20] } { marked[n_20] }
              roots[n_20] ==> marked[n_20] || pending[n_20]
            )) {
              if (*) {
                assume false;
              }
              if ((forall n_22: Ref ::
                { pending[n_22] }
                g[n_22] ==> !(marked[n_22] && pending[n_22])
              )) {
                if (*) {
                  if (pending[n_14] || marked[n_14]) {
                    if (*) {
                      // Exhale precondition of function application
                      havoc QPMask;

                      // -- check that the permission amount is positive


                      // -- check if receiver n$0 is injective
                        assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.car might not be injective. (graph_mark.vpr@222.102--222.107) [621]"}
                          (forall n$0_11: Ref, n$0_11_1: Ref ::
                          { neverTriggered31(n$0_11), neverTriggered31(n$0_11_1) }
                          (((n$0_11 != n$0_11_1 && g[n$0_11]) && g[n$0_11_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_11 != n$0_11_1
                        );

                      // -- check if sufficient permission is held
                        assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.car (graph_mark.vpr@222.102--222.107) [622]"}
                          (forall n$0_11: Ref ::
                          { Heap[n$0_11, car] } { QPMask[n$0_11, car] } { Heap[n$0_11, car] }
                          g[n$0_11] ==> Mask[n$0_11, car] >= FullPerm
                        );

                      // -- assumptions for inverse of receiver n$0
                        assume (forall n$0_11: Ref ::
                          { Heap[n$0_11, car] } { QPMask[n$0_11, car] } { Heap[n$0_11, car] }
                          g[n$0_11] && NoPerm < FullPerm ==> qpRange31(n$0_11) && invRecv31(n$0_11) == n$0_11
                        );
                        assume (forall o_3: Ref ::
                          { invRecv31(o_3) }
                          g[invRecv31(o_3)] && (NoPerm < FullPerm && qpRange31(o_3)) ==> invRecv31(o_3) == o_3
                        );

                      // -- assume permission updates for field car
                        assume (forall o_3: Ref ::
                          { QPMask[o_3, car] }
                          (g[invRecv31(o_3)] && (NoPerm < FullPerm && qpRange31(o_3)) ==> invRecv31(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv31(o_3)] && (NoPerm < FullPerm && qpRange31(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                        );

                      // -- assume permission updates for independent locations
                        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                          { QPMask[o_3, f_5] }
                          f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                        );
                      Mask := QPMask;
                      havoc QPMask;

                      // -- check that the permission amount is positive


                      // -- check if receiver n$0 is injective
                        assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@222.102--222.107) [623]"}
                          (forall n$0_12: Ref, n$0_12_1: Ref ::
                          { neverTriggered32(n$0_12), neverTriggered32(n$0_12_1) }
                          (((n$0_12 != n$0_12_1 && g[n$0_12]) && g[n$0_12_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_12 != n$0_12_1
                        );

                      // -- check if sufficient permission is held
                        assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@222.102--222.107) [624]"}
                          (forall n$0_12: Ref ::
                          { Heap[n$0_12, cdr] } { QPMask[n$0_12, cdr] } { Heap[n$0_12, cdr] }
                          g[n$0_12] ==> Mask[n$0_12, cdr] >= FullPerm
                        );

                      // -- assumptions for inverse of receiver n$0
                        assume (forall n$0_12: Ref ::
                          { Heap[n$0_12, cdr] } { QPMask[n$0_12, cdr] } { Heap[n$0_12, cdr] }
                          g[n$0_12] && NoPerm < FullPerm ==> qpRange32(n$0_12) && invRecv32(n$0_12) == n$0_12
                        );
                        assume (forall o_3: Ref ::
                          { invRecv32(o_3) }
                          g[invRecv32(o_3)] && (NoPerm < FullPerm && qpRange32(o_3)) ==> invRecv32(o_3) == o_3
                        );

                      // -- assume permission updates for field cdr
                        assume (forall o_3: Ref ::
                          { QPMask[o_3, cdr] }
                          (g[invRecv32(o_3)] && (NoPerm < FullPerm && qpRange32(o_3)) ==> invRecv32(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv32(o_3)] && (NoPerm < FullPerm && qpRange32(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                        );

                      // -- assume permission updates for independent locations
                        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                          { QPMask[o_3, f_5] }
                          f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                        );
                      Mask := QPMask;
                      // Finish exhale
                      havoc ExhaleHeap;
                      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                      Heap := ExhaleHeap;
                      // Stop execution
                      assume false;
                    }
                  }
                  assume false;
                }
                if ((forall n_24: Ref ::
                  { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, n_24): bool) }
                  pending[n_24] || marked[n_24] ==> (exists_spath($$(Heap, g), roots, n_24): bool)
                )) {
                  if (*) {
                    if (marked[n1_1] && (g[n2_1] && (!marked[n2_1] && !pending[n2_1]))) {
                      if (*) {
                        // Exhale precondition of function application
                        havoc QPMask;

                        // -- check that the permission amount is positive


                        // -- check if receiver n is injective
                          assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@223.133--223.150) [625]"}
                            (forall n_25: Ref, n_25_1: Ref ::
                            { neverTriggered33(n_25), neverTriggered33(n_25_1) }
                            (((n_25 != n_25_1 && g[n_25]) && g[n_25_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_25 != n_25_1
                          );

                        // -- check if sufficient permission is held
                          assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@223.133--223.150) [626]"}
                            (forall n_25: Ref ::
                            { Heap[n_25, car] } { QPMask[n_25, car] } { Heap[n_25, car] }
                            g[n_25] ==> Mask[n_25, car] >= FullPerm
                          );

                        // -- assumptions for inverse of receiver n
                          assume (forall n_25: Ref ::
                            { Heap[n_25, car] } { QPMask[n_25, car] } { Heap[n_25, car] }
                            g[n_25] && NoPerm < FullPerm ==> qpRange33(n_25) && invRecv33(n_25) == n_25
                          );
                          assume (forall o_3: Ref ::
                            { invRecv33(o_3) }
                            g[invRecv33(o_3)] && (NoPerm < FullPerm && qpRange33(o_3)) ==> invRecv33(o_3) == o_3
                          );

                        // -- assume permission updates for field car
                          assume (forall o_3: Ref ::
                            { QPMask[o_3, car] }
                            (g[invRecv33(o_3)] && (NoPerm < FullPerm && qpRange33(o_3)) ==> invRecv33(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv33(o_3)] && (NoPerm < FullPerm && qpRange33(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
                          );

                        // -- assume permission updates for independent locations
                          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                            { QPMask[o_3, f_5] }
                            f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                          );
                        Mask := QPMask;
                        havoc QPMask;

                        // -- check that the permission amount is positive


                        // -- check if receiver n$0 is injective
                          assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@223.133--223.150) [627]"}
                            (forall n$0_13: Ref, n$0_13_1: Ref ::
                            { neverTriggered34(n$0_13), neverTriggered34(n$0_13_1) }
                            (((n$0_13 != n$0_13_1 && g[n$0_13]) && g[n$0_13_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_13 != n$0_13_1
                          );

                        // -- check if sufficient permission is held
                          assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@223.133--223.150) [628]"}
                            (forall n$0_13: Ref ::
                            { Heap[n$0_13, cdr] } { QPMask[n$0_13, cdr] } { Heap[n$0_13, cdr] }
                            g[n$0_13] ==> Mask[n$0_13, cdr] >= FullPerm
                          );

                        // -- assumptions for inverse of receiver n$0
                          assume (forall n$0_13: Ref ::
                            { Heap[n$0_13, cdr] } { QPMask[n$0_13, cdr] } { Heap[n$0_13, cdr] }
                            g[n$0_13] && NoPerm < FullPerm ==> qpRange34(n$0_13) && invRecv34(n$0_13) == n$0_13
                          );
                          assume (forall o_3: Ref ::
                            { invRecv34(o_3) }
                            g[invRecv34(o_3)] && (NoPerm < FullPerm && qpRange34(o_3)) ==> invRecv34(o_3) == o_3
                          );

                        // -- assume permission updates for field cdr
                          assume (forall o_3: Ref ::
                            { QPMask[o_3, cdr] }
                            (g[invRecv34(o_3)] && (NoPerm < FullPerm && qpRange34(o_3)) ==> invRecv34(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv34(o_3)] && (NoPerm < FullPerm && qpRange34(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
                          );

                        // -- assume permission updates for independent locations
                          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                            { QPMask[o_3, f_5] }
                            f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                          );
                        Mask := QPMask;
                        // Finish exhale
                        havoc ExhaleHeap;
                        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                        Heap := ExhaleHeap;
                        // Stop execution
                        assume false;
                      }
                    }
                    assume false;
                  }
                }
              }
            }
          }
        assume ((forall n_26: Ref ::
          { pending[n_26] } { roots[n_26] }
          roots[n_26] == pending[n_26]
        ) && (forall n_27: Ref ::
          { marked[n_27] }
          g[n_27] ==> !marked[n_27]
        )) || ((forall n_28: Ref ::
          { pending[n_28] } { marked[n_28] }
          roots[n_28] ==> marked[n_28] || pending[n_28]
        ) && ((forall n_29: Ref ::
          { pending[n_29] }
          g[n_29] ==> !(marked[n_29] && pending[n_29])
        ) && ((forall n_30: Ref ::
          { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, n_30): bool) }
          pending[n_30] || marked[n_30] ==> (exists_spath($$(Heap, g), roots, n_30): bool)
        ) && (forall n1_2: Ref, n2_2: Ref ::
          { marked[n1_2], marked[n2_2] }
          marked[n1_2] && (g[n2_2] && (!marked[n2_2] && !pending[n2_2])) ==> !$$(Heap, g)[(create_edge(n1_2, n2_2): EdgeDomainType)]
        ))));
        assume state(Heap, Mask);
        assume false;
      }

    // -- Check the loop body
      if (*) {
        // Reset state
        loopHeap := Heap;
        loopMask := Mask;
        Mask := ZeroMask;
        assume state(Heap, Mask);
        // Inhale invariant
        assume !g[null];
        havoc QPMask;
        assert {:msg "  While statement might fail. Quantified resource n$10.car might not be injective. (graph_mark.vpr@205.19--205.27) [629]"}
          (forall n$10_3: Ref, n$10_3_1: Ref ::

          (((n$10_3 != n$10_3_1 && g[n$10_3]) && g[n$10_3_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$10_3 != n$10_3_1
        );

        // -- Define Inverse Function
          assume (forall n$10_3: Ref ::
            { Heap[n$10_3, car] } { QPMask[n$10_3, car] } { Heap[n$10_3, car] }
            g[n$10_3] && NoPerm < FullPerm ==> qpRange35(n$10_3) && invRecv35(n$10_3) == n$10_3
          );
          assume (forall o_3: Ref ::
            { invRecv35(o_3) }
            (g[invRecv35(o_3)] && NoPerm < FullPerm) && qpRange35(o_3) ==> invRecv35(o_3) == o_3
          );

        // -- Assume set of fields is nonNull
          assume (forall n$10_3: Ref ::
            { Heap[n$10_3, car] } { QPMask[n$10_3, car] } { Heap[n$10_3, car] }
            g[n$10_3] ==> n$10_3 != null
          );

        // -- Define permissions
          assume (forall o_3: Ref ::
            { QPMask[o_3, car] }
            ((g[invRecv35(o_3)] && NoPerm < FullPerm) && qpRange35(o_3) ==> (NoPerm < FullPerm ==> invRecv35(o_3) == o_3) && QPMask[o_3, car] == Mask[o_3, car] + FullPerm) && (!((g[invRecv35(o_3)] && NoPerm < FullPerm) && qpRange35(o_3)) ==> QPMask[o_3, car] == Mask[o_3, car])
          );
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
            f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        havoc QPMask;
        assert {:msg "  While statement might fail. Quantified resource n$11.cdr might not be injective. (graph_mark.vpr@205.19--205.27) [630]"}
          (forall n$11_3: Ref, n$11_3_1: Ref ::

          (((n$11_3 != n$11_3_1 && g[n$11_3]) && g[n$11_3_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$11_3 != n$11_3_1
        );

        // -- Define Inverse Function
          assume (forall n$11_3: Ref ::
            { Heap[n$11_3, cdr] } { QPMask[n$11_3, cdr] } { Heap[n$11_3, cdr] }
            g[n$11_3] && NoPerm < FullPerm ==> qpRange36(n$11_3) && invRecv36(n$11_3) == n$11_3
          );
          assume (forall o_3: Ref ::
            { invRecv36(o_3) }
            (g[invRecv36(o_3)] && NoPerm < FullPerm) && qpRange36(o_3) ==> invRecv36(o_3) == o_3
          );

        // -- Assume set of fields is nonNull
          assume (forall n$11_3: Ref ::
            { Heap[n$11_3, cdr] } { QPMask[n$11_3, cdr] } { Heap[n$11_3, cdr] }
            g[n$11_3] ==> n$11_3 != null
          );

        // -- Define permissions
          assume (forall o_3: Ref ::
            { QPMask[o_3, cdr] }
            ((g[invRecv36(o_3)] && NoPerm < FullPerm) && qpRange36(o_3) ==> (NoPerm < FullPerm ==> invRecv36(o_3) == o_3) && QPMask[o_3, cdr] == Mask[o_3, cdr] + FullPerm) && (!((g[invRecv36(o_3)] && NoPerm < FullPerm) && qpRange36(o_3)) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
          );
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
            f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume (forall n$8_4: Ref ::
          { g[Heap[n$8_4, car]] } { g[n$8_4], Heap[n$8_4, car] }
          g[n$8_4] ==> g[Heap[n$8_4, car]]
        );
        assume (forall n$9_4: Ref ::
          { g[Heap[n$9_4, cdr]] } { g[n$9_4], Heap[n$9_4, cdr] }
          g[n$9_4] ==> g[Heap[n$9_4, cdr]]
        );
        assume g[x_1];
        assume Set#Subset(pending, g);
        assume Set#Subset(marked, g);
        assume state(Heap, Mask);
        assume (exists_spath($$(Heap, g), roots, x_1): bool);
        if (Heap[x_1, cdr] != null) {
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, cdr]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, cdr], Heap[x_1, cdr]): bool)) {
            assume state(Heap, Mask);
            assume (exists_path($$(Heap, g), x_1, Heap[x_1, cdr]): bool);
          }
        }
        if (Heap[x_1, car] != null) {
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, car]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, car], Heap[x_1, car]): bool)) {
            assume state(Heap, Mask);
            assume (exists_path($$(Heap, g), x_1, Heap[x_1, car]): bool);
          }
        }
        assume state(Heap, Mask);
        assume ((forall n_31: Ref ::
          { pending[n_31] } { roots[n_31] }
          roots[n_31] == pending[n_31]
        ) && (forall n_32: Ref ::
          { marked[n_32] }
          g[n_32] ==> !marked[n_32]
        )) || ((forall n_33: Ref ::
          { pending[n_33] } { marked[n_33] }
          roots[n_33] ==> marked[n_33] || pending[n_33]
        ) && ((forall n_34: Ref ::
          { pending[n_34] }
          g[n_34] ==> !(marked[n_34] && pending[n_34])
        ) && ((forall n_35: Ref ::
          { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, n_35): bool) }
          pending[n_35] || marked[n_35] ==> (exists_spath($$(Heap, g), roots, n_35): bool)
        ) && (forall n1_3: Ref, n2_3: Ref ::
          { marked[n1_3], marked[n2_3] }
          marked[n1_3] && (g[n2_3] && (!marked[n2_3] && !pending[n2_3])) ==> !$$(Heap, g)[(create_edge(n1_3, n2_3): EdgeDomainType)]
        ))));
        assume state(Heap, Mask);
        // Check and assume guard
        assume Set#Card(pending) > 0;
        assume state(Heap, Mask);

        // -- Translate loop body

          // -- Translating statement: x := get(pending) -- graph_mark.vpr@226.9--226.26

            // -- Check definedness of get(pending)
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function get might not hold. Assertion |pending| > 0 might not hold. (graph_mark.vpr@226.14--226.26) [631]"}
                  Set#Card(pending) > 0;
                // Stop execution
                assume false;
              }
            x_1 := get(Heap, pending);
            assume state(Heap, Mask);

          // -- Translating statement: pending := (pending setminus Set(x)) -- graph_mark.vpr@227.9--227.43
            pending := Set#Difference(pending, Set#Singleton(x_1));
            assume state(Heap, Mask);

          // -- Translating statement: marked := (marked union Set(x)) -- graph_mark.vpr@230.9--230.38
            marked := Set#Union(marked, Set#Singleton(x_1));
            assume state(Heap, Mask);

          // -- Translating statement: if (x.car != null && !((x.car in marked))) -- graph_mark.vpr@232.9--234.10

            // -- Check definedness of x.car != null && !((x.car in marked))
              assert {:msg "  Conditional statement might fail. There might be insufficient permission to access x.car (graph_mark.vpr@232.14--232.49) [632]"}
                HasDirectPerm(Mask, x_1, car);
              if (Heap[x_1, car] != null) {
                assert {:msg "  Conditional statement might fail. There might be insufficient permission to access x.car (graph_mark.vpr@232.14--232.49) [633]"}
                  HasDirectPerm(Mask, x_1, car);
              }
            if (Heap[x_1, car] != null && !marked[Heap[x_1, car]]) {

              // -- Translating statement: pending := (pending union Set(x.car)) -- graph_mark.vpr@233.13--233.48

                // -- Check definedness of (pending union Set(x.car))
                  assert {:msg "  Assignment might fail. There might be insufficient permission to access x.car (graph_mark.vpr@233.13--233.48) [634]"}
                    HasDirectPerm(Mask, x_1, car);
                pending := Set#Union(pending, Set#Singleton(Heap[x_1, car]));
                assume state(Heap, Mask);
            }
            assume state(Heap, Mask);

          // -- Translating statement: if (x.cdr != null && !((x.cdr in marked))) -- graph_mark.vpr@235.9--237.10

            // -- Check definedness of x.cdr != null && !((x.cdr in marked))
              assert {:msg "  Conditional statement might fail. There might be insufficient permission to access x.cdr (graph_mark.vpr@235.14--235.49) [635]"}
                HasDirectPerm(Mask, x_1, cdr);
              if (Heap[x_1, cdr] != null) {
                assert {:msg "  Conditional statement might fail. There might be insufficient permission to access x.cdr (graph_mark.vpr@235.14--235.49) [636]"}
                  HasDirectPerm(Mask, x_1, cdr);
              }
            if (Heap[x_1, cdr] != null && !marked[Heap[x_1, cdr]]) {

              // -- Translating statement: pending := (pending union Set(x.cdr)) -- graph_mark.vpr@236.13--236.48

                // -- Check definedness of (pending union Set(x.cdr))
                  assert {:msg "  Assignment might fail. There might be insufficient permission to access x.cdr (graph_mark.vpr@236.13--236.48) [637]"}
                    HasDirectPerm(Mask, x_1, cdr);
                pending := Set#Union(pending, Set#Singleton(Heap[x_1, cdr]));
                assume state(Heap, Mask);
            }
            assume state(Heap, Mask);
        // Exhale invariant
        assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. Assertion !((null in g)) might not hold. (graph_mark.vpr@205.19--205.27) [638]"}
          !g[null];
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver n$10 is injective
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. Quantified resource n$10.car might not be injective. (graph_mark.vpr@205.19--205.27) [639]"}
            (forall n$10_4: Ref, n$10_4_1: Ref ::
            { neverTriggered37(n$10_4), neverTriggered37(n$10_4_1) }
            (((n$10_4 != n$10_4_1 && g[n$10_4]) && g[n$10_4_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$10_4 != n$10_4_1
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. There might be insufficient permission to access n$10.car (graph_mark.vpr@205.19--205.27) [640]"}
            (forall n$10_4: Ref ::
            { Heap[n$10_4, car] } { QPMask[n$10_4, car] } { Heap[n$10_4, car] }
            g[n$10_4] ==> Mask[n$10_4, car] >= FullPerm
          );

        // -- assumptions for inverse of receiver n$10
          assume (forall n$10_4: Ref ::
            { Heap[n$10_4, car] } { QPMask[n$10_4, car] } { Heap[n$10_4, car] }
            g[n$10_4] && NoPerm < FullPerm ==> qpRange37(n$10_4) && invRecv37(n$10_4) == n$10_4
          );
          assume (forall o_3: Ref ::
            { invRecv37(o_3) }
            g[invRecv37(o_3)] && (NoPerm < FullPerm && qpRange37(o_3)) ==> invRecv37(o_3) == o_3
          );

        // -- assume permission updates for field car
          assume (forall o_3: Ref ::
            { QPMask[o_3, car] }
            (g[invRecv37(o_3)] && (NoPerm < FullPerm && qpRange37(o_3)) ==> invRecv37(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv37(o_3)] && (NoPerm < FullPerm && qpRange37(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver n$11 is injective
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. Quantified resource n$11.cdr might not be injective. (graph_mark.vpr@205.19--205.27) [641]"}
            (forall n$11_4: Ref, n$11_4_1: Ref ::
            { neverTriggered38(n$11_4), neverTriggered38(n$11_4_1) }
            (((n$11_4 != n$11_4_1 && g[n$11_4]) && g[n$11_4_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$11_4 != n$11_4_1
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. There might be insufficient permission to access n$11.cdr (graph_mark.vpr@205.19--205.27) [642]"}
            (forall n$11_4: Ref ::
            { Heap[n$11_4, cdr] } { QPMask[n$11_4, cdr] } { Heap[n$11_4, cdr] }
            g[n$11_4] ==> Mask[n$11_4, cdr] >= FullPerm
          );

        // -- assumptions for inverse of receiver n$11
          assume (forall n$11_4: Ref ::
            { Heap[n$11_4, cdr] } { QPMask[n$11_4, cdr] } { Heap[n$11_4, cdr] }
            g[n$11_4] && NoPerm < FullPerm ==> qpRange38(n$11_4) && invRecv38(n$11_4) == n$11_4
          );
          assume (forall o_3: Ref ::
            { invRecv38(o_3) }
            g[invRecv38(o_3)] && (NoPerm < FullPerm && qpRange38(o_3)) ==> invRecv38(o_3) == o_3
          );

        // -- assume permission updates for field cdr
          assume (forall o_3: Ref ::
            { QPMask[o_3, cdr] }
            (g[invRecv38(o_3)] && (NoPerm < FullPerm && qpRange38(o_3)) ==> invRecv38(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv38(o_3)] && (NoPerm < FullPerm && qpRange38(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        if (*) {
          if (g[n$8_5]) {
            assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. Assertion (n$8.car in g) might not hold. (graph_mark.vpr@205.19--205.27) [643]"}
              g[Heap[n$8_5, car]];
          }
          assume false;
        }
        assume (forall n$8_6_1: Ref ::
          { g[Heap[n$8_6_1, car]] } { g[n$8_6_1], Heap[n$8_6_1, car] }
          g[n$8_6_1] ==> g[Heap[n$8_6_1, car]]
        );
        if (*) {
          if (g[n$9_5]) {
            assert {:msg "  Loop invariant !((null in g)) && (true && ((forall n$10: Ref :: { n$10.car } (n$10 in g) ==> acc(n$10.car, write)) && (forall n$11: Ref :: { n$11.cdr } (n$11 in g) ==> acc(n$11.cdr, write))) && ((forall n$8: Ref :: { (n$8.car in g) } { (n$8 in g), n$8.car } (n$8 in g) ==> (n$8.car in g)) && (forall n$9: Ref :: { (n$9.cdr in g) } { (n$9 in g), n$9.cdr } (n$9 in g) ==> (n$9.cdr in g)))) might not be preserved. Assertion (n$9.cdr in g) might not hold. (graph_mark.vpr@205.19--205.27) [644]"}
              g[Heap[n$9_5, cdr]];
          }
          assume false;
        }
        assume (forall n$9_6_1: Ref ::
          { g[Heap[n$9_6_1, cdr]] } { g[n$9_6_1], Heap[n$9_6_1, cdr] }
          g[n$9_6_1] ==> g[Heap[n$9_6_1, cdr]]
        );
        assert {:msg "  Loop invariant (x in g) might not be preserved. Assertion (x in g) might not hold. (graph_mark.vpr@208.19--208.25) [645]"}
          g[x_1];
        assert {:msg "  Loop invariant (pending subset g) might not be preserved. Assertion (pending subset g) might not hold. (graph_mark.vpr@209.27--209.35) [646]"}
          Set#Subset(pending, g);
        assert {:msg "  Loop invariant (marked subset g) might not be preserved. Assertion (marked subset g) might not hold. (graph_mark.vpr@210.26--210.34) [647]"}
          Set#Subset(marked, g);
        assert {:msg "  Loop invariant exists_spath($$(g), roots, x) && ((x.cdr != null ==> (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr) ==> exists_path($$(g), x, x.cdr)) && (x.car != null ==> (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car) ==> exists_path($$(g), x, x.car))) might not be preserved. Assertion exists_spath($$(g), roots, x) might not hold. (graph_mark.vpr@212.19--214.118) [648]"}
          (exists_spath($$(Heap, g), roots, x_1): bool);
        if (Heap[x_1, cdr] != null) {
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, cdr]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, cdr], Heap[x_1, cdr]): bool)) {
            assert {:msg "  Loop invariant exists_spath($$(g), roots, x) && ((x.cdr != null ==> (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr) ==> exists_path($$(g), x, x.cdr)) && (x.car != null ==> (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car) ==> exists_path($$(g), x, x.car))) might not be preserved. Assertion exists_path($$(g), x, x.cdr) might not hold. (graph_mark.vpr@212.19--214.118) [649]"}
              (exists_path($$(Heap, g), x_1, Heap[x_1, cdr]): bool);
          }
        }
        if (Heap[x_1, car] != null) {
          if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, car]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, car], Heap[x_1, car]): bool)) {
            assert {:msg "  Loop invariant exists_spath($$(g), roots, x) && ((x.cdr != null ==> (create_edge(x, x.cdr) in $$(g)) && exists_path($$(g), x.cdr, x.cdr) ==> exists_path($$(g), x, x.cdr)) && (x.car != null ==> (create_edge(x, x.car) in $$(g)) && exists_path($$(g), x.car, x.car) ==> exists_path($$(g), x, x.car))) might not be preserved. Assertion exists_path($$(g), x, x.car) might not hold. (graph_mark.vpr@212.19--214.118) [650]"}
              (exists_path($$(Heap, g), x_1, Heap[x_1, car]): bool);
          }
        }
        assert {:msg "  Loop invariant (forall n: Ref :: { (n in pending) } { (n in roots) } (n in roots) == (n in pending)) && (forall n: Ref :: { (n in marked) } (n in g) ==> !((n in marked))) || (forall n: Ref :: { (n in pending) } { (n in marked) } (n in roots) ==> (n in marked) || (n in pending)) && ((forall n: Ref :: { (n in pending) } (n in g) ==> !((n in marked) && (n in pending))) && ((forall n: Ref :: { exists_spath($$(g), roots, n) } (n in pending) || (n in marked) ==> exists_spath($$(g), roots, n)) && (forall n1: Ref, n2: Ref :: { (n1 in marked), (n2 in marked) } (n1 in marked) && ((n2 in g) && (!((n2 in marked)) && !((n2 in pending)))) ==> !((create_edge(n1, n2) in $$(g)))))) might not be preserved. Assertion (forall n: Ref :: { (n in pending) } { (n in roots) } (n in roots) == (n in pending)) && (forall n: Ref :: { (n in marked) } (n in g) ==> !((n in marked))) || (forall n: Ref :: { (n in pending) } { (n in marked) } (n in roots) ==> (n in marked) || (n in pending)) && ((forall n: Ref :: { (n in pending) } (n in g) ==> !((n in marked) && (n in pending))) && ((forall n: Ref :: { exists_spath($$(g), roots, n) } (n in pending) || (n in marked) ==> exists_spath($$(g), roots, n)) && (forall n1: Ref, n2: Ref :: { (n1 in marked), (n2 in marked) } (n1 in marked) && ((n2 in g) && (!((n2 in marked)) && !((n2 in pending)))) ==> !((create_edge(n1, n2) in $$(g)))))) might not hold. (graph_mark.vpr@217.9--223.152) [651]"}
          ((forall n_36: Ref ::
          { pending[n_36] } { roots[n_36] }
          roots[n_36] == pending[n_36]
        ) && (forall n_37: Ref ::
          { marked[n_37] }
          g[n_37] ==> !marked[n_37]
        )) || ((forall n_38: Ref ::
          { pending[n_38] } { marked[n_38] }
          roots[n_38] ==> marked[n_38] || pending[n_38]
        ) && ((forall n_39: Ref ::
          { pending[n_39] }
          g[n_39] ==> !(marked[n_39] && pending[n_39])
        ) && ((forall n_40: Ref ::
          { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, n_40): bool) }
          pending[n_40] || marked[n_40] ==> (exists_spath($$(Heap, g), roots, n_40): bool)
        ) && (forall n1_4: Ref, n2_4: Ref ::
          { marked[n1_4], marked[n2_4] }
          marked[n1_4] && (g[n2_4] && (!marked[n2_4] && !pending[n2_4])) ==> !$$(Heap, g)[(create_edge(n1_4, n2_4): EdgeDomainType)]
        ))));
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Terminate execution
        assume false;
      }

    // -- Inhale loop invariant after loop, and assume guard
      assume !(Set#Card(pending) > 0);
      assume state(Heap, Mask);
      assume !g[null];
      havoc QPMask;
      assert {:msg "  While statement might fail. Quantified resource n$10.car might not be injective. (graph_mark.vpr@205.19--205.27) [652]"}
        (forall n$10_5: Ref, n$10_5_1: Ref ::

        (((n$10_5 != n$10_5_1 && g[n$10_5]) && g[n$10_5_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$10_5 != n$10_5_1
      );

      // -- Define Inverse Function
        assume (forall n$10_5: Ref ::
          { Heap[n$10_5, car] } { QPMask[n$10_5, car] } { Heap[n$10_5, car] }
          g[n$10_5] && NoPerm < FullPerm ==> qpRange39(n$10_5) && invRecv39(n$10_5) == n$10_5
        );
        assume (forall o_3: Ref ::
          { invRecv39(o_3) }
          (g[invRecv39(o_3)] && NoPerm < FullPerm) && qpRange39(o_3) ==> invRecv39(o_3) == o_3
        );

      // -- Assume set of fields is nonNull
        assume (forall n$10_5: Ref ::
          { Heap[n$10_5, car] } { QPMask[n$10_5, car] } { Heap[n$10_5, car] }
          g[n$10_5] ==> n$10_5 != null
        );

      // -- Define permissions
        assume (forall o_3: Ref ::
          { QPMask[o_3, car] }
          ((g[invRecv39(o_3)] && NoPerm < FullPerm) && qpRange39(o_3) ==> (NoPerm < FullPerm ==> invRecv39(o_3) == o_3) && QPMask[o_3, car] == Mask[o_3, car] + FullPerm) && (!((g[invRecv39(o_3)] && NoPerm < FullPerm) && qpRange39(o_3)) ==> QPMask[o_3, car] == Mask[o_3, car])
        );
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
          f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      havoc QPMask;
      assert {:msg "  While statement might fail. Quantified resource n$11.cdr might not be injective. (graph_mark.vpr@205.19--205.27) [653]"}
        (forall n$11_5: Ref, n$11_5_1: Ref ::

        (((n$11_5 != n$11_5_1 && g[n$11_5]) && g[n$11_5_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$11_5 != n$11_5_1
      );

      // -- Define Inverse Function
        assume (forall n$11_5: Ref ::
          { Heap[n$11_5, cdr] } { QPMask[n$11_5, cdr] } { Heap[n$11_5, cdr] }
          g[n$11_5] && NoPerm < FullPerm ==> qpRange40(n$11_5) && invRecv40(n$11_5) == n$11_5
        );
        assume (forall o_3: Ref ::
          { invRecv40(o_3) }
          (g[invRecv40(o_3)] && NoPerm < FullPerm) && qpRange40(o_3) ==> invRecv40(o_3) == o_3
        );

      // -- Assume set of fields is nonNull
        assume (forall n$11_5: Ref ::
          { Heap[n$11_5, cdr] } { QPMask[n$11_5, cdr] } { Heap[n$11_5, cdr] }
          g[n$11_5] ==> n$11_5 != null
        );

      // -- Define permissions
        assume (forall o_3: Ref ::
          { QPMask[o_3, cdr] }
          ((g[invRecv40(o_3)] && NoPerm < FullPerm) && qpRange40(o_3) ==> (NoPerm < FullPerm ==> invRecv40(o_3) == o_3) && QPMask[o_3, cdr] == Mask[o_3, cdr] + FullPerm) && (!((g[invRecv40(o_3)] && NoPerm < FullPerm) && qpRange40(o_3)) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
        );
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
          f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      assume (forall n$8_7: Ref ::
        { g[Heap[n$8_7, car]] } { g[n$8_7], Heap[n$8_7, car] }
        g[n$8_7] ==> g[Heap[n$8_7, car]]
      );
      assume (forall n$9_7: Ref ::
        { g[Heap[n$9_7, cdr]] } { g[n$9_7], Heap[n$9_7, cdr] }
        g[n$9_7] ==> g[Heap[n$9_7, cdr]]
      );
      assume g[x_1];
      assume Set#Subset(pending, g);
      assume Set#Subset(marked, g);
      assume state(Heap, Mask);
      assume (exists_spath($$(Heap, g), roots, x_1): bool);
      if (Heap[x_1, cdr] != null) {
        if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, cdr]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, cdr], Heap[x_1, cdr]): bool)) {
          assume state(Heap, Mask);
          assume (exists_path($$(Heap, g), x_1, Heap[x_1, cdr]): bool);
        }
      }
      if (Heap[x_1, car] != null) {
        if ($$(Heap, g)[(create_edge(x_1, Heap[x_1, car]): EdgeDomainType)] && (exists_path($$(Heap, g), Heap[x_1, car], Heap[x_1, car]): bool)) {
          assume state(Heap, Mask);
          assume (exists_path($$(Heap, g), x_1, Heap[x_1, car]): bool);
        }
      }
      assume state(Heap, Mask);
      assume ((forall n_41: Ref ::
        { pending[n_41] } { roots[n_41] }
        roots[n_41] == pending[n_41]
      ) && (forall n_42: Ref ::
        { marked[n_42] }
        g[n_42] ==> !marked[n_42]
      )) || ((forall n_43: Ref ::
        { pending[n_43] } { marked[n_43] }
        roots[n_43] ==> marked[n_43] || pending[n_43]
      ) && ((forall n_44: Ref ::
        { pending[n_44] }
        g[n_44] ==> !(marked[n_44] && pending[n_44])
      ) && ((forall n_45: Ref ::
        { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, n_45): bool) }
        pending[n_45] || marked[n_45] ==> (exists_spath($$(Heap, g), roots, n_45): bool)
      ) && (forall n1_5: Ref, n2_5: Ref ::
        { marked[n1_5], marked[n2_5] }
        marked[n1_5] && (g[n2_5] && (!marked[n2_5] && !pending[n2_5])) ==> !$$(Heap, g)[(create_edge(n1_5, n2_5): EdgeDomainType)]
      ))));
      assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale apply_noExit($$(g), g, marked) -- graph_mark.vpr@243.12--243.42
    assume state(Heap, Mask);

    // -- Check definedness of apply_noExit($$(g), g, marked)
      if (*) {
        // Exhale precondition of function application
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver n is injective
          assert {:msg "  Precondition of function $$ might not hold. Quantified resource n.car might not be injective. (graph_mark.vpr@243.25--243.30) [654]"}
            (forall n_46: Ref, n_46_1: Ref ::
            { neverTriggered41(n_46), neverTriggered41(n_46_1) }
            (((n_46 != n_46_1 && g[n_46]) && g[n_46_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n_46 != n_46_1
          );

        // -- check if sufficient permission is held
          assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n.car (graph_mark.vpr@243.25--243.30) [655]"}
            (forall n_46: Ref ::
            { Heap[n_46, car] } { QPMask[n_46, car] } { Heap[n_46, car] }
            g[n_46] ==> Mask[n_46, car] >= FullPerm
          );

        // -- assumptions for inverse of receiver n
          assume (forall n_46: Ref ::
            { Heap[n_46, car] } { QPMask[n_46, car] } { Heap[n_46, car] }
            g[n_46] && NoPerm < FullPerm ==> qpRange41(n_46) && invRecv41(n_46) == n_46
          );
          assume (forall o_3: Ref ::
            { invRecv41(o_3) }
            g[invRecv41(o_3)] && (NoPerm < FullPerm && qpRange41(o_3)) ==> invRecv41(o_3) == o_3
          );

        // -- assume permission updates for field car
          assume (forall o_3: Ref ::
            { QPMask[o_3, car] }
            (g[invRecv41(o_3)] && (NoPerm < FullPerm && qpRange41(o_3)) ==> invRecv41(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv41(o_3)] && (NoPerm < FullPerm && qpRange41(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver n$0 is injective
          assert {:msg "  Precondition of function $$ might not hold. Quantified resource n$0.cdr might not be injective. (graph_mark.vpr@243.25--243.30) [656]"}
            (forall n$0_14: Ref, n$0_14_1: Ref ::
            { neverTriggered42(n$0_14), neverTriggered42(n$0_14_1) }
            (((n$0_14 != n$0_14_1 && g[n$0_14]) && g[n$0_14_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$0_14 != n$0_14_1
          );

        // -- check if sufficient permission is held
          assert {:msg "  Precondition of function $$ might not hold. There might be insufficient permission to access n$0.cdr (graph_mark.vpr@243.25--243.30) [657]"}
            (forall n$0_14: Ref ::
            { Heap[n$0_14, cdr] } { QPMask[n$0_14, cdr] } { Heap[n$0_14, cdr] }
            g[n$0_14] ==> Mask[n$0_14, cdr] >= FullPerm
          );

        // -- assumptions for inverse of receiver n$0
          assume (forall n$0_14: Ref ::
            { Heap[n$0_14, cdr] } { QPMask[n$0_14, cdr] } { Heap[n$0_14, cdr] }
            g[n$0_14] && NoPerm < FullPerm ==> qpRange42(n$0_14) && invRecv42(n$0_14) == n$0_14
          );
          assume (forall o_3: Ref ::
            { invRecv42(o_3) }
            g[invRecv42(o_3)] && (NoPerm < FullPerm && qpRange42(o_3)) ==> invRecv42(o_3) == o_3
          );

        // -- assume permission updates for field cdr
          assume (forall o_3: Ref ::
            { QPMask[o_3, cdr] }
            (g[invRecv42(o_3)] && (NoPerm < FullPerm && qpRange42(o_3)) ==> invRecv42(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv42(o_3)] && (NoPerm < FullPerm && qpRange42(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assume (apply_noExit($$(Heap, g), g, marked): bool);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    assert {:msg "  Postcondition of mark might not hold. Assertion (roots subset marked) might not hold. (graph_mark.vpr@193.19--193.32) [658]"}
      Set#Subset(roots, marked);
    assert {:msg "  Postcondition of mark might not hold. Assertion (marked subset g) might not hold. (graph_mark.vpr@194.20--194.28) [659]"}
      Set#Subset(marked, g);
    assert {:msg "  Postcondition of mark might not hold. Assertion !((null in g)) might not hold. (graph_mark.vpr@195.13--195.21) [660]"}
      !g[null];
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver n$6 is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource n$6.car might not be injective. (graph_mark.vpr@195.13--195.21) [661]"}
        (forall n$6_2: Ref, n$6_2_1: Ref ::
        { neverTriggered11(n$6_2), neverTriggered11(n$6_2_1) }
        (((n$6_2 != n$6_2_1 && g[n$6_2]) && g[n$6_2_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$6_2 != n$6_2_1
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of mark might not hold. There might be insufficient permission to access n$6.car (graph_mark.vpr@195.13--195.21) [662]"}
        (forall n$6_2: Ref ::
        { Heap[n$6_2, car] } { QPMask[n$6_2, car] } { Heap[n$6_2, car] }
        g[n$6_2] ==> Mask[n$6_2, car] >= FullPerm
      );

    // -- assumptions for inverse of receiver n$6
      assume (forall n$6_2: Ref ::
        { Heap[n$6_2, car] } { QPMask[n$6_2, car] } { Heap[n$6_2, car] }
        g[n$6_2] && NoPerm < FullPerm ==> qpRange11(n$6_2) && invRecv11(n$6_2) == n$6_2
      );
      assume (forall o_3: Ref ::
        { invRecv11(o_3) }
        g[invRecv11(o_3)] && (NoPerm < FullPerm && qpRange11(o_3)) ==> invRecv11(o_3) == o_3
      );

    // -- assume permission updates for field car
      assume (forall o_3: Ref ::
        { QPMask[o_3, car] }
        (g[invRecv11(o_3)] && (NoPerm < FullPerm && qpRange11(o_3)) ==> invRecv11(o_3) == o_3 && QPMask[o_3, car] == Mask[o_3, car] - FullPerm) && (!(g[invRecv11(o_3)] && (NoPerm < FullPerm && qpRange11(o_3))) ==> QPMask[o_3, car] == Mask[o_3, car])
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != car ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver n$7 is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource n$7.cdr might not be injective. (graph_mark.vpr@195.13--195.21) [663]"}
        (forall n$7_2: Ref, n$7_2_1: Ref ::
        { neverTriggered12(n$7_2), neverTriggered12(n$7_2_1) }
        (((n$7_2 != n$7_2_1 && g[n$7_2]) && g[n$7_2_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> n$7_2 != n$7_2_1
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of mark might not hold. There might be insufficient permission to access n$7.cdr (graph_mark.vpr@195.13--195.21) [664]"}
        (forall n$7_2: Ref ::
        { Heap[n$7_2, cdr] } { QPMask[n$7_2, cdr] } { Heap[n$7_2, cdr] }
        g[n$7_2] ==> Mask[n$7_2, cdr] >= FullPerm
      );

    // -- assumptions for inverse of receiver n$7
      assume (forall n$7_2: Ref ::
        { Heap[n$7_2, cdr] } { QPMask[n$7_2, cdr] } { Heap[n$7_2, cdr] }
        g[n$7_2] && NoPerm < FullPerm ==> qpRange12(n$7_2) && invRecv12(n$7_2) == n$7_2
      );
      assume (forall o_3: Ref ::
        { invRecv12(o_3) }
        g[invRecv12(o_3)] && (NoPerm < FullPerm && qpRange12(o_3)) ==> invRecv12(o_3) == o_3
      );

    // -- assume permission updates for field cdr
      assume (forall o_3: Ref ::
        { QPMask[o_3, cdr] }
        (g[invRecv12(o_3)] && (NoPerm < FullPerm && qpRange12(o_3)) ==> invRecv12(o_3) == o_3 && QPMask[o_3, cdr] == Mask[o_3, cdr] - FullPerm) && (!(g[invRecv12(o_3)] && (NoPerm < FullPerm && qpRange12(o_3))) ==> QPMask[o_3, cdr] == Mask[o_3, cdr])
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != cdr ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    if (*) {
      if (g[n$4_2]) {
        assert {:msg "  Postcondition of mark might not hold. Assertion (n$4.car in g) might not hold. (graph_mark.vpr@195.13--195.21) [665]"}
          g[Heap[n$4_2, car]];
      }
      assume false;
    }
    assume (forall n$4_3_1: Ref ::
      { g[Heap[n$4_3_1, car]] } { g[n$4_3_1], Heap[n$4_3_1, car] }
      g[n$4_3_1] ==> g[Heap[n$4_3_1, car]]
    );
    if (*) {
      if (g[n$5_2]) {
        assert {:msg "  Postcondition of mark might not hold. Assertion (n$5.cdr in g) might not hold. (graph_mark.vpr@195.13--195.21) [666]"}
          g[Heap[n$5_2, cdr]];
      }
      assume false;
    }
    assume (forall n$5_3_1: Ref ::
      { g[Heap[n$5_3_1, cdr]] } { g[n$5_3_1], Heap[n$5_3_1, cdr] }
      g[n$5_3_1] ==> g[Heap[n$5_3_1, cdr]]
    );
    if (*) {
      if (g[v_4_1]) {
        if (marked[v_4_1]) {
          assert {:msg "  Postcondition of mark might not hold. Assertion exists_spath($$(g), roots, v) might not hold. (graph_mark.vpr@196.13--196.130) [667]"}
            (exists_spath($$(Heap, g), roots, v_4_1): bool);
        }
      }
      assume false;
    }
    assume (forall v_5_1: Ref ::
      { marked[v_5_1] } { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, v_5_1): bool) }
      g[v_5_1] ==> marked[v_5_1] ==> (exists_spath($$(Heap, g), roots, v_5_1): bool)
    );
    if (*) {
      if (g[v_6]) {
        if ((exists_spath($$(Heap, g), roots, v_6): bool)) {
          assert {:msg "  Postcondition of mark might not hold. Assertion (v in marked) might not hold. (graph_mark.vpr@197.13--197.130) [668]"}
            marked[v_6];
        }
      }
      assume false;
    }
    assume (forall v_7_1: Ref ::
      { marked[v_7_1] } { (exists_spath($$#frame(CombineFrames(FrameFragment($$#condqp1(Heap, g)), FrameFragment($$#condqp2(Heap, g))), g), roots, v_7_1): bool) }
      g[v_7_1] ==> (exists_spath($$(Heap, g), roots, v_7_1): bool) ==> marked[v_7_1]
    );
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}
