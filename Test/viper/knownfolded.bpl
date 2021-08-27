// RUN: %parallel-boogie "%s" | %OutputCheck "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors

// ==================================================
// Preamble of State module.
// ==================================================

function state(Heap: HeapType, Mask: MaskType): bool;

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
function succHeap(Heap0: HeapType, Heap1: HeapType): bool;
function succHeapTrans(Heap0: HeapType, Heap1: HeapType): bool;
function IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function IsPredicateField<A, B>(f_1: (Field A B)): bool;
function IsWandField<A, B>(f_1: (Field A B)): bool;
function getPredicateId<A, B>(f_1: (Field A B)): int;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[null, pm_f], IsPredicateField(pm_f) }
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
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);
// Updated Heaps are Successor Heaps
axiom (forall <A, B> Heap: HeapType, o: Ref, f_2: (Field A B), v: B ::
  { Heap[o, f_2:=v] }
  succHeap(Heap, Heap[o, f_2:=v])
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
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == NoPerm
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function PredicateMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
function WandMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function Perm(a: real, b: real): Perm;
function GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  GoodMask(Mask) ==> Mask[o_1, f_3] >= NoPerm && ((GoodMask(Mask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> Mask[o_1, f_3] <= FullPerm)
);
function HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> Mask[o_1, f_3] > NoPerm
);
function sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
);
// ==================================================
// Function for trigger used in checks which are never triggered
// ==================================================

function neverTriggered1(y_1: Ref): bool;
function neverTriggered2(y_1: Ref): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function invRecv1(x_1_1: Ref, b_1_1: bool): Ref;
function invRecv2(x_1_1: Ref, b_1_1: bool): Ref;
// ==================================================
// Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale
// ==================================================

function qpRange1(x_1_1: Ref, b_1_1: bool): bool;
function qpRange2(x_1_1: Ref, b_1_1: bool): bool;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function FrameFragment<T>(t: T): FrameType;
function ConditionalFrame(p: Perm, f_5: FrameType): FrameType;
function dummyFunction<T>(t: T): bool;
function CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p: Perm, f_5: FrameType ::
  { ConditionalFrame(p, f_5) }
  ConditionalFrame(p, f_5) == (if p > 0.000000000 then f_5 else EmptyFrame)
);
// Function for recording enclosure of one predicate instance in another
function InsidePredicate<A, B>(p: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType): bool;
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
// Translation of all fields
// ==================================================

const unique f_6: Field NormalField int;
axiom !IsPredicateField(f_6);
axiom !IsWandField(f_6);
const unique g: Field NormalField bool;
axiom !IsPredicateField(g);
axiom !IsWandField(g);

// ==================================================
// Translation of predicate P
// ==================================================

type PredicateType_P;
function P(x: Ref, b_2: bool): Field PredicateType_P FrameType;
function P#sm(x: Ref, b_2: bool): Field PredicateType_P PMaskType;
axiom (forall x: Ref, b_2: bool ::
  { PredicateMaskField(P(x, b_2)) }
  PredicateMaskField(P(x, b_2)) == P#sm(x, b_2)
);
axiom (forall x: Ref, b_2: bool ::
  { P(x, b_2) }
  IsPredicateField(P(x, b_2))
);
axiom (forall x: Ref, b_2: bool ::
  { P(x, b_2) }
  getPredicateId(P(x, b_2)) == 0
);
function P#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function P#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall x: Ref, b_2: bool, x2: Ref, b2: bool ::
  { P(x, b_2), P(x2, b2) }
  P(x, b_2) == P(x2, b2) ==> x == x2 && b_2 == b2
);
axiom (forall x: Ref, b_2: bool, x2: Ref, b2: bool ::
  { P#sm(x, b_2), P#sm(x2, b2) }
  P#sm(x, b_2) == P#sm(x2, b2) ==> x == x2 && b_2 == b2
);

axiom (forall Heap: HeapType, x: Ref, b_2: bool ::
  { P#trigger(Heap, P(x, b_2)) }
  P#everUsed(P(x, b_2))
);

// ==================================================
// Translation of method known_folded_1
// ==================================================

procedure known_folded_1(x: Ref, xs: (Set Ref), b_2: bool) returns ()
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var perm: Perm;
  var newVersion: FrameType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume Heap[x, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Check definedness of (forall y: Ref :: { (y in xs) } (y in xs) ==> acc(P(y, b), write))
      if (*) {
        assume false;
      }
      assume state(Heap, Mask);
    havoc QPMask;
    
    // -- Define Inverse Function
      assume (forall y_1: Ref ::
        { Heap[null, P(y_1, b_2)] } { Mask[null, P(y_1, b_2)] } { xs[y_1] }
        xs[y_1] && NoPerm < FullPerm ==> invRecv1(y_1, b_2) == y_1 && qpRange1(y_1, b_2)
      );
      assume (forall x_1_1: Ref, b_1_1: bool ::
        { invRecv1(x_1_1, b_1_1) }
        (xs[invRecv1(x_1_1, b_1_1)] && NoPerm < FullPerm) && qpRange1(x_1_1, b_1_1) ==> invRecv1(x_1_1, b_1_1) == x_1_1 && b_2 == b_1_1
      );
    
    // -- Define updated permissions
      assume (forall x_1_1: Ref, b_1_1: bool ::
        { QPMask[null, P(x_1_1, b_1_1)] }
        (xs[invRecv1(x_1_1, b_1_1)] && NoPerm < FullPerm) && qpRange1(x_1_1, b_1_1) ==> (NoPerm < FullPerm ==> invRecv1(x_1_1, b_1_1) == x_1_1 && b_2 == b_1_1) && QPMask[null, P(x_1_1, b_1_1)] == Mask[null, P(x_1_1, b_1_1)] + FullPerm
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 0 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall x_1_1: Ref, b_1_1: bool ::
        { QPMask[null, P(x_1_1, b_1_1)] }
        !((xs[invRecv1(x_1_1, b_1_1)] && NoPerm < FullPerm) && qpRange1(x_1_1, b_1_1)) ==> QPMask[null, P(x_1_1, b_1_1)] == Mask[null, P(x_1_1, b_1_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume xs[x];
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
    if (b_2) {
      perm := FullPerm;
      assume x != null;
      PostMask[x, f_6] := PostMask[x, f_6] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of x.f == 0
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.f. (knownfolded.vpr@14.11) [55]"}
          HasDirectPerm(PostMask, x, f_6);
        assume state(PostHeap, PostMask);
      assume PostHeap[x, f_6] == 0;
      assume state(PostHeap, PostMask);
    } else {
      perm := FullPerm;
      assume x != null;
      PostMask[x, g] := PostMask[x, g] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of x.g
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.g. (knownfolded.vpr@14.11) [56]"}
          HasDirectPerm(PostMask, x, g);
        assume state(PostHeap, PostMask);
      assume PostHeap[x, g];
      assume state(PostHeap, PostMask);
    }
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: unfold acc(P(x, b), write) -- knownfolded.vpr@16.3
    assume P#trigger(Heap, P(x, b_2));
    assume Heap[null, P(x, b_2)] == FrameFragment((if b_2 then FrameFragment(Heap[x, f_6]) else FrameFragment(Heap[x, g])));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(x, b) might fail. There might be insufficient permission to access P(x, b). (knownfolded.vpr@16.3) [58]"}
        perm <= Mask[null, P(x, b_2)];
    }
    Mask[null, P(x, b_2)] := Mask[null, P(x, b_2)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(x, b_2))) {
        havoc newVersion;
        Heap[null, P(x, b_2)] := newVersion;
      }
    if (b_2) {
      perm := FullPerm;
      assume x != null;
      Mask[x, f_6] := Mask[x, f_6] + perm;
      assume state(Heap, Mask);
    } else {
      perm := FullPerm;
      assume x != null;
      Mask[x, g] := Mask[x, g] + perm;
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: if (b) -- knownfolded.vpr@18.3
    if (b_2) {
      
      // -- Translating statement: x.f := 0 -- knownfolded.vpr@19.5
        assert {:msg "  Assignment might fail. There might be insufficient permission to access x.f. (knownfolded.vpr@19.5) [59]"}
          FullPerm == Mask[x, f_6];
        Heap[x, f_6] := 0;
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: x.g := true -- knownfolded.vpr@21.5
        assert {:msg "  Assignment might fail. There might be insufficient permission to access x.g. (knownfolded.vpr@21.5) [60]"}
          FullPerm == Mask[x, g];
        Heap[x, g] := true;
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    // Phase 1: pure assertions and fixed permissions
    if (b_2) {
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of test1 might not hold. There might be insufficient permission to access x.f. (knownfolded.vpr@14.11) [61]"}
          perm <= Mask[x, f_6];
      }
      Mask[x, f_6] := Mask[x, f_6] - perm;
      assert {:msg "  Postcondition of test1 might not hold. Assertion x.f == 0 might not hold. (knownfolded.vpr@14.11) [62]"}
        Heap[x, f_6] == 0;
    } else {
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of test1 might not hold. There might be insufficient permission to access x.g. (knownfolded.vpr@14.11) [63]"}
          perm <= Mask[x, g];
      }
      Mask[x, g] := Mask[x, g] - perm;
      assert {:msg "  Postcondition of test1 might not hold. Assertion x.g might not hold. (knownfolded.vpr@14.11) [64]"}
        Heap[x, g];
    }
    // Phase 2: abstract read permissions (and scaled abstract read permissions)
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method known_folded_2
// ==================================================

procedure known_folded_2(x: Ref, xs: (Set Ref), b_2: bool) returns ()
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var newVersion: FrameType;
  var freshVersion: FrameType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume Heap[x, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Check definedness of (forall y: Ref :: { (y in xs) } (y in xs) ==> acc(P(y, b), write))
      if (*) {
        assume false;
      }
      assume state(Heap, Mask);
    havoc QPMask;
    
    // -- Define Inverse Function
      assume (forall y_1: Ref ::
        { Heap[null, P(y_1, b_2)] } { Mask[null, P(y_1, b_2)] } { xs[y_1] }
        xs[y_1] && NoPerm < FullPerm ==> invRecv2(y_1, b_2) == y_1 && qpRange2(y_1, b_2)
      );
      assume (forall x_1_1: Ref, b_1_1: bool ::
        { invRecv2(x_1_1, b_1_1) }
        (xs[invRecv2(x_1_1, b_1_1)] && NoPerm < FullPerm) && qpRange2(x_1_1, b_1_1) ==> invRecv2(x_1_1, b_1_1) == x_1_1 && b_2 == b_1_1
      );
    
    // -- Define updated permissions
      assume (forall x_1_1: Ref, b_1_1: bool ::
        { QPMask[null, P(x_1_1, b_1_1)] }
        (xs[invRecv2(x_1_1, b_1_1)] && NoPerm < FullPerm) && qpRange2(x_1_1, b_1_1) ==> (NoPerm < FullPerm ==> invRecv2(x_1_1, b_1_1) == x_1_1 && b_2 == b_1_1) && QPMask[null, P(x_1_1, b_1_1)] == Mask[null, P(x_1_1, b_1_1)] + FullPerm
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 0 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall x_1_1: Ref, b_1_1: bool ::
        { QPMask[null, P(x_1_1, b_1_1)] }
        !((xs[invRecv2(x_1_1, b_1_1)] && NoPerm < FullPerm) && qpRange2(x_1_1, b_1_1)) ==> QPMask[null, P(x_1_1, b_1_1)] == Mask[null, P(x_1_1, b_1_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume xs[x];
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
    perm := FullPerm;
    PostMask[null, P(x, b_2)] := PostMask[null, P(x, b_2)] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (unfolding acc(P(x, b), write) in (b ? x.f == 0 : x.g))
      UnfoldingHeap := PostHeap;
      UnfoldingMask := PostMask;
      assume P#trigger(UnfoldingHeap, P(x, b_2));
      assume UnfoldingHeap[null, P(x, b_2)] == FrameFragment((if b_2 then FrameFragment(UnfoldingHeap[x, f_6]) else FrameFragment(UnfoldingHeap[x, g])));
      // Phase 1: pure assertions and fixed permissions
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access P(x, b). (knownfolded.vpr@31.11) [65]"}
          perm <= UnfoldingMask[null, P(x, b_2)];
      }
      UnfoldingMask[null, P(x, b_2)] := UnfoldingMask[null, P(x, b_2)] - perm;
      if (b_2) {
        perm := FullPerm;
        assume x != null;
        UnfoldingMask[x, f_6] := UnfoldingMask[x, f_6] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
      } else {
        perm := FullPerm;
        assume x != null;
        UnfoldingMask[x, g] := UnfoldingMask[x, g] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
      }
      assume state(UnfoldingHeap, UnfoldingMask);
      if (b_2) {
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.f. (knownfolded.vpr@31.11) [66]"}
          HasDirectPerm(UnfoldingMask, x, f_6);
      } else {
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.g. (knownfolded.vpr@31.11) [67]"}
          HasDirectPerm(UnfoldingMask, x, g);
      }
      
      // -- Free assumptions
        if (b_2) {
          PostHeap[null, P#sm(x, b_2)][x, f_6] := true;
        } else {
          PostHeap[null, P#sm(x, b_2)][x, g] := true;
        }
        assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
    if (b_2) {
      PostHeap[null, P#sm(x, b_2)][x, f_6] := true;
    } else {
      PostHeap[null, P#sm(x, b_2)][x, g] := true;
    }
    
    // -- Execute unfolding (for extra information)
      UnfoldingHeap := PostHeap;
      UnfoldingMask := PostMask;
      assume P#trigger(UnfoldingHeap, P(x, b_2));
      assume UnfoldingHeap[null, P(x, b_2)] == FrameFragment((if b_2 then FrameFragment(UnfoldingHeap[x, f_6]) else FrameFragment(UnfoldingHeap[x, g])));
      // Phase 1: pure assertions and fixed permissions
      perm := NoPerm;
      perm := perm + FullPerm;
      UnfoldingMask[null, P(x, b_2)] := UnfoldingMask[null, P(x, b_2)] - perm;
      if (b_2) {
        perm := FullPerm;
        assume x != null;
        UnfoldingMask[x, f_6] := UnfoldingMask[x, f_6] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
      } else {
        perm := FullPerm;
        assume x != null;
        UnfoldingMask[x, g] := UnfoldingMask[x, g] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
      }
      assume state(UnfoldingHeap, UnfoldingMask);
    assume (if b_2 then PostHeap[x, f_6] == 0 else PostHeap[x, g]);
    
    // -- Free assumptions
      if (b_2) {
        PostHeap[null, P#sm(x, b_2)][x, f_6] := true;
      } else {
        PostHeap[null, P#sm(x, b_2)][x, g] := true;
      }
      assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: unfold acc(P(x, b), write) -- knownfolded.vpr@33.3
    assume P#trigger(Heap, P(x, b_2));
    assume Heap[null, P(x, b_2)] == FrameFragment((if b_2 then FrameFragment(Heap[x, f_6]) else FrameFragment(Heap[x, g])));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(x, b) might fail. There might be insufficient permission to access P(x, b). (knownfolded.vpr@33.3) [69]"}
        perm <= Mask[null, P(x, b_2)];
    }
    Mask[null, P(x, b_2)] := Mask[null, P(x, b_2)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(x, b_2))) {
        havoc newVersion;
        Heap[null, P(x, b_2)] := newVersion;
      }
    if (b_2) {
      perm := FullPerm;
      assume x != null;
      Mask[x, f_6] := Mask[x, f_6] + perm;
      assume state(Heap, Mask);
    } else {
      perm := FullPerm;
      assume x != null;
      Mask[x, g] := Mask[x, g] + perm;
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: if (b) -- knownfolded.vpr@35.3
    if (b_2) {
      
      // -- Translating statement: x.f := 0 -- knownfolded.vpr@36.5
        assert {:msg "  Assignment might fail. There might be insufficient permission to access x.f. (knownfolded.vpr@36.5) [70]"}
          FullPerm == Mask[x, f_6];
        Heap[x, f_6] := 0;
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: x.g := true -- knownfolded.vpr@38.5
        assert {:msg "  Assignment might fail. There might be insufficient permission to access x.g. (knownfolded.vpr@38.5) [71]"}
          FullPerm == Mask[x, g];
        Heap[x, g] := true;
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(P(x, b), write) -- knownfolded.vpr@40.3
    // Phase 1: pure assertions and fixed permissions
    if (b_2) {
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding P(x, b) might fail. There might be insufficient permission to access x.f. (knownfolded.vpr@40.3) [73]"}
          perm <= Mask[x, f_6];
      }
      Mask[x, f_6] := Mask[x, f_6] - perm;
    } else {
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding P(x, b) might fail. There might be insufficient permission to access x.g. (knownfolded.vpr@40.3) [75]"}
          perm <= Mask[x, g];
      }
      Mask[x, g] := Mask[x, g] - perm;
    }
    // Phase 2: abstract read permissions (and scaled abstract read permissions)
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := FullPerm;
    Mask[null, P(x, b_2)] := Mask[null, P(x, b_2)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume P#trigger(Heap, P(x, b_2));
    assume Heap[null, P(x, b_2)] == FrameFragment((if b_2 then FrameFragment(Heap[x, f_6]) else FrameFragment(Heap[x, g])));
    if (!HasDirectPerm(Mask, null, P(x, b_2))) {
      Heap[null, P#sm(x, b_2)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, P(x, b_2)] := freshVersion;
    }
    if (b_2) {
      Heap[null, P#sm(x, b_2)][x, f_6] := true;
    } else {
      Heap[null, P#sm(x, b_2)][x, g] := true;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of test2 might not hold. There might be insufficient permission to access P(x, b). (knownfolded.vpr@30.11) [76]"}
        perm <= Mask[null, P(x, b_2)];
    }
    Mask[null, P(x, b_2)] := Mask[null, P(x, b_2)] - perm;
    
    // -- Execute unfolding (for extra information)
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume P#trigger(UnfoldingHeap, P(x, b_2));
      assume UnfoldingHeap[null, P(x, b_2)] == FrameFragment((if b_2 then FrameFragment(UnfoldingHeap[x, f_6]) else FrameFragment(UnfoldingHeap[x, g])));
      if (b_2) {
        perm := FullPerm;
        assume x != null;
        UnfoldingMask[x, f_6] := UnfoldingMask[x, f_6] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
      } else {
        perm := FullPerm;
        assume x != null;
        UnfoldingMask[x, g] := UnfoldingMask[x, g] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
      }
      assume state(UnfoldingHeap, UnfoldingMask);
    if (b_2) {
      assert {:msg "  Postcondition of test2 might not hold. Assertion x.f == 0 might not hold. (knownfolded.vpr@31.11) [77]"}
        UnfoldingHeap[x, f_6] == 0;
    } else {
      assert {:msg "  Postcondition of test2 might not hold. Assertion x.g might not hold. (knownfolded.vpr@31.11) [78]"}
        UnfoldingHeap[x, g];
    }
    
    // -- Free assumptions
      if (b_2) {
        Heap[null, P#sm(x, b_2)][x, f_6] := true;
      } else {
        Heap[null, P#sm(x, b_2)][x, g] := true;
      }
      assume state(Heap, Mask);
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}