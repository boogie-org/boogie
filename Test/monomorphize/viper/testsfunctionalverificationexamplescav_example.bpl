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
function  IdenticalOnKnownLocationsLiberal(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function  IsPredicateField<A, B>(f_1: (Field A B)): bool;
function  IsWandField<A, B>(f_1: (Field A B)): bool;
function  getPredicateId<A, B>(f_1: (Field A B)): int;
function  SumHeap(Heap: HeapType, Heap1: HeapType, mask1: MaskType, Heap2: HeapType, mask2: MaskType): bool;
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
// IdenticalOnKnownLiberalLocations Heaps are Successor Heaps
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> succHeap(Heap, ExhaleHeap)
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
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o_2: Ref, f_4: (Field A B) ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask), ExhaleHeap[o_2, f_4] }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o_2, f_4) ==> Heap[o_2, f_4] == ExhaleHeap[o_2, f_4]
);
// Frame all predicate mask locations of predicates with direct permission. But don't propagate information  of locations that are not known-folded to allow for equating with multiple different (but compatible) heaps
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f_1: (Field C FrameType) ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f_1), ExhaleHeap[null, PredicateMaskField(pm_f_1)] }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f_1) && IsPredicateField(pm_f_1) ==> (forall <A, B> o2_1: Ref, f_4: (Field A B) ::
    { ExhaleHeap[null, PredicateMaskField(pm_f_1)][o2_1, f_4] }
    Heap[null, PredicateMaskField(pm_f_1)][o2_1, f_4] ==> ExhaleHeap[null, PredicateMaskField(pm_f_1)][o2_1, f_4]
  )
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f_1: (Field C FrameType) ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f_1) }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f_1) && IsPredicateField(pm_f_1) ==> (forall <A, B> o2_1: Ref, f_4: (Field A B) ::
    { ExhaleHeap[o2_1, f_4] }
    Heap[null, PredicateMaskField(pm_f_1)][o2_1, f_4] ==> Heap[o2_1, f_4] == ExhaleHeap[o2_1, f_4]
  )
);
// Frame all wand mask locations of wands with direct permission (but don't propagate information about locations that are not known-folded)
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f_1: (Field C FrameType) ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask), IsWandField(pm_f_1), ExhaleHeap[null, WandMaskField(pm_f_1)] }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f_1) && IsWandField(pm_f_1) ==> (forall <A, B> o2_1: Ref, f_4: (Field A B) ::
    { ExhaleHeap[null, WandMaskField(pm_f_1)][o2_1, f_4] }
    Heap[null, WandMaskField(pm_f_1)][o2_1, f_4] ==> ExhaleHeap[null, WandMaskField(pm_f_1)][o2_1, f_4]
  )
);
// Frame all locations in the footprint of magic wands
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f_1: (Field C FrameType) ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask), IsWandField(pm_f_1) }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f_1) && IsWandField(pm_f_1) ==> (forall <A, B> o2_1: Ref, f_4: (Field A B) ::
    { ExhaleHeap[o2_1, f_4] }
    Heap[null, WandMaskField(pm_f_1)][o2_1, f_4] ==> Heap[o2_1, f_4] == ExhaleHeap[o2_1, f_4]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o_2: Ref ::
  { IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask), ExhaleHeap[o_2, $allocated] }
  IdenticalOnKnownLocationsLiberal(Heap, ExhaleHeap, Mask) ==> Heap[o_2, $allocated] ==> ExhaleHeap[o_2, $allocated]
);
// ==================================================
// Sum of heaps
// ==================================================

axiom (forall Heap: HeapType, Heap1: HeapType, Mask1: MaskType, Heap2: HeapType, Mask2: MaskType ::
  { SumHeap(Heap, Heap1, Mask1, Heap2, Mask2) }
  SumHeap(Heap, Heap1, Mask1, Heap2, Mask2) <==> IdenticalOnKnownLocationsLiberal(Heap1, Heap, Mask1) && IdenticalOnKnownLocationsLiberal(Heap2, Heap, Mask2)
);

// ==================================================
// Preamble of Permission module.
// ==================================================

type Perm = real;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_3: Ref, f_5: (Field A B) ::
  { ZeroMask[o_3, f_5] }
  ZeroMask[o_3, f_5] == NoPerm
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_3: Ref, f_5: (Field A B) ::
  { ZeroPMask[o_3, f_5] }
  !ZeroPMask[o_3, f_5]
);
function  PredicateMaskField<A>(f_6: (Field A FrameType)): Field A PMaskType;
function  WandMaskField<A>(f_6: (Field A FrameType)): Field A PMaskType;
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
axiom (forall <A, B> Mask: MaskType, o_3: Ref, f_5: (Field A B) ::
  { GoodMask(Mask), Mask[o_3, f_5] }
  GoodMask(Mask) ==> Mask[o_3, f_5] >= NoPerm && ((GoodMask(Mask) && !IsPredicateField(f_5)) && !IsWandField(f_5) ==> Mask[o_3, f_5] <= FullPerm)
);
function  HasDirectPerm<A, B>(Mask: MaskType, o_3: Ref, f_5: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_3: Ref, f_5: (Field A B) ::
  { HasDirectPerm(Mask, o_3, f_5) }
  HasDirectPerm(Mask, o_3, f_5) <==> Mask[o_3, f_5] > NoPerm
);
function  sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_3: Ref, f_5: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_3, f_5] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_3, f_5] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_3, f_5] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_3, f_5] == SummandMask1[o_3, f_5] + SummandMask2[o_3, f_5]
);
// ==================================================
// Function for trigger used in checks which are never triggered
// ==================================================

function  neverTriggered1(lambda46_30$t: Ref): bool;
function  neverTriggered2(lambda46_30$t_1: Ref): bool;
function  neverTriggered3(lambda46_30$t_5: Ref): bool;
function  neverTriggered4(lambda46_30$t_8: Ref): bool;
function  neverTriggered5(lambda46_30$t_11: Ref): bool;
function  neverTriggered6(lambda46_30$t_13: Ref): bool;
function  neverTriggered7(lambda46_30$t_15: Ref): bool;
function  neverTriggered8(lambda46_30$t_16: Ref): bool;
function  neverTriggered9(lambda46_30$t_19: Ref): bool;
function  neverTriggered10(lambda46_30$t_21: Ref): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function  invRecv1(self_1: Ref): Ref;
function  invRecv2(recv: Ref): Ref;
function  invRecv3(self_1_1: Ref): Ref;
function  invRecv4(recv: Ref): Ref;
function  invRecv5(self_1_2: Ref): Ref;
function  invRecv6(recv: Ref): Ref;
function  invRecv7(self_1_3: Ref): Ref;
function  invRecv8(recv: Ref): Ref;
function  invRecv9(self_1_4: Ref): Ref;
function  invRecv10(recv: Ref): Ref;
// ==================================================
// Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale
// ==================================================

function  qpRange1(self_1: Ref): bool;
function  qpRange2(recv: Ref): bool;
function  qpRange3(self_1_1: Ref): bool;
function  qpRange4(recv: Ref): bool;
function  qpRange5(self_1_2: Ref): bool;
function  qpRange6(recv: Ref): bool;
function  qpRange7(self_1_3: Ref): bool;
function  qpRange8(recv: Ref): bool;
function  qpRange9(self_1_4: Ref): bool;
function  qpRange10(recv: Ref): bool;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 22: tuple___val__
// - height 21: tuple___len__
// - height 20: str___val__
// - height 19: str___len__
// - height 18: _isDefined
// - height 17: PSeq___sil_seq__
// - height 16: tuple___getitem__
// - height 15: __prim__bool___box__, bool___unbox__, __prim__int___box__, int___unbox__
// - height 14: Level
// - height 13: str___create__
// - height 12: list___len__
// - height 11: list___sil_seq__
// - height 10: __file__
// - height 9: _checkDefined
// - height 8: PSeq___create__
// - height 7: tuple___create2__
// - height 6: Measure$check
// - height 5: str___eq__
// - height 4: int___gt__
// - height 3: int___sub__
// - height 2: PSeq___len__
// - height 1: int___eq__
// - height 0: __name__
const AssumeFunctionsAbove: int;
// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function  FrameFragment<T>(t: T): FrameType;
function  ConditionalFrame(p: Perm, f_7: FrameType): FrameType;
function  dummyFunction<T>(t: T): bool;
function  CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p: Perm, f_7: FrameType ::
  { ConditionalFrame(p, f_7) }
  ConditionalFrame(p, f_7) == (if p > 0.000000000 then f_7 else EmptyFrame)
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
// Preamble of Sequence module.
// ==================================================

 // diff 0 implemented (no difference)
 // diff 1 implemented (fixes test5 in sequences.sil)
 // diff 2 implemented (fixes m01 and m03 in quantifiedpermissions/issues/issue_0064)
 // diff 3 implemented (no difference)
 // diff 4 implemented (no difference)
 // diff 5 implemented (fixes colourings0 in sequence-incompletenesses test case)
 // diff 6 implemented (no difference)
 // diff 7 implemented
 // diff 8 implemented (allows for contains triggering, without destroying performance of e.g. functions/linkedlists test case)
 // diff 11 implemented
 // diff 13 implemented, for now (may reduce completeness, but there's a known matching loop when the first drop amount is 0); another option would be to add !=0 as an explicit condition
 // diff 14 implemented: eliminate index over take/drop for trivial cases (to avoid matching loops when e.g. s[i..] == s is known)
 // diff 16 implemented: remove general cases of equality-learning between take/drop/append subsequences; only allow when take/drop are at top level (this affects linkedlists test case)
// START BASICS
type Seq T;

function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T): Seq T;
//axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);// (diff 2 (old))
axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Length(Seq#Singleton(t)) == 1);// (diff 2: changed trigger)

function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
s0 != Seq#Empty() && s1 != Seq#Empty() ==> //diff 11: consider removing constraints
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

//axiom (forall<T> s: Seq T :: { Seq#Append(Seq#Empty(),s) } Seq#Append(Seq#Empty(),s) == s); // (diff 11: switched to double-quantified version)
//axiom (forall<T> s: Seq T :: { Seq#Append(s,Seq#Empty()) } Seq#Append(s,Seq#Empty()) == s); // (diff 11: switched to double-quantified version)
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Append(s0,s1) } (s0 == Seq#Empty() ==> Seq#Append(s0,s1) == s1) && (s1 == Seq#Empty() ==> Seq#Append(s0,s1) == s0)); // diff 11: switched to double-quantified version

function Seq#Index<T>(Seq T, int): T;
//axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t); // (diff 2 (old))
axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Index(Seq#Singleton(t), 0) == t); // (diff 2: changed trigger)

// END BASICS

// START INDEX-APPEND-UPDATE

// extra addition function used to force equalities into the e-graph
function Seq#Add(int, int) : int;
axiom (forall i: int, j: int :: {Seq#Add(i,j)} Seq#Add(i,j) == i + j);
function Seq#Sub(int, int) : int;
axiom (forall i: int, j: int :: {Seq#Sub(i,j)} Seq#Sub(i,j) == i - j);

// (diff 3 (old))
//axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // {:weight 25} // AS: dropped weight
//  s0 != Seq#Empty() && s1 != Seq#Empty() ==>
//  ((n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
//  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0)))));

// (diff 3: split axiom, added constraints, replace arithmetic) // diff 11: consider removing constraints
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } { Seq#Index(s0, n), Seq#Append(s0,s1) } // AS: added alternative trigger
  (s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= n && n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)));
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // term below breaks loops
  s0 != Seq#Empty() && s1 != Seq#Empty() && Seq#Length(s0) <= n && n < Seq#Length(Seq#Append(s0,s1)) ==> Seq#Add(Seq#Sub(n,Seq#Length(s0)),Seq#Length(s0)) == n && Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, Seq#Sub(n,Seq#Length(s0))));
// AS: added "reverse triggering" versions of the axioms
axiom (forall<T> s0: Seq T, s1: Seq T, m: int :: { Seq#Index(s1, m), Seq#Append(s0,s1)}  // m == n-|s0|, n == m + |s0|
  s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= m && m < Seq#Length(s1) ==> Seq#Sub(Seq#Add(m,Seq#Length(s0)),Seq#Length(s0)) == m && Seq#Index(Seq#Append(s0,s1), Seq#Add(m,Seq#Length(s0))) == Seq#Index(s1, m));

function Seq#Update<T>(Seq T, int, T): Seq T;
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) } {Seq#Length(s),Seq#Update(s,i,v)} // (diff 4: added trigger)
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) } { Seq#Index(s,n), Seq#Update(s,i,v) }  // (diff 4: added trigger)
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

// END INDEX-APPEND-UPDATE

// START TAKE/DROP

function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
// AS: added triggers
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) } { Seq#Take(s,n), Seq#Length(s)} // (diff 7: add trigger)
  (0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)))
    &&
   (n < 0 ==> Seq#Length(Seq#Take(s,n)) == 0)); // (diff 7: added case for n < 0)

// ** AS: 2nd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {Seq#Index(s,j), Seq#Take(s,n)} // (diff 0: (was already done)) : add trigger // {:weight 25} // AS: dropped weight
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) } {Seq#Length(s), Seq#Drop(s,n)} // (diff 5: added trigger, exchange arithmetic)
  (0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0))
    &&
  (n < 0 ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s)) // (diff 7: added cases for n < 0)
    );

// ** AS: 3rd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
// diff 5 (old)
//axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
//  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
//    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
//
// diff already added // diff -1: try removing this axiom and checking effect
//axiom (forall<T> s: Seq T, n: int, k: int :: { Seq#Drop(s,n), Seq#Index(s,k) } // AS: alternative triggering for above axiom
//  0 <= n && n <= k && k < Seq#Length(s) ==>
//    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

// diff 5: split axiom, added triggering case, exhanged arithmetic

axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
  0 < n && 0 <= j && j < Seq#Length(s)-n ==> // diff 14: change 0 <= n to 0 < n
   Seq#Sub(Seq#Add(j,n),n) == j && Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, Seq#Add(j,n)));

axiom (forall<T> s: Seq T, n: int, i: int :: { Seq#Drop(s,n), Seq#Index(s,i) }
  0 < n && n <= i && i < Seq#Length(s) ==> // diff 14: change 0 <= n to 0 < n
  Seq#Add(Seq#Sub(i,n),n) == i && Seq#Index(Seq#Drop(s,n), Seq#Sub(i,n)) == Seq#Index(s, i)); // i = j + n, j = i - n

// (diff 6a: add axioms for the 0 > n case)
//axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
//  n <= 0 && 0 <= j && j < Seq#Length(s) ==> // diff 14: change n < 0 to n <= 0
//    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j));

// (diff 6a: add axioms for the 0 > n case)
//axiom (forall<T> s: Seq T, n: int, i: int :: { Seq#Drop(s,n), Seq#Index(s,i) }
//  n <= 0 && 0 <= i && i < Seq#Length(s) ==> // diff 14: change n < 0 to n <= 0
//  Seq#Index(Seq#Drop(s,n), i) == Seq#Index(s, i)); // i = j + n, j = i - n

// ** AS: We dropped the weak trigger on this axiom. One option is to strengthen the triggers:
//axiom (forall<T> s, t: Seq T ::
// // { Seq#Append(s, t) }
//  {Seq#Take(Seq#Append(s, t), Seq#Length(s))}{Seq#Drop(Seq#Append(s, t), Seq#Length(s))}
//  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
//  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

// ** AS: another option is to split the axiom (for some reason, this seems in some cases to perform slightly less well (but this could be random):
//axiom (forall<T> s, t: Seq T ::
// { Seq#Take(Seq#Append(s, t), Seq#Length(s)) }
//  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s);

//axiom (forall<T> s, t: Seq T ::
// { Seq#Drop(Seq#Append(s, t), Seq#Length(s)) }
//  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

// (diff 6b: remove these?)
/* Removed: at present, Carbon doesn't generate Seq#Update (but desugars via take/drop/append)
// Commutability of Take and Drop with Update.
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
//        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
        0 <= i && i < n && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
//        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
        0 <= i && n <=i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
//        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
        0 <= i && i < n && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
*/

axiom (forall<T> s: Seq T, t: Seq T, n:int ::
  { Seq#Take(Seq#Append(s,t),n) } //{Seq#Append(s,t), Seq#Take(s,n)} // diff 16: temporarily dropped general case of these
  0 < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Append(s,t),n) == Seq#Take(s,n));

axiom (forall<T> s: Seq T, t: Seq T, n:int ::
  { Seq#Take(Seq#Append(s,t),n) }
  n > 0 && n > Seq#Length(s) ==> Seq#Add(Seq#Sub(n,Seq#Length(s)),Seq#Length(s)) == n && Seq#Take(Seq#Append(s,t),n) == Seq#Append(s,Seq#Take(t,Seq#Sub(n,Seq#Length(s)))));

// diff 16: temporarily dropped general case of these
//axiom (forall<T> s: Seq T, t: Seq T, m:int ::
//  { Seq#Append(s,Seq#Take(t,m)) } //{Seq#Append(s,t), Seq#Take(t,m)} // diff 16: temporarily dropped general case of these // reverse triggering version of above: m = n - |s|, n = m + |s|
//  m > 0 ==> Seq#Sub(Seq#Add(m,Seq#Length(s)),Seq#Length(s)) == m && Seq#Take(Seq#Append(s,t),Seq#Add(m,Seq#Length(s))) == Seq#Append(s,Seq#Take(t,m)));

axiom (forall<T> s: Seq T, t: Seq T, n:int ::
  { Seq#Drop(Seq#Append(s,t),n) } //{Seq#Append(s,t), Seq#Drop(s,n)} // diff 16: temporarily dropped general case of these
  0<n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Append(s,t),n) == Seq#Append(Seq#Drop(s,n),t));

axiom (forall<T> s: Seq T, t: Seq T, n:int ::
  { Seq#Drop(Seq#Append(s,t),n) }
 n > 0 && n > Seq#Length(s) ==> Seq#Add(Seq#Sub(n,Seq#Length(s)),Seq#Length(s)) == n && Seq#Drop(Seq#Append(s,t),n) == Seq#Drop(t,Seq#Sub(n,Seq#Length(s))));

// diff 16: temporarily dropped general case of these
//axiom (forall<T> s: Seq T, t: Seq T, m:int ::
//  { Seq#Append(s,t),Seq#Drop(t,m) } // reverse triggering version of above: m = n - |s|, n = m + |s|
//  m > 0 ==> Seq#Sub(Seq#Add(m,Seq#Length(s)),Seq#Length(s)) == m && Seq#Drop(Seq#Append(s,t),Seq#Add(m,Seq#Length(s))) == Seq#Drop(t,m));

// Additional axioms about common things
axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) } // ** NEW
        n <= 0 ==> Seq#Drop(s, n) == s); // (diff 1: try changing n==0 to n<=0 (should be ok))
axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) } // ** NEW
        n <= 0 ==> Seq#Take(s, n) == Seq#Empty());  // (diff 1: try changing n==0 to n<=0 (should be ok))
// diff 13: remove this?
//axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) } // ** NEW - AS: could have bad triggering behaviour?
//        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
//        Seq#Sub(Seq#Add(m,n),n) == m && Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, Seq#Add(m,n)));

// END TAKE/DROP

// START CONTAINS
// diff 8: skolemisation (old)
function Seq#Contains<T>(Seq T, T): bool;
function Seq#ContainsTrigger<T>(Seq T, T): bool; // usages of Contains inside quantifier triggers are replaced with this
function Seq#Skolem<T>(Seq T, T) : int; // skolem function for Seq#Contains // (diff 8: added)
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) ==>
    (0 <= Seq#Skolem(s,x) && Seq#Skolem(s,x) < Seq#Length(s) && Seq#Index(s,Seq#Skolem(s,x)) == x)); // (diff 8: skolem function)
axiom (forall<T> s: Seq T, x: T, i:int :: { Seq#Contains(s,x), Seq#Index(s,i) } // only trigger if interested in the Contains term
    (0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x ==> Seq#Contains(s,x)));
axiom (forall<T> s: Seq T, i:int :: { Seq#Index(s,i) }
  (0 <= i && i < Seq#Length(s) ==> Seq#ContainsTrigger(s,Seq#Index(s,i))));
// ** AS: made one change here - changed type of x from ref to T
/*axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
*/
// diff 8: skolemisation (new)
/*
function Seq#Skolem<T>(Seq T, T) : int; // skolem function for Seq#Contains
function Seq#SkolemContainsDrop<T>(Seq T, int, T) : int; // skolem function for Seq#Contains over drop
function Seq#SkolemContainsTake<T>(Seq T, int, T) : int; // skolem function for Seq#Contains over take

function Seq#Contains<T>(Seq T, T): bool;
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) ==> s != Seq#Empty() && Seq#Length(s) > 0 && 0 <= Seq#Skolem(s,x) &&
    Seq#Skolem(s,x) < Seq#Length(s) && Seq#Index(s,Seq#Skolem(s,x)) == x);

// AS: note: this is an unusual axiom, but is basically the original
// Consider writing a version without the (precise) first trigger? Also see later versions
axiom (forall<T> s: Seq T, x: T, i:int :: { Seq#Contains(s,x), Seq#Index(s,i) }
  0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x ==> Seq#Contains(s,x));

// ** AS: made one change here - changed type of x from ref to T
axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

// AS: Consider dropping this axiom?
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) } { Seq#Contains(s0,x), Seq#Append(s0,s1)} { Seq#Contains(s1,x), Seq#Append(s0,s1)} // AS: added triggers
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

// AS: split axioms
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) ==>
    (Seq#Take(s, n) != Seq#Empty() && Seq#Length(Seq#Take(s, n)) > 0 &&
     0 <= Seq#SkolemContainsTake(s, n, x) && Seq#SkolemContainsTake(s, n, x) < n &&
      Seq#SkolemContainsTake(s, n, x) < Seq#Length(s) &&
      Seq#Index(s, Seq#SkolemContainsTake(s, n, x)) == x));

axiom (forall<T> s: Seq T, n: int, x: T, i:int ::
  { Seq#Contains(Seq#Take(s, n), x), Seq#Index(s, i) }
    0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x ==>
     Seq#Contains(Seq#Take(s, n), x));

// AS: split axioms
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) ==>
    ( 0 <= Seq#SkolemContainsDrop(s, n, x) && n <= Seq#SkolemContainsDrop(s, n, x) &&
      Seq#SkolemContainsDrop(s, n, x) < Seq#Length(s) &&
      Seq#Index(s, Seq#SkolemContainsDrop(s, n, x)) == x));

axiom (forall<T> s: Seq T, n: int, x: T, i:int ::
  { Seq#Contains(Seq#Drop(s, n), x), Seq#Index(s, i) }
  0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x ==>
  Seq#Contains(Seq#Drop(s, n), x));
*/

// END CONTAINS

// START EQUALS

// diff 9 : skolemise equals (old)
function Seq#Equal<T>(Seq T, Seq T): bool;
/*axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);
*/
// diff 9: skolemise equals (new)
// AS: split axiom
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) ==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#SkolemDiff<T>(Seq T, Seq T) : int; // skolem function for Seq#Equals

axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  (s0==s1 && Seq#Equal(s0,s1)) || (s0!=s1 && !Seq#Equal(s0,s1) && Seq#Length(s0) != Seq#Length(s1)) ||
        (s0 != s1 && !Seq#Equal(s0,s1) && Seq#Length(s0) == Seq#Length(s1) && Seq#SkolemDiff(s0,s1) == Seq#SkolemDiff(s1,s0) && 0 <= Seq#SkolemDiff(s0,s1) && Seq#SkolemDiff(s0,s1) < Seq#Length(s0) &&
         Seq#Index(s0,Seq#SkolemDiff(s0,s1)) != Seq#Index(s1,Seq#SkolemDiff(s0,s1))));

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);


// END EQUALS


// START EXTRAS

// extra stuff not in current Dafny Prelude

// diff 10: variant of trigger (maybe drop these?)
// old:
axiom (forall<T> x, y: T ::
  { Seq#Contains(Seq#Singleton(x),y) }
    Seq#Contains(Seq#Singleton(x),y) <==> x==y);
// new:
/*axiom (forall<T> x, y: T ::
  { Seq#Contains(Seq#Singleton(x),y) }
    Seq#Contains(Seq#Singleton(x),y) ==> x==y);

axiom (forall<T> x: T ::
  { Seq#Singleton(x) }
    Seq#Contains(Seq#Singleton(x),x));
*/

function Seq#Range(min: int, max: int) returns (Seq int);
axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);

axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));

// END EXTRAS


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
// Translation of domain PyType
// ==================================================

// The type for domain PyType
type PyTypeDomainType;

// Translation of domain function extends_
function  extends_(sub: PyTypeDomainType, super: PyTypeDomainType): bool;

// Translation of domain function issubtype
function  issubtype(sub: PyTypeDomainType, super: PyTypeDomainType): bool;

// Translation of domain function isnotsubtype
function  isnotsubtype(sub: PyTypeDomainType, super: PyTypeDomainType): bool;

// Translation of domain function tuple_args
function  tuple_args(t_1: PyTypeDomainType): Seq PyTypeDomainType;

// Translation of domain function typeof
function  typeof(obj: Ref): PyTypeDomainType;

// Translation of domain function get_basic
function  get_basic(t_1: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function union_type_1
function  union_type_1(arg_1: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function union_type_2
function  union_type_2(arg_1: PyTypeDomainType, arg_2: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function union_type_3
function  union_type_3(arg_1: PyTypeDomainType, arg_2: PyTypeDomainType, arg_3: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function union_type_4
function  union_type_4(arg_1: PyTypeDomainType, arg_2: PyTypeDomainType, arg_3: PyTypeDomainType, arg_4: PyTypeDomainType): PyTypeDomainType;

// Translation of domain unique function object
const unique object: PyTypeDomainType;

// Translation of domain unique function list_basic
const unique list_basic: PyTypeDomainType;

// Translation of domain function list
function  list(arg0: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function list_arg
function  list_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function set_basic
const unique set_basic: PyTypeDomainType;

// Translation of domain function set
function  set(arg0: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function set_arg
function  set_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function dict_basic
const unique dict_basic: PyTypeDomainType;

// Translation of domain function dict
function  dict(arg0: PyTypeDomainType, arg1: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function dict_arg
function  dict_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function int
const unique vint: PyTypeDomainType;

// Translation of domain unique function float
const unique float: PyTypeDomainType;

// Translation of domain unique function bool
const unique vbool: PyTypeDomainType;

// Translation of domain unique function NoneType
const unique NoneType: PyTypeDomainType;

// Translation of domain unique function Exception
const unique Exception: PyTypeDomainType;

// Translation of domain unique function ConnectionRefusedError
const unique ConnectionRefusedError: PyTypeDomainType;

// Translation of domain unique function traceback
const unique traceback: PyTypeDomainType;

// Translation of domain unique function str
const unique str: PyTypeDomainType;

// Translation of domain unique function bytes
const unique bytes: PyTypeDomainType;

// Translation of domain unique function tuple_basic
const unique tuple_basic: PyTypeDomainType;

// Translation of domain function tuple
function  tuple(args: (Seq PyTypeDomainType)): PyTypeDomainType;

// Translation of domain function tuple_arg
function  tuple_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function PSeq_basic
const unique PSeq_basic: PyTypeDomainType;

// Translation of domain function PSeq
function  PSeq(arg0: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function PSeq_arg
function  PSeq_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function PSet_basic
const unique PSet_basic: PyTypeDomainType;

// Translation of domain function PSet
function  PSet(arg0: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function PSet_arg
function  PSet_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function PMultiset_basic
const unique PMultiset_basic: PyTypeDomainType;

// Translation of domain function PMultiset
function  PMultiset(arg0: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function PMultiset_arg
function  PMultiset_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function slice
const unique slice: PyTypeDomainType;

// Translation of domain unique function py_range
const unique py_range: PyTypeDomainType;

// Translation of domain unique function Iterator_basic
const unique Iterator_basic: PyTypeDomainType;

// Translation of domain function Iterator
function  Iterator(arg0: PyTypeDomainType): PyTypeDomainType;

// Translation of domain function Iterator_arg
function  Iterator_arg(typ: PyTypeDomainType, index: int): PyTypeDomainType;

// Translation of domain unique function Thread_0
const unique Thread_0: PyTypeDomainType;

// Translation of domain unique function LevelType
const unique LevelType: PyTypeDomainType;

// Translation of domain unique function type
const unique vtype: PyTypeDomainType;

// Translation of domain unique function Place
const unique Place: PyTypeDomainType;

// Translation of domain unique function __prim__Seq_type
const unique __prim__Seq_type: PyTypeDomainType;

// Translation of domain unique function SoldoutException
const unique SoldoutException: PyTypeDomainType;

// Translation of domain unique function Ticket
const unique Ticket: PyTypeDomainType;

// Translation of domain axiom issubtype_transitivity
axiom (forall sub_1: PyTypeDomainType, middle: PyTypeDomainType, super_1: PyTypeDomainType ::
  { (issubtype(sub_1, middle): bool), (issubtype(middle, super_1): bool) }
  (issubtype(sub_1, middle): bool) && (issubtype(middle, super_1): bool) ==> (issubtype(sub_1, super_1): bool)
);

// Translation of domain axiom issubtype_reflexivity
axiom (forall type_: PyTypeDomainType ::
  { (issubtype(type_, type_): bool) }
  (issubtype(type_, type_): bool)
);

// Translation of domain axiom extends_implies_subtype
axiom (forall sub_1: PyTypeDomainType, sub2: PyTypeDomainType ::
  { (extends_(sub_1, sub2): bool) }
  (extends_(sub_1, sub2): bool) ==> (issubtype(sub_1, sub2): bool)
);

// Translation of domain axiom null_nonetype
axiom (forall r_1: Ref ::
  { (typeof(r_1): PyTypeDomainType) }
  (issubtype((typeof(r_1): PyTypeDomainType), NoneType): bool) == (r_1 == null)
);

// Translation of domain axiom issubtype_object
axiom (forall type_: PyTypeDomainType ::
  { (issubtype(type_, object): bool) }
  (issubtype(type_, object): bool)
);

// Translation of domain axiom issubtype_exclusion
axiom (forall sub_1: PyTypeDomainType, sub2: PyTypeDomainType, super_1: PyTypeDomainType ::
  { (extends_(sub_1, super_1): bool), (extends_(sub2, super_1): bool) }
  (extends_(sub_1, super_1): bool) && ((extends_(sub2, super_1): bool) && sub_1 != sub2) ==> (isnotsubtype(sub_1, sub2): bool) && (isnotsubtype(sub2, sub_1): bool)
);

// Translation of domain axiom issubtype_exclusion_2
axiom (forall sub_1: PyTypeDomainType, super_1: PyTypeDomainType ::
  { (issubtype(sub_1, super_1): bool) } { (issubtype(super_1, sub_1): bool) }
  (issubtype(sub_1, super_1): bool) && sub_1 != super_1 ==> !(issubtype(super_1, sub_1): bool)
);

// Translation of domain axiom issubtype_exclusion_propagation
axiom (forall sub_1: PyTypeDomainType, middle: PyTypeDomainType, super_1: PyTypeDomainType ::
  { (issubtype(sub_1, middle): bool), (isnotsubtype(middle, super_1): bool) }
  (issubtype(sub_1, middle): bool) && (isnotsubtype(middle, super_1): bool) ==> !(issubtype(sub_1, super_1): bool)
);

// Translation of domain axiom tuple_arg_def
axiom (forall seq: (Seq PyTypeDomainType), i: int, Z: PyTypeDomainType ::
  { (tuple(seq): PyTypeDomainType), (tuple_arg(Z, i): PyTypeDomainType) }
  (issubtype(Z, (tuple(seq): PyTypeDomainType)): bool) ==> (issubtype((tuple_arg(Z, i): PyTypeDomainType), Seq#Index(seq, i)): bool)
);

// Translation of domain axiom tuple_args_def
axiom (forall seq: (Seq PyTypeDomainType), Z: PyTypeDomainType ::
  { (issubtype(Z, (tuple(seq): PyTypeDomainType)): bool) }
  (issubtype(Z, (tuple(seq): PyTypeDomainType)): bool) ==> Seq#Length((tuple_args(Z): Seq PyTypeDomainType)) == Seq#Length(seq)
);

// Translation of domain axiom tuple_self_subtype
axiom (forall seq1: (Seq PyTypeDomainType), seq2: (Seq PyTypeDomainType) ::
  { Seq#Length(seq1), Seq#Length(seq2) } { Seq#Length(seq1), (tuple(seq2): PyTypeDomainType) } { Seq#Length(seq1), (issubtype((tuple(seq1): PyTypeDomainType), (tuple(seq2): PyTypeDomainType)): bool) } { Seq#Length(seq2), Seq#Length(seq1) } { Seq#Length(seq2), (tuple(seq1): PyTypeDomainType) } { Seq#Length(seq2), (issubtype((tuple(seq1): PyTypeDomainType), (tuple(seq2): PyTypeDomainType)): bool) } { (issubtype((tuple(seq1): PyTypeDomainType), (tuple(seq2): PyTypeDomainType)): bool) }
  !Seq#Equal(seq1, seq2) && (Seq#Length(seq1) == Seq#Length(seq2) && (forall i: int ::
    { (issubtype(Seq#Index(seq1, i), Seq#Index(seq2, i)): bool) }
    i >= 0 && i < Seq#Length(seq1) ==> (issubtype(Seq#Index(seq1, i), Seq#Index(seq2, i)): bool)
  )) ==> (issubtype((tuple(seq1): PyTypeDomainType), (tuple(seq2): PyTypeDomainType)): bool)
);

// Translation of domain axiom union_subtype_1
axiom (forall arg_1_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype(X, (union_type_1(arg_1_1): PyTypeDomainType)): bool) }
  (issubtype(X, (union_type_1(arg_1_1): PyTypeDomainType)): bool) == (issubtype(X, arg_1_1): bool)
);

// Translation of domain axiom union_subtype_2
axiom (forall arg_1_1: PyTypeDomainType, arg_2_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype(X, (union_type_2(arg_1_1, arg_2_1): PyTypeDomainType)): bool) }
  (issubtype(X, (union_type_2(arg_1_1, arg_2_1): PyTypeDomainType)): bool) == ((issubtype(X, arg_1_1): bool) || (issubtype(X, arg_2_1): bool))
);

// Translation of domain axiom union_subtype_3
axiom (forall arg_1_1: PyTypeDomainType, arg_2_1: PyTypeDomainType, arg_3_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype(X, (union_type_3(arg_1_1, arg_2_1, arg_3_1): PyTypeDomainType)): bool) }
  (issubtype(X, (union_type_3(arg_1_1, arg_2_1, arg_3_1): PyTypeDomainType)): bool) == ((issubtype(X, arg_1_1): bool) || ((issubtype(X, arg_2_1): bool) || (issubtype(X, arg_3_1): bool)))
);

// Translation of domain axiom union_subtype_4
axiom (forall arg_1_1: PyTypeDomainType, arg_2_1: PyTypeDomainType, arg_3_1: PyTypeDomainType, arg_4_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype(X, (union_type_4(arg_1_1, arg_2_1, arg_3_1, arg_4_1): PyTypeDomainType)): bool) }
  (issubtype(X, (union_type_4(arg_1_1, arg_2_1, arg_3_1, arg_4_1): PyTypeDomainType)): bool) == ((issubtype(X, arg_1_1): bool) || ((issubtype(X, arg_2_1): bool) || ((issubtype(X, arg_3_1): bool) || (issubtype(X, arg_4_1): bool))))
);

// Translation of domain axiom subtype_union_1
axiom (forall arg_1_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype((union_type_1(arg_1_1): PyTypeDomainType), X): bool) }
  (issubtype((union_type_1(arg_1_1): PyTypeDomainType), X): bool) == (issubtype(arg_1_1, X): bool)
);

// Translation of domain axiom subtype_union_2
axiom (forall arg_1_1: PyTypeDomainType, arg_2_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype((union_type_2(arg_1_1, arg_2_1): PyTypeDomainType), X): bool) }
  (issubtype((union_type_2(arg_1_1, arg_2_1): PyTypeDomainType), X): bool) == ((issubtype(arg_1_1, X): bool) && (issubtype(arg_2_1, X): bool))
);

// Translation of domain axiom subtype_union_3
axiom (forall arg_1_1: PyTypeDomainType, arg_2_1: PyTypeDomainType, arg_3_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype((union_type_3(arg_1_1, arg_2_1, arg_3_1): PyTypeDomainType), X): bool) }
  (issubtype((union_type_3(arg_1_1, arg_2_1, arg_3_1): PyTypeDomainType), X): bool) == ((issubtype(arg_1_1, X): bool) && ((issubtype(arg_2_1, X): bool) && (issubtype(arg_3_1, X): bool)))
);

// Translation of domain axiom subtype_union_4
axiom (forall arg_1_1: PyTypeDomainType, arg_2_1: PyTypeDomainType, arg_3_1: PyTypeDomainType, arg_4_1: PyTypeDomainType, X: PyTypeDomainType ::
  { (issubtype((union_type_4(arg_1_1, arg_2_1, arg_3_1, arg_4_1): PyTypeDomainType), X): bool) }
  (issubtype((union_type_4(arg_1_1, arg_2_1, arg_3_1, arg_4_1): PyTypeDomainType), X): bool) == ((issubtype(arg_1_1, X): bool) && ((issubtype(arg_2_1, X): bool) && ((issubtype(arg_3_1, X): bool) && (issubtype(arg_4_1, X): bool))))
);

// Translation of domain axiom subtype_list
axiom (forall var0: PyTypeDomainType ::
  { (list(var0): PyTypeDomainType) }
  (extends_((list(var0): PyTypeDomainType), object): bool) && (get_basic((list(var0): PyTypeDomainType)): PyTypeDomainType) == list_basic
);

// Translation of domain axiom list_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType ::
  { (list(arg0_1): PyTypeDomainType), (list_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (list(arg0_1): PyTypeDomainType)): bool) ==> (list_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom subtype_set
axiom (forall var0: PyTypeDomainType ::
  { (set(var0): PyTypeDomainType) }
  (extends_((set(var0): PyTypeDomainType), object): bool) && (get_basic((set(var0): PyTypeDomainType)): PyTypeDomainType) == set_basic
);

// Translation of domain axiom set_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType ::
  { (set(arg0_1): PyTypeDomainType), (set_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (set(arg0_1): PyTypeDomainType)): bool) ==> (set_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom subtype_dict
axiom (forall var0: PyTypeDomainType, var1: PyTypeDomainType ::
  { (dict(var0, var1): PyTypeDomainType) }
  (extends_((dict(var0, var1): PyTypeDomainType), object): bool) && (get_basic((dict(var0, var1): PyTypeDomainType)): PyTypeDomainType) == dict_basic
);

// Translation of domain axiom dict_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType, arg1_1: PyTypeDomainType ::
  { (dict(arg0_1, arg1_1): PyTypeDomainType), (dict_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (dict(arg0_1, arg1_1): PyTypeDomainType)): bool) ==> (dict_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom dict_args1
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType, arg1_1: PyTypeDomainType ::
  { (dict(arg0_1, arg1_1): PyTypeDomainType), (dict_arg(Z, 1): PyTypeDomainType) }
  (issubtype(Z, (dict(arg0_1, arg1_1): PyTypeDomainType)): bool) ==> (dict_arg(Z, 1): PyTypeDomainType) == arg1_1
);

// Translation of domain axiom subtype_int
axiom (extends_(vint, float): bool) && (get_basic(vint): PyTypeDomainType) == vint;

// Translation of domain axiom subtype_float
axiom (extends_(float, object): bool) && (get_basic(float): PyTypeDomainType) == float;

// Translation of domain axiom subtype_bool
axiom (extends_(vbool, vint): bool) && (get_basic(vbool): PyTypeDomainType) == vbool;

// Translation of domain axiom subtype_NoneType
axiom (extends_(NoneType, object): bool) && (get_basic(NoneType): PyTypeDomainType) == NoneType;

// Translation of domain axiom subtype_Exception
axiom (extends_(Exception, object): bool) && (get_basic(Exception): PyTypeDomainType) == Exception;

// Translation of domain axiom subtype_ConnectionRefusedError
axiom (extends_(ConnectionRefusedError, Exception): bool) && (get_basic(ConnectionRefusedError): PyTypeDomainType) == ConnectionRefusedError;

// Translation of domain axiom subtype_traceback
axiom (extends_(traceback, object): bool) && (get_basic(traceback): PyTypeDomainType) == traceback;

// Translation of domain axiom subtype_str
axiom (extends_(str, object): bool) && (get_basic(str): PyTypeDomainType) == str;

// Translation of domain axiom subtype_bytes
axiom (extends_(bytes, object): bool) && (get_basic(bytes): PyTypeDomainType) == bytes;

// Translation of domain axiom subtype_tuple
axiom (forall args_1: (Seq PyTypeDomainType) ::
  { (tuple(args_1): PyTypeDomainType) }
  ((forall e: PyTypeDomainType ::
    { Seq#ContainsTrigger(args_1, e) } { Seq#Contains(args_1, e) }
    Seq#Contains(args_1, e) ==> e == object
  ) ==> (extends_((tuple(args_1): PyTypeDomainType), object): bool)) && (get_basic((tuple(args_1): PyTypeDomainType)): PyTypeDomainType) == tuple_basic
);

// Translation of domain axiom subtype_PSeq
axiom (forall var0: PyTypeDomainType ::
  { (PSeq(var0): PyTypeDomainType) }
  (extends_((PSeq(var0): PyTypeDomainType), object): bool) && (get_basic((PSeq(var0): PyTypeDomainType)): PyTypeDomainType) == PSeq_basic
);

// Translation of domain axiom PSeq_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType ::
  { (PSeq(arg0_1): PyTypeDomainType), (PSeq_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (PSeq(arg0_1): PyTypeDomainType)): bool) ==> (PSeq_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom subtype_PSet
axiom (forall var0: PyTypeDomainType ::
  { (PSet(var0): PyTypeDomainType) }
  (extends_((PSet(var0): PyTypeDomainType), object): bool) && (get_basic((PSet(var0): PyTypeDomainType)): PyTypeDomainType) == PSet_basic
);

// Translation of domain axiom PSet_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType ::
  { (PSet(arg0_1): PyTypeDomainType), (PSet_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (PSet(arg0_1): PyTypeDomainType)): bool) ==> (PSet_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom subtype_PMultiset
axiom (forall var0: PyTypeDomainType ::
  { (PMultiset(var0): PyTypeDomainType) }
  (extends_((PMultiset(var0): PyTypeDomainType), object): bool) && (get_basic((PMultiset(var0): PyTypeDomainType)): PyTypeDomainType) == PMultiset_basic
);

// Translation of domain axiom PMultiset_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType ::
  { (PMultiset(arg0_1): PyTypeDomainType), (PMultiset_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (PMultiset(arg0_1): PyTypeDomainType)): bool) ==> (PMultiset_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom subtype_slice
axiom (extends_(slice, object): bool) && (get_basic(slice): PyTypeDomainType) == slice;

// Translation of domain axiom subtype_py_range
axiom (extends_(py_range, object): bool) && (get_basic(py_range): PyTypeDomainType) == py_range;

// Translation of domain axiom subtype_Iterator
axiom (forall var0: PyTypeDomainType ::
  { (Iterator(var0): PyTypeDomainType) }
  (extends_((Iterator(var0): PyTypeDomainType), object): bool) && (get_basic((Iterator(var0): PyTypeDomainType)): PyTypeDomainType) == Iterator_basic
);

// Translation of domain axiom Iterator_args0
axiom (forall Z: PyTypeDomainType, arg0_1: PyTypeDomainType ::
  { (Iterator(arg0_1): PyTypeDomainType), (Iterator_arg(Z, 0): PyTypeDomainType) }
  (issubtype(Z, (Iterator(arg0_1): PyTypeDomainType)): bool) ==> (Iterator_arg(Z, 0): PyTypeDomainType) == arg0_1
);

// Translation of domain axiom subtype_Thread_0
axiom (extends_(Thread_0, object): bool) && (get_basic(Thread_0): PyTypeDomainType) == Thread_0;

// Translation of domain axiom subtype_LevelType
axiom (extends_(LevelType, object): bool) && (get_basic(LevelType): PyTypeDomainType) == LevelType;

// Translation of domain axiom subtype_type
axiom (extends_(vtype, object): bool) && (get_basic(vtype): PyTypeDomainType) == vtype;

// Translation of domain axiom subtype_Place
axiom (extends_(Place, object): bool) && (get_basic(Place): PyTypeDomainType) == Place;

// Translation of domain axiom subtype___prim__Seq_type
axiom (extends_(__prim__Seq_type, object): bool) && (get_basic(__prim__Seq_type): PyTypeDomainType) == __prim__Seq_type;

// Translation of domain axiom subtype_SoldoutException
axiom (extends_(SoldoutException, Exception): bool) && (get_basic(SoldoutException): PyTypeDomainType) == SoldoutException;

// Translation of domain axiom subtype_Ticket
axiom (extends_(Ticket, object): bool) && (get_basic(Ticket): PyTypeDomainType) == Ticket;

// ==================================================
// Translation of domain SIFDomain
// ==================================================

// The type for domain SIFDomain
type SIFDomainDomainType T;

// Translation of domain function Low
function  Low<T>(x: T): bool;

// Translation of domain axiom low_true
axiom (forall <T> x_1: T ::
  { (Low(x_1): bool) }
  (Low(x_1): bool)
);

// ==================================================
// Translation of domain _list_ce_helper
// ==================================================

// The type for domain _list_ce_helper
type _list_ce_helperDomainType;

// Translation of domain function seq_ref_length
function  seq_ref_length(___s: (Seq Ref)): int;

// Translation of domain function seq_ref_index
function  seq_ref_index(___s: (Seq Ref), i_1: int): Ref;

// Translation of domain axiom relate_length
axiom (forall ___s_1: (Seq Ref) ::
  { Seq#Length(___s_1) }
  Seq#Length(___s_1) == (seq_ref_length(___s_1): int)
);

// Translation of domain axiom relate_index
axiom (forall ___s_1: (Seq Ref), ___i: int ::
  { Seq#Index(___s_1, ___i) }
  Seq#Index(___s_1, ___i) == (seq_ref_index(___s_1, ___i): Ref)
);

// ==================================================
// Translation of domain Measure$
// ==================================================

// The type for domain Measure$
type Measure$DomainType;

// Translation of domain function Measure$create
function  Measure$create(guard: bool, key: Ref, value: int): Measure$DomainType;

// Translation of domain function Measure$guard
function  Measure$guard(m: Measure$DomainType): bool;

// Translation of domain function Measure$key
function  Measure$key(m: Measure$DomainType): Ref;

// Translation of domain function Measure$value
function  Measure$value(m: Measure$DomainType): int;

// Translation of domain axiom Measure$A0
axiom (forall g: bool, k: Ref, v_2: int ::
  { (Measure$guard((Measure$create(g, k, v_2): Measure$DomainType)): bool) }
  (Measure$guard((Measure$create(g, k, v_2): Measure$DomainType)): bool) == g
);

// Translation of domain axiom Measure$A1
axiom (forall g: bool, k: Ref, v_2: int ::
  { (Measure$key((Measure$create(g, k, v_2): Measure$DomainType)): Ref) }
  (Measure$key((Measure$create(g, k, v_2): Measure$DomainType)): Ref) == k
);

// Translation of domain axiom Measure$A2
axiom (forall g: bool, k: Ref, v_2: int ::
  { (Measure$value((Measure$create(g, k, v_2): Measure$DomainType)): int) }
  (Measure$value((Measure$create(g, k, v_2): Measure$DomainType)): int) == v_2
);

// ==================================================
// Translation of domain _dict_ce_helper
// ==================================================

// The type for domain _dict_ce_helper
type _dict_ce_helperDomainType;

// Translation of domain function dict_get_helper
function  dict_get_helper(___s: (Set Ref), ___s2: Ref, ___s3: Ref): Ref;

// ==================================================
// Translation of domain _Name
// ==================================================

// The type for domain _Name
type _NameDomainType;

// Translation of domain function _combine
function  _combine(n1: _NameDomainType, n2: _NameDomainType): _NameDomainType;

// Translation of domain function _single
function  _single(n: int): _NameDomainType;

// Translation of domain function _get_combined_prefix
function  _get_combined_prefix(n: _NameDomainType): _NameDomainType;

// Translation of domain function _get_combined_name
function  _get_combined_name(n: _NameDomainType): _NameDomainType;

// Translation of domain function _get_value
function  _get_value(n: _NameDomainType): int;

// Translation of domain function _name_type
function  _name_type(n: _NameDomainType): bool;

// Translation of domain function _is_single
function  _is_single(n: _NameDomainType): bool;

// Translation of domain function _is_combined
function  _is_combined(n: _NameDomainType): bool;

// Translation of domain axiom decompose_single
axiom (forall i: int ::
  { (_single(i): _NameDomainType) }
  (_get_value((_single(i): _NameDomainType)): int) == i
);

// Translation of domain axiom compose_single
axiom (forall n_1: _NameDomainType ::
  { (_get_value(n_1): int) }
  (_is_single(n_1): bool) ==> n_1 == (_single((_get_value(n_1): int)): _NameDomainType)
);

// Translation of domain axiom type_of_single
axiom (forall i: int ::
  { (_single(i): _NameDomainType) }
  (_name_type((_single(i): _NameDomainType)): bool)
);

// Translation of domain axiom decompose_combined
axiom (forall n1_1: _NameDomainType, n2_1: _NameDomainType ::
  { (_combine(n1_1, n2_1): _NameDomainType) }
  (_get_combined_prefix((_combine(n1_1, n2_1): _NameDomainType)): _NameDomainType) == n1_1 && (_get_combined_name((_combine(n1_1, n2_1): _NameDomainType)): _NameDomainType) == n2_1
);

// Translation of domain axiom compose_combined
axiom (forall n_1: _NameDomainType ::
  { (_get_combined_prefix(n_1): _NameDomainType) } { (_get_combined_name(n_1): _NameDomainType) }
  (_is_combined(n_1): bool) ==> n_1 == (_combine((_get_combined_prefix(n_1): _NameDomainType), (_get_combined_name(n_1): _NameDomainType)): _NameDomainType)
);

// Translation of domain axiom type_of_composed
axiom (forall n1_1: _NameDomainType, n2_1: _NameDomainType ::
  { (_combine(n1_1, n2_1): _NameDomainType) }
  !(_name_type((_combine(n1_1, n2_1): _NameDomainType)): bool)
);

// Translation of domain axiom type_is_single
axiom (forall n_1: _NameDomainType ::
  { (_name_type(n_1): bool) }
  (_name_type(n_1): bool) == (_is_single(n_1): bool)
);

// Translation of domain axiom type_is_combined
axiom (forall n_1: _NameDomainType ::
  { (_name_type(n_1): bool) }
  !(_name_type(n_1): bool) == (_is_combined(n_1): bool)
);

// ==================================================
// Translation of all fields
// ==================================================

const unique _val: Field NormalField Ref;
axiom !IsPredicateField(_val);
axiom !IsWandField(_val);
const unique __container: Field NormalField Ref;
axiom !IsPredicateField(__container);
axiom !IsWandField(__container);
const unique __iter_index: Field NormalField int;
axiom !IsPredicateField(__iter_index);
axiom !IsWandField(__iter_index);
const unique __previous: Field NormalField (Seq Ref);
axiom !IsPredicateField(__previous);
axiom !IsWandField(__previous);
const unique list_acc: Field NormalField (Seq Ref);
axiom !IsPredicateField(list_acc);
axiom !IsWandField(list_acc);
const unique set_acc: Field NormalField (Set Ref);
axiom !IsPredicateField(set_acc);
axiom !IsWandField(set_acc);
const unique dict_acc: Field NormalField (Set Ref);
axiom !IsPredicateField(dict_acc);
axiom !IsWandField(dict_acc);
const unique dict_acc2: Field NormalField Ref;
axiom !IsPredicateField(dict_acc2);
axiom !IsWandField(dict_acc2);
const unique Measure$acc: Field NormalField (Seq Ref);
axiom !IsPredicateField(Measure$acc);
axiom !IsWandField(Measure$acc);
const unique MustReleaseBounded: Field NormalField int;
axiom !IsPredicateField(MustReleaseBounded);
axiom !IsWandField(MustReleaseBounded);
const unique MustReleaseUnbounded: Field NormalField int;
axiom !IsPredicateField(MustReleaseUnbounded);
axiom !IsWandField(MustReleaseUnbounded);
const unique Ticket_show_id: Field NormalField Ref;
axiom !IsPredicateField(Ticket_show_id);
axiom !IsWandField(Ticket_show_id);
const unique Ticket_row: Field NormalField Ref;
axiom !IsPredicateField(Ticket_row);
axiom !IsWandField(Ticket_row);
const unique Ticket_seat: Field NormalField Ref;
axiom !IsPredicateField(Ticket_seat);
axiom !IsWandField(Ticket_seat);
const unique Ticket_discount_code: Field NormalField Ref;
axiom !IsPredicateField(Ticket_discount_code);
axiom !IsWandField(Ticket_discount_code);

// ==================================================
// Translation of function _isDefined
// ==================================================

// Uninterpreted function definitions
function  _isDefined(Heap: HeapType, id: int): bool;
function  _isDefined'(Heap: HeapType, id: int): bool;
axiom (forall Heap: HeapType, id: int ::
  { _isDefined(Heap, id) }
  _isDefined(Heap, id) == _isDefined'(Heap, id) && dummyFunction(_isDefined#triggerStateless(id))
);
axiom (forall Heap: HeapType, id: int ::
  { _isDefined'(Heap, id) }
  dummyFunction(_isDefined#triggerStateless(id))
);

// Framing axioms
function  _isDefined#frame(frame: FrameType, id: int): bool;
axiom (forall Heap: HeapType, Mask: MaskType, id: int ::
  { state(Heap, Mask), _isDefined'(Heap, id) }
  state(Heap, Mask) ==> _isDefined'(Heap, id) == _isDefined#frame(EmptyFrame, id)
);

// Trigger function (controlling recursive postconditions)
function  _isDefined#trigger(frame: FrameType, id: int): bool;

// State-independent trigger function
function  _isDefined#triggerStateless(id: int): bool;

// Check contract well-formedness and postcondition
procedure _isDefined#definedness(id: int) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 18;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function _checkDefined
// ==================================================

// Uninterpreted function definitions
function  _checkDefined(Heap: HeapType, val: Ref, id: int): Ref;
function  _checkDefined'(Heap: HeapType, val: Ref, id: int): Ref;
axiom (forall Heap: HeapType, val: Ref, id: int ::
  { _checkDefined(Heap, val, id) }
  _checkDefined(Heap, val, id) == _checkDefined'(Heap, val, id) && dummyFunction(_checkDefined#triggerStateless(val, id))
);
axiom (forall Heap: HeapType, val: Ref, id: int ::
  { _checkDefined'(Heap, val, id) }
  dummyFunction(_checkDefined#triggerStateless(val, id))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, val: Ref, id: int ::
  { state(Heap, Mask), _checkDefined(Heap, val, id) }
  state(Heap, Mask) && AssumeFunctionsAbove < 9 ==> _isDefined(Heap, id) ==> _checkDefined(Heap, val, id) == val
);

// Framing axioms
function  _checkDefined#frame(frame: FrameType, val: Ref, id: int): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, val: Ref, id: int ::
  { state(Heap, Mask), _checkDefined'(Heap, val, id) }
  state(Heap, Mask) ==> _checkDefined'(Heap, val, id) == _checkDefined#frame(EmptyFrame, val, id)
);

// Trigger function (controlling recursive postconditions)
function  _checkDefined#trigger(frame: FrameType, val: Ref, id: int): bool;

// State-independent trigger function
function  _checkDefined#triggerStateless(val: Ref, id: int): Ref;

// Check contract well-formedness and postcondition
procedure _checkDefined#definedness(val: Ref, id: int) returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[val, $allocated];
    assume AssumeFunctionsAbove == 9;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume state(Heap, Mask);
    
    // -- Check definedness of _isDefined(id)
      if (*) {
        // Stop execution
        assume false;
      }
    assume _isDefined(Heap, id);
    assume state(Heap, Mask);
  
  // -- Translate function body
    Result := val;
}

// ==================================================
// Translation of function __file__
// ==================================================

// Uninterpreted function definitions
function  __file__(Heap: HeapType): Ref;
function  __file__'(Heap: HeapType): Ref;
axiom (forall Heap: HeapType ::
  { __file__(Heap) }
  __file__(Heap) == __file__'(Heap) && dummyFunction(__file__#triggerStateless())
);
axiom (forall Heap: HeapType ::
  { __file__'(Heap) }
  dummyFunction(__file__#triggerStateless())
);

// Framing axioms
function  __file__#frame(frame: FrameType): Ref;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask), __file__'(Heap) }
  state(Heap, Mask) ==> __file__'(Heap) == __file__#frame(EmptyFrame)
);

// Trigger function (controlling recursive postconditions)
function  __file__#trigger(frame: FrameType): bool;

// State-independent trigger function
function  __file__#triggerStateless(): Ref;

// Check contract well-formedness and postcondition
procedure __file__#definedness() returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 10;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function __name__
// ==================================================

// Uninterpreted function definitions
function  __name__(Heap: HeapType): Ref;
function  __name__'(Heap: HeapType): Ref;
axiom (forall Heap: HeapType ::
  { __name__(Heap) }
  __name__(Heap) == __name__'(Heap) && dummyFunction(__name__#triggerStateless())
);
axiom (forall Heap: HeapType ::
  { __name__'(Heap) }
  dummyFunction(__name__#triggerStateless())
);

// Framing axioms
function  __name__#frame(frame: FrameType): Ref;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask), __name__'(Heap) }
  state(Heap, Mask) ==> __name__'(Heap) == __name__#frame(EmptyFrame)
);

// Trigger function (controlling recursive postconditions)
function  __name__#trigger(frame: FrameType): bool;

// State-independent trigger function
function  __name__#triggerStateless(): Ref;

// Check contract well-formedness and postcondition
procedure __name__#definedness() returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 0;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function __prim__int___box__
// ==================================================

// Uninterpreted function definitions
function  __prim__int___box__(Heap: HeapType, prim: int): Ref;
function  __prim__int___box__'(Heap: HeapType, prim: int): Ref;
axiom (forall Heap: HeapType, prim: int ::
  { __prim__int___box__(Heap, prim) }
  __prim__int___box__(Heap, prim) == __prim__int___box__'(Heap, prim) && dummyFunction(__prim__int___box__#triggerStateless(prim))
);
axiom (forall Heap: HeapType, prim: int ::
  { __prim__int___box__'(Heap, prim) }
  dummyFunction(__prim__int___box__#triggerStateless(prim))
);

// Framing axioms
function  __prim__int___box__#frame(frame: FrameType, prim: int): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, prim: int ::
  { state(Heap, Mask), __prim__int___box__'(Heap, prim) }
  state(Heap, Mask) ==> __prim__int___box__'(Heap, prim) == __prim__int___box__#frame(EmptyFrame, prim)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, prim: int ::
  { state(Heap, Mask), __prim__int___box__'(Heap, prim) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || __prim__int___box__#trigger(EmptyFrame, prim)) ==> (typeof(__prim__int___box__'(Heap, prim)): PyTypeDomainType) == vint
);
axiom (forall Heap: HeapType, Mask: MaskType, prim: int ::
  { state(Heap, Mask), __prim__int___box__'(Heap, prim) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || __prim__int___box__#trigger(EmptyFrame, prim)) ==> int___unbox__'(Heap, __prim__int___box__'(Heap, prim)) == prim
);

// Trigger function (controlling recursive postconditions)
function  __prim__int___box__#trigger(frame: FrameType, prim: int): bool;

// State-independent trigger function
function  __prim__int___box__#triggerStateless(prim: int): Ref;

// Check contract well-formedness and postcondition
procedure __prim__int___box__#definedness(prim: int) returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 15;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume (typeof(Result): PyTypeDomainType) == vint;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of int___unbox__(result) == prim
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(result), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@472.11--472.32) [2234]"}
          (issubtype((typeof(Result): PyTypeDomainType), vint): bool);
        // Stop execution
        assume false;
      }
    assume int___unbox__(Heap, Result) == prim;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function int___unbox__
// ==================================================

// Uninterpreted function definitions
function  int___unbox__(Heap: HeapType, box: Ref): int;
function  int___unbox__'(Heap: HeapType, box: Ref): int;
axiom (forall Heap: HeapType, box: Ref ::
  { int___unbox__(Heap, box) }
  int___unbox__(Heap, box) == int___unbox__'(Heap, box) && dummyFunction(int___unbox__#triggerStateless(box))
);
axiom (forall Heap: HeapType, box: Ref ::
  { int___unbox__'(Heap, box) }
  dummyFunction(int___unbox__#triggerStateless(box))
);

// Framing axioms
function  int___unbox__#frame(frame: FrameType, box: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, box: Ref ::
  { state(Heap, Mask), int___unbox__'(Heap, box) }
  state(Heap, Mask) ==> int___unbox__'(Heap, box) == int___unbox__#frame(EmptyFrame, box)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, box: Ref ::
  { state(Heap, Mask), int___unbox__'(Heap, box) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || int___unbox__#trigger(EmptyFrame, box)) ==> (issubtype((typeof(box): PyTypeDomainType), vint): bool) ==> !(issubtype((typeof(box): PyTypeDomainType), vbool): bool) ==> __prim__int___box__'(Heap, int___unbox__'(Heap, box)) == box
);
axiom (forall Heap: HeapType, Mask: MaskType, box: Ref ::
  { state(Heap, Mask), int___unbox__'(Heap, box) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || int___unbox__#trigger(EmptyFrame, box)) ==> (issubtype((typeof(box): PyTypeDomainType), vint): bool) ==> (issubtype((typeof(box): PyTypeDomainType), vbool): bool) ==> __prim__bool___box__'(Heap, int___unbox__'(Heap, box) != 0) == box
);

// Trigger function (controlling recursive postconditions)
function  int___unbox__#trigger(frame: FrameType, box: Ref): bool;

// State-independent trigger function
function  int___unbox__#triggerStateless(box: Ref): int;

// Check contract well-formedness and postcondition
procedure int___unbox__#definedness(box: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[box, $allocated];
    assume AssumeFunctionsAbove == 15;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(box): PyTypeDomainType), vint): bool);
    assume state(Heap, Mask);
  
  // -- Checking definedness of postcondition (no body)
    if (!(issubtype((typeof(box): PyTypeDomainType), vbool): bool)) {
      assume state(Heap, Mask);
      
      // -- Check definedness of __prim__int___box__(result) == box
        if (*) {
          // Stop execution
          assume false;
        }
      assume __prim__int___box__(Heap, Result) == box;
    }
    assume state(Heap, Mask);
    if ((issubtype((typeof(box): PyTypeDomainType), vbool): bool)) {
      assume state(Heap, Mask);
      
      // -- Check definedness of __prim__bool___box__(result != 0) == box
        if (*) {
          // Stop execution
          assume false;
        }
      assume __prim__bool___box__(Heap, Result != 0) == box;
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function __prim__bool___box__
// ==================================================

// Uninterpreted function definitions
function  __prim__bool___box__(Heap: HeapType, prim: bool): Ref;
function  __prim__bool___box__'(Heap: HeapType, prim: bool): Ref;
axiom (forall Heap: HeapType, prim: bool ::
  { __prim__bool___box__(Heap, prim) }
  __prim__bool___box__(Heap, prim) == __prim__bool___box__'(Heap, prim) && dummyFunction(__prim__bool___box__#triggerStateless(prim))
);
axiom (forall Heap: HeapType, prim: bool ::
  { __prim__bool___box__'(Heap, prim) }
  dummyFunction(__prim__bool___box__#triggerStateless(prim))
);

// Framing axioms
function  __prim__bool___box__#frame(frame: FrameType, prim: bool): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, prim: bool ::
  { state(Heap, Mask), __prim__bool___box__'(Heap, prim) }
  state(Heap, Mask) ==> __prim__bool___box__'(Heap, prim) == __prim__bool___box__#frame(EmptyFrame, prim)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, prim: bool ::
  { state(Heap, Mask), __prim__bool___box__'(Heap, prim) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || __prim__bool___box__#trigger(EmptyFrame, prim)) ==> (typeof(__prim__bool___box__'(Heap, prim)): PyTypeDomainType) == vbool
);
axiom (forall Heap: HeapType, Mask: MaskType, prim: bool ::
  { state(Heap, Mask), __prim__bool___box__'(Heap, prim) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || __prim__bool___box__#trigger(EmptyFrame, prim)) ==> bool___unbox__'(Heap, __prim__bool___box__'(Heap, prim)) == prim
);
axiom (forall Heap: HeapType, Mask: MaskType, prim: bool ::
  { state(Heap, Mask), __prim__bool___box__'(Heap, prim) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || __prim__bool___box__#trigger(EmptyFrame, prim)) ==> int___unbox__'(Heap, __prim__bool___box__'(Heap, prim)) == (if prim then 1 else 0)
);

// Trigger function (controlling recursive postconditions)
function  __prim__bool___box__#trigger(frame: FrameType, prim: bool): bool;

// State-independent trigger function
function  __prim__bool___box__#triggerStateless(prim: bool): Ref;

// Check contract well-formedness and postcondition
procedure __prim__bool___box__#definedness(prim: bool) returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 15;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume (typeof(Result): PyTypeDomainType) == vbool;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of bool___unbox__(result) == prim
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function bool___unbox__ might not hold. Assertion issubtype(typeof(result), bool()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@483.11--483.33) [2235]"}
          (issubtype((typeof(Result): PyTypeDomainType), vbool): bool);
        // Stop execution
        assume false;
      }
    assume bool___unbox__(Heap, Result) == prim;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of int___unbox__(result) == (prim ? 1 : 0)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(result), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@484.11--484.32) [2236]"}
          (issubtype((typeof(Result): PyTypeDomainType), vint): bool);
        // Stop execution
        assume false;
      }
    assume int___unbox__(Heap, Result) == (if prim then 1 else 0);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function bool___unbox__
// ==================================================

// Uninterpreted function definitions
function  bool___unbox__(Heap: HeapType, box: Ref): bool;
function  bool___unbox__'(Heap: HeapType, box: Ref): bool;
axiom (forall Heap: HeapType, box: Ref ::
  { bool___unbox__(Heap, box) }
  bool___unbox__(Heap, box) == bool___unbox__'(Heap, box) && dummyFunction(bool___unbox__#triggerStateless(box))
);
axiom (forall Heap: HeapType, box: Ref ::
  { bool___unbox__'(Heap, box) }
  dummyFunction(bool___unbox__#triggerStateless(box))
);

// Framing axioms
function  bool___unbox__#frame(frame: FrameType, box: Ref): bool;
axiom (forall Heap: HeapType, Mask: MaskType, box: Ref ::
  { state(Heap, Mask), bool___unbox__'(Heap, box) }
  state(Heap, Mask) ==> bool___unbox__'(Heap, box) == bool___unbox__#frame(EmptyFrame, box)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, box: Ref ::
  { state(Heap, Mask), bool___unbox__'(Heap, box) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 15 || bool___unbox__#trigger(EmptyFrame, box)) ==> (issubtype((typeof(box): PyTypeDomainType), vbool): bool) ==> __prim__bool___box__'(Heap, bool___unbox__'(Heap, box)) == box
);

// Trigger function (controlling recursive postconditions)
function  bool___unbox__#trigger(frame: FrameType, box: Ref): bool;

// State-independent trigger function
function  bool___unbox__#triggerStateless(box: Ref): bool;

// Check contract well-formedness and postcondition
procedure bool___unbox__#definedness(box: Ref) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[box, $allocated];
    assume AssumeFunctionsAbove == 15;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(box): PyTypeDomainType), vbool): bool);
    assume state(Heap, Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume state(Heap, Mask);
    
    // -- Check definedness of __prim__bool___box__(result) == box
      if (*) {
        // Stop execution
        assume false;
      }
    assume __prim__bool___box__(Heap, Result) == box;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function int___eq__
// ==================================================

// Uninterpreted function definitions
function  int___eq__(Heap: HeapType, self: Ref, other: Ref): bool;
function  int___eq__'(Heap: HeapType, self: Ref, other: Ref): bool;
axiom (forall Heap: HeapType, self: Ref, other: Ref ::
  { int___eq__(Heap, self, other) }
  int___eq__(Heap, self, other) == int___eq__'(Heap, self, other) && dummyFunction(int___eq__#triggerStateless(self, other))
);
axiom (forall Heap: HeapType, self: Ref, other: Ref ::
  { int___eq__'(Heap, self, other) }
  dummyFunction(int___eq__#triggerStateless(self, other))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, other: Ref ::
  { state(Heap, Mask), int___eq__(Heap, self, other) }
  state(Heap, Mask) && AssumeFunctionsAbove < 1 ==> (issubtype((typeof(self): PyTypeDomainType), vint): bool) && (issubtype((typeof(other): PyTypeDomainType), vint): bool) ==> int___eq__(Heap, self, other) == (int___unbox__(Heap, self) == int___unbox__(Heap, other))
);

// Framing axioms
function  int___eq__#frame(frame: FrameType, self: Ref, other: Ref): bool;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, other: Ref ::
  { state(Heap, Mask), int___eq__'(Heap, self, other) }
  state(Heap, Mask) ==> int___eq__'(Heap, self, other) == int___eq__#frame(EmptyFrame, self, other)
);

// Trigger function (controlling recursive postconditions)
function  int___eq__#trigger(frame: FrameType, self: Ref, other: Ref): bool;

// State-independent trigger function
function  int___eq__#triggerStateless(self: Ref, other: Ref): bool;

// Check contract well-formedness and postcondition
procedure int___eq__#definedness(self: Ref, other: Ref) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume Heap[other, $allocated];
    assume AssumeFunctionsAbove == 1;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(self): PyTypeDomainType), vint): bool);
    assume state(Heap, Mask);
    assume (issubtype((typeof(other): PyTypeDomainType), vint): bool);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of int___unbox__(self) == int___unbox__(other)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(self), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@496.3--496.22) [2237]"}
          (issubtype((typeof(self): PyTypeDomainType), vint): bool);
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(other), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@496.26--496.46) [2238]"}
          (issubtype((typeof(other): PyTypeDomainType), vint): bool);
        // Stop execution
        assume false;
      }
  
  // -- Translate function body
    Result := int___unbox__(Heap, self) == int___unbox__(Heap, other);
}

// ==================================================
// Translation of function int___gt__
// ==================================================

// Uninterpreted function definitions
function  int___gt__(Heap: HeapType, self: int, other: int): bool;
function  int___gt__'(Heap: HeapType, self: int, other: int): bool;
axiom (forall Heap: HeapType, self: int, other: int ::
  { int___gt__(Heap, self, other) }
  int___gt__(Heap, self, other) == int___gt__'(Heap, self, other) && dummyFunction(int___gt__#triggerStateless(self, other))
);
axiom (forall Heap: HeapType, self: int, other: int ::
  { int___gt__'(Heap, self, other) }
  dummyFunction(int___gt__#triggerStateless(self, other))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, self: int, other: int ::
  { state(Heap, Mask), int___gt__(Heap, self, other) }
  state(Heap, Mask) && AssumeFunctionsAbove < 4 ==> int___gt__(Heap, self, other) == (self > other)
);

// Framing axioms
function  int___gt__#frame(frame: FrameType, self: int, other: int): bool;
axiom (forall Heap: HeapType, Mask: MaskType, self: int, other: int ::
  { state(Heap, Mask), int___gt__'(Heap, self, other) }
  state(Heap, Mask) ==> int___gt__'(Heap, self, other) == int___gt__#frame(EmptyFrame, self, other)
);

// Trigger function (controlling recursive postconditions)
function  int___gt__#trigger(frame: FrameType, self: int, other: int): bool;

// State-independent trigger function
function  int___gt__#triggerStateless(self: int, other: int): bool;

// Check contract well-formedness and postcondition
procedure int___gt__#definedness(self: int, other: int) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 4;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Translate function body
    Result := self > other;
}

// ==================================================
// Translation of function int___sub__
// ==================================================

// Uninterpreted function definitions
function  int___sub__(Heap: HeapType, self: int, other: int): int;
function  int___sub__'(Heap: HeapType, self: int, other: int): int;
axiom (forall Heap: HeapType, self: int, other: int ::
  { int___sub__(Heap, self, other) }
  int___sub__(Heap, self, other) == int___sub__'(Heap, self, other) && dummyFunction(int___sub__#triggerStateless(self, other))
);
axiom (forall Heap: HeapType, self: int, other: int ::
  { int___sub__'(Heap, self, other) }
  dummyFunction(int___sub__#triggerStateless(self, other))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, self: int, other: int ::
  { state(Heap, Mask), int___sub__(Heap, self, other) }
  state(Heap, Mask) && AssumeFunctionsAbove < 3 ==> int___sub__(Heap, self, other) == self - other
);

// Framing axioms
function  int___sub__#frame(frame: FrameType, self: int, other: int): int;
axiom (forall Heap: HeapType, Mask: MaskType, self: int, other: int ::
  { state(Heap, Mask), int___sub__'(Heap, self, other) }
  state(Heap, Mask) ==> int___sub__'(Heap, self, other) == int___sub__#frame(EmptyFrame, self, other)
);

// Trigger function (controlling recursive postconditions)
function  int___sub__#trigger(frame: FrameType, self: int, other: int): bool;

// State-independent trigger function
function  int___sub__#triggerStateless(self: int, other: int): int;

// Check contract well-formedness and postcondition
procedure int___sub__#definedness(self: int, other: int) returns (Result: int)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 3;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Translate function body
    Result := self - other;
}

// ==================================================
// Translation of function list___len__
// ==================================================

// Uninterpreted function definitions
function  list___len__(Heap: HeapType, self: Ref): int;
function  list___len__'(Heap: HeapType, self: Ref): int;
axiom (forall Heap: HeapType, self: Ref ::
  { list___len__(Heap, self) }
  list___len__(Heap, self) == list___len__'(Heap, self) && dummyFunction(list___len__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { list___len__'(Heap, self) }
  dummyFunction(list___len__#triggerStateless(self))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), list___len__(Heap, self) }
  state(Heap, Mask) && AssumeFunctionsAbove < 12 ==> (issubtype((typeof(self): PyTypeDomainType), (list((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool) ==> list___len__(Heap, self) == Seq#Length(Heap[self, list_acc])
);

// Framing axioms
function  list___len__#frame(frame: FrameType, self: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), list___len__'(Heap, self) }
  state(Heap, Mask) ==> list___len__'(Heap, self) == list___len__#frame(FrameFragment(Heap[self, list_acc]), self)
);

// Trigger function (controlling recursive postconditions)
function  list___len__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  list___len__#triggerStateless(self: Ref): int;

// Check contract well-formedness and postcondition
procedure list___len__#definedness(self: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
  var perm: Perm;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 12;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(self): PyTypeDomainType), (list((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
    assume state(Heap, Mask);
    havoc wildcard;
    perm := wildcard;
    assume self != null;
    Mask[self, list_acc] := Mask[self, list_acc] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of |self.list_acc|
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@509.1--514.2) [2239]"}
        HasDirectPerm(Mask, self, list_acc);
  
  // -- Translate function body
    Result := Seq#Length(Heap[self, list_acc]);
}

// ==================================================
// Translation of function list___sil_seq__
// ==================================================

// Uninterpreted function definitions
function  list___sil_seq__(Heap: HeapType, self: Ref): Seq Ref;
function  list___sil_seq__'(Heap: HeapType, self: Ref): Seq Ref;
axiom (forall Heap: HeapType, self: Ref ::
  { list___sil_seq__(Heap, self) }
  list___sil_seq__(Heap, self) == list___sil_seq__'(Heap, self) && dummyFunction(list___sil_seq__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { list___sil_seq__'(Heap, self) }
  dummyFunction(list___sil_seq__#triggerStateless(self))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), list___sil_seq__(Heap, self) }
  state(Heap, Mask) && AssumeFunctionsAbove < 11 ==> list___sil_seq__(Heap, self) == Heap[self, list_acc]
);

// Framing axioms
function  list___sil_seq__#frame(frame: FrameType, self: Ref): Seq Ref;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), list___sil_seq__'(Heap, self) }
  state(Heap, Mask) ==> list___sil_seq__'(Heap, self) == list___sil_seq__#frame(FrameFragment(Heap[self, list_acc]), self)
);

// Trigger function (controlling recursive postconditions)
function  list___sil_seq__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  list___sil_seq__#triggerStateless(self: Ref): Seq Ref;

// Check contract well-formedness and postcondition
procedure list___sil_seq__#definedness(self: Ref) returns (Result: (Seq Ref))
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
  var perm: Perm;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 11;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    havoc wildcard;
    perm := wildcard;
    assume self != null;
    Mask[self, list_acc] := Mask[self, list_acc] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of self.list_acc
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@516.1--520.2) [2240]"}
        HasDirectPerm(Mask, self, list_acc);
  
  // -- Translate function body
    Result := Heap[self, list_acc];
}

// ==================================================
// Translation of function Level
// ==================================================

// Uninterpreted function definitions
function  Level(Heap: HeapType, r_1: Ref): Perm;
function  Level'(Heap: HeapType, r_1: Ref): Perm;
axiom (forall Heap: HeapType, r_1: Ref ::
  { Level(Heap, r_1) }
  Level(Heap, r_1) == Level'(Heap, r_1) && dummyFunction(Level#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { Level'(Heap, r_1) }
  dummyFunction(Level#triggerStateless(r_1))
);

// Framing axioms
function  Level#frame(frame: FrameType, r_1: Ref): Perm;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), Level'(Heap, r_1) }
  state(Heap, Mask) ==> Level'(Heap, r_1) == Level#frame(EmptyFrame, r_1)
);

// Trigger function (controlling recursive postconditions)
function  Level#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  Level#triggerStateless(r_1: Ref): Perm;

// Check contract well-formedness and postcondition
procedure Level#definedness(r_1: Ref) returns (Result: Perm)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 14;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function Measure$check
// ==================================================

// Uninterpreted function definitions
function  Measure$check(Heap: HeapType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int): bool;
function  Measure$check'(Heap: HeapType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int): bool;
axiom (forall Heap: HeapType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int ::
  { Measure$check(Heap, vmap, key_1, value_1) }
  Measure$check(Heap, vmap, key_1, value_1) == Measure$check'(Heap, vmap, key_1, value_1) && dummyFunction(Measure$check#triggerStateless(vmap, key_1, value_1))
);
axiom (forall Heap: HeapType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int ::
  { Measure$check'(Heap, vmap, key_1, value_1) }
  dummyFunction(Measure$check#triggerStateless(vmap, key_1, value_1))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int ::
  { state(Heap, Mask), Measure$check(Heap, vmap, key_1, value_1) }
  state(Heap, Mask) && AssumeFunctionsAbove < 6 ==> Measure$check(Heap, vmap, key_1, value_1) == (forall m_1: Measure$DomainType ::
    { Seq#ContainsTrigger(vmap, m_1) } { Seq#Contains(vmap, m_1) }
    Seq#Contains(vmap, m_1) ==> (Measure$guard(m_1): bool) && (Measure$key(m_1): Ref) == key_1 ==> (Measure$value(m_1): int) > value_1
  )
);

// Framing axioms
function  Measure$check#frame(frame: FrameType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int): bool;
axiom (forall Heap: HeapType, Mask: MaskType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int ::
  { state(Heap, Mask), Measure$check'(Heap, vmap, key_1, value_1) }
  state(Heap, Mask) ==> Measure$check'(Heap, vmap, key_1, value_1) == Measure$check#frame(EmptyFrame, vmap, key_1, value_1)
);

// Trigger function (controlling recursive postconditions)
function  Measure$check#trigger(frame: FrameType, vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int): bool;

// State-independent trigger function
function  Measure$check#triggerStateless(vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int): bool;

// Check contract well-formedness and postcondition
procedure Measure$check#definedness(vmap: (Seq Measure$DomainType), key_1: Ref, value_1: int) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[key_1, $allocated];
    assume AssumeFunctionsAbove == 6;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of (forall m: Measure$ :: { (m in map) } (m in map) ==> Measure$guard(m) && Measure$key(m) == key ==> Measure$value(m) > value)
      if (*) {
        assume false;
      }
  
  // -- Translate function body
    Result := (forall m_2: Measure$DomainType ::
      { Seq#ContainsTrigger(vmap, m_2) } { Seq#Contains(vmap, m_2) }
      Seq#Contains(vmap, m_2) ==> (Measure$guard(m_2): bool) && (Measure$key(m_2): Ref) == key_1 ==> (Measure$value(m_2): int) > value_1
    );
}

// ==================================================
// Translation of function PSeq___create__
// ==================================================

// Uninterpreted function definitions
function  PSeq___create__(Heap: HeapType, prim: (Seq Ref), cont_type: PyTypeDomainType): Ref;
function  PSeq___create__'(Heap: HeapType, prim: (Seq Ref), cont_type: PyTypeDomainType): Ref;
axiom (forall Heap: HeapType, prim: (Seq Ref), cont_type: PyTypeDomainType ::
  { PSeq___create__(Heap, prim, cont_type) }
  PSeq___create__(Heap, prim, cont_type) == PSeq___create__'(Heap, prim, cont_type) && dummyFunction(PSeq___create__#triggerStateless(prim, cont_type))
);
axiom (forall Heap: HeapType, prim: (Seq Ref), cont_type: PyTypeDomainType ::
  { PSeq___create__'(Heap, prim, cont_type) }
  dummyFunction(PSeq___create__#triggerStateless(prim, cont_type))
);

// Framing axioms
function  PSeq___create__#frame(frame: FrameType, prim: (Seq Ref), cont_type: PyTypeDomainType): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, prim: (Seq Ref), cont_type: PyTypeDomainType ::
  { state(Heap, Mask), PSeq___create__'(Heap, prim, cont_type) }
  state(Heap, Mask) ==> PSeq___create__'(Heap, prim, cont_type) == PSeq___create__#frame(EmptyFrame, prim, cont_type)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, prim: (Seq Ref), cont_type: PyTypeDomainType ::
  { state(Heap, Mask), PSeq___create__'(Heap, prim, cont_type) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 8 || PSeq___create__#trigger(EmptyFrame, prim, cont_type)) ==> (typeof(PSeq___create__'(Heap, prim, cont_type)): PyTypeDomainType) == (PSeq(cont_type): PyTypeDomainType)
);
axiom (forall Heap: HeapType, Mask: MaskType, prim: (Seq Ref), cont_type: PyTypeDomainType ::
  { state(Heap, Mask), PSeq___create__'(Heap, prim, cont_type) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 8 || PSeq___create__#trigger(EmptyFrame, prim, cont_type)) ==> Seq#Equal(PSeq___sil_seq__(Heap, PSeq___create__'(Heap, prim, cont_type)), prim)
);

// Trigger function (controlling recursive postconditions)
function  PSeq___create__#trigger(frame: FrameType, prim: (Seq Ref), cont_type: PyTypeDomainType): bool;

// State-independent trigger function
function  PSeq___create__#triggerStateless(prim: (Seq Ref), cont_type: PyTypeDomainType): Ref;

// Check contract well-formedness and postcondition
procedure PSeq___create__#definedness(prim: (Seq Ref), cont_type: PyTypeDomainType) returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 8;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume (typeof(Result): PyTypeDomainType) == (PSeq(cont_type): PyTypeDomainType);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of PSeq___sil_seq__(result) == prim
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function PSeq___sil_seq__ might not hold. Assertion issubtype(typeof(result), PSeq(PSeq_arg(typeof(result), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@532.11--532.35) [2241]"}
          (issubtype((typeof(Result): PyTypeDomainType), (PSeq((PSeq_arg((typeof(Result): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
        // Stop execution
        assume false;
      }
    assume Seq#Equal(PSeq___sil_seq__(Heap, Result), prim);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function PSeq___sil_seq__
// ==================================================

// Uninterpreted function definitions
function  PSeq___sil_seq__(Heap: HeapType, box: Ref): Seq Ref;
function  PSeq___sil_seq__'(Heap: HeapType, box: Ref): Seq Ref;
axiom (forall Heap: HeapType, box: Ref ::
  { PSeq___sil_seq__(Heap, box) }
  PSeq___sil_seq__(Heap, box) == PSeq___sil_seq__'(Heap, box) && dummyFunction(PSeq___sil_seq__#triggerStateless(box))
);
axiom (forall Heap: HeapType, box: Ref ::
  { PSeq___sil_seq__'(Heap, box) }
  dummyFunction(PSeq___sil_seq__#triggerStateless(box))
);

// Framing axioms
function  PSeq___sil_seq__#frame(frame: FrameType, box: Ref): Seq Ref;
axiom (forall Heap: HeapType, Mask: MaskType, box: Ref ::
  { state(Heap, Mask), PSeq___sil_seq__'(Heap, box) }
  state(Heap, Mask) ==> PSeq___sil_seq__'(Heap, box) == PSeq___sil_seq__#frame(EmptyFrame, box)
);

// Trigger function (controlling recursive postconditions)
function  PSeq___sil_seq__#trigger(frame: FrameType, box: Ref): bool;

// State-independent trigger function
function  PSeq___sil_seq__#triggerStateless(box: Ref): Seq Ref;

// Check contract well-formedness and postcondition
procedure PSeq___sil_seq__#definedness(box: Ref) returns (Result: (Seq Ref))
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[box, $allocated];
    assume AssumeFunctionsAbove == 17;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(box): PyTypeDomainType), (PSeq((PSeq_arg((typeof(box): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function PSeq___len__
// ==================================================

// Uninterpreted function definitions
function  PSeq___len__(Heap: HeapType, self: Ref): int;
function  PSeq___len__'(Heap: HeapType, self: Ref): int;
axiom (forall Heap: HeapType, self: Ref ::
  { PSeq___len__(Heap, self) }
  PSeq___len__(Heap, self) == PSeq___len__'(Heap, self) && dummyFunction(PSeq___len__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { PSeq___len__'(Heap, self) }
  dummyFunction(PSeq___len__#triggerStateless(self))
);

// Framing axioms
function  PSeq___len__#frame(frame: FrameType, self: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), PSeq___len__'(Heap, self) }
  state(Heap, Mask) ==> PSeq___len__'(Heap, self) == PSeq___len__#frame(EmptyFrame, self)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), PSeq___len__'(Heap, self) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 2 || PSeq___len__#trigger(EmptyFrame, self)) ==> (issubtype((typeof(self): PyTypeDomainType), (PSeq((PSeq_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool) ==> PSeq___len__'(Heap, self) == Seq#Length(PSeq___sil_seq__(Heap, self))
);

// Trigger function (controlling recursive postconditions)
function  PSeq___len__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  PSeq___len__#triggerStateless(self: Ref): int;

// Check contract well-formedness and postcondition
procedure PSeq___len__#definedness(self: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 2;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(self): PyTypeDomainType), (PSeq((PSeq_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
    assume state(Heap, Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume state(Heap, Mask);
    
    // -- Check definedness of result == |PSeq___sil_seq__(self)|
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function PSeq___sil_seq__ might not hold. Assertion issubtype(typeof(self), PSeq(PSeq_arg(typeof(self), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@541.22--541.44) [2242]"}
          (issubtype((typeof(self): PyTypeDomainType), (PSeq((PSeq_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
        // Stop execution
        assume false;
      }
    assume Result == Seq#Length(PSeq___sil_seq__(Heap, self));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function str___len__
// ==================================================

// Uninterpreted function definitions
function  str___len__(Heap: HeapType, self: Ref): int;
function  str___len__'(Heap: HeapType, self: Ref): int;
axiom (forall Heap: HeapType, self: Ref ::
  { str___len__(Heap, self) }
  str___len__(Heap, self) == str___len__'(Heap, self) && dummyFunction(str___len__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { str___len__'(Heap, self) }
  dummyFunction(str___len__#triggerStateless(self))
);

// Framing axioms
function  str___len__#frame(frame: FrameType, self: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), str___len__'(Heap, self) }
  state(Heap, Mask) ==> str___len__'(Heap, self) == str___len__#frame(EmptyFrame, self)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), str___len__'(Heap, self) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 19 || str___len__#trigger(EmptyFrame, self)) ==> str___len__'(Heap, self) >= 0
);

// Trigger function (controlling recursive postconditions)
function  str___len__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  str___len__#triggerStateless(self: Ref): int;

// Check contract well-formedness and postcondition
procedure str___len__#definedness(self: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 19;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume Result >= 0;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function str___val__
// ==================================================

// Uninterpreted function definitions
function  str___val__(Heap: HeapType, self: Ref): int;
function  str___val__'(Heap: HeapType, self: Ref): int;
axiom (forall Heap: HeapType, self: Ref ::
  { str___val__(Heap, self) }
  str___val__(Heap, self) == str___val__'(Heap, self) && dummyFunction(str___val__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { str___val__'(Heap, self) }
  dummyFunction(str___val__#triggerStateless(self))
);

// Framing axioms
function  str___val__#frame(frame: FrameType, self: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), str___val__'(Heap, self) }
  state(Heap, Mask) ==> str___val__'(Heap, self) == str___val__#frame(EmptyFrame, self)
);

// Trigger function (controlling recursive postconditions)
function  str___val__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  str___val__#triggerStateless(self: Ref): int;

// Check contract well-formedness and postcondition
procedure str___val__#definedness(self: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 20;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function str___create__
// ==================================================

// Uninterpreted function definitions
function  str___create__(Heap: HeapType, len: int, value_1: int): Ref;
function  str___create__'(Heap: HeapType, len: int, value_1: int): Ref;
axiom (forall Heap: HeapType, len: int, value_1: int ::
  { str___create__(Heap, len, value_1) }
  str___create__(Heap, len, value_1) == str___create__'(Heap, len, value_1) && dummyFunction(str___create__#triggerStateless(len, value_1))
);
axiom (forall Heap: HeapType, len: int, value_1: int ::
  { str___create__'(Heap, len, value_1) }
  dummyFunction(str___create__#triggerStateless(len, value_1))
);

// Framing axioms
function  str___create__#frame(frame: FrameType, len: int, value_1: int): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, len: int, value_1: int ::
  { state(Heap, Mask), str___create__'(Heap, len, value_1) }
  state(Heap, Mask) ==> str___create__'(Heap, len, value_1) == str___create__#frame(EmptyFrame, len, value_1)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, len: int, value_1: int ::
  { state(Heap, Mask), str___create__'(Heap, len, value_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 13 || str___create__#trigger(EmptyFrame, len, value_1)) ==> str___len__(Heap, str___create__'(Heap, len, value_1)) == len
);
axiom (forall Heap: HeapType, Mask: MaskType, len: int, value_1: int ::
  { state(Heap, Mask), str___create__'(Heap, len, value_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 13 || str___create__#trigger(EmptyFrame, len, value_1)) ==> str___val__(Heap, str___create__'(Heap, len, value_1)) == value_1
);
axiom (forall Heap: HeapType, Mask: MaskType, len: int, value_1: int ::
  { state(Heap, Mask), str___create__'(Heap, len, value_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 13 || str___create__#trigger(EmptyFrame, len, value_1)) ==> (typeof(str___create__'(Heap, len, value_1)): PyTypeDomainType) == str
);

// Trigger function (controlling recursive postconditions)
function  str___create__#trigger(frame: FrameType, len: int, value_1: int): bool;

// State-independent trigger function
function  str___create__#triggerStateless(len: int, value_1: int): Ref;

// Check contract well-formedness and postcondition
procedure str___create__#definedness(len: int, value_1: int) returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 13;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume state(Heap, Mask);
    
    // -- Check definedness of str___len__(result) == len
      if (*) {
        // Stop execution
        assume false;
      }
    assume str___len__(Heap, Result) == len;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of str___val__(result) == value
      if (*) {
        // Stop execution
        assume false;
      }
    assume str___val__(Heap, Result) == value_1;
    assume state(Heap, Mask);
    assume (typeof(Result): PyTypeDomainType) == str;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function str___eq__
// ==================================================

// Uninterpreted function definitions
function  str___eq__(Heap: HeapType, self: Ref, other: Ref): bool;
function  str___eq__'(Heap: HeapType, self: Ref, other: Ref): bool;
axiom (forall Heap: HeapType, self: Ref, other: Ref ::
  { str___eq__(Heap, self, other) }
  str___eq__(Heap, self, other) == str___eq__'(Heap, self, other) && dummyFunction(str___eq__#triggerStateless(self, other))
);
axiom (forall Heap: HeapType, self: Ref, other: Ref ::
  { str___eq__'(Heap, self, other) }
  dummyFunction(str___eq__#triggerStateless(self, other))
);

// Framing axioms
function  str___eq__#frame(frame: FrameType, self: Ref, other: Ref): bool;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, other: Ref ::
  { state(Heap, Mask), str___eq__'(Heap, self, other) }
  state(Heap, Mask) ==> str___eq__'(Heap, self, other) == str___eq__#frame(EmptyFrame, self, other)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, other: Ref ::
  { state(Heap, Mask), str___eq__'(Heap, self, other) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 5 || str___eq__#trigger(EmptyFrame, self, other)) ==> (issubtype((typeof(self): PyTypeDomainType), str): bool) ==> (str___val__(Heap, self) == str___val__(Heap, other)) == str___eq__'(Heap, self, other)
);
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, other: Ref ::
  { state(Heap, Mask), str___eq__'(Heap, self, other) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 5 || str___eq__#trigger(EmptyFrame, self, other)) ==> (issubtype((typeof(self): PyTypeDomainType), str): bool) ==> str___eq__'(Heap, self, other) ==> str___len__(Heap, self) == str___len__(Heap, other)
);

// Trigger function (controlling recursive postconditions)
function  str___eq__#trigger(frame: FrameType, self: Ref, other: Ref): bool;

// State-independent trigger function
function  str___eq__#triggerStateless(self: Ref, other: Ref): bool;

// Check contract well-formedness and postcondition
procedure str___eq__#definedness(self: Ref, other: Ref) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume Heap[other, $allocated];
    assume AssumeFunctionsAbove == 5;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(self): PyTypeDomainType), str): bool);
    assume state(Heap, Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume state(Heap, Mask);
    
    // -- Check definedness of (str___val__(self) == str___val__(other)) == result
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Stop execution
        assume false;
      }
    assume (str___val__(Heap, self) == str___val__(Heap, other)) == Result;
    assume state(Heap, Mask);
    if (Result) {
      assume state(Heap, Mask);
      
      // -- Check definedness of str___len__(self) == str___len__(other)
        if (*) {
          // Stop execution
          assume false;
        }
        if (*) {
          // Stop execution
          assume false;
        }
      assume str___len__(Heap, self) == str___len__(Heap, other);
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function tuple___val__
// ==================================================

// Uninterpreted function definitions
function  tuple___val__(Heap: HeapType, self: Ref): Seq Ref;
function  tuple___val__'(Heap: HeapType, self: Ref): Seq Ref;
axiom (forall Heap: HeapType, self: Ref ::
  { tuple___val__(Heap, self) }
  tuple___val__(Heap, self) == tuple___val__'(Heap, self) && dummyFunction(tuple___val__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { tuple___val__'(Heap, self) }
  dummyFunction(tuple___val__#triggerStateless(self))
);

// Framing axioms
function  tuple___val__#frame(frame: FrameType, self: Ref): Seq Ref;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), tuple___val__'(Heap, self) }
  state(Heap, Mask) ==> tuple___val__'(Heap, self) == tuple___val__#frame(EmptyFrame, self)
);

// Trigger function (controlling recursive postconditions)
function  tuple___val__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  tuple___val__#triggerStateless(self: Ref): Seq Ref;

// Check contract well-formedness and postcondition
procedure tuple___val__#definedness(self: Ref) returns (Result: (Seq Ref))
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 22;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function tuple___create2__
// ==================================================

// Uninterpreted function definitions
function  tuple___create2__(Heap: HeapType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int): Ref;
function  tuple___create2__'(Heap: HeapType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int): Ref;
axiom (forall Heap: HeapType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { tuple___create2__(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  tuple___create2__(Heap, arg0_1, arg1_1, t0, t1, ctr) == tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) && dummyFunction(tuple___create2__#triggerStateless(arg0_1, arg1_1, t0, t1, ctr))
);
axiom (forall Heap: HeapType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  dummyFunction(tuple___create2__#triggerStateless(arg0_1, arg1_1, t0, t1, ctr))
);

// Framing axioms
function  tuple___create2__#frame(frame: FrameType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) ==> tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) == tuple___create2__#frame(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 7 || tuple___create2__#trigger(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)) ==> (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool) && (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool) ==> tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) != null
);
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 7 || tuple___create2__#trigger(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)) ==> (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool) && (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool) ==> (typeof(tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr)): PyTypeDomainType) == (tuple(Seq#Append(Seq#Singleton(t0), Seq#Singleton(t1))): PyTypeDomainType)
);
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 7 || tuple___create2__#trigger(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)) ==> (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool) && (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool) ==> Seq#Equal((tuple_args((typeof(tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr)): PyTypeDomainType)): Seq PyTypeDomainType), Seq#Append(Seq#Singleton(t0), Seq#Singleton(t1)))
);
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 7 || tuple___create2__#trigger(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)) ==> (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool) && (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool) ==> Seq#Equal((tuple_args((typeof(tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr)): PyTypeDomainType)): Seq PyTypeDomainType), Seq#Append(Seq#Singleton(t0), Seq#Singleton(t1)))
);
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 7 || tuple___create2__#trigger(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)) ==> (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool) && (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool) ==> Seq#Equal(tuple___val__(Heap, tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr)), Seq#Append(Seq#Singleton(arg0_1), Seq#Singleton(arg1_1)))
);
axiom (forall Heap: HeapType, Mask: MaskType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int ::
  { state(Heap, Mask), tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 7 || tuple___create2__#trigger(EmptyFrame, arg0_1, arg1_1, t0, t1, ctr)) ==> (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool) && (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool) ==> tuple___len__(Heap, tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr)) == 2 && (tuple___getitem__(Heap, tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr), 0) == arg0_1 && tuple___getitem__(Heap, tuple___create2__'(Heap, arg0_1, arg1_1, t0, t1, ctr), 1) == arg1_1)
);

// Trigger function (controlling recursive postconditions)
function  tuple___create2__#trigger(frame: FrameType, arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int): bool;

// State-independent trigger function
function  tuple___create2__#triggerStateless(arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int): Ref;

// Check contract well-formedness and postcondition
procedure tuple___create2__#definedness(arg0_1: Ref, arg1_1: Ref, t0: PyTypeDomainType, t1: PyTypeDomainType, ctr: int) returns (Result: Ref)
  modifies Heap, Mask;
{
  var ln_1: int;
  var ln_3: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[arg0_1, $allocated];
    assume Heap[arg1_1, $allocated];
    assume AssumeFunctionsAbove == 7;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    assume (issubtype((typeof(arg0_1): PyTypeDomainType), t0): bool);
    assume state(Heap, Mask);
    assume (issubtype((typeof(arg1_1): PyTypeDomainType), t1): bool);
    assume state(Heap, Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume Result != null;
    assume state(Heap, Mask);
    assume (typeof(Result): PyTypeDomainType) == (tuple(Seq#Append(Seq#Singleton(t0), Seq#Singleton(t1))): PyTypeDomainType);
    assume state(Heap, Mask);
    assume Seq#Equal((tuple_args((typeof(Result): PyTypeDomainType)): Seq PyTypeDomainType), Seq#Append(Seq#Singleton(t0), Seq#Singleton(t1)));
    assume state(Heap, Mask);
    assume Seq#Equal((tuple_args((typeof(Result): PyTypeDomainType)): Seq PyTypeDomainType), Seq#Append(Seq#Singleton(t0), Seq#Singleton(t1)));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of tuple___val__(result) == Seq(arg0, arg1)
      if (*) {
        // Stop execution
        assume false;
      }
    assume Seq#Equal(tuple___val__(Heap, Result), Seq#Append(Seq#Singleton(arg0_1), Seq#Singleton(arg1_1)));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of tuple___len__(result) == 2
      if (*) {
        // Stop execution
        assume false;
      }
    assume tuple___len__(Heap, Result) == 2;
    assume state(Heap, Mask);
    
    // -- Check definedness of tuple___getitem__(result, 0) == arg0
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(result)) in (0 >= 0 ==> 0 < ln) && (0 < 0 ==> 0 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@574.42--574.70) [2243]"}
          0 < tuple___len__(Heap, Result);
        
        // -- Free assumptions (exhale module)
          ln_1 := tuple___len__(Heap, Result);
        // Stop execution
        assume false;
      }
    assume tuple___getitem__(Heap, Result, 0) == arg0_1;
    assume state(Heap, Mask);
    
    // -- Check definedness of tuple___getitem__(result, 1) == arg1
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(result)) in (1 >= 0 ==> 1 < ln) && (1 < 0 ==> 1 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@574.82--574.110) [2244]"}
          1 < tuple___len__(Heap, Result);
        
        // -- Free assumptions (exhale module)
          ln_3 := tuple___len__(Heap, Result);
        // Stop execution
        assume false;
      }
    assume tuple___getitem__(Heap, Result, 1) == arg1_1;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function tuple___len__
// ==================================================

// Uninterpreted function definitions
function  tuple___len__(Heap: HeapType, self: Ref): int;
function  tuple___len__'(Heap: HeapType, self: Ref): int;
axiom (forall Heap: HeapType, self: Ref ::
  { tuple___len__(Heap, self) }
  tuple___len__(Heap, self) == tuple___len__'(Heap, self) && dummyFunction(tuple___len__#triggerStateless(self))
);
axiom (forall Heap: HeapType, self: Ref ::
  { tuple___len__'(Heap, self) }
  dummyFunction(tuple___len__#triggerStateless(self))
);

// Framing axioms
function  tuple___len__#frame(frame: FrameType, self: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), tuple___len__'(Heap, self) }
  state(Heap, Mask) ==> tuple___len__'(Heap, self) == tuple___len__#frame(EmptyFrame, self)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), tuple___len__'(Heap, self) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 21 || tuple___len__#trigger(EmptyFrame, self)) ==> tuple___len__'(Heap, self) == Seq#Length((tuple_args((typeof(self): PyTypeDomainType)): Seq PyTypeDomainType))
);
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref ::
  { state(Heap, Mask), tuple___len__'(Heap, self) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 21 || tuple___len__#trigger(EmptyFrame, self)) ==> tuple___len__'(Heap, self) == Seq#Length(tuple___val__(Heap, self))
);

// Trigger function (controlling recursive postconditions)
function  tuple___len__#trigger(frame: FrameType, self: Ref): bool;

// State-independent trigger function
function  tuple___len__#triggerStateless(self: Ref): int;

// Check contract well-formedness and postcondition
procedure tuple___len__#definedness(self: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 21;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    assume Result == Seq#Length((tuple_args((typeof(self): PyTypeDomainType)): Seq PyTypeDomainType));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of result == |tuple___val__(self)|
      if (*) {
        // Stop execution
        assume false;
      }
    assume Result == Seq#Length(tuple___val__(Heap, self));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function tuple___getitem__
// ==================================================

// Uninterpreted function definitions
function  tuple___getitem__(Heap: HeapType, self: Ref, key_1: int): Ref;
function  tuple___getitem__'(Heap: HeapType, self: Ref, key_1: int): Ref;
axiom (forall Heap: HeapType, self: Ref, key_1: int ::
  { tuple___getitem__(Heap, self, key_1) }
  tuple___getitem__(Heap, self, key_1) == tuple___getitem__'(Heap, self, key_1) && dummyFunction(tuple___getitem__#triggerStateless(self, key_1))
);
axiom (forall Heap: HeapType, self: Ref, key_1: int ::
  { tuple___getitem__'(Heap, self, key_1) }
  dummyFunction(tuple___getitem__#triggerStateless(self, key_1))
);

// Framing axioms
function  tuple___getitem__#frame(frame: FrameType, self: Ref, key_1: int): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, key_1: int ::
  { state(Heap, Mask), tuple___getitem__'(Heap, self, key_1) }
  state(Heap, Mask) ==> tuple___getitem__'(Heap, self, key_1) == tuple___getitem__#frame(CombineFrames(FrameFragment((if key_1 >= 0 then EmptyFrame else EmptyFrame)), FrameFragment((if key_1 < 0 then EmptyFrame else EmptyFrame))), self, key_1)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, key_1: int ::
  { state(Heap, Mask), tuple___getitem__'(Heap, self, key_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 16 || tuple___getitem__#trigger(CombineFrames(FrameFragment((if key_1 >= 0 then EmptyFrame else EmptyFrame)), FrameFragment((if key_1 < 0 then EmptyFrame else EmptyFrame))), self, key_1)) ==> (key_1 >= 0 ==> key_1 < tuple___len__(Heap, self)) && (key_1 < 0 ==> key_1 >= -tuple___len__(Heap, self)) ==> key_1 >= 0 ==> (issubtype((typeof(tuple___getitem__'(Heap, self, key_1)): PyTypeDomainType), (tuple_arg((typeof(self): PyTypeDomainType), key_1): PyTypeDomainType)): bool)
);
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, key_1: int ::
  { state(Heap, Mask), tuple___getitem__'(Heap, self, key_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 16 || tuple___getitem__#trigger(CombineFrames(FrameFragment((if key_1 >= 0 then EmptyFrame else EmptyFrame)), FrameFragment((if key_1 < 0 then EmptyFrame else EmptyFrame))), self, key_1)) ==> (key_1 >= 0 ==> key_1 < tuple___len__(Heap, self)) && (key_1 < 0 ==> key_1 >= -tuple___len__(Heap, self)) ==> key_1 < 0 ==> (issubtype((typeof(tuple___getitem__'(Heap, self, key_1)): PyTypeDomainType), (tuple_arg((typeof(self): PyTypeDomainType), tuple___len__(Heap, self) + key_1): PyTypeDomainType)): bool)
);
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, key_1: int ::
  { state(Heap, Mask), tuple___getitem__'(Heap, self, key_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 16 || tuple___getitem__#trigger(CombineFrames(FrameFragment((if key_1 >= 0 then EmptyFrame else EmptyFrame)), FrameFragment((if key_1 < 0 then EmptyFrame else EmptyFrame))), self, key_1)) ==> (key_1 >= 0 ==> key_1 < tuple___len__(Heap, self)) && (key_1 < 0 ==> key_1 >= -tuple___len__(Heap, self)) ==> key_1 >= 0 ==> tuple___getitem__'(Heap, self, key_1) == Seq#Index(tuple___val__(Heap, self), key_1)
);
axiom (forall Heap: HeapType, Mask: MaskType, self: Ref, key_1: int ::
  { state(Heap, Mask), tuple___getitem__'(Heap, self, key_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 16 || tuple___getitem__#trigger(CombineFrames(FrameFragment((if key_1 >= 0 then EmptyFrame else EmptyFrame)), FrameFragment((if key_1 < 0 then EmptyFrame else EmptyFrame))), self, key_1)) ==> (key_1 >= 0 ==> key_1 < tuple___len__(Heap, self)) && (key_1 < 0 ==> key_1 >= -tuple___len__(Heap, self)) ==> key_1 < 0 ==> tuple___getitem__'(Heap, self, key_1) == Seq#Index(tuple___val__(Heap, self), tuple___len__(Heap, self) + key_1)
);

// Trigger function (controlling recursive postconditions)
function  tuple___getitem__#trigger(frame: FrameType, self: Ref, key_1: int): bool;

// State-independent trigger function
function  tuple___getitem__#triggerStateless(self: Ref, key_1: int): Ref;

// Check contract well-formedness and postcondition
procedure tuple___getitem__#definedness(self: Ref, key_1: int) returns (Result: Ref)
  modifies Heap, Mask;
{
  var ln_1: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[self, $allocated];
    assume AssumeFunctionsAbove == 16;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    
    // -- Check definedness of tuple___len__(self)
      if (*) {
        // Stop execution
        assume false;
      }
    ln_1 := tuple___len__(Heap, self);
    if (key_1 >= 0) {
      assume key_1 < ln_1;
    }
    if (key_1 < 0) {
      assume key_1 >= -ln_1;
    }
    assume state(Heap, Mask);
  
  // -- Checking definedness of postcondition (no body)
    if (key_1 >= 0) {
      assume (issubtype((typeof(Result): PyTypeDomainType), (tuple_arg((typeof(self): PyTypeDomainType), key_1): PyTypeDomainType)): bool);
    }
    assume state(Heap, Mask);
    if (key_1 < 0) {
      assume state(Heap, Mask);
      
      // -- Check definedness of issubtype(typeof(result), tuple_arg(typeof(self), tuple___len__(self) + key))
        if (*) {
          // Stop execution
          assume false;
        }
      assume (issubtype((typeof(Result): PyTypeDomainType), (tuple_arg((typeof(self): PyTypeDomainType), tuple___len__(Heap, self) + key_1): PyTypeDomainType)): bool);
    }
    assume state(Heap, Mask);
    if (key_1 >= 0) {
      assume state(Heap, Mask);
      
      // -- Check definedness of result == tuple___val__(self)[key]
        if (*) {
          // Stop execution
          assume false;
        }
        assert {:msg "  Contract might not be well-formed. Index tuple___val__(self)[key] into tuple___val__(self) might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@586.11--586.58) [2245]"}
          key_1 >= 0;
        assert {:msg "  Contract might not be well-formed. Index tuple___val__(self)[key] into tuple___val__(self) might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@586.11--586.58) [2246]"}
          key_1 < Seq#Length(tuple___val__(Heap, self));
      assume Result == Seq#Index(tuple___val__(Heap, self), key_1);
    }
    assume state(Heap, Mask);
    if (key_1 < 0) {
      assume state(Heap, Mask);
      
      // -- Check definedness of result == tuple___val__(self)[tuple___len__(self) + key]
        if (*) {
          // Stop execution
          assume false;
        }
        if (*) {
          // Stop execution
          assume false;
        }
        assert {:msg "  Contract might not be well-formed. Index tuple___val__(self)[tuple___len__(self) + key] into tuple___val__(self) might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@587.11--587.79) [2247]"}
          tuple___len__(Heap, self) + key_1 >= 0;
        assert {:msg "  Contract might not be well-formed. Index tuple___val__(self)[tuple___len__(self) + key] into tuple___val__(self) might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@587.11--587.79) [2248]"}
          tuple___len__(Heap, self) + key_1 < Seq#Length(tuple___val__(Heap, self));
      assume Result == Seq#Index(tuple___val__(Heap, self), tuple___len__(Heap, self) + key_1);
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of predicate MustTerminate
// ==================================================

type PredicateType_MustTerminate;
function  MustTerminate(r_1: Ref): Field PredicateType_MustTerminate FrameType;
function  MustTerminate#sm(r_1: Ref): Field PredicateType_MustTerminate PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(MustTerminate(r_1)) }
  PredicateMaskField(MustTerminate(r_1)) == MustTerminate#sm(r_1)
);
axiom (forall r_1: Ref ::
  { MustTerminate(r_1) }
  IsPredicateField(MustTerminate(r_1))
);
axiom (forall r_1: Ref ::
  { MustTerminate(r_1) }
  getPredicateId(MustTerminate(r_1)) == 0
);
function  MustTerminate#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  MustTerminate#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { MustTerminate(r_1), MustTerminate(r2) }
  MustTerminate(r_1) == MustTerminate(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { MustTerminate#sm(r_1), MustTerminate#sm(r2) }
  MustTerminate#sm(r_1) == MustTerminate#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { MustTerminate#trigger(Heap, MustTerminate(r_1)) }
  MustTerminate#everUsed(MustTerminate(r_1))
);

// ==================================================
// Translation of predicate MustInvokeBounded
// ==================================================

type PredicateType_MustInvokeBounded;
function  MustInvokeBounded(r_1: Ref): Field PredicateType_MustInvokeBounded FrameType;
function  MustInvokeBounded#sm(r_1: Ref): Field PredicateType_MustInvokeBounded PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(MustInvokeBounded(r_1)) }
  PredicateMaskField(MustInvokeBounded(r_1)) == MustInvokeBounded#sm(r_1)
);
axiom (forall r_1: Ref ::
  { MustInvokeBounded(r_1) }
  IsPredicateField(MustInvokeBounded(r_1))
);
axiom (forall r_1: Ref ::
  { MustInvokeBounded(r_1) }
  getPredicateId(MustInvokeBounded(r_1)) == 1
);
function  MustInvokeBounded#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  MustInvokeBounded#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { MustInvokeBounded(r_1), MustInvokeBounded(r2) }
  MustInvokeBounded(r_1) == MustInvokeBounded(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { MustInvokeBounded#sm(r_1), MustInvokeBounded#sm(r2) }
  MustInvokeBounded#sm(r_1) == MustInvokeBounded#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { MustInvokeBounded#trigger(Heap, MustInvokeBounded(r_1)) }
  MustInvokeBounded#everUsed(MustInvokeBounded(r_1))
);

// ==================================================
// Translation of predicate MustInvokeUnbounded
// ==================================================

type PredicateType_MustInvokeUnbounded;
function  MustInvokeUnbounded(r_1: Ref): Field PredicateType_MustInvokeUnbounded FrameType;
function  MustInvokeUnbounded#sm(r_1: Ref): Field PredicateType_MustInvokeUnbounded PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(MustInvokeUnbounded(r_1)) }
  PredicateMaskField(MustInvokeUnbounded(r_1)) == MustInvokeUnbounded#sm(r_1)
);
axiom (forall r_1: Ref ::
  { MustInvokeUnbounded(r_1) }
  IsPredicateField(MustInvokeUnbounded(r_1))
);
axiom (forall r_1: Ref ::
  { MustInvokeUnbounded(r_1) }
  getPredicateId(MustInvokeUnbounded(r_1)) == 2
);
function  MustInvokeUnbounded#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  MustInvokeUnbounded#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { MustInvokeUnbounded(r_1), MustInvokeUnbounded(r2) }
  MustInvokeUnbounded(r_1) == MustInvokeUnbounded(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { MustInvokeUnbounded#sm(r_1), MustInvokeUnbounded#sm(r2) }
  MustInvokeUnbounded#sm(r_1) == MustInvokeUnbounded#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { MustInvokeUnbounded#trigger(Heap, MustInvokeUnbounded(r_1)) }
  MustInvokeUnbounded#everUsed(MustInvokeUnbounded(r_1))
);

// ==================================================
// Translation of predicate _MaySet
// ==================================================

type PredicateType__MaySet;
function  _MaySet(rec: Ref, id: int): Field PredicateType__MaySet FrameType;
function  _MaySet#sm(rec: Ref, id: int): Field PredicateType__MaySet PMaskType;
axiom (forall rec: Ref, id: int ::
  { PredicateMaskField(_MaySet(rec, id)) }
  PredicateMaskField(_MaySet(rec, id)) == _MaySet#sm(rec, id)
);
axiom (forall rec: Ref, id: int ::
  { _MaySet(rec, id) }
  IsPredicateField(_MaySet(rec, id))
);
axiom (forall rec: Ref, id: int ::
  { _MaySet(rec, id) }
  getPredicateId(_MaySet(rec, id)) == 3
);
function  _MaySet#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  _MaySet#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall rec: Ref, id: int, rec2: Ref, id2: int ::
  { _MaySet(rec, id), _MaySet(rec2, id2) }
  _MaySet(rec, id) == _MaySet(rec2, id2) ==> rec == rec2 && id == id2
);
axiom (forall rec: Ref, id: int, rec2: Ref, id2: int ::
  { _MaySet#sm(rec, id), _MaySet#sm(rec2, id2) }
  _MaySet#sm(rec, id) == _MaySet#sm(rec2, id2) ==> rec == rec2 && id == id2
);

axiom (forall Heap: HeapType, rec: Ref, id: int ::
  { _MaySet#trigger(Heap, _MaySet(rec, id)) }
  _MaySet#everUsed(_MaySet(rec, id))
);

// ==================================================
// Translation of predicate Ticket_state
// ==================================================

type PredicateType_Ticket_state;
function  Ticket_state(self_1: Ref): Field PredicateType_Ticket_state FrameType;
function  Ticket_state#sm(self_1: Ref): Field PredicateType_Ticket_state PMaskType;
axiom (forall self_1: Ref ::
  { PredicateMaskField(Ticket_state(self_1)) }
  PredicateMaskField(Ticket_state(self_1)) == Ticket_state#sm(self_1)
);
axiom (forall self_1: Ref ::
  { Ticket_state(self_1) }
  IsPredicateField(Ticket_state(self_1))
);
axiom (forall self_1: Ref ::
  { Ticket_state(self_1) }
  getPredicateId(Ticket_state(self_1)) == 4
);
function  Ticket_state#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  Ticket_state#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall self_1: Ref, self_12: Ref ::
  { Ticket_state(self_1), Ticket_state(self_12) }
  Ticket_state(self_1) == Ticket_state(self_12) ==> self_1 == self_12
);
axiom (forall self_1: Ref, self_12: Ref ::
  { Ticket_state#sm(self_1), Ticket_state#sm(self_12) }
  Ticket_state#sm(self_1) == Ticket_state#sm(self_12) ==> self_1 == self_12
);

axiom (forall Heap: HeapType, self_1: Ref ::
  { Ticket_state#trigger(Heap, Ticket_state(self_1)) }
  Ticket_state#everUsed(Ticket_state(self_1))
);

procedure Ticket_state#definedness(self_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  
  // -- Check definedness of predicate body of Ticket_state
    
    // -- Initializing the state
      Mask := ZeroMask;
      assume state(Heap, Mask);
      assume AssumeFunctionsAbove == -1;
      assume Heap[self_1, $allocated];
    assume (issubtype((typeof(self_1): PyTypeDomainType), Ticket): bool);
    if ((issubtype((typeof(self_1): PyTypeDomainType), Ticket): bool)) {
      perm := FullPerm;
      assume self_1 != null;
      Mask[self_1, Ticket_show_id] := Mask[self_1, Ticket_show_id] + perm;
      assume state(Heap, Mask);
      
      // -- Check definedness of issubtype(typeof(self_1.Ticket_show_id), int())
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access self_1.Ticket_show_id (testsfunctionalverificationexamplescav_example.py.vpr@598.1--600.2) [2249]"}
          HasDirectPerm(Mask, self_1, Ticket_show_id);
      assume (issubtype((typeof(Heap[self_1, Ticket_show_id]): PyTypeDomainType), vint): bool);
      perm := FullPerm;
      assume self_1 != null;
      Mask[self_1, Ticket_row] := Mask[self_1, Ticket_row] + perm;
      assume state(Heap, Mask);
      
      // -- Check definedness of issubtype(typeof(self_1.Ticket_row), int())
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access self_1.Ticket_row (testsfunctionalverificationexamplescav_example.py.vpr@598.1--600.2) [2250]"}
          HasDirectPerm(Mask, self_1, Ticket_row);
      assume (issubtype((typeof(Heap[self_1, Ticket_row]): PyTypeDomainType), vint): bool);
      perm := FullPerm;
      assume self_1 != null;
      Mask[self_1, Ticket_seat] := Mask[self_1, Ticket_seat] + perm;
      assume state(Heap, Mask);
      
      // -- Check definedness of issubtype(typeof(self_1.Ticket_seat), int())
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access self_1.Ticket_seat (testsfunctionalverificationexamplescav_example.py.vpr@598.1--600.2) [2251]"}
          HasDirectPerm(Mask, self_1, Ticket_seat);
      assume (issubtype((typeof(Heap[self_1, Ticket_seat]): PyTypeDomainType), vint): bool);
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method get_seats
// ==================================================

procedure get_seats(_cthread_159: Ref, _caller_measures_159: (Seq Measure$DomainType), _residue_159: Perm, id_0: Ref, num_0: Ref) returns (_current_wait_level_159: Perm, _res: Ref, _err: Ref)
  modifies Heap, Mask;
{
  var _r_0: Ref;
  var _r_0_2: Ref;
  var _r_0_4: Ref;
  var _r_0_6: Ref;
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r: Ref;
  var _r_2: Ref;
  var wildcard: real where wildcard > NoPerm;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_159, $allocated];
    assume Heap[id_0, $allocated];
    assume Heap[num_0, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_159 != null;
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_159): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(id_0): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(num_0): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of int___gt__(int___unbox__(num_0), 0)
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(num_0), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@607.23--607.43) [2252]"}
              (issubtype((typeof(num_0): PyTypeDomainType), vint): bool);
            // Stop execution
            assume false;
          }
          if (*) {
            // Stop execution
            assume false;
          }
        assume int___gt__(Heap, int___unbox__(Heap, num_0), 0);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_159, _cthread_159, 1) || perm(MustTerminate(_cthread_159)) == none && ((forperm _r_0: Ref [MustInvokeBounded(_r_0)] :: false) && ((forperm _r_0: Ref [MustInvokeUnbounded(_r_0)] :: false) && ((forperm _r_0: Ref [_r_0.MustReleaseBounded] :: false) && (forperm _r_0: Ref [_r_0.MustReleaseUnbounded] :: false))))
          if (*) {
            // Stop execution
            assume false;
          }
          if (!Measure$check(Heap, _caller_measures_159, _cthread_159, 1)) {
            if (Mask[null, MustTerminate(_cthread_159)] == NoPerm) {
              if (*) {
                if (HasDirectPerm(Mask, null, MustInvokeBounded(_r_0))) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_0) (testsfunctionalverificationexamplescav_example.py.vpr@609.12--609.359) [2253]"}
                    HasDirectPerm(Mask, null, MustInvokeBounded(_r_0));
                }
                assume false;
              }
              if ((forall _r_0_1: Ref ::
                { Mask[null, MustInvokeBounded(_r_0_1)] }
                HasDirectPerm(Mask, null, MustInvokeBounded(_r_0_1)) ==> false
              )) {
                if (*) {
                  if (HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_0_2))) {
                    assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_0) (testsfunctionalverificationexamplescav_example.py.vpr@609.12--609.359) [2254]"}
                      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_0_2));
                  }
                  assume false;
                }
                if ((forall _r_0_3: Ref ::
                  { Mask[null, MustInvokeUnbounded(_r_0_3)] }
                  HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_0_3)) ==> false
                )) {
                  if (*) {
                    if (HasDirectPerm(Mask, _r_0_4, MustReleaseBounded)) {
                      assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_0.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@609.12--609.359) [2255]"}
                        HasDirectPerm(Mask, _r_0_4, MustReleaseBounded);
                    }
                    assume false;
                  }
                  if ((forall _r_0_5: Ref ::
                    { Mask[_r_0_5, MustReleaseBounded] }
                    HasDirectPerm(Mask, _r_0_5, MustReleaseBounded) ==> false
                  )) {
                    if (*) {
                      if (HasDirectPerm(Mask, _r_0_6, MustReleaseUnbounded)) {
                        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_0.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@609.12--609.359) [2256]"}
                          HasDirectPerm(Mask, _r_0_6, MustReleaseUnbounded);
                      }
                      assume false;
                    }
                  }
                }
              }
            }
          }
        assume Measure$check(Heap, _caller_measures_159, _cthread_159, 1) || (Mask[null, MustTerminate(_cthread_159)] == NoPerm && ((forall _r_0_7: Ref ::
          { Mask[null, MustInvokeBounded(_r_0_7)] }
          HasDirectPerm(Mask, null, MustInvokeBounded(_r_0_7)) ==> false
        ) && ((forall _r_0_8: Ref ::
          { Mask[null, MustInvokeUnbounded(_r_0_8)] }
          HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_0_8)) ==> false
        ) && ((forall _r_0_9: Ref ::
          { Mask[_r_0_9, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_0_9, MustReleaseBounded) ==> false
        ) && (forall _r_0_10: Ref ::
          { Mask[_r_0_10, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_0_10, MustReleaseUnbounded) ==> false
        )))));
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_159 != null;
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_159): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(id_0): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(num_0): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of int___gt__(int___unbox__(num_0), 0)
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(num_0), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@607.23--607.43) [2257]"}
            (issubtype((typeof(num_0): PyTypeDomainType), vint): bool);
          // Stop execution
          assume false;
        }
        if (*) {
          // Stop execution
          assume false;
        }
      assume int___gt__(Heap, int___unbox__(Heap, num_0), 0);
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, MustTerminate(_cthread_159)] := Mask[null, MustTerminate(_cthread_159)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r: Ref [_r.MustReleaseBounded] :: Level(_r) <= _current_wait_level_159)
          if (*) {
            if (HasDirectPerm(PostMask, _r, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@610.11--610.232) [2258]"}
                HasDirectPerm(PostMask, _r, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_1: Ref ::
          { PostMask[_r_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_1, MustReleaseBounded) ==> Level(PostHeap, _r_1) <= _current_wait_level_159
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r: Ref [_r.MustReleaseUnbounded] :: Level(_r) <= _current_wait_level_159)
          if (*) {
            if (HasDirectPerm(PostMask, _r_2, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@610.11--610.232) [2259]"}
                HasDirectPerm(PostMask, _r_2, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_3: Ref ::
          { PostMask[_r_3, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_3, MustReleaseUnbounded) ==> Level(PostHeap, _r_3) <= _current_wait_level_159
        );
        assume _residue_159 <= _current_wait_level_159;
        assume state(PostHeap, PostMask);
        if (_err == null) {
          assume (issubtype((typeof(_res): PyTypeDomainType), (list((tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): PyTypeDomainType)): bool);
        }
        assume state(PostHeap, PostMask);
        if (_err == null) {
          perm := FullPerm;
          assume _res != null;
          PostMask[_res, list_acc] := PostMask[_res, list_acc] + perm;
          assume state(PostHeap, PostMask);
        }
        assume state(PostHeap, PostMask);
        if (_err == null) {
          assume state(PostHeap, PostMask);
          
          // -- Check definedness of int___eq__(__prim__int___box__(list___len__(_res)), num_0)
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_res), list(list_arg(typeof(_res), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.59--613.77) [2260]"}
                (issubtype((typeof(_res): PyTypeDomainType), (list((list_arg((typeof(_res): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
              assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@613.59--613.77) [2261]"}
                PostMask[_res, list_acc] > NoPerm;
              havoc wildcard;
              assume wildcard < PostMask[_res, list_acc];
              PostMask[_res, list_acc] := PostMask[_res, list_acc] - wildcard;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
              PostHeap := ExhaleHeap;
              // Stop execution
              assume false;
            }
            if (*) {
              // Stop execution
              assume false;
            }
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function int___eq__ might not hold. Assertion issubtype(typeof(__prim__int___box__(list___len__(_res))), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.28--613.86) [2262]"}
                (issubtype((typeof(__prim__int___box__(PostHeap, list___len__(PostHeap, _res))): PyTypeDomainType), vint): bool);
              assert {:msg "  Precondition of function int___eq__ might not hold. Assertion issubtype(typeof(num_0), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.28--613.86) [2263]"}
                (issubtype((typeof(num_0): PyTypeDomainType), vint): bool);
              // Stop execution
              assume false;
            }
          assume int___eq__(PostHeap, __prim__int___box__(PostHeap, list___len__(PostHeap, _res)), num_0);
        }
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        if (_err != null) {
          assume (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
        }
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      if (_err == null) {
        assume (issubtype((typeof(_res): PyTypeDomainType), (list((tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): PyTypeDomainType)): bool);
      }
      assume state(PostHeap, PostMask);
      if (_err == null) {
        perm := FullPerm;
        assume _res != null;
        PostMask[_res, list_acc] := PostMask[_res, list_acc] + perm;
        assume state(PostHeap, PostMask);
      }
      assume state(PostHeap, PostMask);
      if (_err == null) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of int___eq__(__prim__int___box__(list___len__(_res)), num_0)
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_res), list(list_arg(typeof(_res), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.59--613.77) [2264]"}
              (issubtype((typeof(_res): PyTypeDomainType), (list((list_arg((typeof(_res): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
            assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@613.59--613.77) [2265]"}
              PostMask[_res, list_acc] > NoPerm;
            havoc wildcard;
            assume wildcard < PostMask[_res, list_acc];
            PostMask[_res, list_acc] := PostMask[_res, list_acc] - wildcard;
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
            PostHeap := ExhaleHeap;
            // Stop execution
            assume false;
          }
          if (*) {
            // Stop execution
            assume false;
          }
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function int___eq__ might not hold. Assertion issubtype(typeof(__prim__int___box__(list___len__(_res))), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.28--613.86) [2266]"}
              (issubtype((typeof(__prim__int___box__(PostHeap, list___len__(PostHeap, _res))): PyTypeDomainType), vint): bool);
            assert {:msg "  Precondition of function int___eq__ might not hold. Assertion issubtype(typeof(num_0), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.28--613.86) [2267]"}
              (issubtype((typeof(num_0): PyTypeDomainType), vint): bool);
            // Stop execution
            assume false;
          }
        assume int___eq__(PostHeap, __prim__int___box__(PostHeap, list___len__(PostHeap, _res)), num_0);
      }
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      if (_err != null) {
        assume (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
      }
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: _res := null -- testsfunctionalverificationexamplescav_example.py.vpr@618.3--618.15
    _res := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale false -- testsfunctionalverificationexamplescav_example.py.vpr@619.3--619.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    if (_err == null) {
      assert {:msg "  Postcondition of get_seats might not hold. Assertion issubtype(typeof(_res), list(tuple(Seq(int(), int())))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@611.11--611.83) [2268]"}
        (issubtype((typeof(_res): PyTypeDomainType), (list((tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): PyTypeDomainType)): bool);
    }
    if (_err == null) {
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of get_seats might not hold. There might be insufficient permission to access _res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@612.11--612.53) [2269]"}
          perm <= Mask[_res, list_acc];
      }
      Mask[_res, list_acc] := Mask[_res, list_acc] - perm;
    }
    if (_err == null) {
      assert {:msg "  Postcondition of get_seats might not hold. Assertion int___eq__(__prim__int___box__(list___len__(_res)), num_0) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@613.11--613.86) [2270]"}
        int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, _res)), num_0);
    }
    if (_err != null) {
      assert {:msg "  Postcondition of get_seats might not hold. Assertion issubtype(typeof(_err), SoldoutException()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@615.11--615.71) [2271]"}
        (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
    }
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method order_tickets
// ==================================================

procedure order_tickets(_cthread_160: Ref, _caller_measures_160: (Seq Measure$DomainType), _residue_160: Perm, num_1: Ref, show_id: Ref, code_0: Ref) returns (_current_wait_level_160: Perm, _res: Ref, _err: Ref)
  modifies Heap, Mask;
{
  var loop_end_lblGuard: bool;
  var __end_lblGuard: bool;
  var post_loop_lblGuard: bool;
  var _r_5: Ref;
  var _r_5_2: Ref;
  var _r_5_4: Ref;
  var _r_5_6: Ref;
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_3_1: Ref;
  var _r_3_2: Ref;
  var _r_4: Ref;
  var _r_4_2: Ref;
  var _r_4_4: Ref;
  var _r_4_6: Ref;
  var seats: Ref;
  var res: Ref;
  var row_0: Ref;
  var seat_0: Ref;
  var ticket: Ref;
  var num_2: Ref;
  var show_id_0: Ref;
  var code_1: Ref;
  var get_seats_res: Ref;
  var list_0: Ref;
  var iterable: Ref;
  var iter: Ref;
  var loop_target: Ref;
  var iter_err: Ref;
  var Ticket_res: Ref;
  var _method_measures_160: (Seq Measure$DomainType);
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var _cwl_160: Perm;
  var ExhaleHeap: HeapType;
  var ln_1: int;
  var ln_3: int;
  var seqtmp: (Seq Ref);
  var _loop_original_must_terminate: Perm;
  var _loop_termination_flag: bool;
  var _loop_check_before: bool;
  var QPMask: MaskType;
  var lambda46_30$t_2_1: Ref;
  var frameMask74: MaskType;
  var frameHeap74: HeapType;
  var _loop_measures: (Seq Measure$DomainType);
  var _r_1_1: Ref;
  var _residue_161: Perm;
  var _r_1_3: Ref;
  var ln_5: int;
  var ln_7: int;
  var wildcard: real where wildcard > NoPerm;
  var lambda46_30$t_3: Ref;
  var lambda46_30$t_4: Ref;
  var lambda46_30$t_6: Ref;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var freshObj: Ref;
  var arg_row: Ref;
  var arg_seat: Ref;
  var arg_self: Ref;
  var arg_item: Ref;
  var Labelloop_endMask: MaskType;
  var Labelloop_endHeap: HeapType;
  var ln_9: int;
  var ln_11: int;
  var lambda46_30$t_17: Ref;
  var Labelpost_loopMask: MaskType;
  var Labelpost_loopHeap: HeapType;
  var Label__endMask: MaskType;
  var Label__endHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    loop_end_lblGuard := false;
    __end_lblGuard := false;
    post_loop_lblGuard := false;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_160, $allocated];
    assume Heap[num_1, $allocated];
    assume Heap[show_id, $allocated];
    assume Heap[code_0, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_160 != null;
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(num_1): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(show_id): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume code_0 == null || (issubtype((typeof(code_0): PyTypeDomainType), str): bool);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of int___gt__(int___unbox__(num_1), 0)
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(num_1), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@628.23--628.43) [2272]"}
              (issubtype((typeof(num_1): PyTypeDomainType), vint): bool);
            // Stop execution
            assume false;
          }
          if (*) {
            // Stop execution
            assume false;
          }
        assume int___gt__(Heap, int___unbox__(Heap, num_1), 0);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_160, _cthread_160, 2) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_5: Ref [MustInvokeBounded(_r_5)] :: false) && ((forperm _r_5: Ref [MustInvokeUnbounded(_r_5)] :: false) && ((forperm _r_5: Ref [_r_5.MustReleaseBounded] :: false) && (forperm _r_5: Ref [_r_5.MustReleaseUnbounded] :: false))))
          if (*) {
            // Stop execution
            assume false;
          }
          if (!Measure$check(Heap, _caller_measures_160, _cthread_160, 2)) {
            if (Mask[null, MustTerminate(_cthread_160)] == NoPerm) {
              if (*) {
                if (HasDirectPerm(Mask, null, MustInvokeBounded(_r_5))) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_5) (testsfunctionalverificationexamplescav_example.py.vpr@630.12--630.359) [2273]"}
                    HasDirectPerm(Mask, null, MustInvokeBounded(_r_5));
                }
                assume false;
              }
              if ((forall _r_5_1: Ref ::
                { Mask[null, MustInvokeBounded(_r_5_1)] }
                HasDirectPerm(Mask, null, MustInvokeBounded(_r_5_1)) ==> false
              )) {
                if (*) {
                  if (HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_5_2))) {
                    assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_5) (testsfunctionalverificationexamplescav_example.py.vpr@630.12--630.359) [2274]"}
                      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_5_2));
                  }
                  assume false;
                }
                if ((forall _r_5_3: Ref ::
                  { Mask[null, MustInvokeUnbounded(_r_5_3)] }
                  HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_5_3)) ==> false
                )) {
                  if (*) {
                    if (HasDirectPerm(Mask, _r_5_4, MustReleaseBounded)) {
                      assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_5.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@630.12--630.359) [2275]"}
                        HasDirectPerm(Mask, _r_5_4, MustReleaseBounded);
                    }
                    assume false;
                  }
                  if ((forall _r_5_5: Ref ::
                    { Mask[_r_5_5, MustReleaseBounded] }
                    HasDirectPerm(Mask, _r_5_5, MustReleaseBounded) ==> false
                  )) {
                    if (*) {
                      if (HasDirectPerm(Mask, _r_5_6, MustReleaseUnbounded)) {
                        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_5.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@630.12--630.359) [2276]"}
                          HasDirectPerm(Mask, _r_5_6, MustReleaseUnbounded);
                      }
                      assume false;
                    }
                  }
                }
              }
            }
          }
        assume Measure$check(Heap, _caller_measures_160, _cthread_160, 2) || (Mask[null, MustTerminate(_cthread_160)] == NoPerm && ((forall _r_5_7: Ref ::
          { Mask[null, MustInvokeBounded(_r_5_7)] }
          HasDirectPerm(Mask, null, MustInvokeBounded(_r_5_7)) ==> false
        ) && ((forall _r_5_8: Ref ::
          { Mask[null, MustInvokeUnbounded(_r_5_8)] }
          HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_5_8)) ==> false
        ) && ((forall _r_5_9: Ref ::
          { Mask[_r_5_9, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_5_9, MustReleaseBounded) ==> false
        ) && (forall _r_5_10: Ref ::
          { Mask[_r_5_10, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_5_10, MustReleaseUnbounded) ==> false
        )))));
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_160 != null;
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(num_1): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(show_id): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume code_0 == null || (issubtype((typeof(code_0): PyTypeDomainType), str): bool);
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of int___gt__(int___unbox__(num_1), 0)
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function int___unbox__ might not hold. Assertion issubtype(typeof(num_1), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@628.23--628.43) [2277]"}
            (issubtype((typeof(num_1): PyTypeDomainType), vint): bool);
          // Stop execution
          assume false;
        }
        if (*) {
          // Stop execution
          assume false;
        }
      assume int___gt__(Heap, int___unbox__(Heap, num_1), 0);
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, MustTerminate(_cthread_160)] := Mask[null, MustTerminate(_cthread_160)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_3: Ref [_r_3.MustReleaseBounded] :: Level(_r_3) <= _current_wait_level_160)
          if (*) {
            if (HasDirectPerm(PostMask, _r_3_1, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_3.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@631.11--631.244) [2278]"}
                HasDirectPerm(PostMask, _r_3_1, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_3_1_1: Ref ::
          { PostMask[_r_3_1_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_3_1_1, MustReleaseBounded) ==> Level(PostHeap, _r_3_1_1) <= _current_wait_level_160
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_3: Ref [_r_3.MustReleaseUnbounded] :: Level(_r_3) <= _current_wait_level_160)
          if (*) {
            if (HasDirectPerm(PostMask, _r_3_2, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_3.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@631.11--631.244) [2279]"}
                HasDirectPerm(PostMask, _r_3_2, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_3_3: Ref ::
          { PostMask[_r_3_3, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_3_3, MustReleaseUnbounded) ==> Level(PostHeap, _r_3_3) <= _current_wait_level_160
        );
        assume _residue_160 <= _current_wait_level_160;
        assume state(PostHeap, PostMask);
        if (_err == null) {
          assume (issubtype((typeof(_res): PyTypeDomainType), (list(Ticket): PyTypeDomainType)): bool);
        }
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        if (_err != null) {
          assume (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
        }
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      if (_err == null) {
        assume (issubtype((typeof(_res): PyTypeDomainType), (list(Ticket): PyTypeDomainType)): bool);
      }
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      if (_err != null) {
        assume (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of (forperm _r_4: Ref [MustInvokeBounded(_r_4)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeBounded(_r_4))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_4) (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2280]"}
              HasDirectPerm(PostMask, null, MustInvokeBounded(_r_4));
          }
          assume false;
        }
      assume (forall _r_4_1: Ref ::
        { PostMask[null, MustInvokeBounded(_r_4_1)] }
        HasDirectPerm(PostMask, null, MustInvokeBounded(_r_4_1)) ==> false
      );
      
      // -- Check definedness of (forperm _r_4: Ref [MustInvokeUnbounded(_r_4)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_4_2))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_4) (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2281]"}
              HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_4_2));
          }
          assume false;
        }
      assume (forall _r_4_3: Ref ::
        { PostMask[null, MustInvokeUnbounded(_r_4_3)] }
        HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_4_3)) ==> false
      );
      
      // -- Check definedness of (forperm _r_4: Ref [_r_4.MustReleaseBounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_4_4, MustReleaseBounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_4.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2282]"}
              HasDirectPerm(PostMask, _r_4_4, MustReleaseBounded);
          }
          assume false;
        }
      assume (forall _r_4_5: Ref ::
        { PostMask[_r_4_5, MustReleaseBounded] }
        HasDirectPerm(PostMask, _r_4_5, MustReleaseBounded) ==> false
      );
      
      // -- Check definedness of (forperm _r_4: Ref [_r_4.MustReleaseUnbounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_4_6, MustReleaseUnbounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_4.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2283]"}
              HasDirectPerm(PostMask, _r_4_6, MustReleaseUnbounded);
          }
          assume false;
        }
      assume (forall _r_4_7: Ref ::
        { PostMask[_r_4_7, MustReleaseUnbounded] }
        HasDirectPerm(PostMask, _r_4_7, MustReleaseUnbounded) ==> false
      );
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Assumptions about local variables
    assume Heap[seats, $allocated];
    assume Heap[res, $allocated];
    assume Heap[row_0, $allocated];
    assume Heap[seat_0, $allocated];
    assume Heap[ticket, $allocated];
    assume Heap[num_2, $allocated];
    assume Heap[show_id_0, $allocated];
    assume Heap[code_1, $allocated];
    assume Heap[get_seats_res, $allocated];
    assume Heap[list_0, $allocated];
    assume Heap[iterable, $allocated];
    assume Heap[iter, $allocated];
    assume Heap[loop_target, $allocated];
    assume Heap[iter_err, $allocated];
    assume Heap[Ticket_res, $allocated];
  
  // -- Translating statement: // id = 1
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 2
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 3
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 4
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 5
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 6
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 7
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 8
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 9
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 10
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 11
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 12
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 13
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 14
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 15
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 16
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 17
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 18
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 19
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 20
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 21
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 22
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 23
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 24
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 25
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 26
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 27
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 28
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 29
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 30
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 31
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 32
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 33
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 34
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 35
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 36
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 37
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 38
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 39
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 40
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 41
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 42
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 43
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 44
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 45
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 46
  // _method_measures_160 := Seq(Measure$create(true, _cthread_160, 2)) -- testsfunctionalverificationexamplescav_example.py.vpr@660.3--660.69
    _method_measures_160 := Seq#Singleton((Measure$create(true, _cthread_160, 2): Measure$DomainType));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 47
  // _res := null -- testsfunctionalverificationexamplescav_example.py.vpr@661.3--661.15
    _res := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 48
  // _err := null -- testsfunctionalverificationexamplescav_example.py.vpr@662.3--662.15
    _err := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 49
  // num_2 := num_1 -- testsfunctionalverificationexamplescav_example.py.vpr@663.3--663.17
    num_2 := num_1;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 50
  // show_id_0 := show_id -- testsfunctionalverificationexamplescav_example.py.vpr@664.3--664.23
    show_id_0 := show_id;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 51
  // code_1 := code_0 -- testsfunctionalverificationexamplescav_example.py.vpr@665.3--665.19
    code_1 := code_0;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 52
  // _cwl_160, get_seats_res, _err := get_seats(_cthread_160, _method_measures_160,
  //   _residue_160, show_id_0, num_2) -- testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113
    PreCallHeap := Heap;
    PreCallMask := Mask;
    havoc _cwl_160, get_seats_res, _err;
    
    // -- Exhaling precondition
      assert {:msg "  The precondition of method get_seats might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113) [2284]"}
        _cthread_160 != null;
      assert {:msg "  The precondition of method get_seats might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113) [2285]"}
        (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
      assert {:msg "  The precondition of method get_seats might not hold. Assertion issubtype(typeof(show_id_0), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113) [2286]"}
        (issubtype((typeof(show_id_0): PyTypeDomainType), vint): bool);
      assert {:msg "  The precondition of method get_seats might not hold. Assertion issubtype(typeof(num_2), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113) [2287]"}
        (issubtype((typeof(num_2): PyTypeDomainType), vint): bool);
      assert {:msg "  The precondition of method get_seats might not hold. Assertion int___gt__(int___unbox__(num_2), 0) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113) [2288]"}
        int___gt__(Heap, int___unbox__(Heap, num_2), 0);
      assert {:msg "  The precondition of method get_seats might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_0: Ref [MustInvokeBounded(_r_0)] :: false) && ((forperm _r_0: Ref [MustInvokeUnbounded(_r_0)] :: false) && ((forperm _r_0: Ref [_r_0.MustReleaseBounded] :: false) && (forperm _r_0: Ref [_r_0.MustReleaseUnbounded] :: false)))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@666.3--666.113) [2289]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1) || (Mask[null, MustTerminate(_cthread_160)] == NoPerm && ((forall _r_0_11: Ref ::
        { Mask[null, MustInvokeBounded(_r_0_11)] }
        HasDirectPerm(Mask, null, MustInvokeBounded(_r_0_11)) ==> false
      ) && ((forall _r_0_1: Ref ::
        { Mask[null, MustInvokeUnbounded(_r_0_1)] }
        HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_0_1)) ==> false
      ) && ((forall _r_0_2_1: Ref ::
        { Mask[_r_0_2_1, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_0_2_1, MustReleaseBounded) ==> false
      ) && (forall _r_0_3: Ref ::
        { Mask[_r_0_3, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_0_3, MustReleaseUnbounded) ==> false
      )))));
      // Finish exhale
      havoc ExhaleHeap;
      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
      Heap := ExhaleHeap;
    
    // -- Inhaling postcondition
      assume state(Heap, Mask);
      assume (forall _r_6: Ref ::
        { Mask[_r_6, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_6, MustReleaseBounded) ==> Level(Heap, _r_6) <= _cwl_160
      );
      assume state(Heap, Mask);
      assume (forall _r_1: Ref ::
        { Mask[_r_1, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_1, MustReleaseUnbounded) ==> Level(Heap, _r_1) <= _cwl_160
      );
      assume _residue_160 <= _cwl_160;
      if (_err == null) {
        assume (issubtype((typeof(get_seats_res): PyTypeDomainType), (list((tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): PyTypeDomainType)): bool);
      }
      if (_err == null) {
        perm := FullPerm;
        assume get_seats_res != null;
        Mask[get_seats_res, list_acc] := Mask[get_seats_res, list_acc] + perm;
        assume state(Heap, Mask);
      }
      if (_err == null) {
        assume state(Heap, Mask);
        assume int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, get_seats_res)), num_2);
      }
      if (_err != null) {
        assume (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
      }
      assume state(Heap, Mask);
    assume Heap[get_seats_res, $allocated];
    assume Heap[_err, $allocated];
    assume state(Heap, Mask);
  
  // -- Translating statement: if (_err != null) -- testsfunctionalverificationexamplescav_example.py.vpr@667.3--670.4
    if (_err != null) {
      
      // -- Translating statement: // id = 53
  // _err := _err -- testsfunctionalverificationexamplescav_example.py.vpr@668.5--668.17
        _err := _err;
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 54
  // goto __end -- testsfunctionalverificationexamplescav_example.py.vpr@669.5--669.15
        goto __end;
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: // id = 55
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 56
  // seats := get_seats_res -- testsfunctionalverificationexamplescav_example.py.vpr@671.3--671.25
    seats := get_seats_res;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 57
  // inhale _isDefined(495873779059) -- testsfunctionalverificationexamplescav_example.py.vpr@672.3--672.34
    assume state(Heap, Mask);
    
    // -- Check definedness of _isDefined(495873779059)
      if (*) {
        // Stop execution
        assume false;
      }
    assume _isDefined(Heap, 495873779059);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 58
  // _cwl_160, list_0 := list___init__(_cthread_160, _method_measures_160, _residue_160) -- testsfunctionalverificationexamplescav_example.py.vpr@673.3--673.86
    PreCallHeap := Heap;
    PreCallMask := Mask;
    havoc _cwl_160, list_0;
    
    // -- Exhaling precondition
      assert {:msg "  The precondition of method list___init__ might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@673.3--673.86) [2290]"}
        _cthread_160 != null;
      assert {:msg "  The precondition of method list___init__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@673.3--673.86) [2291]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      assert {:msg "  The precondition of method list___init__ might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@673.3--673.86) [2292]"}
        (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
      assert {:msg "  The precondition of method list___init__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@673.3--673.86) [2293]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
    
    // -- Inhaling postcondition
      assume state(Heap, Mask);
      assume (forall _r_19: Ref ::
        { Mask[_r_19, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_19, MustReleaseBounded) ==> Level(Heap, _r_19) <= _cwl_160
      );
      assume state(Heap, Mask);
      assume (forall _r_19_1: Ref ::
        { Mask[_r_19_1, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_19_1, MustReleaseUnbounded) ==> Level(Heap, _r_19_1) <= _cwl_160
      );
      assume _residue_160 <= _cwl_160;
      perm := FullPerm;
      assume list_0 != null;
      Mask[list_0, list_acc] := Mask[list_0, list_acc] + perm;
      assume state(Heap, Mask);
      assume Seq#Equal(Heap[list_0, list_acc], (Seq#Empty(): Seq Ref));
      assume (typeof(list_0): PyTypeDomainType) == (list((list_arg((typeof(list_0): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType);
      assume (Low(list_0): bool);
      assume state(Heap, Mask);
    assume Heap[list_0, $allocated];
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 59
  // inhale issubtype(typeof(list_0), list(Ticket())) -- testsfunctionalverificationexamplescav_example.py.vpr@674.3--674.51
    assume (issubtype((typeof(list_0): PyTypeDomainType), (list(Ticket): PyTypeDomainType)): bool);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 60
  // res := list_0 -- testsfunctionalverificationexamplescav_example.py.vpr@675.3--675.16
    res := list_0;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 61
  // inhale _isDefined(7562610) -- testsfunctionalverificationexamplescav_example.py.vpr@676.3--676.29
    assume state(Heap, Mask);
    
    // -- Check definedness of _isDefined(7562610)
      if (*) {
        // Stop execution
        assume false;
      }
    assume _isDefined(Heap, 7562610);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 62
  // iterable := _checkDefined(seats, 495873779059) -- testsfunctionalverificationexamplescav_example.py.vpr@677.3--677.49
    
    // -- Check definedness of _checkDefined(seats, 495873779059)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(495873779059) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@677.15--677.49) [2294]"}
          _isDefined(Heap, 495873779059);
        // Stop execution
        assume false;
      }
    iterable := _checkDefined(Heap, seats, 495873779059);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 63
  // _cwl_160, iter := list___iter__(_cthread_160, _method_measures_160, _residue_160,
  //   iterable) -- testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94
    PreCallHeap := Heap;
    PreCallMask := Mask;
    havoc _cwl_160, iter;
    
    // -- Exhaling precondition
      assert {:msg "  The precondition of method list___iter__ might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2295]"}
        _cthread_160 != null;
      assert {:msg "  The precondition of method list___iter__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2296]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      assert {:msg "  The precondition of method list___iter__ might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2297]"}
        (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
      assert {:msg "  The precondition of method list___iter__ might not hold. Assertion issubtype(typeof(iterable), list(list_arg(typeof(iterable), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2298]"}
        (issubtype((typeof(iterable): PyTypeDomainType), (list((list_arg((typeof(iterable): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
      assert {:msg "  The precondition of method list___iter__ might not hold. Fraction 1 / 10 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2299]"}
        1 / 10 >= NoPerm;
      perm := 1 / 10;
      if (perm != NoPerm) {
        assert {:msg "  The precondition of method list___iter__ might not hold. There might be insufficient permission to access iterable.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2300]"}
          perm <= Mask[iterable, list_acc];
      }
      Mask[iterable, list_acc] := Mask[iterable, list_acc] - perm;
      assert {:msg "  The precondition of method list___iter__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2301]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      // Finish exhale
      havoc ExhaleHeap;
      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
      Heap := ExhaleHeap;
    
    // -- Inhaling postcondition
      assume state(Heap, Mask);
      assume (forall _r_23: Ref ::
        { Mask[_r_23, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_23, MustReleaseBounded) ==> Level(Heap, _r_23) <= _cwl_160
      );
      assume state(Heap, Mask);
      assume (forall _r_23_1: Ref ::
        { Mask[_r_23_1, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_23_1, MustReleaseUnbounded) ==> Level(Heap, _r_23_1) <= _cwl_160
      );
      assume _residue_160 <= _cwl_160;
      assume iter != iterable;
      perm := 1 / 20;
      assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2302]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> iter != null;
      Mask[iter, list_acc] := Mask[iter, list_acc] + perm;
      assume state(Heap, Mask);
      perm := 1 / 20;
      assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@678.3--678.94) [2303]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> iterable != null;
      Mask[iterable, list_acc] := Mask[iterable, list_acc] + perm;
      assume state(Heap, Mask);
      assume Seq#Equal(Heap[iter, list_acc], Heap[iterable, list_acc]);
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __container] := Mask[iter, __container] + perm;
      assume state(Heap, Mask);
      assume Heap[iter, __container] == iterable;
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __iter_index] := Mask[iter, __iter_index] + perm;
      assume state(Heap, Mask);
      assume Heap[iter, __iter_index] == 0;
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __previous] := Mask[iter, __previous] + perm;
      assume state(Heap, Mask);
      assume Seq#Equal(Heap[iter, __previous], (Seq#Empty(): Seq Ref));
      assume (issubtype((typeof(iter): PyTypeDomainType), (Iterator((list_arg((typeof(iterable): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
      assume state(Heap, Mask);
    assume Heap[iter, $allocated];
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 64
  // _cwl_160, loop_target, iter_err := Iterator___next__(_cthread_160, _method_measures_160,
  //   _residue_160, iter) -- testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111
    PreCallHeap := Heap;
    PreCallMask := Mask;
    havoc _cwl_160, loop_target, iter_err;
    
    // -- Exhaling precondition
      assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2304]"}
        _cthread_160 != null;
      assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2305]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2306]"}
        (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
      assert {:msg "  The precondition of method Iterator___next__ might not hold. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2307]"}
        1 / 40 >= NoPerm;
      perm := 1 / 40;
      if (perm != NoPerm) {
        assert {:msg "  The precondition of method Iterator___next__ might not hold. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2308]"}
          perm <= Mask[iter, list_acc];
      }
      Mask[iter, list_acc] := Mask[iter, list_acc] - perm;
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  The precondition of method Iterator___next__ might not hold. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2309]"}
          perm <= Mask[iter, __iter_index];
      }
      Mask[iter, __iter_index] := Mask[iter, __iter_index] - perm;
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  The precondition of method Iterator___next__ might not hold. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2310]"}
          perm <= Mask[iter, __previous];
      }
      Mask[iter, __previous] := Mask[iter, __previous] - perm;
      assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2311]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      // Finish exhale
      havoc ExhaleHeap;
      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
      Heap := ExhaleHeap;
    
    // -- Inhaling postcondition
      assume state(Heap, Mask);
      assume (forall _r_15: Ref ::
        { Mask[_r_15, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_15, MustReleaseBounded) ==> Level(Heap, _r_15) <= _cwl_160
      );
      assume state(Heap, Mask);
      assume (forall _r_15_1: Ref ::
        { Mask[_r_15_1, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_15_1, MustReleaseUnbounded) ==> Level(Heap, _r_15_1) <= _cwl_160
      );
      assume _residue_160 <= _cwl_160;
      perm := 1 / 40;
      assert {:msg "  Method call might fail. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@679.3--679.111) [2312]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> iter != null;
      Mask[iter, list_acc] := Mask[iter, list_acc] + perm;
      assume state(Heap, Mask);
      assume Seq#Equal(Heap[iter, list_acc], old(PreCallHeap)[iter, list_acc]);
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __iter_index] := Mask[iter, __iter_index] + perm;
      assume state(Heap, Mask);
      assume Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]) + 1;
      assume (old(PreCallHeap)[iter, __iter_index] == Seq#Length(old(PreCallHeap)[iter, list_acc])) == (iter_err != null);
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __previous] := Mask[iter, __previous] + perm;
      assume state(Heap, Mask);
      if (iter_err == null) {
        assume Heap[iter, __iter_index] == old(PreCallHeap)[iter, __iter_index] + 1;
      }
      if (iter_err == null) {
        assume Heap[iter, __iter_index] > 0;
      }
      if (iter_err == null) {
        assume Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume Heap[iter, __iter_index] > 0;
      }
      if (iter_err != null) {
        assume Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
      }
      if (iter_err != null) {
        assume Heap[iter, __iter_index] == Seq#Length(Heap[iter, list_acc]);
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
        assume Seq#Contains(Heap[iter, list_acc], loop_target);
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume (issubtype((typeof(loop_target): PyTypeDomainType), (Iterator_arg((typeof(iter): PyTypeDomainType), 0): PyTypeDomainType)): bool);
      }
      assume (forall r_1: Ref ::
        { Seq#ContainsTrigger(Heap[iter, __previous], r_1) } { Seq#Contains(Heap[iter, __previous], r_1) }
        Seq#Contains(Heap[iter, __previous], r_1) == (Seq#Contains(old(PreCallHeap)[iter, __previous], r_1) || ((Heap[iter, __iter_index] > 1 && (r_1 == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 2) && iter_err == null)) || (Heap[iter, __iter_index] > 0 && (iter_err != null && r_1 == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1)))))
      );
      assume state(Heap, Mask);
    assume Heap[loop_target, $allocated];
    assume Heap[iter_err, $allocated];
    assume state(Heap, Mask);
  
  // -- Translating statement: if (iter_err == null) -- testsfunctionalverificationexamplescav_example.py.vpr@680.3--685.4
    if (iter_err == null) {
      
      // -- Translating statement: // id = 65
  // row_0 := tuple___getitem__(loop_target, 0) -- testsfunctionalverificationexamplescav_example.py.vpr@681.5--681.47
        
        // -- Check definedness of tuple___getitem__(loop_target, 0)
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(loop_target)) in (0 >= 0 ==> 0 < ln) && (0 < 0 ==> 0 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@681.14--681.47) [2313]"}
              0 < tuple___len__(Heap, loop_target);
            
            // -- Free assumptions (exhale module)
              ln_1 := tuple___len__(Heap, loop_target);
            // Stop execution
            assume false;
          }
        row_0 := tuple___getitem__(Heap, loop_target, 0);
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 66
  // inhale _isDefined(207760093042) -- testsfunctionalverificationexamplescav_example.py.vpr@682.5--682.36
        assume state(Heap, Mask);
        
        // -- Check definedness of _isDefined(207760093042)
          if (*) {
            // Stop execution
            assume false;
          }
        assume _isDefined(Heap, 207760093042);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 67
  // seat_0 := tuple___getitem__(loop_target, 1) -- testsfunctionalverificationexamplescav_example.py.vpr@683.5--683.48
        
        // -- Check definedness of tuple___getitem__(loop_target, 1)
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(loop_target)) in (1 >= 0 ==> 1 < ln) && (1 < 0 ==> 1 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@683.15--683.48) [2314]"}
              1 < tuple___len__(Heap, loop_target);
            
            // -- Free assumptions (exhale module)
              ln_3 := tuple___len__(Heap, loop_target);
            // Stop execution
            assume false;
          }
        seat_0 := tuple___getitem__(Heap, loop_target, 1);
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 68
  // inhale _isDefined(53186532566387) -- testsfunctionalverificationexamplescav_example.py.vpr@684.5--684.38
        assume state(Heap, Mask);
        
        // -- Check definedness of _isDefined(53186532566387)
          if (*) {
            // Stop execution
            assume false;
          }
        assume _isDefined(Heap, 53186532566387);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: // id = 69
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 70
  // seqtmp := iterable.list_acc -- testsfunctionalverificationexamplescav_example.py.vpr@686.3--686.30
    
    // -- Check definedness of iterable.list_acc
      assert {:msg "  Assignment might fail. There might be insufficient permission to access iterable.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@686.3--686.30) [2315]"}
        HasDirectPerm(Mask, iterable, list_acc);
    seqtmp := Heap[iterable, list_acc];
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 71
  // _loop_original_must_terminate := perm(MustTerminate(_cthread_160)) -- testsfunctionalverificationexamplescav_example.py.vpr@688.3--688.69
    _loop_original_must_terminate := Mask[null, MustTerminate(_cthread_160)];
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 72
  // _loop_termination_flag := true -- testsfunctionalverificationexamplescav_example.py.vpr@690.3--690.33
    _loop_termination_flag := true;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 73
  // // LoopInfo(None,Set())
  // _loop_check_before := true -- testsfunctionalverificationexamplescav_example.py.vpr@692.3--692.29
    _loop_check_before := true;
    assume state(Heap, Mask);
  
  // -- Translating statement: while (iter_err == null) -- testsfunctionalverificationexamplescav_example.py.vpr@693.3--751.4
    
    // -- Before loop head74
      
      // -- Exhale loop invariant before loop
        assert {:msg "  Loop invariant acc(iterable.list_acc, 1 / 20) might not hold on entry. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2316]"}
          1 / 20 >= NoPerm;
        perm := 1 / 20;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iterable.list_acc, 1 / 20) might not hold on entry. There might be insufficient permission to access iterable.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2317]"}
            perm <= Mask[iterable, list_acc];
        }
        Mask[iterable, list_acc] := Mask[iterable, list_acc] - perm;
        assert {:msg "  Loop invariant acc(iter.list_acc, 1 / 20) might not hold on entry. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2318]"}
          1 / 20 >= NoPerm;
        perm := 1 / 20;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iter.list_acc, 1 / 20) might not hold on entry. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2319]"}
            perm <= Mask[iter, list_acc];
        }
        Mask[iter, list_acc] := Mask[iter, list_acc] - perm;
        assert {:msg "  Loop invariant iter.list_acc == iterable.list_acc might not hold on entry. Assertion iter.list_acc == iterable.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@697.15--697.49) [2320]"}
          Seq#Equal(Heap[iter, list_acc], Heap[iterable, list_acc]);
        assert {:msg "  Loop invariant seqtmp == iterable.list_acc might not hold on entry. Assertion seqtmp == iterable.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@698.15--698.42) [2321]"}
          Seq#Equal(seqtmp, Heap[iterable, list_acc]);
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iter.__iter_index, write) might not hold on entry. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@699.15--699.44) [2322]"}
            perm <= Mask[iter, __iter_index];
        }
        Mask[iter, __iter_index] := Mask[iter, __iter_index] - perm;
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iter.__previous, write) might not hold on entry. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@700.15--700.42) [2323]"}
            perm <= Mask[iter, __previous];
        }
        Mask[iter, __previous] := Mask[iter, __previous] - perm;
        if (iter_err == null) {
          assert {:msg "  Loop invariant iter_err == null ==> iter.__iter_index - 1 == |iter.__previous| might not hold on entry. Assertion iter.__iter_index - 1 == |iter.__previous| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@701.15--701.78) [2324]"}
            Heap[iter, __iter_index] - 1 == Seq#Length(Heap[iter, __previous]);
        }
        if (iter_err != null) {
          assert {:msg "  Loop invariant iter_err != null ==> iter.__iter_index == |iter.__previous| might not hold on entry. Assertion iter.__iter_index == |iter.__previous| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@702.15--702.74) [2325]"}
            Heap[iter, __iter_index] == Seq#Length(Heap[iter, __previous]);
        }
        if (iter_err == null) {
          assert {:msg "  Loop invariant iter_err == null ==> |iter.list_acc| > 0 might not hold on entry. Assertion |iter.list_acc| > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@703.15--703.55) [2326]"}
            Seq#Length(Heap[iter, list_acc]) > 0;
        }
        assert {:msg "  Loop invariant iter.__iter_index >= 0 && iter.__iter_index <= |iter.list_acc| might not hold on entry. Assertion iter.__iter_index >= 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2327]"}
          Heap[iter, __iter_index] >= 0;
        assert {:msg "  Loop invariant iter.__iter_index >= 0 && iter.__iter_index <= |iter.list_acc| might not hold on entry. Assertion iter.__iter_index <= |iter.list_acc| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2328]"}
          Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> iter.__iter_index > 0 might not hold on entry. Assertion iter.__iter_index > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@705.15--705.60) [2329]"}
            Heap[iter, __iter_index] > 0;
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> loop_target == iter.list_acc[iter.__iter_index - 1] might not hold on entry. Assertion loop_target == iter.list_acc[iter.__iter_index - 1] might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2330]"}
            loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> (loop_target in iter.list_acc) might not hold on entry. Assertion (loop_target in iter.list_acc) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@707.15--707.69) [2331]"}
            Seq#Contains(Heap[iter, list_acc], loop_target);
        }
        if (iter_err == null) {
          assert {:msg "  Loop invariant iter_err == null ==> iter.__previous == iter.list_acc[..iter.__iter_index - 1] might not hold on entry. Assertion iter.__previous == iter.list_acc[..iter.__iter_index - 1] might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@708.15--708.93) [2332]"}
            Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> issubtype(typeof(loop_target), tuple(Seq(int(), int()))) might not hold on entry. Assertion issubtype(typeof(loop_target), tuple(Seq(int(), int()))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@709.15--709.95) [2333]"}
            (issubtype((typeof(loop_target): PyTypeDomainType), (tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): bool);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> row_0 == tuple___getitem__(loop_target, 0) && _isDefined(207760093042) might not hold on entry. Assertion row_0 == tuple___getitem__(loop_target, 0) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@710.15--710.109) [2334]"}
            row_0 == tuple___getitem__(Heap, loop_target, 0);
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> row_0 == tuple___getitem__(loop_target, 0) && _isDefined(207760093042) might not hold on entry. Assertion _isDefined(207760093042) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@710.15--710.109) [2335]"}
            _isDefined(Heap, 207760093042);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> seat_0 == tuple___getitem__(loop_target, 1) && _isDefined(53186532566387) might not hold on entry. Assertion seat_0 == tuple___getitem__(loop_target, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@711.15--711.112) [2336]"}
            seat_0 == tuple___getitem__(Heap, loop_target, 1);
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> seat_0 == tuple___getitem__(loop_target, 1) && _isDefined(53186532566387) might not hold on entry. Assertion _isDefined(53186532566387) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@711.15--711.112) [2337]"}
            _isDefined(Heap, 53186532566387);
        }
        if (iter_err != null) {
          assert {:msg "  Loop invariant iter_err != null ==> iter.__previous == iter.list_acc might not hold on entry. Assertion iter.__previous == iter.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@712.15--712.68) [2338]"}
            Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
        }
        if (Seq#Length(Heap[iter, list_acc]) == 0) {
          assert {:msg "  Loop invariant |iter.list_acc| == 0 ==> iter_err != null might not hold on entry. Assertion iter_err != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@713.15--713.56) [2339]"}
            iter_err != null;
        }
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(_checkDefined(res, 7562610).list_acc, write) && int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))) might not hold on entry. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@715.15--715.217) [2340]"}
            perm <= Mask[_checkDefined(Heap, res, 7562610), list_acc];
        }
        Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] - perm;
        assert {:msg "  Loop invariant acc(_checkDefined(res, 7562610).list_acc, write) && int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))) might not hold on entry. Assertion int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.15--715.217) [2341]"}
          int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, _checkDefined(Heap, res, 7562610))), __prim__int___box__(Heap, PSeq___len__(Heap, PSeq___create__(Heap, Heap[iter, __previous], vint))));
        havoc QPMask;
        
        // -- check that the permission amount is positive
          
        
        // -- check if receiver acc(Ticket_state(lambda46_30$t), write) is injective
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not hold on entry. Quantified resource Ticket_state(lambda46_30$t) might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2342]"}
            (forall lambda46_30$t: Ref, lambda46_30$t_2: Ref ::
            { neverTriggered1(lambda46_30$t), neverTriggered1(lambda46_30$t_2) }
            (((lambda46_30$t != lambda46_30$t_2 && ((issubtype((typeof(lambda46_30$t): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t))) && ((issubtype((typeof(lambda46_30$t_2): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_2))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t != lambda46_30$t_2
          );
        
        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not hold on entry. There might be insufficient permission to access Ticket_state(lambda46_30$t) (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2343]"}
            (forall lambda46_30$t: Ref ::
            { Heap[null, Ticket_state(lambda46_30$t)] } { Mask[null, Ticket_state(lambda46_30$t)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t) }
            (issubtype((typeof(lambda46_30$t): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t) ==> Mask[null, Ticket_state(lambda46_30$t)] >= FullPerm
          );
        
        // -- assumptions for inverse of receiver acc(Ticket_state(lambda46_30$t), write)
          assume (forall lambda46_30$t: Ref ::
            { Heap[null, Ticket_state(lambda46_30$t)] } { Mask[null, Ticket_state(lambda46_30$t)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t) }
            ((issubtype((typeof(lambda46_30$t): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t)) && NoPerm < FullPerm ==> invRecv1(lambda46_30$t) == lambda46_30$t && qpRange1(lambda46_30$t)
          );
          assume (forall self_1: Ref ::
            { invRecv1(self_1) }
            (((issubtype((typeof(invRecv1(self_1)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv1(self_1))) && NoPerm < FullPerm) && qpRange1(self_1) ==> invRecv1(self_1) == self_1
          );
        
        // -- assume permission updates for predicate Ticket_state
          assume (forall self_1: Ref ::
            { QPMask[null, Ticket_state(self_1)] }
            (((issubtype((typeof(invRecv1(self_1)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv1(self_1))) && NoPerm < FullPerm) && qpRange1(self_1) ==> invRecv1(self_1) == self_1 && QPMask[null, Ticket_state(self_1)] == Mask[null, Ticket_state(self_1)] - FullPerm
          );
          assume (forall self_1: Ref ::
            { QPMask[null, Ticket_state(self_1)] }
            !((((issubtype((typeof(invRecv1(self_1)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv1(self_1))) && NoPerm < FullPerm) && qpRange1(self_1)) ==> QPMask[null, Ticket_state(self_1)] == Mask[null, Ticket_state(self_1)]
          );
        
        // -- assume permission updates for independent locations 
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
            (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 4 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
        Mask := QPMask;
        havoc QPMask;
        
        // -- check that the permission amount is positive
          
        
        // -- check if receiver lambda46_30$t is injective
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not hold on entry. Quantified resource lambda46_30$t.Ticket_discount_code might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2344]"}
            (forall lambda46_30$t_1: Ref, lambda46_30$t_1_1: Ref ::
            { neverTriggered2(lambda46_30$t_1), neverTriggered2(lambda46_30$t_1_1) }
            (((lambda46_30$t_1 != lambda46_30$t_1_1 && ((issubtype((typeof(lambda46_30$t_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_1) && code_1 != null))) && ((issubtype((typeof(lambda46_30$t_1_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_1_1) && code_1 != null))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_1 != lambda46_30$t_1_1
          );
        
        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not hold on entry. There might be insufficient permission to access lambda46_30$t.Ticket_discount_code (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2345]"}
            (forall lambda46_30$t_1: Ref ::
            { Heap[lambda46_30$t_1, Ticket_discount_code] } { QPMask[lambda46_30$t_1, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_1) }
            (issubtype((typeof(lambda46_30$t_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_1) && code_1 != null) ==> Mask[lambda46_30$t_1, Ticket_discount_code] >= FullPerm
          );
        
        // -- assumptions for inverse of receiver lambda46_30$t
          assume (forall lambda46_30$t_1: Ref ::
            { Heap[lambda46_30$t_1, Ticket_discount_code] } { QPMask[lambda46_30$t_1, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_1) }
            ((issubtype((typeof(lambda46_30$t_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_1) && code_1 != null)) && NoPerm < FullPerm ==> qpRange2(lambda46_30$t_1) && invRecv2(lambda46_30$t_1) == lambda46_30$t_1
          );
          assume (forall o_4: Ref ::
            { invRecv2(o_4) }
            ((issubtype((typeof(invRecv2(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv2(o_4)) && code_1 != null)) && (NoPerm < FullPerm && qpRange2(o_4)) ==> invRecv2(o_4) == o_4
          );
        
        // -- assume permission updates for field Ticket_discount_code
          assume (forall o_4: Ref ::
            { QPMask[o_4, Ticket_discount_code] }
            (((issubtype((typeof(invRecv2(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv2(o_4)) && code_1 != null)) && (NoPerm < FullPerm && qpRange2(o_4)) ==> invRecv2(o_4) == o_4 && QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code] - FullPerm) && (!(((issubtype((typeof(invRecv2(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv2(o_4)) && code_1 != null)) && (NoPerm < FullPerm && qpRange2(o_4))) ==> QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code])
          );
        
        // -- assume permission updates for independent locations
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { QPMask[o_4, f_6] }
            f_6 != Ticket_discount_code ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
        Mask := QPMask;
        if (*) {
          if ((issubtype((typeof(lambda46_30$t_2_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_2_1) && code_1 != null)) {
            assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not hold on entry. Assertion issubtype(typeof(lambda46_30$t.Ticket_discount_code), str()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2346]"}
              (issubtype((typeof(Heap[lambda46_30$t_2_1, Ticket_discount_code]): PyTypeDomainType), str): bool);
          }
          assume false;
        }
        assume (forall lambda46_30$t_3_1: Ref ::
          { Seq#ContainsTrigger(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_3_1) } { Seq#Contains(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_3_1) }
          (issubtype((typeof(lambda46_30$t_3_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_3_1) && code_1 != null) ==> (issubtype((typeof(Heap[lambda46_30$t_3_1, Ticket_discount_code]): PyTypeDomainType), str): bool)
        );
        if (iter_err == null) {
          assert {:msg "  Loop invariant (iter_err == null ==> int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610))) > 0) && [acc(MustTerminate(_cthread_160), write), true] might not hold on entry. Assertion int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610))) > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@717.15--717.197) [2347]"}
            int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610))) > 0;
        }
        if (_loop_check_before) {
          assert {:msg "  Loop invariant [true, _loop_check_before ==> _loop_termination_flag || (!(iter_err == null) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))))] might not hold on entry. Assertion _loop_termination_flag || (!(iter_err == null) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false))))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@718.15--718.380) [2348]"}
            _loop_termination_flag || (!(iter_err == null) || (Mask[null, MustTerminate(_cthread_160)] == NoPerm && ((forall _r_2_1: Ref ::
            { Mask[null, MustInvokeBounded(_r_2_1)] }
            HasDirectPerm(Mask, null, MustInvokeBounded(_r_2_1)) ==> false
          ) && ((forall _r_2_1_1: Ref ::
            { Mask[null, MustInvokeUnbounded(_r_2_1_1)] }
            HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_2_1_1)) ==> false
          ) && ((forall _r_2_2: Ref ::
            { Mask[_r_2_2, MustReleaseBounded] }
            HasDirectPerm(Mask, _r_2_2, MustReleaseBounded) ==> false
          ) && (forall _r_2_3: Ref ::
            { Mask[_r_2_3, MustReleaseUnbounded] }
            HasDirectPerm(Mask, _r_2_3, MustReleaseUnbounded) ==> false
          ))))));
        }
        if (!_loop_check_before) {
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not hold on entry. Assertion (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2349]"}
            (forall _r_2_4: Ref ::
            { Mask[null, MustInvokeBounded(_r_2_4)] }
            HasDirectPerm(Mask, null, MustInvokeBounded(_r_2_4)) ==> false
          );
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not hold on entry. Assertion (forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2350]"}
            (forall _r_2_5: Ref ::
            { Mask[null, MustInvokeUnbounded(_r_2_5)] }
            HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_2_5)) ==> false
          );
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not hold on entry. Assertion (forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2351]"}
            (forall _r_2_6: Ref ::
            { Mask[_r_2_6, MustReleaseBounded] }
            HasDirectPerm(Mask, _r_2_6, MustReleaseBounded) ==> false
          );
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not hold on entry. Assertion (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2352]"}
            (forall _r_2_7: Ref ::
            { Mask[_r_2_7, MustReleaseUnbounded] }
            HasDirectPerm(Mask, _r_2_7, MustReleaseUnbounded) ==> false
          );
        }
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
      
      // -- Store frame in mask associated with loop
        frameMask74 := Mask;
        frameHeap74 := Heap;
    
    // -- Havoc loop written variables (except locals)
      havoc _cwl_160, loop_target, iter_err, _loop_measures, Ticket_res, ticket, row_0, seat_0, _loop_check_before;
      assume Heap[loop_target, $allocated];
      assume Heap[iter_err, $allocated];
      assume Heap[Ticket_res, $allocated];
      assume Heap[ticket, $allocated];
      assume Heap[row_0, $allocated];
      assume Heap[seat_0, $allocated];
    
    // -- Check definedness of invariant
      if (*) {
        assume state(Heap, Mask);
        
        // -- Check definedness of (forperm _r_1: Ref [_r_1.MustReleaseBounded] :: Level(_r_1) <= _residue_161)
          if (*) {
            if (HasDirectPerm(Mask, _r_1_1, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_1.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@694.15--694.215) [2353]"}
                HasDirectPerm(Mask, _r_1_1, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_1_2: Ref ::
          { Mask[_r_1_2, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_1_2, MustReleaseBounded) ==> Level(Heap, _r_1_2) <= _residue_161
        );
        assume state(Heap, Mask);
        
        // -- Check definedness of (forperm _r_1: Ref [_r_1.MustReleaseUnbounded] :: Level(_r_1) <= _residue_161)
          if (*) {
            if (HasDirectPerm(Mask, _r_1_3, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_1.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@694.15--694.215) [2354]"}
                HasDirectPerm(Mask, _r_1_3, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_1_4: Ref ::
          { Mask[_r_1_4, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_1_4, MustReleaseUnbounded) ==> Level(Heap, _r_1_4) <= _residue_161
        );
        assume _residue_160 <= _residue_161;
        assume state(Heap, Mask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2355]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> iterable != null;
        Mask[iterable, list_acc] := Mask[iterable, list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2356]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> iter != null;
        Mask[iter, list_acc] := Mask[iter, list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of iter.list_acc == iterable.list_acc
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@697.15--697.49) [2357]"}
            HasDirectPerm(Mask, iter, list_acc);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iterable.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@697.15--697.49) [2358]"}
            HasDirectPerm(Mask, iterable, list_acc);
        assume Seq#Equal(Heap[iter, list_acc], Heap[iterable, list_acc]);
        assume state(Heap, Mask);
        
        // -- Check definedness of seqtmp == iterable.list_acc
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iterable.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@698.15--698.42) [2359]"}
            HasDirectPerm(Mask, iterable, list_acc);
        assume Seq#Equal(seqtmp, Heap[iterable, list_acc]);
        assume state(Heap, Mask);
        perm := FullPerm;
        assume iter != null;
        Mask[iter, __iter_index] := Mask[iter, __iter_index] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := FullPerm;
        assume iter != null;
        Mask[iter, __previous] := Mask[iter, __previous] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        if (iter_err == null) {
          
          // -- Check definedness of iter.__iter_index - 1 == |iter.__previous|
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@701.15--701.78) [2360]"}
              HasDirectPerm(Mask, iter, __iter_index);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@701.15--701.78) [2361]"}
              HasDirectPerm(Mask, iter, __previous);
          assume Heap[iter, __iter_index] - 1 == Seq#Length(Heap[iter, __previous]);
        }
        assume state(Heap, Mask);
        if (iter_err != null) {
          
          // -- Check definedness of iter.__iter_index == |iter.__previous|
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@702.15--702.74) [2362]"}
              HasDirectPerm(Mask, iter, __iter_index);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@702.15--702.74) [2363]"}
              HasDirectPerm(Mask, iter, __previous);
          assume Heap[iter, __iter_index] == Seq#Length(Heap[iter, __previous]);
        }
        assume state(Heap, Mask);
        if (iter_err == null) {
          
          // -- Check definedness of |iter.list_acc| > 0
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@703.15--703.55) [2364]"}
              HasDirectPerm(Mask, iter, list_acc);
          assume Seq#Length(Heap[iter, list_acc]) > 0;
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of iter.__iter_index >= 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2365]"}
            HasDirectPerm(Mask, iter, __iter_index);
        assume Heap[iter, __iter_index] >= 0;
        
        // -- Check definedness of iter.__iter_index <= |iter.list_acc|
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2366]"}
            HasDirectPerm(Mask, iter, __iter_index);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2367]"}
            HasDirectPerm(Mask, iter, list_acc);
        assume Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]);
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@705.15--705.60) [2368]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          
          // -- Check definedness of iter.__iter_index > 0
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@705.15--705.60) [2369]"}
              HasDirectPerm(Mask, iter, __iter_index);
          assume Heap[iter, __iter_index] > 0;
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2370]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          
          // -- Check definedness of loop_target == iter.list_acc[iter.__iter_index - 1]
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2371]"}
              HasDirectPerm(Mask, iter, list_acc);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2372]"}
              HasDirectPerm(Mask, iter, __iter_index);
            assert {:msg "  Contract might not be well-formed. Index iter.list_acc[iter.__iter_index - 1] into iter.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2373]"}
              Heap[iter, __iter_index] - 1 >= 0;
            assert {:msg "  Contract might not be well-formed. Index iter.list_acc[iter.__iter_index - 1] into iter.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2374]"}
              Heap[iter, __iter_index] - 1 < Seq#Length(Heap[iter, list_acc]);
          assume loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@707.15--707.69) [2375]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          
          // -- Check definedness of (loop_target in iter.list_acc)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@707.15--707.69) [2376]"}
              HasDirectPerm(Mask, iter, list_acc);
          assume Seq#Contains(Heap[iter, list_acc], loop_target);
        }
        assume state(Heap, Mask);
        if (iter_err == null) {
          
          // -- Check definedness of iter.__previous == iter.list_acc[..iter.__iter_index - 1]
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@708.15--708.93) [2377]"}
              HasDirectPerm(Mask, iter, __previous);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@708.15--708.93) [2378]"}
              HasDirectPerm(Mask, iter, list_acc);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@708.15--708.93) [2379]"}
              HasDirectPerm(Mask, iter, __iter_index);
          assume Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@709.15--709.95) [2380]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume (issubtype((typeof(loop_target): PyTypeDomainType), (tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): bool);
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@710.15--710.109) [2381]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume state(Heap, Mask);
          
          // -- Check definedness of row_0 == tuple___getitem__(loop_target, 0)
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(loop_target)) in (0 >= 0 ==> 0 < ln) && (0 < 0 ==> 0 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@710.48--710.81) [2382]"}
                0 < tuple___len__(Heap, loop_target);
              
              // -- Free assumptions (exhale module)
                ln_5 := tuple___len__(Heap, loop_target);
              // Stop execution
              assume false;
            }
          assume row_0 == tuple___getitem__(Heap, loop_target, 0);
          assume state(Heap, Mask);
          
          // -- Check definedness of _isDefined(207760093042)
            if (*) {
              // Stop execution
              assume false;
            }
          assume _isDefined(Heap, 207760093042);
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@711.15--711.112) [2383]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume state(Heap, Mask);
          
          // -- Check definedness of seat_0 == tuple___getitem__(loop_target, 1)
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(loop_target)) in (1 >= 0 ==> 1 < ln) && (1 < 0 ==> 1 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@711.49--711.82) [2384]"}
                1 < tuple___len__(Heap, loop_target);
              
              // -- Free assumptions (exhale module)
                ln_7 := tuple___len__(Heap, loop_target);
              // Stop execution
              assume false;
            }
          assume seat_0 == tuple___getitem__(Heap, loop_target, 1);
          assume state(Heap, Mask);
          
          // -- Check definedness of _isDefined(53186532566387)
            if (*) {
              // Stop execution
              assume false;
            }
          assume _isDefined(Heap, 53186532566387);
        }
        assume state(Heap, Mask);
        if (iter_err != null) {
          
          // -- Check definedness of iter.__previous == iter.list_acc
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@712.15--712.68) [2385]"}
              HasDirectPerm(Mask, iter, __previous);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@712.15--712.68) [2386]"}
              HasDirectPerm(Mask, iter, list_acc);
          assume Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
        }
        assume state(Heap, Mask);
        
        // -- Check definedness of |iter.list_acc| == 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@713.15--713.56) [2387]"}
            HasDirectPerm(Mask, iter, list_acc);
        if (Seq#Length(Heap[iter, list_acc]) == 0) {
          assume iter_err != null;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of acc(_checkDefined(res, 7562610).list_acc, write)
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.19--715.46) [2388]"}
              _isDefined(Heap, 7562610);
            // Stop execution
            assume false;
          }
        perm := FullPerm;
        assume _checkDefined(Heap, res, 7562610) != null;
        Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int()))))
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.111--715.138) [2389]"}
              _isDefined(Heap, 7562610);
            // Stop execution
            assume false;
          }
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(res, 7562610)), list(list_arg(typeof(_checkDefined(res, 7562610)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.98--715.139) [2390]"}
              (issubtype((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
            assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@715.98--715.139) [2391]"}
              Mask[_checkDefined(Heap, res, 7562610), list_acc] > NoPerm;
            havoc wildcard;
            assume wildcard < Mask[_checkDefined(Heap, res, 7562610), list_acc];
            Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] - wildcard;
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
            // Stop execution
            assume false;
          }
          if (*) {
            // Stop execution
            assume false;
          }
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@715.15--715.217) [2392]"}
            HasDirectPerm(Mask, iter, __previous);
          if (*) {
            // Stop execution
            assume false;
          }
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function PSeq___len__ might not hold. Assertion issubtype(typeof(PSeq___create__(iter.__previous, int())), PSeq(PSeq_arg(typeof(PSeq___create__(iter.__previous, int())), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.162--715.215) [2393]"}
              (issubtype((typeof(PSeq___create__(Heap, Heap[iter, __previous], vint)): PyTypeDomainType), (PSeq((PSeq_arg((typeof(PSeq___create__(Heap, Heap[iter, __previous], vint)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
            // Stop execution
            assume false;
          }
          if (*) {
            // Stop execution
            assume false;
          }
          if (*) {
            // Exhale precondition of function application
            assert {:msg "  Precondition of function int___eq__ might not hold. Assertion issubtype(typeof(__prim__int___box__(list___len__(_checkDefined(res, 7562610)))), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.67--715.217) [2394]"}
              (issubtype((typeof(__prim__int___box__(Heap, list___len__(Heap, _checkDefined(Heap, res, 7562610)))): PyTypeDomainType), vint): bool);
            assert {:msg "  Precondition of function int___eq__ might not hold. Assertion issubtype(typeof(__prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.67--715.217) [2395]"}
              (issubtype((typeof(__prim__int___box__(Heap, PSeq___len__(Heap, PSeq___create__(Heap, Heap[iter, __previous], vint)))): PyTypeDomainType), vint): bool);
            // Stop execution
            assume false;
          }
        assume int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, _checkDefined(Heap, res, 7562610))), __prim__int___box__(Heap, PSeq___len__(Heap, PSeq___create__(Heap, Heap[iter, __previous], vint))));
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write))
          if (*) {
            if ((issubtype((typeof(lambda46_30$t_3): PyTypeDomainType), Ticket): bool)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2396]"}
                HasDirectPerm(Mask, _checkDefined(Heap, res, 7562610), list_acc);
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@716.177--716.204) [2397]"}
                  _isDefined(Heap, 7562610);
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        havoc QPMask;
        
        // -- check if receiver acc(Ticket_state(lambda46_30$t), write) is injective
          assert {:msg "  Contract might not be well-formed. Quantified resource Ticket_state(lambda46_30$t) might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2398]"}
            (forall lambda46_30$t_5: Ref, lambda46_30$t_5_1: Ref ::
            { neverTriggered3(lambda46_30$t_5), neverTriggered3(lambda46_30$t_5_1) }
            (((lambda46_30$t_5 != lambda46_30$t_5_1 && ((issubtype((typeof(lambda46_30$t_5): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_5))) && ((issubtype((typeof(lambda46_30$t_5_1): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_5_1))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_5 != lambda46_30$t_5_1
          );
        
        // -- Define Inverse Function
          assume (forall lambda46_30$t_5: Ref ::
            { Heap[null, Ticket_state(lambda46_30$t_5)] } { Mask[null, Ticket_state(lambda46_30$t_5)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_5) }
            ((issubtype((typeof(lambda46_30$t_5): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_5)) && NoPerm < FullPerm ==> invRecv3(lambda46_30$t_5) == lambda46_30$t_5 && qpRange3(lambda46_30$t_5)
          );
          assume (forall self_1_1: Ref ::
            { invRecv3(self_1_1) }
            (((issubtype((typeof(invRecv3(self_1_1)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv3(self_1_1))) && NoPerm < FullPerm) && qpRange3(self_1_1) ==> invRecv3(self_1_1) == self_1_1
          );
        
        // -- Define updated permissions
          assume (forall self_1_1: Ref ::
            { QPMask[null, Ticket_state(self_1_1)] }
            (((issubtype((typeof(invRecv3(self_1_1)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv3(self_1_1))) && NoPerm < FullPerm) && qpRange3(self_1_1) ==> (NoPerm < FullPerm ==> invRecv3(self_1_1) == self_1_1) && QPMask[null, Ticket_state(self_1_1)] == Mask[null, Ticket_state(self_1_1)] + FullPerm
          );
        
        // -- Define independent locations
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
            (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 4 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
          assume (forall self_1_1: Ref ::
            { QPMask[null, Ticket_state(self_1_1)] }
            !((((issubtype((typeof(invRecv3(self_1_1)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv3(self_1_1))) && NoPerm < FullPerm) && qpRange3(self_1_1)) ==> QPMask[null, Ticket_state(self_1_1)] == Mask[null, Ticket_state(self_1_1)]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write))
          if (*) {
            if ((issubtype((typeof(lambda46_30$t_4): PyTypeDomainType), Ticket): bool)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2399]"}
                HasDirectPerm(Mask, _checkDefined(Heap, res, 7562610), list_acc);
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@716.417--716.444) [2400]"}
                  _isDefined(Heap, 7562610);
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        havoc QPMask;
        assert {:msg "  Contract might not be well-formed. Quantified resource lambda46_30$t.Ticket_discount_code might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2401]"}
          (forall lambda46_30$t_8: Ref, lambda46_30$t_8_1: Ref ::
          
          (((lambda46_30$t_8 != lambda46_30$t_8_1 && ((issubtype((typeof(lambda46_30$t_8): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_8) && code_1 != null))) && ((issubtype((typeof(lambda46_30$t_8_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_8_1) && code_1 != null))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_8 != lambda46_30$t_8_1
        );
        
        // -- Define Inverse Function
          assume (forall lambda46_30$t_8: Ref ::
            { Heap[lambda46_30$t_8, Ticket_discount_code] } { QPMask[lambda46_30$t_8, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_8) }
            ((issubtype((typeof(lambda46_30$t_8): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_8) && code_1 != null)) && NoPerm < FullPerm ==> qpRange4(lambda46_30$t_8) && invRecv4(lambda46_30$t_8) == lambda46_30$t_8
          );
          assume (forall o_4: Ref ::
            { invRecv4(o_4) }
            (((issubtype((typeof(invRecv4(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv4(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange4(o_4) ==> invRecv4(o_4) == o_4
          );
        
        // -- Assume set of fields is nonNull
          assume (forall lambda46_30$t_8: Ref ::
            { Heap[lambda46_30$t_8, Ticket_discount_code] } { QPMask[lambda46_30$t_8, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_8) }
            (issubtype((typeof(lambda46_30$t_8): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_8) && code_1 != null) ==> lambda46_30$t_8 != null
          );
        
        // -- Define permissions
          assume (forall o_4: Ref ::
            { QPMask[o_4, Ticket_discount_code] }
            ((((issubtype((typeof(invRecv4(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv4(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange4(o_4) ==> (NoPerm < FullPerm ==> invRecv4(o_4) == o_4) && QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code] + FullPerm) && (!((((issubtype((typeof(invRecv4(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv4(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange4(o_4)) ==> QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code])
          );
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
            f_6 != Ticket_discount_code ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str()))
          if (*) {
            if ((issubtype((typeof(lambda46_30$t_6): PyTypeDomainType), Ticket): bool)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2402]"}
                HasDirectPerm(Mask, _checkDefined(Heap, res, 7562610), list_acc);
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@716.682--716.709) [2403]"}
                  _isDefined(Heap, 7562610);
                // Stop execution
                assume false;
              }
            }
            if ((issubtype((typeof(lambda46_30$t_6): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_6) && code_1 != null)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access lambda46_30$t.Ticket_discount_code (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2404]"}
                HasDirectPerm(Mask, lambda46_30$t_6, Ticket_discount_code);
            }
            assume false;
          }
        assume (forall lambda46_30$t_10: Ref ::
          { Seq#ContainsTrigger(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_10) } { Seq#Contains(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_10) }
          (issubtype((typeof(lambda46_30$t_10): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_10) && code_1 != null) ==> (issubtype((typeof(Heap[lambda46_30$t_10, Ticket_discount_code]): PyTypeDomainType), str): bool)
        );
        assume state(Heap, Mask);
        if (iter_err == null) {
          assume state(Heap, Mask);
          
          // -- Check definedness of int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610))) > 0
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(495873779059) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@717.62--717.96) [2405]"}
                _isDefined(Heap, 495873779059);
              // Stop execution
              assume false;
            }
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(seats, 495873779059)), list(list_arg(typeof(_checkDefined(seats, 495873779059)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@717.49--717.97) [2406]"}
                (issubtype((typeof(_checkDefined(Heap, seats, 495873779059)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, seats, 495873779059)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
              assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(seats, 495873779059).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@717.49--717.97) [2407]"}
                Mask[_checkDefined(Heap, seats, 495873779059), list_acc] > NoPerm;
              havoc wildcard;
              assume wildcard < Mask[_checkDefined(Heap, seats, 495873779059), list_acc];
              Mask[_checkDefined(Heap, seats, 495873779059), list_acc] := Mask[_checkDefined(Heap, seats, 495873779059), list_acc] - wildcard;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
              // Stop execution
              assume false;
            }
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@717.112--717.139) [2408]"}
                _isDefined(Heap, 7562610);
              // Stop execution
              assume false;
            }
            if (*) {
              // Exhale precondition of function application
              assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(res, 7562610)), list(list_arg(typeof(_checkDefined(res, 7562610)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@717.99--717.140) [2409]"}
                (issubtype((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
              assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@717.99--717.140) [2410]"}
                Mask[_checkDefined(Heap, res, 7562610), list_acc] > NoPerm;
              havoc wildcard;
              assume wildcard < Mask[_checkDefined(Heap, res, 7562610), list_acc];
              Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] - wildcard;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
              // Stop execution
              assume false;
            }
            if (*) {
              // Stop execution
              assume false;
            }
          assume int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610))) > 0;
        }
        perm := FullPerm;
        Mask[null, MustTerminate(_cthread_160)] := Mask[null, MustTerminate(_cthread_160)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
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
        assume state(Heap, Mask);
        assume (forall _r_1_5: Ref ::
          { Mask[_r_1_5, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_1_5, MustReleaseBounded) ==> Level(Heap, _r_1_5) <= _residue_161
        );
        assume state(Heap, Mask);
        assume (forall _r_1_6: Ref ::
          { Mask[_r_1_6, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_1_6, MustReleaseUnbounded) ==> Level(Heap, _r_1_6) <= _residue_161
        );
        assume _residue_160 <= _residue_161;
        perm := 1 / 20;
        assert {:msg "  While statement might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2411]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> iterable != null;
        Mask[iterable, list_acc] := Mask[iterable, list_acc] + perm;
        assume state(Heap, Mask);
        perm := 1 / 20;
        assert {:msg "  While statement might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2412]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> iter != null;
        Mask[iter, list_acc] := Mask[iter, list_acc] + perm;
        assume state(Heap, Mask);
        assume Seq#Equal(Heap[iter, list_acc], Heap[iterable, list_acc]);
        assume Seq#Equal(seqtmp, Heap[iterable, list_acc]);
        perm := FullPerm;
        assume iter != null;
        Mask[iter, __iter_index] := Mask[iter, __iter_index] + perm;
        assume state(Heap, Mask);
        perm := FullPerm;
        assume iter != null;
        Mask[iter, __previous] := Mask[iter, __previous] + perm;
        assume state(Heap, Mask);
        if (iter_err == null) {
          assume Heap[iter, __iter_index] - 1 == Seq#Length(Heap[iter, __previous]);
        }
        if (iter_err != null) {
          assume Heap[iter, __iter_index] == Seq#Length(Heap[iter, __previous]);
        }
        if (iter_err == null) {
          assume Seq#Length(Heap[iter, list_acc]) > 0;
        }
        assume Heap[iter, __iter_index] >= 0;
        assume Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume Heap[iter, __iter_index] > 0;
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume Seq#Contains(Heap[iter, list_acc], loop_target);
        }
        if (iter_err == null) {
          assume Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume (issubtype((typeof(loop_target): PyTypeDomainType), (tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): bool);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume state(Heap, Mask);
          assume row_0 == tuple___getitem__(Heap, loop_target, 0);
          assume state(Heap, Mask);
          assume _isDefined(Heap, 207760093042);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assume state(Heap, Mask);
          assume seat_0 == tuple___getitem__(Heap, loop_target, 1);
          assume state(Heap, Mask);
          assume _isDefined(Heap, 53186532566387);
        }
        if (iter_err != null) {
          assume Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
        }
        if (Seq#Length(Heap[iter, list_acc]) == 0) {
          assume iter_err != null;
        }
        assume state(Heap, Mask);
        perm := FullPerm;
        assume _checkDefined(Heap, res, 7562610) != null;
        Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, _checkDefined(Heap, res, 7562610))), __prim__int___box__(Heap, PSeq___len__(Heap, PSeq___create__(Heap, Heap[iter, __previous], vint))));
        assume state(Heap, Mask);
        havoc QPMask;
        
        // -- check if receiver acc(Ticket_state(lambda46_30$t), write) is injective
          assert {:msg "  While statement might fail. Quantified resource Ticket_state(lambda46_30$t) might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2413]"}
            (forall lambda46_30$t_11: Ref, lambda46_30$t_11_1: Ref ::
            { neverTriggered5(lambda46_30$t_11), neverTriggered5(lambda46_30$t_11_1) }
            (((lambda46_30$t_11 != lambda46_30$t_11_1 && ((issubtype((typeof(lambda46_30$t_11): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_11))) && ((issubtype((typeof(lambda46_30$t_11_1): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_11_1))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_11 != lambda46_30$t_11_1
          );
        
        // -- Define Inverse Function
          assume (forall lambda46_30$t_11: Ref ::
            { Heap[null, Ticket_state(lambda46_30$t_11)] } { Mask[null, Ticket_state(lambda46_30$t_11)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_11) }
            ((issubtype((typeof(lambda46_30$t_11): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_11)) && NoPerm < FullPerm ==> invRecv5(lambda46_30$t_11) == lambda46_30$t_11 && qpRange5(lambda46_30$t_11)
          );
          assume (forall self_1_2: Ref ::
            { invRecv5(self_1_2) }
            (((issubtype((typeof(invRecv5(self_1_2)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv5(self_1_2))) && NoPerm < FullPerm) && qpRange5(self_1_2) ==> invRecv5(self_1_2) == self_1_2
          );
        
        // -- Define updated permissions
          assume (forall self_1_2: Ref ::
            { QPMask[null, Ticket_state(self_1_2)] }
            (((issubtype((typeof(invRecv5(self_1_2)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv5(self_1_2))) && NoPerm < FullPerm) && qpRange5(self_1_2) ==> (NoPerm < FullPerm ==> invRecv5(self_1_2) == self_1_2) && QPMask[null, Ticket_state(self_1_2)] == Mask[null, Ticket_state(self_1_2)] + FullPerm
          );
        
        // -- Define independent locations
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
            (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 4 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
          assume (forall self_1_2: Ref ::
            { QPMask[null, Ticket_state(self_1_2)] }
            !((((issubtype((typeof(invRecv5(self_1_2)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv5(self_1_2))) && NoPerm < FullPerm) && qpRange5(self_1_2)) ==> QPMask[null, Ticket_state(self_1_2)] == Mask[null, Ticket_state(self_1_2)]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        havoc QPMask;
        assert {:msg "  While statement might fail. Quantified resource lambda46_30$t.Ticket_discount_code might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2414]"}
          (forall lambda46_30$t_13: Ref, lambda46_30$t_13_1: Ref ::
          
          (((lambda46_30$t_13 != lambda46_30$t_13_1 && ((issubtype((typeof(lambda46_30$t_13): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_13) && code_1 != null))) && ((issubtype((typeof(lambda46_30$t_13_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_13_1) && code_1 != null))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_13 != lambda46_30$t_13_1
        );
        
        // -- Define Inverse Function
          assume (forall lambda46_30$t_13: Ref ::
            { Heap[lambda46_30$t_13, Ticket_discount_code] } { QPMask[lambda46_30$t_13, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_13) }
            ((issubtype((typeof(lambda46_30$t_13): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_13) && code_1 != null)) && NoPerm < FullPerm ==> qpRange6(lambda46_30$t_13) && invRecv6(lambda46_30$t_13) == lambda46_30$t_13
          );
          assume (forall o_4: Ref ::
            { invRecv6(o_4) }
            (((issubtype((typeof(invRecv6(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv6(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange6(o_4) ==> invRecv6(o_4) == o_4
          );
        
        // -- Assume set of fields is nonNull
          assume (forall lambda46_30$t_13: Ref ::
            { Heap[lambda46_30$t_13, Ticket_discount_code] } { QPMask[lambda46_30$t_13, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_13) }
            (issubtype((typeof(lambda46_30$t_13): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_13) && code_1 != null) ==> lambda46_30$t_13 != null
          );
        
        // -- Define permissions
          assume (forall o_4: Ref ::
            { QPMask[o_4, Ticket_discount_code] }
            ((((issubtype((typeof(invRecv6(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv6(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange6(o_4) ==> (NoPerm < FullPerm ==> invRecv6(o_4) == o_4) && QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code] + FullPerm) && (!((((issubtype((typeof(invRecv6(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv6(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange6(o_4)) ==> QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code])
          );
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
            f_6 != Ticket_discount_code ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume (forall lambda46_30$t_14: Ref ::
          { Seq#ContainsTrigger(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_14) } { Seq#Contains(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_14) }
          (issubtype((typeof(lambda46_30$t_14): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_14) && code_1 != null) ==> (issubtype((typeof(Heap[lambda46_30$t_14, Ticket_discount_code]): PyTypeDomainType), str): bool)
        );
        if (iter_err == null) {
          assume state(Heap, Mask);
          assume int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610))) > 0;
        }
        perm := FullPerm;
        Mask[null, MustTerminate(_cthread_160)] := Mask[null, MustTerminate(_cthread_160)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        // Check and assume guard
        assume iter_err == null;
        assume state(Heap, Mask);
        
        // -- Translate loop body
          
          // -- Translating statement: // id = 75
  // _loop_measures := Seq(Measure$create(true, _cthread_160, int___sub__(list___len__(_checkDefined(seats,
  //   495873779059)), list___len__(_checkDefined(res, 7562610))))) -- testsfunctionalverificationexamplescav_example.py.vpr@721.5--721.168
            
            // -- Check definedness of Seq(Measure$create(true, _cthread_160, int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610)))))
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(495873779059) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@721.87--721.121) [2415]"}
                  _isDefined(Heap, 495873779059);
                // Stop execution
                assume false;
              }
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(seats, 495873779059)), list(list_arg(typeof(_checkDefined(seats, 495873779059)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@721.74--721.122) [2416]"}
                  (issubtype((typeof(_checkDefined(Heap, seats, 495873779059)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, seats, 495873779059)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
                assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(seats, 495873779059).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@721.74--721.122) [2417]"}
                  Mask[_checkDefined(Heap, seats, 495873779059), list_acc] > NoPerm;
                havoc wildcard;
                assume wildcard < Mask[_checkDefined(Heap, seats, 495873779059), list_acc];
                Mask[_checkDefined(Heap, seats, 495873779059), list_acc] := Mask[_checkDefined(Heap, seats, 495873779059), list_acc] - wildcard;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@721.137--721.164) [2418]"}
                  _isDefined(Heap, 7562610);
                // Stop execution
                assume false;
              }
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(res, 7562610)), list(list_arg(typeof(_checkDefined(res, 7562610)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@721.124--721.165) [2419]"}
                  (issubtype((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
                assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@721.124--721.165) [2420]"}
                  Mask[_checkDefined(Heap, res, 7562610), list_acc] > NoPerm;
                havoc wildcard;
                assume wildcard < Mask[_checkDefined(Heap, res, 7562610), list_acc];
                Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] - wildcard;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              if (*) {
                // Stop execution
                assume false;
              }
            _loop_measures := Seq#Singleton((Measure$create(true, _cthread_160, int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610)))): Measure$DomainType));
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 76
  // Ticket_res := new() -- testsfunctionalverificationexamplescav_example.py.vpr@722.5--722.24
            havoc freshObj;
            assume freshObj != null && !Heap[freshObj, $allocated];
            Heap[freshObj, $allocated] := true;
            Ticket_res := freshObj;
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 77
  // inhale typeof(Ticket_res) == Ticket() -- testsfunctionalverificationexamplescav_example.py.vpr@723.5--723.42
            assume (typeof(Ticket_res): PyTypeDomainType) == Ticket;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 78
  // inhale acc(_MaySet(Ticket_res, 2036589462893379814238060391131476), write) -- testsfunctionalverificationexamplescav_example.py.vpr@724.5--724.79
            perm := FullPerm;
            Mask[null, _MaySet(Ticket_res, 2036589462893379814238060391131476)] := Mask[null, _MaySet(Ticket_res, 2036589462893379814238060391131476)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 79
  // inhale acc(_MaySet(Ticket_res, 564017441487491594152276), write) -- testsfunctionalverificationexamplescav_example.py.vpr@725.5--725.69
            perm := FullPerm;
            Mask[null, _MaySet(Ticket_res, 564017441487491594152276)] := Mask[null, _MaySet(Ticket_res, 564017441487491594152276)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 80
  // inhale acc(_MaySet(Ticket_res, 140695336058778200607779156), write) -- testsfunctionalverificationexamplescav_example.py.vpr@726.5--726.72
            perm := FullPerm;
            Mask[null, _MaySet(Ticket_res, 140695336058778200607779156)] := Mask[null, _MaySet(Ticket_res, 140695336058778200607779156)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 81
  // inhale acc(_MaySet(Ticket_res, 578847845651634811226368290157834565233854867796), write) -- testsfunctionalverificationexamplescav_example.py.vpr@727.5--727.93
            perm := FullPerm;
            Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 82
  // _cwl_160 := Ticket___init__(_cthread_160, _method_measures_160, _residue_161,
  //   Ticket_res, show_id_0, _checkDefined(row_0, 207760093042), _checkDefined(seat_0,
  //   53186532566387)) -- testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180
            PreCallHeap := Heap;
            PreCallMask := Mask;
            
            // -- Check definedness of _checkDefined(row_0, 207760093042)
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(207760093042) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.106--728.140) [2421]"}
                  _isDefined(Heap, 207760093042);
                // Stop execution
                assume false;
              }
            
            // -- Check definedness of _checkDefined(seat_0, 53186532566387)
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(53186532566387) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.142--728.179) [2422]"}
                  _isDefined(Heap, 53186532566387);
                // Stop execution
                assume false;
              }
            arg_row := _checkDefined(Heap, row_0, 207760093042);
            arg_seat := _checkDefined(Heap, seat_0, 53186532566387);
            havoc _cwl_160;
            
            // -- Exhaling precondition
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2423]"}
                _cthread_160 != null;
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2424]"}
                (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion Ticket_res != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2425]"}
                Ticket_res != null;
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Ticket___init__ might not hold. There might be insufficient permission to access _MaySet(Ticket_res, 2036589462893379814238060391131476) (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2426]"}
                  perm <= Mask[null, _MaySet(Ticket_res, 2036589462893379814238060391131476)];
              }
              Mask[null, _MaySet(Ticket_res, 2036589462893379814238060391131476)] := Mask[null, _MaySet(Ticket_res, 2036589462893379814238060391131476)] - perm;
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Ticket___init__ might not hold. There might be insufficient permission to access _MaySet(Ticket_res, 564017441487491594152276) (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2427]"}
                  perm <= Mask[null, _MaySet(Ticket_res, 564017441487491594152276)];
              }
              Mask[null, _MaySet(Ticket_res, 564017441487491594152276)] := Mask[null, _MaySet(Ticket_res, 564017441487491594152276)] - perm;
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Ticket___init__ might not hold. There might be insufficient permission to access _MaySet(Ticket_res, 140695336058778200607779156) (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2428]"}
                  perm <= Mask[null, _MaySet(Ticket_res, 140695336058778200607779156)];
              }
              Mask[null, _MaySet(Ticket_res, 140695336058778200607779156)] := Mask[null, _MaySet(Ticket_res, 140695336058778200607779156)] - perm;
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Ticket___init__ might not hold. There might be insufficient permission to access _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796) (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2429]"}
                  perm <= Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)];
              }
              Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)] - perm;
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion issubtype(typeof(Ticket_res), Ticket()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2430]"}
                (issubtype((typeof(Ticket_res): PyTypeDomainType), Ticket): bool);
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion issubtype(typeof(show_id_0), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2431]"}
                (issubtype((typeof(show_id_0): PyTypeDomainType), vint): bool);
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion issubtype(typeof(_checkDefined(row_0, 207760093042)), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2432]"}
                (issubtype((typeof(arg_row): PyTypeDomainType), vint): bool);
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion issubtype(typeof(_checkDefined(seat_0, 53186532566387)), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2433]"}
                (issubtype((typeof(arg_seat): PyTypeDomainType), vint): bool);
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion Ticket_res != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2434]"}
                Ticket_res != null;
              assert {:msg "  The precondition of method Ticket___init__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_8: Ref [MustInvokeBounded(_r_8)] :: false) && ((forperm _r_8: Ref [MustInvokeUnbounded(_r_8)] :: false) && ((forperm _r_8: Ref [_r_8.MustReleaseBounded] :: false) && (forperm _r_8: Ref [_r_8.MustReleaseUnbounded] :: false)))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@728.5--728.180) [2435]"}
                Measure$check(Heap, _method_measures_160, _cthread_160, 1) || (Mask[null, MustTerminate(_cthread_160)] == NoPerm && ((forall _r_8: Ref ::
                { Mask[null, MustInvokeBounded(_r_8)] }
                HasDirectPerm(Mask, null, MustInvokeBounded(_r_8)) ==> false
              ) && ((forall _r_8_1: Ref ::
                { Mask[null, MustInvokeUnbounded(_r_8_1)] }
                HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_8_1)) ==> false
              ) && ((forall _r_8_2: Ref ::
                { Mask[_r_8_2, MustReleaseBounded] }
                HasDirectPerm(Mask, _r_8_2, MustReleaseBounded) ==> false
              ) && (forall _r_8_3: Ref ::
                { Mask[_r_8_3, MustReleaseUnbounded] }
                HasDirectPerm(Mask, _r_8_3, MustReleaseUnbounded) ==> false
              )))));
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
            
            // -- Inhaling postcondition
              assume state(Heap, Mask);
              assume (forall _r_6_1: Ref ::
                { Mask[_r_6_1, MustReleaseBounded] }
                HasDirectPerm(Mask, _r_6_1, MustReleaseBounded) ==> Level(Heap, _r_6_1) <= _cwl_160
              );
              assume state(Heap, Mask);
              assume (forall _r_6_1_1: Ref ::
                { Mask[_r_6_1_1, MustReleaseUnbounded] }
                HasDirectPerm(Mask, _r_6_1_1, MustReleaseUnbounded) ==> Level(Heap, _r_6_1_1) <= _cwl_160
              );
              assume _residue_161 <= _cwl_160;
              perm := FullPerm;
              Mask[null, Ticket_state(Ticket_res)] := Mask[null, Ticket_state(Ticket_res)] + perm;
              assume state(Heap, Mask);
              perm := FullPerm;
              Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(Ticket_res, 578847845651634811226368290157834565233854867796)] + perm;
              assume state(Heap, Mask);
              assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 83
  // ticket := Ticket_res -- testsfunctionalverificationexamplescav_example.py.vpr@729.5--729.25
            ticket := Ticket_res;
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 84
  // inhale _isDefined(127978942196084) -- testsfunctionalverificationexamplescav_example.py.vpr@730.5--730.39
            assume state(Heap, Mask);
            
            // -- Check definedness of _isDefined(127978942196084)
              if (*) {
                // Stop execution
                assume false;
              }
            assume _isDefined(Heap, 127978942196084);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: if (code_1 != null) -- testsfunctionalverificationexamplescav_example.py.vpr@731.5--737.6
            if (code_1 != null) {
              
              // -- Translating statement: // id = 85
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
                assume state(Heap, Mask);
              
              // -- Translating statement: if (perm(_MaySet(_checkDefined(ticket, 127978942196084), 578847845651634811226368290157834565233854867796)) > none) -- testsfunctionalverificationexamplescav_example.py.vpr@732.7--735.8
                
                // -- Check definedness of perm(_MaySet(_checkDefined(ticket, 127978942196084), 578847845651634811226368290157834565233854867796)) > none
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(127978942196084) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@732.24--732.62) [2436]"}
                      _isDefined(Heap, 127978942196084);
                    // Stop execution
                    assume false;
                  }
                if (NoPerm < Mask[null, _MaySet(_checkDefined(Heap, ticket, 127978942196084), 578847845651634811226368290157834565233854867796)]) {
                  
                  // -- Translating statement: // id = 86
  // exhale acc(_MaySet(_checkDefined(ticket, 127978942196084), 578847845651634811226368290157834565233854867796), write) -- testsfunctionalverificationexamplescav_example.py.vpr@733.9--733.125
                    
                    // -- Check definedness of acc(_MaySet(_checkDefined(ticket, 127978942196084), 578847845651634811226368290157834565233854867796), write)
                      if (*) {
                        // Exhale precondition of function application
                        assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(127978942196084) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@733.28--733.66) [2437]"}
                          _isDefined(Heap, 127978942196084);
                        // Stop execution
                        assume false;
                      }
                    perm := FullPerm;
                    if (perm != NoPerm) {
                      assert {:msg "  Exhale might fail. There might be insufficient permission to access _MaySet(_checkDefined(ticket, 127978942196084), 578847845651634811226368290157834565233854867796) (testsfunctionalverificationexamplescav_example.py.vpr@733.16--733.125) [2438]"}
                        perm <= Mask[null, _MaySet(_checkDefined(Heap, ticket, 127978942196084), 578847845651634811226368290157834565233854867796)];
                    }
                    Mask[null, _MaySet(_checkDefined(Heap, ticket, 127978942196084), 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(_checkDefined(Heap, ticket, 127978942196084), 578847845651634811226368290157834565233854867796)] - perm;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    assume state(Heap, Mask);
                  
                  // -- Translating statement: // id = 87
  // inhale acc(_checkDefined(ticket, 127978942196084).Ticket_discount_code, write) -- testsfunctionalverificationexamplescav_example.py.vpr@734.9--734.87
                    assume state(Heap, Mask);
                    
                    // -- Check definedness of acc(_checkDefined(ticket, 127978942196084).Ticket_discount_code, write)
                      if (*) {
                        // Exhale precondition of function application
                        assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(127978942196084) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@734.20--734.58) [2439]"}
                          _isDefined(Heap, 127978942196084);
                        // Stop execution
                        assume false;
                      }
                    perm := FullPerm;
                    assume _checkDefined(Heap, ticket, 127978942196084) != null;
                    Mask[_checkDefined(Heap, ticket, 127978942196084), Ticket_discount_code] := Mask[_checkDefined(Heap, ticket, 127978942196084), Ticket_discount_code] + perm;
                    assume state(Heap, Mask);
                    assume state(Heap, Mask);
                    assume state(Heap, Mask);
                } else {
                  
                  // -- Translating statement: // id = 88
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
                    assume state(Heap, Mask);
                }
                assume state(Heap, Mask);
              
              // -- Translating statement: // id = 89
  // _checkDefined(ticket, 127978942196084).Ticket_discount_code := code_1 -- testsfunctionalverificationexamplescav_example.py.vpr@736.7--736.76
                
                // -- Check definedness of _checkDefined(ticket, 127978942196084)
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(127978942196084) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@736.7--736.45) [2440]"}
                      _isDefined(Heap, 127978942196084);
                    // Stop execution
                    assume false;
                  }
                assert {:msg "  Assignment might fail. There might be insufficient permission to access _checkDefined(ticket, 127978942196084).Ticket_discount_code (testsfunctionalverificationexamplescav_example.py.vpr@736.7--736.76) [2441]"}
                  FullPerm == Mask[_checkDefined(Heap, ticket, 127978942196084), Ticket_discount_code];
                Heap[_checkDefined(Heap, ticket, 127978942196084), Ticket_discount_code] := code_1;
                assume state(Heap, Mask);
            } else {
              
              // -- Translating statement: // id = 90
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
                assume state(Heap, Mask);
            }
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 91
  // _cwl_160 := list_append(_cthread_160, _method_measures_160, _residue_161, _checkDefined(res,
  //   7562610), _checkDefined(ticket, 127978942196084)) -- testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147
            PreCallHeap := Heap;
            PreCallMask := Mask;
            
            // -- Check definedness of _checkDefined(res, 7562610)
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.79--738.106) [2442]"}
                  _isDefined(Heap, 7562610);
                // Stop execution
                assume false;
              }
            
            // -- Check definedness of _checkDefined(ticket, 127978942196084)
              if (*) {
                // Exhale precondition of function application
                assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(127978942196084) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.108--738.146) [2443]"}
                  _isDefined(Heap, 127978942196084);
                // Stop execution
                assume false;
              }
            arg_self := _checkDefined(Heap, res, 7562610);
            arg_item := _checkDefined(Heap, ticket, 127978942196084);
            havoc _cwl_160;
            
            // -- Exhaling precondition
              assert {:msg "  The precondition of method list_append might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2444]"}
                _cthread_160 != null;
              assert {:msg "  The precondition of method list_append might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2445]"}
                Measure$check(Heap, _method_measures_160, _cthread_160, 1);
              assert {:msg "  The precondition of method list_append might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2446]"}
                (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
              assert {:msg "  The precondition of method list_append might not hold. Assertion issubtype(typeof(_checkDefined(res, 7562610)), list(list_arg(typeof(_checkDefined(res, 7562610)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2447]"}
                (issubtype((typeof(arg_self): PyTypeDomainType), (list((list_arg((typeof(arg_self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method list_append might not hold. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2448]"}
                  perm <= Mask[arg_self, list_acc];
              }
              Mask[arg_self, list_acc] := Mask[arg_self, list_acc] - perm;
              assert {:msg "  The precondition of method list_append might not hold. Assertion issubtype(typeof(_checkDefined(ticket, 127978942196084)), list_arg(typeof(_checkDefined(res, 7562610)), 0)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2449]"}
                (issubtype((typeof(arg_item): PyTypeDomainType), (list_arg((typeof(arg_self): PyTypeDomainType), 0): PyTypeDomainType)): bool);
              assert {:msg "  The precondition of method list_append might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@738.5--738.147) [2450]"}
                Measure$check(Heap, _method_measures_160, _cthread_160, 1);
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
            
            // -- Inhaling postcondition
              assume state(Heap, Mask);
              assume (forall _r_21: Ref ::
                { Mask[_r_21, MustReleaseBounded] }
                HasDirectPerm(Mask, _r_21, MustReleaseBounded) ==> Level(Heap, _r_21) <= _cwl_160
              );
              assume state(Heap, Mask);
              assume (forall _r_21_1: Ref ::
                { Mask[_r_21_1, MustReleaseUnbounded] }
                HasDirectPerm(Mask, _r_21_1, MustReleaseUnbounded) ==> Level(Heap, _r_21_1) <= _cwl_160
              );
              assume _residue_161 <= _cwl_160;
              perm := FullPerm;
              assume arg_self != null;
              Mask[arg_self, list_acc] := Mask[arg_self, list_acc] + perm;
              assume state(Heap, Mask);
              assume Seq#Equal(Heap[arg_self, list_acc], Seq#Append(old(PreCallHeap)[arg_self, list_acc], Seq#Singleton(arg_item)));
              assume state(Heap, Mask);
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 92
  // label loop_end -- testsfunctionalverificationexamplescav_example.py.vpr@739.5--739.19
            loop_end:
            Labelloop_endMask := Mask;
            Labelloop_endHeap := Heap;
            loop_end_lblGuard := true;
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 93
  // _cwl_160, loop_target, iter_err := Iterator___next__(_cthread_160, _method_measures_160,
  //   _residue_160, iter) -- testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113
            PreCallHeap := Heap;
            PreCallMask := Mask;
            havoc _cwl_160, loop_target, iter_err;
            
            // -- Exhaling precondition
              assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2451]"}
                _cthread_160 != null;
              assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2452]"}
                Measure$check(Heap, _method_measures_160, _cthread_160, 1);
              assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2453]"}
                (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
              assert {:msg "  The precondition of method Iterator___next__ might not hold. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2454]"}
                1 / 40 >= NoPerm;
              perm := 1 / 40;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Iterator___next__ might not hold. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2455]"}
                  perm <= Mask[iter, list_acc];
              }
              Mask[iter, list_acc] := Mask[iter, list_acc] - perm;
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Iterator___next__ might not hold. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2456]"}
                  perm <= Mask[iter, __iter_index];
              }
              Mask[iter, __iter_index] := Mask[iter, __iter_index] - perm;
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  The precondition of method Iterator___next__ might not hold. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2457]"}
                  perm <= Mask[iter, __previous];
              }
              Mask[iter, __previous] := Mask[iter, __previous] - perm;
              assert {:msg "  The precondition of method Iterator___next__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2458]"}
                Measure$check(Heap, _method_measures_160, _cthread_160, 1);
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
            
            // -- Inhaling postcondition
              assume state(Heap, Mask);
              assume (forall _r_15_2: Ref ::
                { Mask[_r_15_2, MustReleaseBounded] }
                HasDirectPerm(Mask, _r_15_2, MustReleaseBounded) ==> Level(Heap, _r_15_2) <= _cwl_160
              );
              assume state(Heap, Mask);
              assume (forall _r_15_3: Ref ::
                { Mask[_r_15_3, MustReleaseUnbounded] }
                HasDirectPerm(Mask, _r_15_3, MustReleaseUnbounded) ==> Level(Heap, _r_15_3) <= _cwl_160
              );
              assume _residue_160 <= _cwl_160;
              perm := 1 / 40;
              assert {:msg "  Method call might fail. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@740.5--740.113) [2459]"}
                perm >= NoPerm;
              assume perm > NoPerm ==> iter != null;
              Mask[iter, list_acc] := Mask[iter, list_acc] + perm;
              assume state(Heap, Mask);
              assume Seq#Equal(Heap[iter, list_acc], old(PreCallHeap)[iter, list_acc]);
              perm := FullPerm;
              assume iter != null;
              Mask[iter, __iter_index] := Mask[iter, __iter_index] + perm;
              assume state(Heap, Mask);
              assume Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]) + 1;
              assume (old(PreCallHeap)[iter, __iter_index] == Seq#Length(old(PreCallHeap)[iter, list_acc])) == (iter_err != null);
              perm := FullPerm;
              assume iter != null;
              Mask[iter, __previous] := Mask[iter, __previous] + perm;
              assume state(Heap, Mask);
              if (iter_err == null) {
                assume Heap[iter, __iter_index] == old(PreCallHeap)[iter, __iter_index] + 1;
              }
              if (iter_err == null) {
                assume Heap[iter, __iter_index] > 0;
              }
              if (iter_err == null) {
                assume Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
              }
              if (Seq#Length(Heap[iter, list_acc]) > 0) {
                assume Heap[iter, __iter_index] > 0;
              }
              if (iter_err != null) {
                assume Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
              }
              if (iter_err != null) {
                assume Heap[iter, __iter_index] == Seq#Length(Heap[iter, list_acc]);
              }
              if (Seq#Length(Heap[iter, list_acc]) > 0) {
                assume loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
                assume Seq#Contains(Heap[iter, list_acc], loop_target);
              }
              if (Seq#Length(Heap[iter, list_acc]) > 0) {
                assume (issubtype((typeof(loop_target): PyTypeDomainType), (Iterator_arg((typeof(iter): PyTypeDomainType), 0): PyTypeDomainType)): bool);
              }
              assume (forall r_1_1: Ref ::
                { Seq#ContainsTrigger(Heap[iter, __previous], r_1_1) } { Seq#Contains(Heap[iter, __previous], r_1_1) }
                Seq#Contains(Heap[iter, __previous], r_1_1) == (Seq#Contains(old(PreCallHeap)[iter, __previous], r_1_1) || ((Heap[iter, __iter_index] > 1 && (r_1_1 == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 2) && iter_err == null)) || (Heap[iter, __iter_index] > 0 && (iter_err != null && r_1_1 == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1)))))
              );
              assume state(Heap, Mask);
            assume Heap[loop_target, $allocated];
            assume Heap[iter_err, $allocated];
            assume state(Heap, Mask);
          
          // -- Translating statement: if (iter_err == null) -- testsfunctionalverificationexamplescav_example.py.vpr@741.5--746.6
            if (iter_err == null) {
              
              // -- Translating statement: // id = 94
  // row_0 := tuple___getitem__(loop_target, 0) -- testsfunctionalverificationexamplescav_example.py.vpr@742.7--742.49
                
                // -- Check definedness of tuple___getitem__(loop_target, 0)
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(loop_target)) in (0 >= 0 ==> 0 < ln) && (0 < 0 ==> 0 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@742.16--742.49) [2460]"}
                      0 < tuple___len__(Heap, loop_target);
                    
                    // -- Free assumptions (exhale module)
                      ln_9 := tuple___len__(Heap, loop_target);
                    // Stop execution
                    assume false;
                  }
                row_0 := tuple___getitem__(Heap, loop_target, 0);
                assume state(Heap, Mask);
              
              // -- Translating statement: // id = 95
  // inhale _isDefined(207760093042) -- testsfunctionalverificationexamplescav_example.py.vpr@743.7--743.38
                assume state(Heap, Mask);
                
                // -- Check definedness of _isDefined(207760093042)
                  if (*) {
                    // Stop execution
                    assume false;
                  }
                assume _isDefined(Heap, 207760093042);
                assume state(Heap, Mask);
                assume state(Heap, Mask);
              
              // -- Translating statement: // id = 96
  // seat_0 := tuple___getitem__(loop_target, 1) -- testsfunctionalverificationexamplescav_example.py.vpr@744.7--744.50
                
                // -- Check definedness of tuple___getitem__(loop_target, 1)
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(loop_target)) in (1 >= 0 ==> 1 < ln) && (1 < 0 ==> 1 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@744.17--744.50) [2461]"}
                      1 < tuple___len__(Heap, loop_target);
                    
                    // -- Free assumptions (exhale module)
                      ln_11 := tuple___len__(Heap, loop_target);
                    // Stop execution
                    assume false;
                  }
                seat_0 := tuple___getitem__(Heap, loop_target, 1);
                assume state(Heap, Mask);
              
              // -- Translating statement: // id = 97
  // inhale _isDefined(53186532566387) -- testsfunctionalverificationexamplescav_example.py.vpr@745.7--745.40
                assume state(Heap, Mask);
                
                // -- Check definedness of _isDefined(53186532566387)
                  if (*) {
                    // Stop execution
                    assume false;
                  }
                assume _isDefined(Heap, 53186532566387);
                assume state(Heap, Mask);
                assume state(Heap, Mask);
            } else {
              
              // -- Translating statement: // id = 98
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
                assume state(Heap, Mask);
            }
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 99
  // _loop_check_before := false -- testsfunctionalverificationexamplescav_example.py.vpr@748.5--748.32
            _loop_check_before := false;
            assume state(Heap, Mask);
          
          // -- Translating statement: // id = 100
  // assert _loop_termination_flag ==>
  //   !(iter_err == null) ||
  //   Measure$check(_loop_measures, _cthread_160, int___sub__(list___len__(_checkDefined(seats,
  //   495873779059)), list___len__(_checkDefined(res, 7562610)))) -- testsfunctionalverificationexamplescav_example.py.vpr@750.5--750.211
            
            // -- Check definedness of _loop_termination_flag ==> !(iter_err == null) || Measure$check(_loop_measures, _cthread_160, int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610))))
              if (_loop_termination_flag) {
                if (iter_err == null) {
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(495873779059) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@750.131--750.165) [2462]"}
                      _isDefined(Heap, 495873779059);
                    // Stop execution
                    assume false;
                  }
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(seats, 495873779059)), list(list_arg(typeof(_checkDefined(seats, 495873779059)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@750.118--750.166) [2463]"}
                      (issubtype((typeof(_checkDefined(Heap, seats, 495873779059)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, seats, 495873779059)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
                    assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(seats, 495873779059).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@750.118--750.166) [2464]"}
                      Mask[_checkDefined(Heap, seats, 495873779059), list_acc] > NoPerm;
                    havoc wildcard;
                    assume wildcard < Mask[_checkDefined(Heap, seats, 495873779059), list_acc];
                    Mask[_checkDefined(Heap, seats, 495873779059), list_acc] := Mask[_checkDefined(Heap, seats, 495873779059), list_acc] - wildcard;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    // Stop execution
                    assume false;
                  }
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@750.181--750.208) [2465]"}
                      _isDefined(Heap, 7562610);
                    // Stop execution
                    assume false;
                  }
                  if (*) {
                    // Exhale precondition of function application
                    assert {:msg "  Precondition of function list___len__ might not hold. Assertion issubtype(typeof(_checkDefined(res, 7562610)), list(list_arg(typeof(_checkDefined(res, 7562610)), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@750.168--750.209) [2466]"}
                      (issubtype((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), (list((list_arg((typeof(_checkDefined(Heap, res, 7562610)): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
                    assert {:msg "  Precondition of function list___len__ might not hold. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@750.168--750.209) [2467]"}
                      Mask[_checkDefined(Heap, res, 7562610), list_acc] > NoPerm;
                    havoc wildcard;
                    assume wildcard < Mask[_checkDefined(Heap, res, 7562610), list_acc];
                    Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] - wildcard;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    // Stop execution
                    assume false;
                  }
                  if (*) {
                    // Stop execution
                    assume false;
                  }
                  if (*) {
                    // Stop execution
                    assume false;
                  }
                }
              }
            if (_loop_termination_flag) {
              assert {:msg "  Assert might fail. Assertion !(iter_err == null) || Measure$check(_loop_measures, _cthread_160, int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610)))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@750.12--750.211) [2468]"}
                !(iter_err == null) || Measure$check(Heap, _loop_measures, _cthread_160, int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610))));
            }
            assume state(Heap, Mask);
        // Exhale invariant
        assert {:msg "  Loop invariant acc(iterable.list_acc, 1 / 20) might not be preserved. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2469]"}
          1 / 20 >= NoPerm;
        perm := 1 / 20;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iterable.list_acc, 1 / 20) might not be preserved. There might be insufficient permission to access iterable.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2470]"}
            perm <= Mask[iterable, list_acc];
        }
        Mask[iterable, list_acc] := Mask[iterable, list_acc] - perm;
        assert {:msg "  Loop invariant acc(iter.list_acc, 1 / 20) might not be preserved. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2471]"}
          1 / 20 >= NoPerm;
        perm := 1 / 20;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iter.list_acc, 1 / 20) might not be preserved. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2472]"}
            perm <= Mask[iter, list_acc];
        }
        Mask[iter, list_acc] := Mask[iter, list_acc] - perm;
        assert {:msg "  Loop invariant iter.list_acc == iterable.list_acc might not be preserved. Assertion iter.list_acc == iterable.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@697.15--697.49) [2473]"}
          Seq#Equal(Heap[iter, list_acc], Heap[iterable, list_acc]);
        assert {:msg "  Loop invariant seqtmp == iterable.list_acc might not be preserved. Assertion seqtmp == iterable.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@698.15--698.42) [2474]"}
          Seq#Equal(seqtmp, Heap[iterable, list_acc]);
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iter.__iter_index, write) might not be preserved. There might be insufficient permission to access iter.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@699.15--699.44) [2475]"}
            perm <= Mask[iter, __iter_index];
        }
        Mask[iter, __iter_index] := Mask[iter, __iter_index] - perm;
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(iter.__previous, write) might not be preserved. There might be insufficient permission to access iter.__previous (testsfunctionalverificationexamplescav_example.py.vpr@700.15--700.42) [2476]"}
            perm <= Mask[iter, __previous];
        }
        Mask[iter, __previous] := Mask[iter, __previous] - perm;
        if (iter_err == null) {
          assert {:msg "  Loop invariant iter_err == null ==> iter.__iter_index - 1 == |iter.__previous| might not be preserved. Assertion iter.__iter_index - 1 == |iter.__previous| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@701.15--701.78) [2477]"}
            Heap[iter, __iter_index] - 1 == Seq#Length(Heap[iter, __previous]);
        }
        if (iter_err != null) {
          assert {:msg "  Loop invariant iter_err != null ==> iter.__iter_index == |iter.__previous| might not be preserved. Assertion iter.__iter_index == |iter.__previous| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@702.15--702.74) [2478]"}
            Heap[iter, __iter_index] == Seq#Length(Heap[iter, __previous]);
        }
        if (iter_err == null) {
          assert {:msg "  Loop invariant iter_err == null ==> |iter.list_acc| > 0 might not be preserved. Assertion |iter.list_acc| > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@703.15--703.55) [2479]"}
            Seq#Length(Heap[iter, list_acc]) > 0;
        }
        assert {:msg "  Loop invariant iter.__iter_index >= 0 && iter.__iter_index <= |iter.list_acc| might not be preserved. Assertion iter.__iter_index >= 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2480]"}
          Heap[iter, __iter_index] >= 0;
        assert {:msg "  Loop invariant iter.__iter_index >= 0 && iter.__iter_index <= |iter.list_acc| might not be preserved. Assertion iter.__iter_index <= |iter.list_acc| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@704.15--704.77) [2481]"}
          Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]);
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> iter.__iter_index > 0 might not be preserved. Assertion iter.__iter_index > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@705.15--705.60) [2482]"}
            Heap[iter, __iter_index] > 0;
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> loop_target == iter.list_acc[iter.__iter_index - 1] might not be preserved. Assertion loop_target == iter.list_acc[iter.__iter_index - 1] might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@706.15--706.90) [2483]"}
            loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> (loop_target in iter.list_acc) might not be preserved. Assertion (loop_target in iter.list_acc) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@707.15--707.69) [2484]"}
            Seq#Contains(Heap[iter, list_acc], loop_target);
        }
        if (iter_err == null) {
          assert {:msg "  Loop invariant iter_err == null ==> iter.__previous == iter.list_acc[..iter.__iter_index - 1] might not be preserved. Assertion iter.__previous == iter.list_acc[..iter.__iter_index - 1] might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@708.15--708.93) [2485]"}
            Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> issubtype(typeof(loop_target), tuple(Seq(int(), int()))) might not be preserved. Assertion issubtype(typeof(loop_target), tuple(Seq(int(), int()))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@709.15--709.95) [2486]"}
            (issubtype((typeof(loop_target): PyTypeDomainType), (tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): bool);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> row_0 == tuple___getitem__(loop_target, 0) && _isDefined(207760093042) might not be preserved. Assertion row_0 == tuple___getitem__(loop_target, 0) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@710.15--710.109) [2487]"}
            row_0 == tuple___getitem__(Heap, loop_target, 0);
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> row_0 == tuple___getitem__(loop_target, 0) && _isDefined(207760093042) might not be preserved. Assertion _isDefined(207760093042) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@710.15--710.109) [2488]"}
            _isDefined(Heap, 207760093042);
        }
        if (Seq#Length(Heap[iter, list_acc]) > 0) {
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> seat_0 == tuple___getitem__(loop_target, 1) && _isDefined(53186532566387) might not be preserved. Assertion seat_0 == tuple___getitem__(loop_target, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@711.15--711.112) [2489]"}
            seat_0 == tuple___getitem__(Heap, loop_target, 1);
          assert {:msg "  Loop invariant |iter.list_acc| > 0 ==> seat_0 == tuple___getitem__(loop_target, 1) && _isDefined(53186532566387) might not be preserved. Assertion _isDefined(53186532566387) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@711.15--711.112) [2490]"}
            _isDefined(Heap, 53186532566387);
        }
        if (iter_err != null) {
          assert {:msg "  Loop invariant iter_err != null ==> iter.__previous == iter.list_acc might not be preserved. Assertion iter.__previous == iter.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@712.15--712.68) [2491]"}
            Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
        }
        if (Seq#Length(Heap[iter, list_acc]) == 0) {
          assert {:msg "  Loop invariant |iter.list_acc| == 0 ==> iter_err != null might not be preserved. Assertion iter_err != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@713.15--713.56) [2492]"}
            iter_err != null;
        }
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(_checkDefined(res, 7562610).list_acc, write) && int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))) might not be preserved. There might be insufficient permission to access _checkDefined(res, 7562610).list_acc (testsfunctionalverificationexamplescav_example.py.vpr@715.15--715.217) [2493]"}
            perm <= Mask[_checkDefined(Heap, res, 7562610), list_acc];
        }
        Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] - perm;
        assert {:msg "  Loop invariant acc(_checkDefined(res, 7562610).list_acc, write) && int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))) might not be preserved. Assertion int___eq__(__prim__int___box__(list___len__(_checkDefined(res, 7562610))), __prim__int___box__(PSeq___len__(PSeq___create__(iter.__previous, int())))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@715.15--715.217) [2494]"}
          int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, _checkDefined(Heap, res, 7562610))), __prim__int___box__(Heap, PSeq___len__(Heap, PSeq___create__(Heap, Heap[iter, __previous], vint))));
        havoc QPMask;
        
        // -- check that the permission amount is positive
          
        
        // -- check if receiver acc(Ticket_state(lambda46_30$t), write) is injective
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not be preserved. Quantified resource Ticket_state(lambda46_30$t) might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2495]"}
            (forall lambda46_30$t_15: Ref, lambda46_30$t_15_1: Ref ::
            { neverTriggered7(lambda46_30$t_15), neverTriggered7(lambda46_30$t_15_1) }
            (((lambda46_30$t_15 != lambda46_30$t_15_1 && ((issubtype((typeof(lambda46_30$t_15): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_15))) && ((issubtype((typeof(lambda46_30$t_15_1): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_15_1))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_15 != lambda46_30$t_15_1
          );
        
        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not be preserved. There might be insufficient permission to access Ticket_state(lambda46_30$t) (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2496]"}
            (forall lambda46_30$t_15: Ref ::
            { Heap[null, Ticket_state(lambda46_30$t_15)] } { Mask[null, Ticket_state(lambda46_30$t_15)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_15) }
            (issubtype((typeof(lambda46_30$t_15): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_15) ==> Mask[null, Ticket_state(lambda46_30$t_15)] >= FullPerm
          );
        
        // -- assumptions for inverse of receiver acc(Ticket_state(lambda46_30$t), write)
          assume (forall lambda46_30$t_15: Ref ::
            { Heap[null, Ticket_state(lambda46_30$t_15)] } { Mask[null, Ticket_state(lambda46_30$t_15)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_15) }
            ((issubtype((typeof(lambda46_30$t_15): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_15)) && NoPerm < FullPerm ==> invRecv7(lambda46_30$t_15) == lambda46_30$t_15 && qpRange7(lambda46_30$t_15)
          );
          assume (forall self_1_3: Ref ::
            { invRecv7(self_1_3) }
            (((issubtype((typeof(invRecv7(self_1_3)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv7(self_1_3))) && NoPerm < FullPerm) && qpRange7(self_1_3) ==> invRecv7(self_1_3) == self_1_3
          );
        
        // -- assume permission updates for predicate Ticket_state
          assume (forall self_1_3: Ref ::
            { QPMask[null, Ticket_state(self_1_3)] }
            (((issubtype((typeof(invRecv7(self_1_3)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv7(self_1_3))) && NoPerm < FullPerm) && qpRange7(self_1_3) ==> invRecv7(self_1_3) == self_1_3 && QPMask[null, Ticket_state(self_1_3)] == Mask[null, Ticket_state(self_1_3)] - FullPerm
          );
          assume (forall self_1_3: Ref ::
            { QPMask[null, Ticket_state(self_1_3)] }
            !((((issubtype((typeof(invRecv7(self_1_3)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv7(self_1_3))) && NoPerm < FullPerm) && qpRange7(self_1_3)) ==> QPMask[null, Ticket_state(self_1_3)] == Mask[null, Ticket_state(self_1_3)]
          );
        
        // -- assume permission updates for independent locations 
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
            (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 4 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
        Mask := QPMask;
        havoc QPMask;
        
        // -- check that the permission amount is positive
          
        
        // -- check if receiver lambda46_30$t is injective
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not be preserved. Quantified resource lambda46_30$t.Ticket_discount_code might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2497]"}
            (forall lambda46_30$t_16: Ref, lambda46_30$t_16_1: Ref ::
            { neverTriggered8(lambda46_30$t_16), neverTriggered8(lambda46_30$t_16_1) }
            (((lambda46_30$t_16 != lambda46_30$t_16_1 && ((issubtype((typeof(lambda46_30$t_16): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_16) && code_1 != null))) && ((issubtype((typeof(lambda46_30$t_16_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_16_1) && code_1 != null))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_16 != lambda46_30$t_16_1
          );
        
        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not be preserved. There might be insufficient permission to access lambda46_30$t.Ticket_discount_code (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2498]"}
            (forall lambda46_30$t_16: Ref ::
            { Heap[lambda46_30$t_16, Ticket_discount_code] } { QPMask[lambda46_30$t_16, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_16) }
            (issubtype((typeof(lambda46_30$t_16): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_16) && code_1 != null) ==> Mask[lambda46_30$t_16, Ticket_discount_code] >= FullPerm
          );
        
        // -- assumptions for inverse of receiver lambda46_30$t
          assume (forall lambda46_30$t_16: Ref ::
            { Heap[lambda46_30$t_16, Ticket_discount_code] } { QPMask[lambda46_30$t_16, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_16) }
            ((issubtype((typeof(lambda46_30$t_16): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_16) && code_1 != null)) && NoPerm < FullPerm ==> qpRange8(lambda46_30$t_16) && invRecv8(lambda46_30$t_16) == lambda46_30$t_16
          );
          assume (forall o_4: Ref ::
            { invRecv8(o_4) }
            ((issubtype((typeof(invRecv8(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv8(o_4)) && code_1 != null)) && (NoPerm < FullPerm && qpRange8(o_4)) ==> invRecv8(o_4) == o_4
          );
        
        // -- assume permission updates for field Ticket_discount_code
          assume (forall o_4: Ref ::
            { QPMask[o_4, Ticket_discount_code] }
            (((issubtype((typeof(invRecv8(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv8(o_4)) && code_1 != null)) && (NoPerm < FullPerm && qpRange8(o_4)) ==> invRecv8(o_4) == o_4 && QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code] - FullPerm) && (!(((issubtype((typeof(invRecv8(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv8(o_4)) && code_1 != null)) && (NoPerm < FullPerm && qpRange8(o_4))) ==> QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code])
          );
        
        // -- assume permission updates for independent locations
          assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
            { QPMask[o_4, f_6] }
            f_6 != Ticket_discount_code ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
          );
        Mask := QPMask;
        if (*) {
          if ((issubtype((typeof(lambda46_30$t_17): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_17) && code_1 != null)) {
            assert {:msg "  Loop invariant true && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && (lambda46_30$t in _checkDefined(res, 7562610).list_acc) ==> acc(Ticket_state(lambda46_30$t), write)) && ((forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> acc(lambda46_30$t.Ticket_discount_code, write)) && (forall lambda46_30$t: Ref :: { (lambda46_30$t in _checkDefined(res, 7562610).list_acc) } issubtype(typeof(lambda46_30$t), Ticket()) && ((lambda46_30$t in _checkDefined(res, 7562610).list_acc) && code_1 != null) ==> issubtype(typeof(lambda46_30$t.Ticket_discount_code), str())))) might not be preserved. Assertion issubtype(typeof(lambda46_30$t.Ticket_discount_code), str()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2499]"}
              (issubtype((typeof(Heap[lambda46_30$t_17, Ticket_discount_code]): PyTypeDomainType), str): bool);
          }
          assume false;
        }
        assume (forall lambda46_30$t_18_1: Ref ::
          { Seq#ContainsTrigger(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_18_1) } { Seq#Contains(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_18_1) }
          (issubtype((typeof(lambda46_30$t_18_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_18_1) && code_1 != null) ==> (issubtype((typeof(Heap[lambda46_30$t_18_1, Ticket_discount_code]): PyTypeDomainType), str): bool)
        );
        if (iter_err == null) {
          assert {:msg "  Loop invariant (iter_err == null ==> int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610))) > 0) && [acc(MustTerminate(_cthread_160), write), true] might not be preserved. Assertion int___sub__(list___len__(_checkDefined(seats, 495873779059)), list___len__(_checkDefined(res, 7562610))) > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@717.15--717.197) [2500]"}
            int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610))) > 0;
        }
        if (_loop_check_before) {
          assert {:msg "  Loop invariant [true, _loop_check_before ==> _loop_termination_flag || (!(iter_err == null) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))))] might not be preserved. Assertion _loop_termination_flag || (!(iter_err == null) || perm(MustTerminate(_cthread_160)) == none && ((forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false))))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@718.15--718.380) [2501]"}
            _loop_termination_flag || (!(iter_err == null) || (Mask[null, MustTerminate(_cthread_160)] == NoPerm && ((forall _r_2_8: Ref ::
            { Mask[null, MustInvokeBounded(_r_2_8)] }
            HasDirectPerm(Mask, null, MustInvokeBounded(_r_2_8)) ==> false
          ) && ((forall _r_2_9: Ref ::
            { Mask[null, MustInvokeUnbounded(_r_2_9)] }
            HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_2_9)) ==> false
          ) && ((forall _r_2_10: Ref ::
            { Mask[_r_2_10, MustReleaseBounded] }
            HasDirectPerm(Mask, _r_2_10, MustReleaseBounded) ==> false
          ) && (forall _r_2_11: Ref ::
            { Mask[_r_2_11, MustReleaseUnbounded] }
            HasDirectPerm(Mask, _r_2_11, MustReleaseUnbounded) ==> false
          ))))));
        }
        if (!_loop_check_before) {
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not be preserved. Assertion (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2502]"}
            (forall _r_2_12: Ref ::
            { Mask[null, MustInvokeBounded(_r_2_12)] }
            HasDirectPerm(Mask, null, MustInvokeBounded(_r_2_12)) ==> false
          );
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not be preserved. Assertion (forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2503]"}
            (forall _r_2_13: Ref ::
            { Mask[null, MustInvokeUnbounded(_r_2_13)] }
            HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_2_13)) ==> false
          );
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not be preserved. Assertion (forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2504]"}
            (forall _r_2_14: Ref ::
            { Mask[_r_2_14, MustReleaseBounded] }
            HasDirectPerm(Mask, _r_2_14, MustReleaseBounded) ==> false
          );
          assert {:msg "  Loop invariant [true, !_loop_check_before ==> (forperm _r_2: Ref [MustInvokeBounded(_r_2)] :: false) && ((forperm _r_2: Ref [MustInvokeUnbounded(_r_2)] :: false) && ((forperm _r_2: Ref [_r_2.MustReleaseBounded] :: false) && (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false)))] might not be preserved. Assertion (forperm _r_2: Ref [_r_2.MustReleaseUnbounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@719.15--719.283) [2505]"}
            (forall _r_2_15: Ref ::
            { Mask[_r_2_15, MustReleaseUnbounded] }
            HasDirectPerm(Mask, _r_2_15, MustReleaseUnbounded) ==> false
          );
        }
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Terminate execution
        assume false;
      }
    
    // -- Inhale loop invariant after loop, and assume guard
      assume !(iter_err == null);
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      assume (forall _r_1_7: Ref ::
        { Mask[_r_1_7, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_1_7, MustReleaseBounded) ==> Level(Heap, _r_1_7) <= _residue_161
      );
      assume state(Heap, Mask);
      assume (forall _r_1_8: Ref ::
        { Mask[_r_1_8, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_1_8, MustReleaseUnbounded) ==> Level(Heap, _r_1_8) <= _residue_161
      );
      assume _residue_160 <= _residue_161;
      perm := 1 / 20;
      assert {:msg "  While statement might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@695.15--695.45) [2506]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> iterable != null;
      Mask[iterable, list_acc] := Mask[iterable, list_acc] + perm;
      assume state(Heap, Mask);
      perm := 1 / 20;
      assert {:msg "  While statement might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@696.15--696.41) [2507]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> iter != null;
      Mask[iter, list_acc] := Mask[iter, list_acc] + perm;
      assume state(Heap, Mask);
      assume Seq#Equal(Heap[iter, list_acc], Heap[iterable, list_acc]);
      assume Seq#Equal(seqtmp, Heap[iterable, list_acc]);
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __iter_index] := Mask[iter, __iter_index] + perm;
      assume state(Heap, Mask);
      perm := FullPerm;
      assume iter != null;
      Mask[iter, __previous] := Mask[iter, __previous] + perm;
      assume state(Heap, Mask);
      if (iter_err == null) {
        assume Heap[iter, __iter_index] - 1 == Seq#Length(Heap[iter, __previous]);
      }
      if (iter_err != null) {
        assume Heap[iter, __iter_index] == Seq#Length(Heap[iter, __previous]);
      }
      if (iter_err == null) {
        assume Seq#Length(Heap[iter, list_acc]) > 0;
      }
      assume Heap[iter, __iter_index] >= 0;
      assume Heap[iter, __iter_index] <= Seq#Length(Heap[iter, list_acc]);
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume Heap[iter, __iter_index] > 0;
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume loop_target == Seq#Index(Heap[iter, list_acc], Heap[iter, __iter_index] - 1);
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume Seq#Contains(Heap[iter, list_acc], loop_target);
      }
      if (iter_err == null) {
        assume Seq#Equal(Heap[iter, __previous], Seq#Take(Heap[iter, list_acc], Heap[iter, __iter_index] - 1));
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume (issubtype((typeof(loop_target): PyTypeDomainType), (tuple(Seq#Append(Seq#Singleton(vint), Seq#Singleton(vint))): PyTypeDomainType)): bool);
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume state(Heap, Mask);
        assume row_0 == tuple___getitem__(Heap, loop_target, 0);
        assume state(Heap, Mask);
        assume _isDefined(Heap, 207760093042);
      }
      if (Seq#Length(Heap[iter, list_acc]) > 0) {
        assume state(Heap, Mask);
        assume seat_0 == tuple___getitem__(Heap, loop_target, 1);
        assume state(Heap, Mask);
        assume _isDefined(Heap, 53186532566387);
      }
      if (iter_err != null) {
        assume Seq#Equal(Heap[iter, __previous], Heap[iter, list_acc]);
      }
      if (Seq#Length(Heap[iter, list_acc]) == 0) {
        assume iter_err != null;
      }
      assume state(Heap, Mask);
      perm := FullPerm;
      assume _checkDefined(Heap, res, 7562610) != null;
      Mask[_checkDefined(Heap, res, 7562610), list_acc] := Mask[_checkDefined(Heap, res, 7562610), list_acc] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      assume int___eq__(Heap, __prim__int___box__(Heap, list___len__(Heap, _checkDefined(Heap, res, 7562610))), __prim__int___box__(Heap, PSeq___len__(Heap, PSeq___create__(Heap, Heap[iter, __previous], vint))));
      assume state(Heap, Mask);
      havoc QPMask;
      
      // -- check if receiver acc(Ticket_state(lambda46_30$t), write) is injective
        assert {:msg "  While statement might fail. Quantified resource Ticket_state(lambda46_30$t) might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2508]"}
          (forall lambda46_30$t_19: Ref, lambda46_30$t_19_1: Ref ::
          { neverTriggered9(lambda46_30$t_19), neverTriggered9(lambda46_30$t_19_1) }
          (((lambda46_30$t_19 != lambda46_30$t_19_1 && ((issubtype((typeof(lambda46_30$t_19): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_19))) && ((issubtype((typeof(lambda46_30$t_19_1): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_19_1))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_19 != lambda46_30$t_19_1
        );
      
      // -- Define Inverse Function
        assume (forall lambda46_30$t_19: Ref ::
          { Heap[null, Ticket_state(lambda46_30$t_19)] } { Mask[null, Ticket_state(lambda46_30$t_19)] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_19) }
          ((issubtype((typeof(lambda46_30$t_19): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_19)) && NoPerm < FullPerm ==> invRecv9(lambda46_30$t_19) == lambda46_30$t_19 && qpRange9(lambda46_30$t_19)
        );
        assume (forall self_1_4: Ref ::
          { invRecv9(self_1_4) }
          (((issubtype((typeof(invRecv9(self_1_4)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv9(self_1_4))) && NoPerm < FullPerm) && qpRange9(self_1_4) ==> invRecv9(self_1_4) == self_1_4
        );
      
      // -- Define updated permissions
        assume (forall self_1_4: Ref ::
          { QPMask[null, Ticket_state(self_1_4)] }
          (((issubtype((typeof(invRecv9(self_1_4)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv9(self_1_4))) && NoPerm < FullPerm) && qpRange9(self_1_4) ==> (NoPerm < FullPerm ==> invRecv9(self_1_4) == self_1_4) && QPMask[null, Ticket_state(self_1_4)] == Mask[null, Ticket_state(self_1_4)] + FullPerm
        );
      
      // -- Define independent locations
        assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
          { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
          (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 4 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
        );
        assume (forall self_1_4: Ref ::
          { QPMask[null, Ticket_state(self_1_4)] }
          !((((issubtype((typeof(invRecv9(self_1_4)): PyTypeDomainType), Ticket): bool) && Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv9(self_1_4))) && NoPerm < FullPerm) && qpRange9(self_1_4)) ==> QPMask[null, Ticket_state(self_1_4)] == Mask[null, Ticket_state(self_1_4)]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      havoc QPMask;
      assert {:msg "  While statement might fail. Quantified resource lambda46_30$t.Ticket_discount_code might not be injective. (testsfunctionalverificationexamplescav_example.py.vpr@716.15--716.803) [2509]"}
        (forall lambda46_30$t_21: Ref, lambda46_30$t_21_1: Ref ::
        
        (((lambda46_30$t_21 != lambda46_30$t_21_1 && ((issubtype((typeof(lambda46_30$t_21): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_21) && code_1 != null))) && ((issubtype((typeof(lambda46_30$t_21_1): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_21_1) && code_1 != null))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> lambda46_30$t_21 != lambda46_30$t_21_1
      );
      
      // -- Define Inverse Function
        assume (forall lambda46_30$t_21: Ref ::
          { Heap[lambda46_30$t_21, Ticket_discount_code] } { QPMask[lambda46_30$t_21, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_21) }
          ((issubtype((typeof(lambda46_30$t_21): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_21) && code_1 != null)) && NoPerm < FullPerm ==> qpRange10(lambda46_30$t_21) && invRecv10(lambda46_30$t_21) == lambda46_30$t_21
        );
        assume (forall o_4: Ref ::
          { invRecv10(o_4) }
          (((issubtype((typeof(invRecv10(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv10(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange10(o_4) ==> invRecv10(o_4) == o_4
        );
      
      // -- Assume set of fields is nonNull
        assume (forall lambda46_30$t_21: Ref ::
          { Heap[lambda46_30$t_21, Ticket_discount_code] } { QPMask[lambda46_30$t_21, Ticket_discount_code] } { Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_21) }
          (issubtype((typeof(lambda46_30$t_21): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_21) && code_1 != null) ==> lambda46_30$t_21 != null
        );
      
      // -- Define permissions
        assume (forall o_4: Ref ::
          { QPMask[o_4, Ticket_discount_code] }
          ((((issubtype((typeof(invRecv10(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv10(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange10(o_4) ==> (NoPerm < FullPerm ==> invRecv10(o_4) == o_4) && QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code] + FullPerm) && (!((((issubtype((typeof(invRecv10(o_4)): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], invRecv10(o_4)) && code_1 != null)) && NoPerm < FullPerm) && qpRange10(o_4)) ==> QPMask[o_4, Ticket_discount_code] == Mask[o_4, Ticket_discount_code])
        );
        assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
          { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
          f_6 != Ticket_discount_code ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      assume (forall lambda46_30$t_22: Ref ::
        { Seq#ContainsTrigger(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_22) } { Seq#Contains(Heap[_checkDefined#frame(EmptyFrame, res, 7562610), list_acc], lambda46_30$t_22) }
        (issubtype((typeof(lambda46_30$t_22): PyTypeDomainType), Ticket): bool) && (Seq#Contains(Heap[_checkDefined(Heap, res, 7562610), list_acc], lambda46_30$t_22) && code_1 != null) ==> (issubtype((typeof(Heap[lambda46_30$t_22, Ticket_discount_code]): PyTypeDomainType), str): bool)
      );
      if (iter_err == null) {
        assume state(Heap, Mask);
        assume int___sub__(Heap, list___len__(Heap, _checkDefined(Heap, seats, 495873779059)), list___len__(Heap, _checkDefined(Heap, res, 7562610))) > 0;
      }
      perm := FullPerm;
      Mask[null, MustTerminate(_cthread_160)] := Mask[null, MustTerminate(_cthread_160)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 101
  // // LoopInfo(None,Set())
  // exhale perm(MustTerminate(_cthread_160)) > none ==>
  //   acc(MustTerminate(_cthread_160), perm(MustTerminate(_cthread_160)) -
  //   _loop_original_must_terminate) -- testsfunctionalverificationexamplescav_example.py.vpr@753.3--753.154
    if (NoPerm < Mask[null, MustTerminate(_cthread_160)]) {
      assert {:msg "  Exhale might fail. Fraction perm(MustTerminate(_cthread_160)) - _loop_original_must_terminate might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@753.10--753.154) [2510]"}
        Mask[null, MustTerminate(_cthread_160)] - _loop_original_must_terminate >= NoPerm;
      perm := Mask[null, MustTerminate(_cthread_160)] - _loop_original_must_terminate;
      if (perm != NoPerm) {
        assert {:msg "  Exhale might fail. There might be insufficient permission to access MustTerminate(_cthread_160) (testsfunctionalverificationexamplescav_example.py.vpr@753.10--753.154) [2511]"}
          perm <= Mask[null, MustTerminate(_cthread_160)];
      }
      Mask[null, MustTerminate(_cthread_160)] := Mask[null, MustTerminate(_cthread_160)] - perm;
    }
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 102
  // _cwl_160 := Iterator___del__(_cthread_160, _method_measures_160, _residue_161,
  //   iter) -- testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87
    PreCallHeap := Heap;
    PreCallMask := Mask;
    havoc _cwl_160;
    
    // -- Exhaling precondition
      assert {:msg "  The precondition of method Iterator___del__ might not hold. Assertion _cthread_160 != null might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2512]"}
        _cthread_160 != null;
      assert {:msg "  The precondition of method Iterator___del__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2513]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      assert {:msg "  The precondition of method Iterator___del__ might not hold. Assertion issubtype(typeof(_cthread_160), Thread_0()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2514]"}
        (issubtype((typeof(_cthread_160): PyTypeDomainType), Thread_0): bool);
      assert {:msg "  The precondition of method Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2515]"}
        1 / 20 >= NoPerm;
      perm := 1 / 20;
      if (perm != NoPerm) {
        assert {:msg "  The precondition of method Iterator___del__ might not hold. There might be insufficient permission to access iter.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2516]"}
          perm <= Mask[iter, list_acc];
      }
      Mask[iter, list_acc] := Mask[iter, list_acc] - perm;
      assert {:msg "  The precondition of method Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2517]"}
        1 / 20 >= NoPerm;
      perm := 1 / 20;
      if (perm != NoPerm) {
        assert {:msg "  The precondition of method Iterator___del__ might not hold. There might be insufficient permission to access iter.__container (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2518]"}
          perm <= Mask[iter, __container];
      }
      Mask[iter, __container] := Mask[iter, __container] - perm;
      assert {:msg "  The precondition of method Iterator___del__ might not hold. Assertion Measure$check(_method_measures_160, _cthread_160, 1) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2519]"}
        Measure$check(Heap, _method_measures_160, _cthread_160, 1);
      // Finish exhale
      havoc ExhaleHeap;
      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
      Heap := ExhaleHeap;
    
    // -- Inhaling postcondition
      assume state(Heap, Mask);
      assume (forall _r_17: Ref ::
        { Mask[_r_17, MustReleaseBounded] }
        HasDirectPerm(Mask, _r_17, MustReleaseBounded) ==> Level(Heap, _r_17) <= _cwl_160
      );
      assume state(Heap, Mask);
      assume (forall _r_17_1: Ref ::
        { Mask[_r_17_1, MustReleaseUnbounded] }
        HasDirectPerm(Mask, _r_17_1, MustReleaseUnbounded) ==> Level(Heap, _r_17_1) <= _cwl_160
      );
      assume _residue_161 <= _cwl_160;
      perm := 1 / 20;
      assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2520]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> iter != null;
      Mask[iter, __container] := Mask[iter, __container] + perm;
      assume state(Heap, Mask);
      if ((issubtype((typeof(Heap[iter, __container]): PyTypeDomainType), (list((list_arg((typeof(Heap[iter, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
        perm := 1 / 20;
        assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2521]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> Heap[iter, __container] != null;
        Mask[Heap[iter, __container], list_acc] := Mask[Heap[iter, __container], list_acc] + perm;
        assume state(Heap, Mask);
      }
      if ((issubtype((typeof(Heap[iter, __container]): PyTypeDomainType), (dict((dict_arg((typeof(Heap[iter, __container]): PyTypeDomainType), 0): PyTypeDomainType), (dict_arg((typeof(Heap[iter, __container]): PyTypeDomainType), 1): PyTypeDomainType)): PyTypeDomainType)): bool)) {
        perm := 1 / 20;
        assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2522]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> Heap[iter, __container] != null;
        Mask[Heap[iter, __container], dict_acc] := Mask[Heap[iter, __container], dict_acc] + perm;
        assume state(Heap, Mask);
        perm := 1 / 20;
        assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2523]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> Heap[iter, __container] != null;
        Mask[Heap[iter, __container], dict_acc2] := Mask[Heap[iter, __container], dict_acc2] + perm;
        assume state(Heap, Mask);
      }
      if ((issubtype((typeof(Heap[iter, __container]): PyTypeDomainType), (set((set_arg((typeof(Heap[iter, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
        perm := 1 / 20;
        assert {:msg "  Method call might fail. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@754.3--754.87) [2524]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> Heap[iter, __container] != null;
        Mask[Heap[iter, __container], set_acc] := Mask[Heap[iter, __container], set_acc] + perm;
        assume state(Heap, Mask);
      }
      assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 103
  // _res := null -- testsfunctionalverificationexamplescav_example.py.vpr@755.3--755.15
    _res := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 104
  // _err := null -- testsfunctionalverificationexamplescav_example.py.vpr@756.3--756.15
    _err := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 105
  // label post_loop -- testsfunctionalverificationexamplescav_example.py.vpr@757.3--757.18
    post_loop:
    Labelpost_loopMask := Mask;
    Labelpost_loopHeap := Heap;
    post_loop_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 106
  // _res := null -- testsfunctionalverificationexamplescav_example.py.vpr@758.3--758.15
    _res := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 107
  // _err := null -- testsfunctionalverificationexamplescav_example.py.vpr@759.3--759.15
    _err := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 108
  // _res := _checkDefined(res, 7562610) -- testsfunctionalverificationexamplescav_example.py.vpr@760.3--760.38
    
    // -- Check definedness of _checkDefined(res, 7562610)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function _checkDefined might not hold. Assertion _isDefined(7562610) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@760.11--760.38) [2525]"}
          _isDefined(Heap, 7562610);
        // Stop execution
        assume false;
      }
    _res := _checkDefined(Heap, res, 7562610);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 109
  // goto __end -- testsfunctionalverificationexamplescav_example.py.vpr@761.3--761.13
    goto __end;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 110
  // goto __end -- testsfunctionalverificationexamplescav_example.py.vpr@762.3--762.13
    goto __end;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 111
  // label __end -- testsfunctionalverificationexamplescav_example.py.vpr@763.3--763.14
    __end:
    Label__endMask := Mask;
    Label__endHeap := Heap;
    __end_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    if (_err == null) {
      assert {:msg "  Postcondition of order_tickets might not hold. Assertion issubtype(typeof(_res), list(Ticket())) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@632.11--632.67) [2526]"}
        (issubtype((typeof(_res): PyTypeDomainType), (list(Ticket): PyTypeDomainType)): bool);
    }
    if (_err != null) {
      assert {:msg "  Postcondition of order_tickets might not hold. Assertion issubtype(typeof(_err), SoldoutException()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@634.11--634.71) [2527]"}
        (issubtype((typeof(_err): PyTypeDomainType), SoldoutException): bool);
    }
    assert {:msg "  Postcondition of order_tickets might not hold. Assertion (forperm _r_4: Ref [MustInvokeBounded(_r_4)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2528]"}
      (forall _r_4_8: Ref ::
      { Mask[null, MustInvokeBounded(_r_4_8)] }
      HasDirectPerm(Mask, null, MustInvokeBounded(_r_4_8)) ==> false
    );
    assert {:msg "  Postcondition of order_tickets might not hold. Assertion (forperm _r_4: Ref [MustInvokeUnbounded(_r_4)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2529]"}
      (forall _r_4_9: Ref ::
      { Mask[null, MustInvokeUnbounded(_r_4_9)] }
      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_4_9)) ==> false
    );
    assert {:msg "  Postcondition of order_tickets might not hold. Assertion (forperm _r_4: Ref [_r_4.MustReleaseBounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2530]"}
      (forall _r_4_10: Ref ::
      { Mask[_r_4_10, MustReleaseBounded] }
      HasDirectPerm(Mask, _r_4_10, MustReleaseBounded) ==> false
    );
    assert {:msg "  Postcondition of order_tickets might not hold. Assertion (forperm _r_4: Ref [_r_4.MustReleaseUnbounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@635.11--635.255) [2531]"}
      (forall _r_4_11: Ref ::
      { Mask[_r_4_11, MustReleaseUnbounded] }
      HasDirectPerm(Mask, _r_4_11, MustReleaseUnbounded) ==> false
    );
}

// ==================================================
// Translation of method Ticket___init__
// ==================================================

procedure Ticket___init__(_cthread_156: Ref, _caller_measures_156: (Seq Measure$DomainType), _residue_156: Perm, self: Ref, show: Ref, row: Ref, seat: Ref) returns (_current_wait_level_156: Perm)
  modifies Heap, Mask;
{
  var __end_lblGuard: bool;
  var perm: Perm;
  var _r_8_4: Ref;
  var _r_8_5: Ref;
  var _r_8_6: Ref;
  var _r_8_7: Ref;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_6_2: Ref;
  var _r_6_3: Ref;
  var _r_7: Ref;
  var _r_7_2: Ref;
  var _r_7_4: Ref;
  var _r_7_6: Ref;
  var _err: Ref;
  var self_2: Ref;
  var show_0: Ref;
  var row_1: Ref;
  var seat_1: Ref;
  var _method_measures_156: (Seq Measure$DomainType);
  var ExhaleHeap: HeapType;
  var ln_1: int;
  var ln_3: int;
  var freshVersion: FrameType;
  var Label__endMask: MaskType;
  var Label__endHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    __end_lblGuard := false;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_156, $allocated];
    assume Heap[self, $allocated];
    assume Heap[show, $allocated];
    assume Heap[row, $allocated];
    assume Heap[seat, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_156 != null;
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_156): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume self != null;
        assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, _MaySet(self, 2036589462893379814238060391131476)] := Mask[null, _MaySet(self, 2036589462893379814238060391131476)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, _MaySet(self, 564017441487491594152276)] := Mask[null, _MaySet(self, 564017441487491594152276)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, _MaySet(self, 140695336058778200607779156)] := Mask[null, _MaySet(self, 140695336058778200607779156)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume (issubtype((typeof(self): PyTypeDomainType), Ticket): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(show): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(row): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(seat): PyTypeDomainType), vint): bool);
        assume state(Heap, Mask);
        assume self != null;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_156, _cthread_156, 1) || perm(MustTerminate(_cthread_156)) == none && ((forperm _r_8: Ref [MustInvokeBounded(_r_8)] :: false) && ((forperm _r_8: Ref [MustInvokeUnbounded(_r_8)] :: false) && ((forperm _r_8: Ref [_r_8.MustReleaseBounded] :: false) && (forperm _r_8: Ref [_r_8.MustReleaseUnbounded] :: false))))
          if (*) {
            // Stop execution
            assume false;
          }
          if (!Measure$check(Heap, _caller_measures_156, _cthread_156, 1)) {
            if (Mask[null, MustTerminate(_cthread_156)] == NoPerm) {
              if (*) {
                if (HasDirectPerm(Mask, null, MustInvokeBounded(_r_8_4))) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_8) (testsfunctionalverificationexamplescav_example.py.vpr@780.12--780.359) [2532]"}
                    HasDirectPerm(Mask, null, MustInvokeBounded(_r_8_4));
                }
                assume false;
              }
              if ((forall _r_8_1: Ref ::
                { Mask[null, MustInvokeBounded(_r_8_1)] }
                HasDirectPerm(Mask, null, MustInvokeBounded(_r_8_1)) ==> false
              )) {
                if (*) {
                  if (HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_8_5))) {
                    assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_8) (testsfunctionalverificationexamplescav_example.py.vpr@780.12--780.359) [2533]"}
                      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_8_5));
                  }
                  assume false;
                }
                if ((forall _r_8_3: Ref ::
                  { Mask[null, MustInvokeUnbounded(_r_8_3)] }
                  HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_8_3)) ==> false
                )) {
                  if (*) {
                    if (HasDirectPerm(Mask, _r_8_6, MustReleaseBounded)) {
                      assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_8.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@780.12--780.359) [2534]"}
                        HasDirectPerm(Mask, _r_8_6, MustReleaseBounded);
                    }
                    assume false;
                  }
                  if ((forall _r_8_5_1: Ref ::
                    { Mask[_r_8_5_1, MustReleaseBounded] }
                    HasDirectPerm(Mask, _r_8_5_1, MustReleaseBounded) ==> false
                  )) {
                    if (*) {
                      if (HasDirectPerm(Mask, _r_8_7, MustReleaseUnbounded)) {
                        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_8.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@780.12--780.359) [2535]"}
                          HasDirectPerm(Mask, _r_8_7, MustReleaseUnbounded);
                      }
                      assume false;
                    }
                  }
                }
              }
            }
          }
        assume Measure$check(Heap, _caller_measures_156, _cthread_156, 1) || (Mask[null, MustTerminate(_cthread_156)] == NoPerm && ((forall _r_8_7_1: Ref ::
          { Mask[null, MustInvokeBounded(_r_8_7_1)] }
          HasDirectPerm(Mask, null, MustInvokeBounded(_r_8_7_1)) ==> false
        ) && ((forall _r_8_8: Ref ::
          { Mask[null, MustInvokeUnbounded(_r_8_8)] }
          HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_8_8)) ==> false
        ) && ((forall _r_8_9: Ref ::
          { Mask[_r_8_9, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_8_9, MustReleaseBounded) ==> false
        ) && (forall _r_8_10: Ref ::
          { Mask[_r_8_10, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_8_10, MustReleaseUnbounded) ==> false
        )))));
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_156 != null;
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_156): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      assume self != null;
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, _MaySet(self, 2036589462893379814238060391131476)] := Mask[null, _MaySet(self, 2036589462893379814238060391131476)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, _MaySet(self, 564017441487491594152276)] := Mask[null, _MaySet(self, 564017441487491594152276)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, _MaySet(self, 140695336058778200607779156)] := Mask[null, _MaySet(self, 140695336058778200607779156)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      assume (issubtype((typeof(self): PyTypeDomainType), Ticket): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(show): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(row): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(seat): PyTypeDomainType), vint): bool);
      assume state(Heap, Mask);
      assume self != null;
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, MustTerminate(_cthread_156)] := Mask[null, MustTerminate(_cthread_156)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_6: Ref [_r_6.MustReleaseBounded] :: Level(_r_6) <= _current_wait_level_156)
          if (*) {
            if (HasDirectPerm(PostMask, _r_6_2, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_6.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@781.11--781.244) [2536]"}
                HasDirectPerm(PostMask, _r_6_2, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_6_1_1: Ref ::
          { PostMask[_r_6_1_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_6_1_1, MustReleaseBounded) ==> Level(PostHeap, _r_6_1_1) <= _current_wait_level_156
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_6: Ref [_r_6.MustReleaseUnbounded] :: Level(_r_6) <= _current_wait_level_156)
          if (*) {
            if (HasDirectPerm(PostMask, _r_6_3, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_6.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@781.11--781.244) [2537]"}
                HasDirectPerm(PostMask, _r_6_3, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_6_3_1: Ref ::
          { PostMask[_r_6_3_1, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_6_3_1, MustReleaseUnbounded) ==> Level(PostHeap, _r_6_3_1) <= _current_wait_level_156
        );
        assume _residue_156 <= _current_wait_level_156;
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        PostMask[null, Ticket_state(self)] := PostMask[null, Ticket_state(self)] + perm;
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        PostMask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] := PostMask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      PostMask[null, Ticket_state(self)] := PostMask[null, Ticket_state(self)] + perm;
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      PostMask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] := PostMask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of (forperm _r_7: Ref [MustInvokeBounded(_r_7)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeBounded(_r_7))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_7) (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2538]"}
              HasDirectPerm(PostMask, null, MustInvokeBounded(_r_7));
          }
          assume false;
        }
      assume (forall _r_7_1: Ref ::
        { PostMask[null, MustInvokeBounded(_r_7_1)] }
        HasDirectPerm(PostMask, null, MustInvokeBounded(_r_7_1)) ==> false
      );
      
      // -- Check definedness of (forperm _r_7: Ref [MustInvokeUnbounded(_r_7)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_7_2))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_7) (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2539]"}
              HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_7_2));
          }
          assume false;
        }
      assume (forall _r_7_3: Ref ::
        { PostMask[null, MustInvokeUnbounded(_r_7_3)] }
        HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_7_3)) ==> false
      );
      
      // -- Check definedness of (forperm _r_7: Ref [_r_7.MustReleaseBounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_7_4, MustReleaseBounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_7.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2540]"}
              HasDirectPerm(PostMask, _r_7_4, MustReleaseBounded);
          }
          assume false;
        }
      assume (forall _r_7_5: Ref ::
        { PostMask[_r_7_5, MustReleaseBounded] }
        HasDirectPerm(PostMask, _r_7_5, MustReleaseBounded) ==> false
      );
      
      // -- Check definedness of (forperm _r_7: Ref [_r_7.MustReleaseUnbounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_7_6, MustReleaseUnbounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_7.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2541]"}
              HasDirectPerm(PostMask, _r_7_6, MustReleaseUnbounded);
          }
          assume false;
        }
      assume (forall _r_7_7: Ref ::
        { PostMask[_r_7_7, MustReleaseUnbounded] }
        HasDirectPerm(PostMask, _r_7_7, MustReleaseUnbounded) ==> false
      );
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Assumptions about local variables
    assume Heap[_err, $allocated];
    assume Heap[self_2, $allocated];
    assume Heap[show_0, $allocated];
    assume Heap[row_1, $allocated];
    assume Heap[seat_1, $allocated];
  
  // -- Translating statement: // id = 1
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 2
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 3
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 4
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 5
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 6
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 7
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 8
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 9
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 10
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 11
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 12
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 13
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 14
  // _method_measures_156 := Seq(Measure$create(true, _cthread_156, 1)) -- testsfunctionalverificationexamplescav_example.py.vpr@792.3--792.69
    _method_measures_156 := Seq#Singleton((Measure$create(true, _cthread_156, 1): Measure$DomainType));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 15
  // inhale typeof(self) == Ticket() -- testsfunctionalverificationexamplescav_example.py.vpr@793.3--793.34
    assume (typeof(self): PyTypeDomainType) == Ticket;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 16
  // _err := null -- testsfunctionalverificationexamplescav_example.py.vpr@794.3--794.15
    _err := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 17
  // self_2 := self -- testsfunctionalverificationexamplescav_example.py.vpr@795.3--795.17
    self_2 := self;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 18
  // show_0 := show -- testsfunctionalverificationexamplescav_example.py.vpr@796.3--796.17
    show_0 := show;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 19
  // row_1 := row -- testsfunctionalverificationexamplescav_example.py.vpr@797.3--797.15
    row_1 := row;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 20
  // seat_1 := seat -- testsfunctionalverificationexamplescav_example.py.vpr@798.3--798.17
    seat_1 := seat;
    assume state(Heap, Mask);
  
  // -- Translating statement: if (perm(_MaySet(self_2, 2036589462893379814238060391131476)) > none) -- testsfunctionalverificationexamplescav_example.py.vpr@799.3--802.4
    if (NoPerm < Mask[null, _MaySet(self_2, 2036589462893379814238060391131476)]) {
      
      // -- Translating statement: // id = 21
  // exhale acc(_MaySet(self_2, 2036589462893379814238060391131476), write) -- testsfunctionalverificationexamplescav_example.py.vpr@800.5--800.75
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Exhale might fail. There might be insufficient permission to access _MaySet(self_2, 2036589462893379814238060391131476) (testsfunctionalverificationexamplescav_example.py.vpr@800.12--800.75) [2543]"}
            perm <= Mask[null, _MaySet(self_2, 2036589462893379814238060391131476)];
        }
        Mask[null, _MaySet(self_2, 2036589462893379814238060391131476)] := Mask[null, _MaySet(self_2, 2036589462893379814238060391131476)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 22
  // inhale acc(self_2.Ticket_show_id, write) -- testsfunctionalverificationexamplescav_example.py.vpr@801.5--801.45
        perm := FullPerm;
        assume self_2 != null;
        Mask[self_2, Ticket_show_id] := Mask[self_2, Ticket_show_id] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: // id = 23
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 24
  // self_2.Ticket_show_id := show_0 -- testsfunctionalverificationexamplescav_example.py.vpr@803.3--803.34
    assert {:msg "  Assignment might fail. There might be insufficient permission to access self_2.Ticket_show_id (testsfunctionalverificationexamplescav_example.py.vpr@803.3--803.34) [2545]"}
      FullPerm == Mask[self_2, Ticket_show_id];
    Heap[self_2, Ticket_show_id] := show_0;
    assume state(Heap, Mask);
  
  // -- Translating statement: if (perm(_MaySet(self_2, 564017441487491594152276)) > none) -- testsfunctionalverificationexamplescav_example.py.vpr@804.3--807.4
    if (NoPerm < Mask[null, _MaySet(self_2, 564017441487491594152276)]) {
      
      // -- Translating statement: // id = 25
  // exhale acc(_MaySet(self_2, 564017441487491594152276), write) -- testsfunctionalverificationexamplescav_example.py.vpr@805.5--805.65
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Exhale might fail. There might be insufficient permission to access _MaySet(self_2, 564017441487491594152276) (testsfunctionalverificationexamplescav_example.py.vpr@805.12--805.65) [2547]"}
            perm <= Mask[null, _MaySet(self_2, 564017441487491594152276)];
        }
        Mask[null, _MaySet(self_2, 564017441487491594152276)] := Mask[null, _MaySet(self_2, 564017441487491594152276)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 26
  // inhale acc(self_2.Ticket_row, write) -- testsfunctionalverificationexamplescav_example.py.vpr@806.5--806.41
        perm := FullPerm;
        assume self_2 != null;
        Mask[self_2, Ticket_row] := Mask[self_2, Ticket_row] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: // id = 27
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 28
  // self_2.Ticket_row := tuple___getitem__(tuple___create2__(row_1, seat_1, int(),
  //   int(), 0), 0) -- testsfunctionalverificationexamplescav_example.py.vpr@808.3--808.95
    
    // -- Check definedness of tuple___getitem__(tuple___create2__(row_1, seat_1, int(), int(), 0), 0)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function tuple___create2__ might not hold. Assertion issubtype(typeof(row_1), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@808.42--808.91) [2549]"}
          (issubtype((typeof(row_1): PyTypeDomainType), vint): bool);
        assert {:msg "  Precondition of function tuple___create2__ might not hold. Assertion issubtype(typeof(seat_1), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@808.42--808.91) [2550]"}
          (issubtype((typeof(seat_1): PyTypeDomainType), vint): bool);
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(tuple___create2__(row_1, seat_1, int(), int(), 0))) in (0 >= 0 ==> 0 < ln) && (0 < 0 ==> 0 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@808.24--808.95) [2551]"}
          0 < tuple___len__(Heap, tuple___create2__(Heap, row_1, seat_1, vint, vint, 0));
        
        // -- Free assumptions (exhale module)
          ln_1 := tuple___len__(Heap, tuple___create2__(Heap, row_1, seat_1, vint, vint, 0));
        // Stop execution
        assume false;
      }
    assert {:msg "  Assignment might fail. There might be insufficient permission to access self_2.Ticket_row (testsfunctionalverificationexamplescav_example.py.vpr@808.3--808.95) [2552]"}
      FullPerm == Mask[self_2, Ticket_row];
    Heap[self_2, Ticket_row] := tuple___getitem__(Heap, tuple___create2__(Heap, row_1, seat_1, vint, vint, 0), 0);
    assume state(Heap, Mask);
  
  // -- Translating statement: if (perm(_MaySet(self_2, 140695336058778200607779156)) > none) -- testsfunctionalverificationexamplescav_example.py.vpr@809.3--812.4
    if (NoPerm < Mask[null, _MaySet(self_2, 140695336058778200607779156)]) {
      
      // -- Translating statement: // id = 29
  // exhale acc(_MaySet(self_2, 140695336058778200607779156), write) -- testsfunctionalverificationexamplescav_example.py.vpr@810.5--810.68
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Exhale might fail. There might be insufficient permission to access _MaySet(self_2, 140695336058778200607779156) (testsfunctionalverificationexamplescav_example.py.vpr@810.12--810.68) [2554]"}
            perm <= Mask[null, _MaySet(self_2, 140695336058778200607779156)];
        }
        Mask[null, _MaySet(self_2, 140695336058778200607779156)] := Mask[null, _MaySet(self_2, 140695336058778200607779156)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 30
  // inhale acc(self_2.Ticket_seat, write) -- testsfunctionalverificationexamplescav_example.py.vpr@811.5--811.42
        perm := FullPerm;
        assume self_2 != null;
        Mask[self_2, Ticket_seat] := Mask[self_2, Ticket_seat] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: // id = 31
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 32
  // self_2.Ticket_seat := tuple___getitem__(tuple___create2__(row_1, seat_1, int(),
  //   int(), 0), 1) -- testsfunctionalverificationexamplescav_example.py.vpr@813.3--813.96
    
    // -- Check definedness of tuple___getitem__(tuple___create2__(row_1, seat_1, int(), int(), 0), 1)
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function tuple___create2__ might not hold. Assertion issubtype(typeof(row_1), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@813.43--813.92) [2556]"}
          (issubtype((typeof(row_1): PyTypeDomainType), vint): bool);
        assert {:msg "  Precondition of function tuple___create2__ might not hold. Assertion issubtype(typeof(seat_1), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@813.43--813.92) [2557]"}
          (issubtype((typeof(seat_1): PyTypeDomainType), vint): bool);
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function tuple___getitem__ might not hold. Assertion (let ln == (tuple___len__(tuple___create2__(row_1, seat_1, int(), int(), 0))) in (1 >= 0 ==> 1 < ln) && (1 < 0 ==> 1 >= -ln)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@813.25--813.96) [2558]"}
          1 < tuple___len__(Heap, tuple___create2__(Heap, row_1, seat_1, vint, vint, 0));
        
        // -- Free assumptions (exhale module)
          ln_3 := tuple___len__(Heap, tuple___create2__(Heap, row_1, seat_1, vint, vint, 0));
        // Stop execution
        assume false;
      }
    assert {:msg "  Assignment might fail. There might be insufficient permission to access self_2.Ticket_seat (testsfunctionalverificationexamplescav_example.py.vpr@813.3--813.96) [2559]"}
      FullPerm == Mask[self_2, Ticket_seat];
    Heap[self_2, Ticket_seat] := tuple___getitem__(Heap, tuple___create2__(Heap, row_1, seat_1, vint, vint, 0), 1);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 33
  // fold acc(Ticket_state(self_2), write) -- testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40
    assert {:msg "  Folding Ticket_state(self_2) might fail. Assertion issubtype(typeof(self_2), Ticket()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2561]"}
      (issubtype((typeof(self_2): PyTypeDomainType), Ticket): bool);
    if ((issubtype((typeof(self_2): PyTypeDomainType), Ticket): bool)) {
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding Ticket_state(self_2) might fail. There might be insufficient permission to access self_2.Ticket_show_id (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2563]"}
          perm <= Mask[self_2, Ticket_show_id];
      }
      Mask[self_2, Ticket_show_id] := Mask[self_2, Ticket_show_id] - perm;
      assert {:msg "  Folding Ticket_state(self_2) might fail. Assertion issubtype(typeof(self_2.Ticket_show_id), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2564]"}
        (issubtype((typeof(Heap[self_2, Ticket_show_id]): PyTypeDomainType), vint): bool);
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding Ticket_state(self_2) might fail. There might be insufficient permission to access self_2.Ticket_row (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2566]"}
          perm <= Mask[self_2, Ticket_row];
      }
      Mask[self_2, Ticket_row] := Mask[self_2, Ticket_row] - perm;
      assert {:msg "  Folding Ticket_state(self_2) might fail. Assertion issubtype(typeof(self_2.Ticket_row), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2567]"}
        (issubtype((typeof(Heap[self_2, Ticket_row]): PyTypeDomainType), vint): bool);
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding Ticket_state(self_2) might fail. There might be insufficient permission to access self_2.Ticket_seat (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2569]"}
          perm <= Mask[self_2, Ticket_seat];
      }
      Mask[self_2, Ticket_seat] := Mask[self_2, Ticket_seat] - perm;
      assert {:msg "  Folding Ticket_state(self_2) might fail. Assertion issubtype(typeof(self_2.Ticket_seat), int()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@814.3--814.40) [2570]"}
        (issubtype((typeof(Heap[self_2, Ticket_seat]): PyTypeDomainType), vint): bool);
    }
    perm := FullPerm;
    Mask[null, Ticket_state(self_2)] := Mask[null, Ticket_state(self_2)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume Ticket_state#trigger(Heap, Ticket_state(self_2));
    assume Heap[null, Ticket_state(self_2)] == FrameFragment((if (issubtype((typeof(self_2): PyTypeDomainType), Ticket): bool) then CombineFrames(FrameFragment(Heap[self_2, Ticket_show_id]), CombineFrames(FrameFragment(Heap[self_2, Ticket_row]), FrameFragment(Heap[self_2, Ticket_seat]))) else EmptyFrame));
    if (!HasDirectPerm(Mask, null, Ticket_state(self_2))) {
      Heap[null, Ticket_state#sm(self_2)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, Ticket_state(self_2)] := freshVersion;
    }
    if ((issubtype((typeof(self_2): PyTypeDomainType), Ticket): bool)) {
      Heap[null, Ticket_state#sm(self_2)][self_2, Ticket_show_id] := true;
      Heap[null, Ticket_state#sm(self_2)][self_2, Ticket_row] := true;
      Heap[null, Ticket_state#sm(self_2)][self_2, Ticket_seat] := true;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 34
  // goto __end -- testsfunctionalverificationexamplescav_example.py.vpr@815.3--815.13
    goto __end;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 35
  // label __end -- testsfunctionalverificationexamplescav_example.py.vpr@816.3--816.14
    __end:
    Label__endMask := Mask;
    Label__endHeap := Heap;
    __end_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Ticket___init__ might not hold. There might be insufficient permission to access Ticket_state(self) (testsfunctionalverificationexamplescav_example.py.vpr@782.11--782.120) [2572]"}
        perm <= Mask[null, Ticket_state(self)];
    }
    Mask[null, Ticket_state(self)] := Mask[null, Ticket_state(self)] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Ticket___init__ might not hold. There might be insufficient permission to access _MaySet(self, 578847845651634811226368290157834565233854867796) (testsfunctionalverificationexamplescav_example.py.vpr@782.11--782.120) [2573]"}
        perm <= Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)];
    }
    Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(self, 578847845651634811226368290157834565233854867796)] - perm;
    assert {:msg "  Postcondition of Ticket___init__ might not hold. Assertion (forperm _r_7: Ref [MustInvokeBounded(_r_7)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2574]"}
      (forall _r_7_8: Ref ::
      { Mask[null, MustInvokeBounded(_r_7_8)] }
      HasDirectPerm(Mask, null, MustInvokeBounded(_r_7_8)) ==> false
    );
    assert {:msg "  Postcondition of Ticket___init__ might not hold. Assertion (forperm _r_7: Ref [MustInvokeUnbounded(_r_7)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2575]"}
      (forall _r_7_9: Ref ::
      { Mask[null, MustInvokeUnbounded(_r_7_9)] }
      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_7_9)) ==> false
    );
    assert {:msg "  Postcondition of Ticket___init__ might not hold. Assertion (forperm _r_7: Ref [_r_7.MustReleaseBounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2576]"}
      (forall _r_7_10: Ref ::
      { Mask[_r_7_10, MustReleaseBounded] }
      HasDirectPerm(Mask, _r_7_10, MustReleaseBounded) ==> false
    );
    assert {:msg "  Postcondition of Ticket___init__ might not hold. Assertion (forperm _r_7: Ref [_r_7.MustReleaseUnbounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@783.11--783.255) [2577]"}
      (forall _r_7_11: Ref ::
      { Mask[_r_7_11, MustReleaseUnbounded] }
      HasDirectPerm(Mask, _r_7_11, MustReleaseUnbounded) ==> false
    );
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method Ticket_set_discount
// ==================================================

procedure Ticket_set_discount(_cthread_157: Ref, _caller_measures_157: (Seq Measure$DomainType), _residue_157: Perm, self_0: Ref, code: Ref) returns (_current_wait_level_157: Perm)
  modifies Heap, Mask;
{
  var __end_lblGuard: bool;
  var perm: Perm;
  var _r_11: Ref;
  var _r_11_2: Ref;
  var _r_11_4: Ref;
  var _r_11_6: Ref;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_9: Ref;
  var _r_9_2: Ref;
  var _r_10: Ref;
  var _r_10_2: Ref;
  var _r_10_4: Ref;
  var _r_10_6: Ref;
  var _err: Ref;
  var self_3: Ref;
  var code_2: Ref;
  var _method_measures_157: (Seq Measure$DomainType);
  var ExhaleHeap: HeapType;
  var Label__endMask: MaskType;
  var Label__endHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    __end_lblGuard := false;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_157, $allocated];
    assume Heap[self_0, $allocated];
    assume Heap[code, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_157 != null;
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_157): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(self_0): PyTypeDomainType), Ticket): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(code): PyTypeDomainType), str): bool);
        assume state(Heap, Mask);
        assume self_0 != null;
        assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, _MaySet(self_0, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(self_0, 578847845651634811226368290157834565233854867796)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume Mask[null, MustTerminate(_cthread_157)] == NoPerm;
        
        // -- Check definedness of (forperm _r_11: Ref [MustInvokeBounded(_r_11)] :: false)
          if (*) {
            if (HasDirectPerm(Mask, null, MustInvokeBounded(_r_11))) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_11) (testsfunctionalverificationexamplescav_example.py.vpr@826.12--826.311) [2578]"}
                HasDirectPerm(Mask, null, MustInvokeBounded(_r_11));
            }
            assume false;
          }
        assume (forall _r_11_1: Ref ::
          { Mask[null, MustInvokeBounded(_r_11_1)] }
          HasDirectPerm(Mask, null, MustInvokeBounded(_r_11_1)) ==> false
        );
        
        // -- Check definedness of (forperm _r_11: Ref [MustInvokeUnbounded(_r_11)] :: false)
          if (*) {
            if (HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_11_2))) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_11) (testsfunctionalverificationexamplescav_example.py.vpr@826.12--826.311) [2579]"}
                HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_11_2));
            }
            assume false;
          }
        assume (forall _r_11_3: Ref ::
          { Mask[null, MustInvokeUnbounded(_r_11_3)] }
          HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_11_3)) ==> false
        );
        
        // -- Check definedness of (forperm _r_11: Ref [_r_11.MustReleaseBounded] :: false)
          if (*) {
            if (HasDirectPerm(Mask, _r_11_4, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_11.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@826.12--826.311) [2580]"}
                HasDirectPerm(Mask, _r_11_4, MustReleaseBounded);
            }
            assume false;
          }
        assume (forall _r_11_5: Ref ::
          { Mask[_r_11_5, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_11_5, MustReleaseBounded) ==> false
        );
        
        // -- Check definedness of (forperm _r_11: Ref [_r_11.MustReleaseUnbounded] :: false)
          if (*) {
            if (HasDirectPerm(Mask, _r_11_6, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_11.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@826.12--826.311) [2581]"}
                HasDirectPerm(Mask, _r_11_6, MustReleaseUnbounded);
            }
            assume false;
          }
        assume (forall _r_11_7: Ref ::
          { Mask[_r_11_7, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_11_7, MustReleaseUnbounded) ==> false
        );
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_157 != null;
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_157): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(self_0): PyTypeDomainType), Ticket): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(code): PyTypeDomainType), str): bool);
      assume state(Heap, Mask);
      assume self_0 != null;
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, _MaySet(self_0, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(self_0, 578847845651634811226368290157834565233854867796)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_9: Ref [_r_9.MustReleaseBounded] :: Level(_r_9) <= _current_wait_level_157)
          if (*) {
            if (HasDirectPerm(PostMask, _r_9, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_9.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@827.11--827.244) [2582]"}
                HasDirectPerm(PostMask, _r_9, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_9_1: Ref ::
          { PostMask[_r_9_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_9_1, MustReleaseBounded) ==> Level(PostHeap, _r_9_1) <= _current_wait_level_157
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_9: Ref [_r_9.MustReleaseUnbounded] :: Level(_r_9) <= _current_wait_level_157)
          if (*) {
            if (HasDirectPerm(PostMask, _r_9_2, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_9.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@827.11--827.244) [2583]"}
                HasDirectPerm(PostMask, _r_9_2, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_9_3: Ref ::
          { PostMask[_r_9_3, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_9_3, MustReleaseUnbounded) ==> Level(PostHeap, _r_9_3) <= _current_wait_level_157
        );
        assume _residue_157 <= _current_wait_level_157;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of (forperm _r_10: Ref [MustInvokeBounded(_r_10)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeBounded(_r_10))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_10) (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2584]"}
              HasDirectPerm(PostMask, null, MustInvokeBounded(_r_10));
          }
          assume false;
        }
      assume (forall _r_10_1: Ref ::
        { PostMask[null, MustInvokeBounded(_r_10_1)] }
        HasDirectPerm(PostMask, null, MustInvokeBounded(_r_10_1)) ==> false
      );
      
      // -- Check definedness of (forperm _r_10: Ref [MustInvokeUnbounded(_r_10)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_10_2))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_10) (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2585]"}
              HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_10_2));
          }
          assume false;
        }
      assume (forall _r_10_3: Ref ::
        { PostMask[null, MustInvokeUnbounded(_r_10_3)] }
        HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_10_3)) ==> false
      );
      
      // -- Check definedness of (forperm _r_10: Ref [_r_10.MustReleaseBounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_10_4, MustReleaseBounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_10.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2586]"}
              HasDirectPerm(PostMask, _r_10_4, MustReleaseBounded);
          }
          assume false;
        }
      assume (forall _r_10_5: Ref ::
        { PostMask[_r_10_5, MustReleaseBounded] }
        HasDirectPerm(PostMask, _r_10_5, MustReleaseBounded) ==> false
      );
      
      // -- Check definedness of (forperm _r_10: Ref [_r_10.MustReleaseUnbounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_10_6, MustReleaseUnbounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_10.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2587]"}
              HasDirectPerm(PostMask, _r_10_6, MustReleaseUnbounded);
          }
          assume false;
        }
      assume (forall _r_10_7: Ref ::
        { PostMask[_r_10_7, MustReleaseUnbounded] }
        HasDirectPerm(PostMask, _r_10_7, MustReleaseUnbounded) ==> false
      );
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Assumptions about local variables
    assume Heap[_err, $allocated];
    assume Heap[self_3, $allocated];
    assume Heap[code_2, $allocated];
  
  // -- Translating statement: // id = 1
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 2
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 3
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 4
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 5
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 6
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 7
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 8
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 9
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 10
  // _method_measures_157 := Seq[Measure$]() -- testsfunctionalverificationexamplescav_example.py.vpr@835.3--835.42
    _method_measures_157 := (Seq#Empty(): Seq Measure$DomainType);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 11
  // inhale typeof(self_0) == Ticket() -- testsfunctionalverificationexamplescav_example.py.vpr@836.3--836.36
    assume (typeof(self_0): PyTypeDomainType) == Ticket;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 12
  // _err := null -- testsfunctionalverificationexamplescav_example.py.vpr@837.3--837.15
    _err := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 13
  // self_3 := self_0 -- testsfunctionalverificationexamplescav_example.py.vpr@838.3--838.19
    self_3 := self_0;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 14
  // code_2 := code -- testsfunctionalverificationexamplescav_example.py.vpr@839.3--839.17
    code_2 := code;
    assume state(Heap, Mask);
  
  // -- Translating statement: if (perm(_MaySet(self_3, 578847845651634811226368290157834565233854867796)) > none) -- testsfunctionalverificationexamplescav_example.py.vpr@840.3--843.4
    if (NoPerm < Mask[null, _MaySet(self_3, 578847845651634811226368290157834565233854867796)]) {
      
      // -- Translating statement: // id = 15
  // exhale acc(_MaySet(self_3, 578847845651634811226368290157834565233854867796), write) -- testsfunctionalverificationexamplescav_example.py.vpr@841.5--841.89
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Exhale might fail. There might be insufficient permission to access _MaySet(self_3, 578847845651634811226368290157834565233854867796) (testsfunctionalverificationexamplescav_example.py.vpr@841.12--841.89) [2589]"}
            perm <= Mask[null, _MaySet(self_3, 578847845651634811226368290157834565233854867796)];
        }
        Mask[null, _MaySet(self_3, 578847845651634811226368290157834565233854867796)] := Mask[null, _MaySet(self_3, 578847845651634811226368290157834565233854867796)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        assume state(Heap, Mask);
      
      // -- Translating statement: // id = 16
  // inhale acc(self_3.Ticket_discount_code, write) -- testsfunctionalverificationexamplescav_example.py.vpr@842.5--842.51
        perm := FullPerm;
        assume self_3 != null;
        Mask[self_3, Ticket_discount_code] := Mask[self_3, Ticket_discount_code] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: // id = 17
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 18
  // self_3.Ticket_discount_code := code_2 -- testsfunctionalverificationexamplescav_example.py.vpr@844.3--844.40
    assert {:msg "  Assignment might fail. There might be insufficient permission to access self_3.Ticket_discount_code (testsfunctionalverificationexamplescav_example.py.vpr@844.3--844.40) [2591]"}
      FullPerm == Mask[self_3, Ticket_discount_code];
    Heap[self_3, Ticket_discount_code] := code_2;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 19
  // goto __end -- testsfunctionalverificationexamplescav_example.py.vpr@845.3--845.13
    goto __end;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 20
  // label __end -- testsfunctionalverificationexamplescav_example.py.vpr@846.3--846.14
    __end:
    Label__endMask := Mask;
    Label__endHeap := Heap;
    __end_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of Ticket_set_discount might not hold. Assertion (forperm _r_10: Ref [MustInvokeBounded(_r_10)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2592]"}
      (forall _r_10_8: Ref ::
      { Mask[null, MustInvokeBounded(_r_10_8)] }
      HasDirectPerm(Mask, null, MustInvokeBounded(_r_10_8)) ==> false
    );
    assert {:msg "  Postcondition of Ticket_set_discount might not hold. Assertion (forperm _r_10: Ref [MustInvokeUnbounded(_r_10)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2593]"}
      (forall _r_10_9: Ref ::
      { Mask[null, MustInvokeUnbounded(_r_10_9)] }
      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_10_9)) ==> false
    );
    assert {:msg "  Postcondition of Ticket_set_discount might not hold. Assertion (forperm _r_10: Ref [_r_10.MustReleaseBounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2594]"}
      (forall _r_10_10: Ref ::
      { Mask[_r_10_10, MustReleaseBounded] }
      HasDirectPerm(Mask, _r_10_10, MustReleaseBounded) ==> false
    );
    assert {:msg "  Postcondition of Ticket_set_discount might not hold. Assertion (forperm _r_10: Ref [_r_10.MustReleaseUnbounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@828.11--828.263) [2595]"}
      (forall _r_10_11: Ref ::
      { Mask[_r_10_11, MustReleaseUnbounded] }
      HasDirectPerm(Mask, _r_10_11, MustReleaseUnbounded) ==> false
    );
}

// ==================================================
// Translation of method main
// ==================================================

procedure main(_cthread_161: Ref, _caller_measures_161: (Seq Measure$DomainType), _residue_162: Perm) returns (_current_wait_level_161: Perm)
  modifies Heap, Mask;
{
  var __end_lblGuard: bool;
  var _r_14: Ref;
  var _r_14_2: Ref;
  var _r_14_4: Ref;
  var _r_14_6: Ref;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_12: Ref;
  var _r_12_2: Ref;
  var _r_13: Ref;
  var _r_13_2: Ref;
  var _r_13_4: Ref;
  var _r_13_6: Ref;
  var _method_measures_161: (Seq Measure$DomainType);
  var module_defined_0: bool;
  var module_names_0: (Set _NameDomainType);
  var perm: Perm;
  var Label__endMask: MaskType;
  var Label__endHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    __end_lblGuard := false;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_161, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_161 != null;
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_161): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume Mask[null, MustTerminate(_cthread_161)] == NoPerm;
        
        // -- Check definedness of (forperm _r_14: Ref [MustInvokeBounded(_r_14)] :: false)
          if (*) {
            if (HasDirectPerm(Mask, null, MustInvokeBounded(_r_14))) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_14) (testsfunctionalverificationexamplescav_example.py.vpr@852.12--852.311) [2596]"}
                HasDirectPerm(Mask, null, MustInvokeBounded(_r_14));
            }
            assume false;
          }
        assume (forall _r_14_1: Ref ::
          { Mask[null, MustInvokeBounded(_r_14_1)] }
          HasDirectPerm(Mask, null, MustInvokeBounded(_r_14_1)) ==> false
        );
        
        // -- Check definedness of (forperm _r_14: Ref [MustInvokeUnbounded(_r_14)] :: false)
          if (*) {
            if (HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_14_2))) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_14) (testsfunctionalverificationexamplescav_example.py.vpr@852.12--852.311) [2597]"}
                HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_14_2));
            }
            assume false;
          }
        assume (forall _r_14_3: Ref ::
          { Mask[null, MustInvokeUnbounded(_r_14_3)] }
          HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_14_3)) ==> false
        );
        
        // -- Check definedness of (forperm _r_14: Ref [_r_14.MustReleaseBounded] :: false)
          if (*) {
            if (HasDirectPerm(Mask, _r_14_4, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_14.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@852.12--852.311) [2598]"}
                HasDirectPerm(Mask, _r_14_4, MustReleaseBounded);
            }
            assume false;
          }
        assume (forall _r_14_5: Ref ::
          { Mask[_r_14_5, MustReleaseBounded] }
          HasDirectPerm(Mask, _r_14_5, MustReleaseBounded) ==> false
        );
        
        // -- Check definedness of (forperm _r_14: Ref [_r_14.MustReleaseUnbounded] :: false)
          if (*) {
            if (HasDirectPerm(Mask, _r_14_6, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_14.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@852.12--852.311) [2599]"}
                HasDirectPerm(Mask, _r_14_6, MustReleaseUnbounded);
            }
            assume false;
          }
        assume (forall _r_14_7: Ref ::
          { Mask[_r_14_7, MustReleaseUnbounded] }
          HasDirectPerm(Mask, _r_14_7, MustReleaseUnbounded) ==> false
        );
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_161 != null;
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_161): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_12: Ref [_r_12.MustReleaseBounded] :: Level(_r_12) <= _current_wait_level_161)
          if (*) {
            if (HasDirectPerm(PostMask, _r_12, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_12.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@853.11--853.250) [2600]"}
                HasDirectPerm(PostMask, _r_12, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_12_1: Ref ::
          { PostMask[_r_12_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_12_1, MustReleaseBounded) ==> Level(PostHeap, _r_12_1) <= _current_wait_level_161
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_12: Ref [_r_12.MustReleaseUnbounded] :: Level(_r_12) <= _current_wait_level_161)
          if (*) {
            if (HasDirectPerm(PostMask, _r_12_2, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_12.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@853.11--853.250) [2601]"}
                HasDirectPerm(PostMask, _r_12_2, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_12_3: Ref ::
          { PostMask[_r_12_3, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_12_3, MustReleaseUnbounded) ==> Level(PostHeap, _r_12_3) <= _current_wait_level_161
        );
        assume _residue_162 <= _current_wait_level_161;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of (forperm _r_13: Ref [MustInvokeBounded(_r_13)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeBounded(_r_13))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeBounded(_r_13) (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2602]"}
              HasDirectPerm(PostMask, null, MustInvokeBounded(_r_13));
          }
          assume false;
        }
      assume (forall _r_13_1: Ref ::
        { PostMask[null, MustInvokeBounded(_r_13_1)] }
        HasDirectPerm(PostMask, null, MustInvokeBounded(_r_13_1)) ==> false
      );
      
      // -- Check definedness of (forperm _r_13: Ref [MustInvokeUnbounded(_r_13)] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_13_2))) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access MustInvokeUnbounded(_r_13) (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2603]"}
              HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_13_2));
          }
          assume false;
        }
      assume (forall _r_13_3: Ref ::
        { PostMask[null, MustInvokeUnbounded(_r_13_3)] }
        HasDirectPerm(PostMask, null, MustInvokeUnbounded(_r_13_3)) ==> false
      );
      
      // -- Check definedness of (forperm _r_13: Ref [_r_13.MustReleaseBounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_13_4, MustReleaseBounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_13.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2604]"}
              HasDirectPerm(PostMask, _r_13_4, MustReleaseBounded);
          }
          assume false;
        }
      assume (forall _r_13_5: Ref ::
        { PostMask[_r_13_5, MustReleaseBounded] }
        HasDirectPerm(PostMask, _r_13_5, MustReleaseBounded) ==> false
      );
      
      // -- Check definedness of (forperm _r_13: Ref [_r_13.MustReleaseUnbounded] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, _r_13_6, MustReleaseUnbounded)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_13.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2605]"}
              HasDirectPerm(PostMask, _r_13_6, MustReleaseUnbounded);
          }
          assume false;
        }
      assume (forall _r_13_7: Ref ::
        { PostMask[_r_13_7, MustReleaseUnbounded] }
        HasDirectPerm(PostMask, _r_13_7, MustReleaseUnbounded) ==> false
      );
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: // id = 1
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 2
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 3
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 4
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 5
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 6
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 7
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 8
  // _method_measures_161 := Seq[Measure$]() -- testsfunctionalverificationexamplescav_example.py.vpr@860.3--860.42
    _method_measures_161 := (Seq#Empty(): Seq Measure$DomainType);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 9
  // module_defined_0 := true -- testsfunctionalverificationexamplescav_example.py.vpr@861.3--861.27
    module_defined_0 := true;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 10
  // module_names_0 := Set[_Name]() -- testsfunctionalverificationexamplescav_example.py.vpr@862.3--862.33
    module_names_0 := (Set#Empty(): Set _NameDomainType);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 11
  // module_names_0 := (module_names_0 union Set(_single(6872323072689856351))) -- testsfunctionalverificationexamplescav_example.py.vpr@863.3--863.77
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(6872323072689856351): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 12
  // inhale acc(__file__()._val, 99 / 100) &&
  //   (issubtype(typeof(__file__()._val), str()) &&
  //   issubtype(typeof(__file__()._val), str())) -- testsfunctionalverificationexamplescav_example.py.vpr@864.3--864.130
    assume state(Heap, Mask);
    
    // -- Check definedness of acc(__file__()._val, 99 / 100)
      if (*) {
        // Stop execution
        assume false;
      }
    perm := 99 / 100;
    assert {:msg "  Inhale might fail. Fraction 99 / 100 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@864.10--864.130) [2606]"}
      perm >= NoPerm;
    assume perm > NoPerm ==> __file__(Heap) != null;
    Mask[__file__(Heap), _val] := Mask[__file__(Heap), _val] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of issubtype(typeof(__file__()._val), str())
      assert {:msg "  Inhale might fail. There might be insufficient permission to access __file__()._val (testsfunctionalverificationexamplescav_example.py.vpr@864.10--864.130) [2607]"}
        HasDirectPerm(Mask, __file__(Heap), _val);
      if (*) {
        // Stop execution
        assume false;
      }
    assume (issubtype((typeof(Heap[__file__(Heap), _val]): PyTypeDomainType), str): bool);
    assume state(Heap, Mask);
    
    // -- Check definedness of issubtype(typeof(__file__()._val), str())
      assert {:msg "  Inhale might fail. There might be insufficient permission to access __file__()._val (testsfunctionalverificationexamplescav_example.py.vpr@864.10--864.130) [2608]"}
        HasDirectPerm(Mask, __file__(Heap), _val);
      if (*) {
        // Stop execution
        assume false;
      }
    assume (issubtype((typeof(Heap[__file__(Heap), _val]): PyTypeDomainType), str): bool);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 13
  // module_names_0 := (module_names_0 union Set(_single(6872323076851130207))) -- testsfunctionalverificationexamplescav_example.py.vpr@865.3--865.77
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(6872323076851130207): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 14
  // inhale acc(__name__()._val, 99 / 100) &&
  //   (issubtype(typeof(__name__()._val), str()) &&
  //   (issubtype(typeof(__name__()._val), str()) &&
  //   str___eq__(str___create__(8, 6872332955275845471), __name__()._val))) -- testsfunctionalverificationexamplescav_example.py.vpr@866.3--866.201
    assume state(Heap, Mask);
    
    // -- Check definedness of acc(__name__()._val, 99 / 100)
      if (*) {
        // Stop execution
        assume false;
      }
    perm := 99 / 100;
    assert {:msg "  Inhale might fail. Fraction 99 / 100 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@866.10--866.201) [2609]"}
      perm >= NoPerm;
    assume perm > NoPerm ==> __name__(Heap) != null;
    Mask[__name__(Heap), _val] := Mask[__name__(Heap), _val] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of issubtype(typeof(__name__()._val), str())
      assert {:msg "  Inhale might fail. There might be insufficient permission to access __name__()._val (testsfunctionalverificationexamplescav_example.py.vpr@866.10--866.201) [2610]"}
        HasDirectPerm(Mask, __name__(Heap), _val);
      if (*) {
        // Stop execution
        assume false;
      }
    assume (issubtype((typeof(Heap[__name__(Heap), _val]): PyTypeDomainType), str): bool);
    assume state(Heap, Mask);
    
    // -- Check definedness of issubtype(typeof(__name__()._val), str())
      assert {:msg "  Inhale might fail. There might be insufficient permission to access __name__()._val (testsfunctionalverificationexamplescav_example.py.vpr@866.10--866.201) [2611]"}
        HasDirectPerm(Mask, __name__(Heap), _val);
      if (*) {
        // Stop execution
        assume false;
      }
    assume (issubtype((typeof(Heap[__name__(Heap), _val]): PyTypeDomainType), str): bool);
    assume state(Heap, Mask);
    
    // -- Check definedness of str___eq__(str___create__(8, 6872332955275845471), __name__()._val)
      if (*) {
        // Stop execution
        assume false;
      }
      assert {:msg "  Inhale might fail. There might be insufficient permission to access __name__()._val (testsfunctionalverificationexamplescav_example.py.vpr@866.10--866.201) [2612]"}
        HasDirectPerm(Mask, __name__(Heap), _val);
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        assert {:msg "  Precondition of function str___eq__ might not hold. Assertion issubtype(typeof(str___create__(8, 6872332955275845471)), str()) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@866.134--866.201) [2613]"}
          (issubtype((typeof(str___create__(Heap, 8, 6872332955275845471)): PyTypeDomainType), str): bool);
        // Stop execution
        assume false;
      }
    assume str___eq__(Heap, str___create__(Heap, 8, 6872332955275845471), Heap[__name__(Heap), _val]);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 15
  // module_names_0 := (module_names_0 union
  //   Set(_single(8038062462289584464661321053517))) -- testsfunctionalverificationexamplescav_example.py.vpr@867.3--867.89
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(8038062462289584464661321053517): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 16
  // module_names_0 := (module_names_0 union Set(_single(1953720652))) -- testsfunctionalverificationexamplescav_example.py.vpr@868.3--868.68
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(1953720652): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 17
  // module_names_0 := (module_names_0 union Set(_single(435611006292))) -- testsfunctionalverificationexamplescav_example.py.vpr@869.3--869.70
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(435611006292): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 18
  // module_names_0 := (module_names_0 union
  //   Set(_single(146793563365898239306910909426909867859))) -- testsfunctionalverificationexamplescav_example.py.vpr@870.3--870.97
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(146793563365898239306910909426909867859): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 19
  // module_names_0 := (module_names_0 union
  //   Set(_single(2129761664003936118119))) -- testsfunctionalverificationexamplescav_example.py.vpr@871.3--871.80
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(2129761664003936118119): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 20
  // module_names_0 := (module_names_0 union Set(_single(6872339552563453791))) -- testsfunctionalverificationexamplescav_example.py.vpr@872.3--872.77
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(6872339552563453791): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 21
  // module_names_0 := (module_names_0 union
  //   Set(_single(36033797551066912423438214515))) -- testsfunctionalverificationexamplescav_example.py.vpr@873.3--873.87
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(36033797551066912423438214515): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 22
  // module_names_0 := (module_names_0 union Set(_single(127978942196052))) -- testsfunctionalverificationexamplescav_example.py.vpr@874.3--874.73
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(127978942196052): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 23
  // module_names_0 := (module_names_0 union
  //   Set(_single(9147261558914496062541770551919))) -- testsfunctionalverificationexamplescav_example.py.vpr@875.3--875.89
    module_names_0 := Set#Union(module_names_0, Set#Singleton((_single(9147261558914496062541770551919): _NameDomainType)));
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 24
  // goto __end -- testsfunctionalverificationexamplescav_example.py.vpr@876.3--876.13
    goto __end;
    assume state(Heap, Mask);
  
  // -- Translating statement: // id = 25
  // label __end -- testsfunctionalverificationexamplescav_example.py.vpr@877.3--877.14
    __end:
    Label__endMask := Mask;
    Label__endHeap := Heap;
    __end_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of main might not hold. Assertion (forperm _r_13: Ref [MustInvokeBounded(_r_13)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2614]"}
      (forall _r_13_8: Ref ::
      { Mask[null, MustInvokeBounded(_r_13_8)] }
      HasDirectPerm(Mask, null, MustInvokeBounded(_r_13_8)) ==> false
    );
    assert {:msg "  Postcondition of main might not hold. Assertion (forperm _r_13: Ref [MustInvokeUnbounded(_r_13)] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2615]"}
      (forall _r_13_9: Ref ::
      { Mask[null, MustInvokeUnbounded(_r_13_9)] }
      HasDirectPerm(Mask, null, MustInvokeUnbounded(_r_13_9)) ==> false
    );
    assert {:msg "  Postcondition of main might not hold. Assertion (forperm _r_13: Ref [_r_13.MustReleaseBounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2616]"}
      (forall _r_13_10: Ref ::
      { Mask[_r_13_10, MustReleaseBounded] }
      HasDirectPerm(Mask, _r_13_10, MustReleaseBounded) ==> false
    );
    assert {:msg "  Postcondition of main might not hold. Assertion (forperm _r_13: Ref [_r_13.MustReleaseUnbounded] :: false) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@854.11--854.263) [2617]"}
      (forall _r_13_11: Ref ::
      { Mask[_r_13_11, MustReleaseUnbounded] }
      HasDirectPerm(Mask, _r_13_11, MustReleaseUnbounded) ==> false
    );
}

// ==================================================
// Translation of method Iterator___next__
// ==================================================

procedure Iterator___next__(_cthread_149: Ref, _caller_measures_149: (Seq Measure$DomainType), _residue_149: Perm, self: Ref) returns (_current_wait_level_149: Perm, _res: Ref, _err: Ref)
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_15_4: Ref;
  var _r_15_5: Ref;
  var r_2: Ref;
  var r_4: Ref;
  var r_4_1: Ref;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_149, $allocated];
    assume Heap[self, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_149 != null;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_149, _cthread_149, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_149, _cthread_149, 1);
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_149): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        perm := 1 / 40;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@884.12--884.38) [2618]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        Mask[self, list_acc] := Mask[self, list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := FullPerm;
        assume self != null;
        Mask[self, __iter_index] := Mask[self, __iter_index] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := FullPerm;
        assume self != null;
        Mask[self, __previous] := Mask[self, __previous] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_149, _cthread_149, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_149, _cthread_149, 1);
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_149 != null;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of Measure$check(_caller_measures_149, _cthread_149, 1)
        if (*) {
          // Stop execution
          assume false;
        }
      assume Measure$check(Heap, _caller_measures_149, _cthread_149, 1);
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_149): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      perm := 1 / 40;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@884.12--884.38) [2619]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      Mask[self, list_acc] := Mask[self, list_acc] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      perm := FullPerm;
      assume self != null;
      Mask[self, __iter_index] := Mask[self, __iter_index] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      perm := FullPerm;
      assume self != null;
      Mask[self, __previous] := Mask[self, __previous] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_15: Ref [_r_15.MustReleaseBounded] :: Level(_r_15) <= _current_wait_level_149)
          if (*) {
            if (HasDirectPerm(PostMask, _r_15_4, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_15.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@888.11--888.250) [2620]"}
                HasDirectPerm(PostMask, _r_15_4, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_15_1: Ref ::
          { PostMask[_r_15_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_15_1, MustReleaseBounded) ==> Level(PostHeap, _r_15_1) <= _current_wait_level_149
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_15: Ref [_r_15.MustReleaseUnbounded] :: Level(_r_15) <= _current_wait_level_149)
          if (*) {
            if (HasDirectPerm(PostMask, _r_15_5, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_15.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@888.11--888.250) [2621]"}
                HasDirectPerm(PostMask, _r_15_5, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_15_3: Ref ::
          { PostMask[_r_15_3, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_15_3, MustReleaseUnbounded) ==> Level(PostHeap, _r_15_3) <= _current_wait_level_149
        );
        assume _residue_149 <= _current_wait_level_149;
        assume state(PostHeap, PostMask);
        perm := 1 / 40;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2622]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        PostMask[self, list_acc] := PostMask[self, list_acc] + perm;
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of self.list_acc == old(self.list_acc)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2623]"}
            HasDirectPerm(PostMask, self, list_acc);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2624]"}
            HasDirectPerm(old(Mask), self, list_acc);
        assume Seq#Equal(PostHeap[self, list_acc], old(Heap)[self, list_acc]);
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume self != null;
        PostMask[self, __iter_index] := PostMask[self, __iter_index] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of self.__iter_index <= |self.list_acc| + 1
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@891.11--891.51) [2625]"}
            HasDirectPerm(PostMask, self, __iter_index);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@891.11--891.51) [2626]"}
            HasDirectPerm(PostMask, self, list_acc);
        assume PostHeap[self, __iter_index] <= Seq#Length(PostHeap[self, list_acc]) + 1;
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of old(self.__iter_index == |self.list_acc|) == (_err != null)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@892.11--892.70) [2627]"}
            HasDirectPerm(old(Mask), self, __iter_index);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@892.11--892.70) [2628]"}
            HasDirectPerm(old(Mask), self, list_acc);
        assume (old(Heap)[self, __iter_index] == Seq#Length(old(Heap)[self, list_acc])) == (_err != null);
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume self != null;
        PostMask[self, __previous] := PostMask[self, __previous] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        if (_err == null) {
          
          // -- Check definedness of self.__iter_index == old(self.__iter_index) + 1
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@894.11--894.75) [2629]"}
              HasDirectPerm(PostMask, self, __iter_index);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@894.11--894.75) [2630]"}
              HasDirectPerm(old(Mask), self, __iter_index);
          assume PostHeap[self, __iter_index] == old(Heap)[self, __iter_index] + 1;
        }
        assume state(PostHeap, PostMask);
        if (_err == null) {
          
          // -- Check definedness of self.__iter_index > 0
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@895.11--895.49) [2631]"}
              HasDirectPerm(PostMask, self, __iter_index);
          assume PostHeap[self, __iter_index] > 0;
        }
        assume state(PostHeap, PostMask);
        if (_err == null) {
          
          // -- Check definedness of self.__previous == self.list_acc[..self.__iter_index - 1]
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2632]"}
              HasDirectPerm(PostMask, self, __previous);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2633]"}
              HasDirectPerm(PostMask, self, list_acc);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2634]"}
              HasDirectPerm(PostMask, self, __iter_index);
          assume Seq#Equal(PostHeap[self, __previous], Seq#Take(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 1));
        }
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of |self.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@897.11--897.56) [2635]"}
            HasDirectPerm(PostMask, self, list_acc);
        if (Seq#Length(PostHeap[self, list_acc]) > 0) {
          
          // -- Check definedness of self.__iter_index > 0
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@897.11--897.56) [2636]"}
              HasDirectPerm(PostMask, self, __iter_index);
          assume PostHeap[self, __iter_index] > 0;
        }
        assume state(PostHeap, PostMask);
        if (_err != null) {
          
          // -- Check definedness of self.__previous == self.list_acc
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@898.11--898.60) [2637]"}
              HasDirectPerm(PostMask, self, __previous);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@898.11--898.60) [2638]"}
              HasDirectPerm(PostMask, self, list_acc);
          assume Seq#Equal(PostHeap[self, __previous], PostHeap[self, list_acc]);
        }
        assume state(PostHeap, PostMask);
        if (_err != null) {
          
          // -- Check definedness of self.__iter_index == |self.list_acc|
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@899.11--899.64) [2639]"}
              HasDirectPerm(PostMask, self, __iter_index);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@899.11--899.64) [2640]"}
              HasDirectPerm(PostMask, self, list_acc);
          assume PostHeap[self, __iter_index] == Seq#Length(PostHeap[self, list_acc]);
        }
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of |self.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2641]"}
            HasDirectPerm(PostMask, self, list_acc);
        if (Seq#Length(PostHeap[self, list_acc]) > 0) {
          
          // -- Check definedness of _res == self.list_acc[self.__iter_index - 1]
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2642]"}
              HasDirectPerm(PostMask, self, list_acc);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2643]"}
              HasDirectPerm(PostMask, self, __iter_index);
            assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2644]"}
              PostHeap[self, __iter_index] - 1 >= 0;
            assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2645]"}
              PostHeap[self, __iter_index] - 1 < Seq#Length(PostHeap[self, list_acc]);
          assume _res == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 1);
          
          // -- Check definedness of (_res in self.list_acc)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2646]"}
              HasDirectPerm(PostMask, self, list_acc);
          assume Seq#Contains(PostHeap[self, list_acc], _res);
        }
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of |self.list_acc| > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@901.11--901.89) [2647]"}
            HasDirectPerm(PostMask, self, list_acc);
        if (Seq#Length(PostHeap[self, list_acc]) > 0) {
          assume (issubtype((typeof(_res): PyTypeDomainType), (Iterator_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): bool);
        }
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forall r: Ref :: { (r in self.__previous) } (r in self.__previous) == ((r in old(self.__previous)) || (self.__iter_index > 1 && (r == self.list_acc[self.__iter_index - 2] && _err == null) || self.__iter_index > 0 && (_err != null && r == self.list_acc[self.__iter_index - 1]))))
          if (*) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2648]"}
              HasDirectPerm(PostMask, self, __previous);
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2649]"}
              HasDirectPerm(old(Mask), self, __previous);
            if (!Seq#Contains(old(Heap)[self, __previous], r_2)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2650]"}
                HasDirectPerm(PostMask, self, __iter_index);
              if (PostHeap[self, __iter_index] > 1) {
                assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2651]"}
                  HasDirectPerm(PostMask, self, list_acc);
                assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2652]"}
                  HasDirectPerm(PostMask, self, __iter_index);
                assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 2] into self.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2653]"}
                  PostHeap[self, __iter_index] - 2 >= 0;
                assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 2] into self.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2654]"}
                  PostHeap[self, __iter_index] - 2 < Seq#Length(PostHeap[self, list_acc]);
              }
              if (!(PostHeap[self, __iter_index] > 1 && (r_2 == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 2) && _err == null))) {
                assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2655]"}
                  HasDirectPerm(PostMask, self, __iter_index);
                if (PostHeap[self, __iter_index] > 0) {
                  if (_err != null) {
                    assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2656]"}
                      HasDirectPerm(PostMask, self, list_acc);
                    assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2657]"}
                      HasDirectPerm(PostMask, self, __iter_index);
                    assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2658]"}
                      PostHeap[self, __iter_index] - 1 >= 0;
                    assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2659]"}
                      PostHeap[self, __iter_index] - 1 < Seq#Length(PostHeap[self, list_acc]);
                  }
                }
              }
            }
            assume false;
          }
        assume (forall r_3: Ref ::
          { Seq#ContainsTrigger(PostHeap[self, __previous], r_3) } { Seq#Contains(PostHeap[self, __previous], r_3) }
          Seq#Contains(PostHeap[self, __previous], r_3) == (Seq#Contains(old(Heap)[self, __previous], r_3) || ((PostHeap[self, __iter_index] > 1 && (r_3 == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 2) && _err == null)) || (PostHeap[self, __iter_index] > 0 && (_err != null && r_3 == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 1)))))
        );
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      perm := 1 / 40;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2660]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      PostMask[self, list_acc] := PostMask[self, list_acc] + perm;
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of self.list_acc == old(self.list_acc)
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2661]"}
          HasDirectPerm(PostMask, self, list_acc);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2662]"}
          HasDirectPerm(old(Mask), self, list_acc);
      assume Seq#Equal(PostHeap[self, list_acc], old(Heap)[self, list_acc]);
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume self != null;
      PostMask[self, __iter_index] := PostMask[self, __iter_index] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of self.__iter_index <= |self.list_acc| + 1
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@891.11--891.51) [2663]"}
          HasDirectPerm(PostMask, self, __iter_index);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@891.11--891.51) [2664]"}
          HasDirectPerm(PostMask, self, list_acc);
      assume PostHeap[self, __iter_index] <= Seq#Length(PostHeap[self, list_acc]) + 1;
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of old(self.__iter_index == |self.list_acc|) == (_err != null)
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@892.11--892.70) [2665]"}
          HasDirectPerm(old(Mask), self, __iter_index);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@892.11--892.70) [2666]"}
          HasDirectPerm(old(Mask), self, list_acc);
      assume (old(Heap)[self, __iter_index] == Seq#Length(old(Heap)[self, list_acc])) == (_err != null);
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume self != null;
      PostMask[self, __previous] := PostMask[self, __previous] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      if (_err == null) {
        
        // -- Check definedness of self.__iter_index == old(self.__iter_index) + 1
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@894.11--894.75) [2667]"}
            HasDirectPerm(PostMask, self, __iter_index);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@894.11--894.75) [2668]"}
            HasDirectPerm(old(Mask), self, __iter_index);
        assume PostHeap[self, __iter_index] == old(Heap)[self, __iter_index] + 1;
      }
      assume state(PostHeap, PostMask);
      if (_err == null) {
        
        // -- Check definedness of self.__iter_index > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@895.11--895.49) [2669]"}
            HasDirectPerm(PostMask, self, __iter_index);
        assume PostHeap[self, __iter_index] > 0;
      }
      assume state(PostHeap, PostMask);
      if (_err == null) {
        
        // -- Check definedness of self.__previous == self.list_acc[..self.__iter_index - 1]
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2670]"}
            HasDirectPerm(PostMask, self, __previous);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2671]"}
            HasDirectPerm(PostMask, self, list_acc);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2672]"}
            HasDirectPerm(PostMask, self, __iter_index);
        assume Seq#Equal(PostHeap[self, __previous], Seq#Take(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 1));
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of |self.list_acc| > 0
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@897.11--897.56) [2673]"}
          HasDirectPerm(PostMask, self, list_acc);
      if (Seq#Length(PostHeap[self, list_acc]) > 0) {
        
        // -- Check definedness of self.__iter_index > 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@897.11--897.56) [2674]"}
            HasDirectPerm(PostMask, self, __iter_index);
        assume PostHeap[self, __iter_index] > 0;
      }
      assume state(PostHeap, PostMask);
      if (_err != null) {
        
        // -- Check definedness of self.__previous == self.list_acc
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@898.11--898.60) [2675]"}
            HasDirectPerm(PostMask, self, __previous);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@898.11--898.60) [2676]"}
            HasDirectPerm(PostMask, self, list_acc);
        assume Seq#Equal(PostHeap[self, __previous], PostHeap[self, list_acc]);
      }
      assume state(PostHeap, PostMask);
      if (_err != null) {
        
        // -- Check definedness of self.__iter_index == |self.list_acc|
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@899.11--899.64) [2677]"}
            HasDirectPerm(PostMask, self, __iter_index);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@899.11--899.64) [2678]"}
            HasDirectPerm(PostMask, self, list_acc);
        assume PostHeap[self, __iter_index] == Seq#Length(PostHeap[self, list_acc]);
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of |self.list_acc| > 0
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2679]"}
          HasDirectPerm(PostMask, self, list_acc);
      if (Seq#Length(PostHeap[self, list_acc]) > 0) {
        
        // -- Check definedness of _res == self.list_acc[self.__iter_index - 1]
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2680]"}
            HasDirectPerm(PostMask, self, list_acc);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2681]"}
            HasDirectPerm(PostMask, self, __iter_index);
          assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2682]"}
            PostHeap[self, __iter_index] - 1 >= 0;
          assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2683]"}
            PostHeap[self, __iter_index] - 1 < Seq#Length(PostHeap[self, list_acc]);
        assume _res == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 1);
        
        // -- Check definedness of (_res in self.list_acc)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2684]"}
            HasDirectPerm(PostMask, self, list_acc);
        assume Seq#Contains(PostHeap[self, list_acc], _res);
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of |self.list_acc| > 0
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@901.11--901.89) [2685]"}
          HasDirectPerm(PostMask, self, list_acc);
      if (Seq#Length(PostHeap[self, list_acc]) > 0) {
        assume (issubtype((typeof(_res): PyTypeDomainType), (Iterator_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): bool);
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of (forall r: Ref :: { (r in self.__previous) } (r in self.__previous) == ((r in old(self.__previous)) || (self.__iter_index > 1 && (r == self.list_acc[self.__iter_index - 2] && _err == null) || self.__iter_index > 0 && (_err != null && r == self.list_acc[self.__iter_index - 1]))))
        if (*) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2686]"}
            HasDirectPerm(PostMask, self, __previous);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2687]"}
            HasDirectPerm(old(Mask), self, __previous);
          if (!Seq#Contains(old(Heap)[self, __previous], r_4)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2688]"}
              HasDirectPerm(PostMask, self, __iter_index);
            if (PostHeap[self, __iter_index] > 1) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2689]"}
                HasDirectPerm(PostMask, self, list_acc);
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2690]"}
                HasDirectPerm(PostMask, self, __iter_index);
              assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 2] into self.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2691]"}
                PostHeap[self, __iter_index] - 2 >= 0;
              assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 2] into self.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2692]"}
                PostHeap[self, __iter_index] - 2 < Seq#Length(PostHeap[self, list_acc]);
            }
            if (!(PostHeap[self, __iter_index] > 1 && (r_4 == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 2) && _err == null))) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2693]"}
                HasDirectPerm(PostMask, self, __iter_index);
              if (PostHeap[self, __iter_index] > 0) {
                if (_err != null) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2694]"}
                    HasDirectPerm(PostMask, self, list_acc);
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2695]"}
                    HasDirectPerm(PostMask, self, __iter_index);
                  assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2696]"}
                    PostHeap[self, __iter_index] - 1 >= 0;
                  assert {:msg "  Contract might not be well-formed. Index self.list_acc[self.__iter_index - 1] into self.list_acc might exceed sequence length. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2697]"}
                    PostHeap[self, __iter_index] - 1 < Seq#Length(PostHeap[self, list_acc]);
                }
              }
            }
          }
          assume false;
        }
      assume (forall r_1_1: Ref ::
        { Seq#ContainsTrigger(PostHeap[self, __previous], r_1_1) } { Seq#Contains(PostHeap[self, __previous], r_1_1) }
        Seq#Contains(PostHeap[self, __previous], r_1_1) == (Seq#Contains(old(Heap)[self, __previous], r_1_1) || ((PostHeap[self, __iter_index] > 1 && (r_1_1 == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 2) && _err == null)) || (PostHeap[self, __iter_index] > 0 && (_err != null && r_1_1 == Seq#Index(PostHeap[self, list_acc], PostHeap[self, __iter_index] - 1)))))
      );
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale false -- testsfunctionalverificationexamplescav_example.py.vpr@905.3--905.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of Iterator___next__ might not hold. Fraction 1 / 40 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2698]"}
      1 / 40 >= NoPerm;
    perm := 1 / 40;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2699]"}
        perm <= Mask[self, list_acc];
    }
    Mask[self, list_acc] := Mask[self, list_acc] - perm;
    assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.list_acc == old(self.list_acc) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@889.11--889.76) [2700]"}
      Seq#Equal(Heap[self, list_acc], old(Heap)[self, list_acc]);
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. There might be insufficient permission to access self.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@890.11--890.40) [2701]"}
        perm <= Mask[self, __iter_index];
    }
    Mask[self, __iter_index] := Mask[self, __iter_index] - perm;
    assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__iter_index <= |self.list_acc| + 1 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@891.11--891.51) [2702]"}
      Heap[self, __iter_index] <= Seq#Length(Heap[self, list_acc]) + 1;
    assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion old(self.__iter_index == |self.list_acc|) == (_err != null) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@892.11--892.70) [2703]"}
      (old(Heap)[self, __iter_index] == Seq#Length(old(Heap)[self, list_acc])) == (_err != null);
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. There might be insufficient permission to access self.__previous (testsfunctionalverificationexamplescav_example.py.vpr@893.11--893.38) [2704]"}
        perm <= Mask[self, __previous];
    }
    Mask[self, __previous] := Mask[self, __previous] - perm;
    if (_err == null) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__iter_index == old(self.__iter_index) + 1 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@894.11--894.75) [2705]"}
        Heap[self, __iter_index] == old(Heap)[self, __iter_index] + 1;
    }
    if (_err == null) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__iter_index > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@895.11--895.49) [2706]"}
        Heap[self, __iter_index] > 0;
    }
    if (_err == null) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__previous == self.list_acc[..self.__iter_index - 1] might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@896.11--896.85) [2707]"}
        Seq#Equal(Heap[self, __previous], Seq#Take(Heap[self, list_acc], Heap[self, __iter_index] - 1));
    }
    if (Seq#Length(Heap[self, list_acc]) > 0) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__iter_index > 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@897.11--897.56) [2708]"}
        Heap[self, __iter_index] > 0;
    }
    if (_err != null) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__previous == self.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@898.11--898.60) [2709]"}
        Seq#Equal(Heap[self, __previous], Heap[self, list_acc]);
    }
    if (_err != null) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion self.__iter_index == |self.list_acc| might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@899.11--899.64) [2710]"}
        Heap[self, __iter_index] == Seq#Length(Heap[self, list_acc]);
    }
    if (Seq#Length(Heap[self, list_acc]) > 0) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion _res == self.list_acc[self.__iter_index - 1] might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2711]"}
        _res == Seq#Index(Heap[self, list_acc], Heap[self, __iter_index] - 1);
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion (_res in self.list_acc) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@900.11--900.106) [2712]"}
        Seq#Contains(Heap[self, list_acc], _res);
    }
    if (Seq#Length(Heap[self, list_acc]) > 0) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion issubtype(typeof(_res), Iterator_arg(typeof(self), 0)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@901.11--901.89) [2713]"}
        (issubtype((typeof(_res): PyTypeDomainType), (Iterator_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): bool);
    }
    if (*) {
      assert {:msg "  Postcondition of Iterator___next__ might not hold. Assertion (r in self.__previous) == ((r in old(self.__previous)) || (self.__iter_index > 1 && (r == self.list_acc[self.__iter_index - 2] && _err == null) || self.__iter_index > 0 && (_err != null && r == self.list_acc[self.__iter_index - 1]))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@902.12--902.289) [2714]"}
        Seq#Contains(Heap[self, __previous], r_4_1) == (Seq#Contains(old(Heap)[self, __previous], r_4_1) || ((Heap[self, __iter_index] > 1 && (r_4_1 == Seq#Index(Heap[self, list_acc], Heap[self, __iter_index] - 2) && _err == null)) || (Heap[self, __iter_index] > 0 && (_err != null && r_4_1 == Seq#Index(Heap[self, list_acc], Heap[self, __iter_index] - 1)))));
      assume false;
    }
    assume (forall r_5_1: Ref ::
      { Seq#ContainsTrigger(Heap[self, __previous], r_5_1) } { Seq#Contains(Heap[self, __previous], r_5_1) }
      Seq#Contains(Heap[self, __previous], r_5_1) == (Seq#Contains(old(Heap)[self, __previous], r_5_1) || ((Heap[self, __iter_index] > 1 && (r_5_1 == Seq#Index(Heap[self, list_acc], Heap[self, __iter_index] - 2) && _err == null)) || (Heap[self, __iter_index] > 0 && (_err != null && r_5_1 == Seq#Index(Heap[self, list_acc], Heap[self, __iter_index] - 1)))))
    );
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method Iterator___del__
// ==================================================

procedure Iterator___del__(_cthread_150: Ref, _caller_measures_150: (Seq Measure$DomainType), _residue_150: Perm, self: Ref) returns (_current_wait_level_150: Perm)
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_17_2: Ref;
  var _r_17_3: Ref;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_150, $allocated];
    assume Heap[self, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_150 != null;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_150, _cthread_150, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_150, _cthread_150, 1);
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_150): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@912.12--912.38) [2715]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        Mask[self, list_acc] := Mask[self, list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@913.12--913.41) [2716]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        Mask[self, __container] := Mask[self, __container] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_150, _cthread_150, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_150, _cthread_150, 1);
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_150 != null;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of Measure$check(_caller_measures_150, _cthread_150, 1)
        if (*) {
          // Stop execution
          assume false;
        }
      assume Measure$check(Heap, _caller_measures_150, _cthread_150, 1);
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_150): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      perm := 1 / 20;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@912.12--912.38) [2717]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      Mask[self, list_acc] := Mask[self, list_acc] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      perm := 1 / 20;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@913.12--913.41) [2718]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      Mask[self, __container] := Mask[self, __container] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_17: Ref [_r_17.MustReleaseBounded] :: Level(_r_17) <= _current_wait_level_150)
          if (*) {
            if (HasDirectPerm(PostMask, _r_17_2, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_17.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@915.11--915.250) [2719]"}
                HasDirectPerm(PostMask, _r_17_2, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_17_1: Ref ::
          { PostMask[_r_17_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_17_1, MustReleaseBounded) ==> Level(PostHeap, _r_17_1) <= _current_wait_level_150
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_17: Ref [_r_17.MustReleaseUnbounded] :: Level(_r_17) <= _current_wait_level_150)
          if (*) {
            if (HasDirectPerm(PostMask, _r_17_3, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_17.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@915.11--915.250) [2720]"}
                HasDirectPerm(PostMask, _r_17_3, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_17_3_1: Ref ::
          { PostMask[_r_17_3_1, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_17_3_1, MustReleaseUnbounded) ==> Level(PostHeap, _r_17_3_1) <= _current_wait_level_150
        );
        assume _residue_150 <= _current_wait_level_150;
        assume state(PostHeap, PostMask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@916.11--916.40) [2721]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        PostMask[self, __container] := PostMask[self, __container] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of issubtype(typeof(self.__container), list(list_arg(typeof(self.__container), 0)))
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2722]"}
            HasDirectPerm(PostMask, self, __container);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2723]"}
            HasDirectPerm(PostMask, self, __container);
        if ((issubtype((typeof(PostHeap[self, __container]): PyTypeDomainType), (list((list_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
          
          // -- Check definedness of acc(self.__container.list_acc, 1 / 20)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2724]"}
              HasDirectPerm(PostMask, self, __container);
          perm := 1 / 20;
          assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2725]"}
            perm >= NoPerm;
          assume perm > NoPerm ==> PostHeap[self, __container] != null;
          PostMask[PostHeap[self, __container], list_acc] := PostMask[PostHeap[self, __container], list_acc] + perm;
          assume state(PostHeap, PostMask);
        }
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of issubtype(typeof(self.__container), dict(dict_arg(typeof(self.__container), 0), dict_arg(typeof(self.__container), 1)))
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2726]"}
            HasDirectPerm(PostMask, self, __container);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2727]"}
            HasDirectPerm(PostMask, self, __container);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2728]"}
            HasDirectPerm(PostMask, self, __container);
        if ((issubtype((typeof(PostHeap[self, __container]): PyTypeDomainType), (dict((dict_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType), (dict_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 1): PyTypeDomainType)): PyTypeDomainType)): bool)) {
          
          // -- Check definedness of acc(self.__container.dict_acc, 1 / 20)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2729]"}
              HasDirectPerm(PostMask, self, __container);
          perm := 1 / 20;
          assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2730]"}
            perm >= NoPerm;
          assume perm > NoPerm ==> PostHeap[self, __container] != null;
          PostMask[PostHeap[self, __container], dict_acc] := PostMask[PostHeap[self, __container], dict_acc] + perm;
          assume state(PostHeap, PostMask);
          
          // -- Check definedness of acc(self.__container.dict_acc2, 1 / 20)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2731]"}
              HasDirectPerm(PostMask, self, __container);
          perm := 1 / 20;
          assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2732]"}
            perm >= NoPerm;
          assume perm > NoPerm ==> PostHeap[self, __container] != null;
          PostMask[PostHeap[self, __container], dict_acc2] := PostMask[PostHeap[self, __container], dict_acc2] + perm;
          assume state(PostHeap, PostMask);
        }
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of issubtype(typeof(self.__container), set(set_arg(typeof(self.__container), 0)))
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2733]"}
            HasDirectPerm(PostMask, self, __container);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2734]"}
            HasDirectPerm(PostMask, self, __container);
        if ((issubtype((typeof(PostHeap[self, __container]): PyTypeDomainType), (set((set_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
          
          // -- Check definedness of acc(self.__container.set_acc, 1 / 20)
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2735]"}
              HasDirectPerm(PostMask, self, __container);
          perm := 1 / 20;
          assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2736]"}
            perm >= NoPerm;
          assume perm > NoPerm ==> PostHeap[self, __container] != null;
          PostMask[PostHeap[self, __container], set_acc] := PostMask[PostHeap[self, __container], set_acc] + perm;
          assume state(PostHeap, PostMask);
        }
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      perm := 1 / 20;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@916.11--916.40) [2737]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      PostMask[self, __container] := PostMask[self, __container] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of issubtype(typeof(self.__container), list(list_arg(typeof(self.__container), 0)))
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2738]"}
          HasDirectPerm(PostMask, self, __container);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2739]"}
          HasDirectPerm(PostMask, self, __container);
      if ((issubtype((typeof(PostHeap[self, __container]): PyTypeDomainType), (list((list_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
        
        // -- Check definedness of acc(self.__container.list_acc, 1 / 20)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2740]"}
            HasDirectPerm(PostMask, self, __container);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2741]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> PostHeap[self, __container] != null;
        PostMask[PostHeap[self, __container], list_acc] := PostMask[PostHeap[self, __container], list_acc] + perm;
        assume state(PostHeap, PostMask);
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of issubtype(typeof(self.__container), dict(dict_arg(typeof(self.__container), 0), dict_arg(typeof(self.__container), 1)))
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2742]"}
          HasDirectPerm(PostMask, self, __container);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2743]"}
          HasDirectPerm(PostMask, self, __container);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2744]"}
          HasDirectPerm(PostMask, self, __container);
      if ((issubtype((typeof(PostHeap[self, __container]): PyTypeDomainType), (dict((dict_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType), (dict_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 1): PyTypeDomainType)): PyTypeDomainType)): bool)) {
        
        // -- Check definedness of acc(self.__container.dict_acc, 1 / 20)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2745]"}
            HasDirectPerm(PostMask, self, __container);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2746]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> PostHeap[self, __container] != null;
        PostMask[PostHeap[self, __container], dict_acc] := PostMask[PostHeap[self, __container], dict_acc] + perm;
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of acc(self.__container.dict_acc2, 1 / 20)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2747]"}
            HasDirectPerm(PostMask, self, __container);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2748]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> PostHeap[self, __container] != null;
        PostMask[PostHeap[self, __container], dict_acc2] := PostMask[PostHeap[self, __container], dict_acc2] + perm;
        assume state(PostHeap, PostMask);
      }
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of issubtype(typeof(self.__container), set(set_arg(typeof(self.__container), 0)))
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2749]"}
          HasDirectPerm(PostMask, self, __container);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2750]"}
          HasDirectPerm(PostMask, self, __container);
      if ((issubtype((typeof(PostHeap[self, __container]): PyTypeDomainType), (set((set_arg((typeof(PostHeap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
        
        // -- Check definedness of acc(self.__container.set_acc, 1 / 20)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2751]"}
            HasDirectPerm(PostMask, self, __container);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2752]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> PostHeap[self, __container] != null;
        PostMask[PostHeap[self, __container], set_acc] := PostMask[PostHeap[self, __container], set_acc] + perm;
        assume state(PostHeap, PostMask);
      }
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale false -- testsfunctionalverificationexamplescav_example.py.vpr@922.3--922.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@916.11--916.40) [2753]"}
      1 / 20 >= NoPerm;
    perm := 1 / 20;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Iterator___del__ might not hold. There might be insufficient permission to access self.__container (testsfunctionalverificationexamplescav_example.py.vpr@916.11--916.40) [2754]"}
        perm <= Mask[self, __container];
    }
    Mask[self, __container] := Mask[self, __container] - perm;
    if ((issubtype((typeof(Heap[self, __container]): PyTypeDomainType), (list((list_arg((typeof(Heap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
      assert {:msg "  Postcondition of Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2755]"}
        1 / 20 >= NoPerm;
      perm := 1 / 20;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of Iterator___del__ might not hold. There might be insufficient permission to access self.__container.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@917.11--917.134) [2756]"}
          perm <= Mask[Heap[self, __container], list_acc];
      }
      Mask[Heap[self, __container], list_acc] := Mask[Heap[self, __container], list_acc] - perm;
    }
    if ((issubtype((typeof(Heap[self, __container]): PyTypeDomainType), (dict((dict_arg((typeof(Heap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType), (dict_arg((typeof(Heap[self, __container]): PyTypeDomainType), 1): PyTypeDomainType)): PyTypeDomainType)): bool)) {
      assert {:msg "  Postcondition of Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2757]"}
        1 / 20 >= NoPerm;
      perm := 1 / 20;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of Iterator___del__ might not hold. There might be insufficient permission to access self.__container.dict_acc (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2758]"}
          perm <= Mask[Heap[self, __container], dict_acc];
      }
      Mask[Heap[self, __container], dict_acc] := Mask[Heap[self, __container], dict_acc] - perm;
      assert {:msg "  Postcondition of Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2759]"}
        1 / 20 >= NoPerm;
      perm := 1 / 20;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of Iterator___del__ might not hold. There might be insufficient permission to access self.__container.dict_acc2 (testsfunctionalverificationexamplescav_example.py.vpr@918.11--918.216) [2760]"}
          perm <= Mask[Heap[self, __container], dict_acc2];
      }
      Mask[Heap[self, __container], dict_acc2] := Mask[Heap[self, __container], dict_acc2] - perm;
    }
    if ((issubtype((typeof(Heap[self, __container]): PyTypeDomainType), (set((set_arg((typeof(Heap[self, __container]): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool)) {
      assert {:msg "  Postcondition of Iterator___del__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2761]"}
        1 / 20 >= NoPerm;
      perm := 1 / 20;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of Iterator___del__ might not hold. There might be insufficient permission to access self.__container.set_acc (testsfunctionalverificationexamplescav_example.py.vpr@919.11--919.131) [2762]"}
          perm <= Mask[Heap[self, __container], set_acc];
      }
      Mask[Heap[self, __container], set_acc] := Mask[Heap[self, __container], set_acc] - perm;
    }
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method list___init__
// ==================================================

procedure list___init__(_cthread_8: Ref, _caller_measures_8: (Seq Measure$DomainType), _residue_8: Perm) returns (_current_wait_level_8: Perm, res: Ref)
  modifies Heap, Mask;
{
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_19_2: Ref;
  var _r_19_3: Ref;
  var perm: Perm;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_8, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_8 != null;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_8, _cthread_8, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_8, _cthread_8, 1);
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_8): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_8, _cthread_8, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_8, _cthread_8, 1);
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_8 != null;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of Measure$check(_caller_measures_8, _cthread_8, 1)
        if (*) {
          // Stop execution
          assume false;
        }
      assume Measure$check(Heap, _caller_measures_8, _cthread_8, 1);
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_8): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_19: Ref [_r_19.MustReleaseBounded] :: Level(_r_19) <= _current_wait_level_8)
          if (*) {
            if (HasDirectPerm(PostMask, _r_19_2, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_19.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@930.11--930.242) [2763]"}
                HasDirectPerm(PostMask, _r_19_2, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_19_1: Ref ::
          { PostMask[_r_19_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_19_1, MustReleaseBounded) ==> Level(PostHeap, _r_19_1) <= _current_wait_level_8
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_19: Ref [_r_19.MustReleaseUnbounded] :: Level(_r_19) <= _current_wait_level_8)
          if (*) {
            if (HasDirectPerm(PostMask, _r_19_3, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_19.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@930.11--930.242) [2764]"}
                HasDirectPerm(PostMask, _r_19_3, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_19_3_1: Ref ::
          { PostMask[_r_19_3_1, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_19_3_1, MustReleaseUnbounded) ==> Level(PostHeap, _r_19_3_1) <= _current_wait_level_8
        );
        assume _residue_8 <= _current_wait_level_8;
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume res != null;
        PostMask[res, list_acc] := PostMask[res, list_acc] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of res.list_acc == Seq[Ref]()
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@932.11--932.37) [2765]"}
            HasDirectPerm(PostMask, res, list_acc);
        assume Seq#Equal(PostHeap[res, list_acc], (Seq#Empty(): Seq Ref));
        assume state(PostHeap, PostMask);
        assume (typeof(res): PyTypeDomainType) == (list((list_arg((typeof(res): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType);
        assume state(PostHeap, PostMask);
        assume (Low(res): bool);
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume res != null;
      PostMask[res, list_acc] := PostMask[res, list_acc] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of res.list_acc == Seq[Ref]()
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@932.11--932.37) [2766]"}
          HasDirectPerm(PostMask, res, list_acc);
      assume Seq#Equal(PostHeap[res, list_acc], (Seq#Empty(): Seq Ref));
      assume state(PostHeap, PostMask);
      assume (typeof(res): PyTypeDomainType) == (list((list_arg((typeof(res): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType);
      assume state(PostHeap, PostMask);
      assume (Low(res): bool);
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale false -- testsfunctionalverificationexamplescav_example.py.vpr@937.3--937.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list___init__ might not hold. There might be insufficient permission to access res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@931.11--931.35) [2767]"}
        perm <= Mask[res, list_acc];
    }
    Mask[res, list_acc] := Mask[res, list_acc] - perm;
    assert {:msg "  Postcondition of list___init__ might not hold. Assertion res.list_acc == Seq[Ref]() might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@932.11--932.37) [2768]"}
      Seq#Equal(Heap[res, list_acc], (Seq#Empty(): Seq Ref));
    assert {:msg "  Postcondition of list___init__ might not hold. Assertion typeof(res) == list(list_arg(typeof(res), 0)) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@933.11--933.56) [2769]"}
      (typeof(res): PyTypeDomainType) == (list((list_arg((typeof(res): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType);
    assert {:msg "  Postcondition of list___init__ might not hold. Assertion (Low(res): Bool) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@934.11--934.19) [2770]"}
      (Low(res): bool);
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method list_append
// ==================================================

procedure list_append(_cthread_9: Ref, _caller_measures_9: (Seq Measure$DomainType), _residue_9: Perm, self: Ref, item: Ref) returns (_current_wait_level_9: Perm)
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_21_2: Ref;
  var _r_21_3: Ref;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_9, $allocated];
    assume Heap[self, $allocated];
    assume Heap[item, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_9 != null;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_9, _cthread_9, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_9, _cthread_9, 1);
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_9): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(self): PyTypeDomainType), (list((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
        assume state(Heap, Mask);
        perm := FullPerm;
        assume self != null;
        Mask[self, list_acc] := Mask[self, list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume (issubtype((typeof(item): PyTypeDomainType), (list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): bool);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_9, _cthread_9, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_9, _cthread_9, 1);
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_9 != null;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of Measure$check(_caller_measures_9, _cthread_9, 1)
        if (*) {
          // Stop execution
          assume false;
        }
      assume Measure$check(Heap, _caller_measures_9, _cthread_9, 1);
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_9): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(self): PyTypeDomainType), (list((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
      assume state(Heap, Mask);
      perm := FullPerm;
      assume self != null;
      Mask[self, list_acc] := Mask[self, list_acc] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      assume (issubtype((typeof(item): PyTypeDomainType), (list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): bool);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_21: Ref [_r_21.MustReleaseBounded] :: Level(_r_21) <= _current_wait_level_9)
          if (*) {
            if (HasDirectPerm(PostMask, _r_21_2, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_21.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@948.11--948.242) [2771]"}
                HasDirectPerm(PostMask, _r_21_2, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_21_1: Ref ::
          { PostMask[_r_21_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_21_1, MustReleaseBounded) ==> Level(PostHeap, _r_21_1) <= _current_wait_level_9
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_21: Ref [_r_21.MustReleaseUnbounded] :: Level(_r_21) <= _current_wait_level_9)
          if (*) {
            if (HasDirectPerm(PostMask, _r_21_3, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_21.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@948.11--948.242) [2772]"}
                HasDirectPerm(PostMask, _r_21_3, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_21_3_1: Ref ::
          { PostMask[_r_21_3_1, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_21_3_1, MustReleaseUnbounded) ==> Level(PostHeap, _r_21_3_1) <= _current_wait_level_9
        );
        assume _residue_9 <= _current_wait_level_9;
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume self != null;
        PostMask[self, list_acc] := PostMask[self, list_acc] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of self.list_acc == old(self.list_acc) ++ Seq(item)
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@950.11--950.59) [2773]"}
            HasDirectPerm(PostMask, self, list_acc);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@950.11--950.59) [2774]"}
            HasDirectPerm(old(Mask), self, list_acc);
        assume Seq#Equal(PostHeap[self, list_acc], Seq#Append(old(Heap)[self, list_acc], Seq#Singleton(item)));
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume self != null;
      PostMask[self, list_acc] := PostMask[self, list_acc] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of self.list_acc == old(self.list_acc) ++ Seq(item)
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@950.11--950.59) [2775]"}
          HasDirectPerm(PostMask, self, list_acc);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@950.11--950.59) [2776]"}
          HasDirectPerm(old(Mask), self, list_acc);
      assume Seq#Equal(PostHeap[self, list_acc], Seq#Append(old(Heap)[self, list_acc], Seq#Singleton(item)));
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale false -- testsfunctionalverificationexamplescav_example.py.vpr@953.3--953.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list_append might not hold. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@949.11--949.36) [2777]"}
        perm <= Mask[self, list_acc];
    }
    Mask[self, list_acc] := Mask[self, list_acc] - perm;
    assert {:msg "  Postcondition of list_append might not hold. Assertion self.list_acc == old(self.list_acc) ++ Seq(item) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@950.11--950.59) [2778]"}
      Seq#Equal(Heap[self, list_acc], Seq#Append(old(Heap)[self, list_acc], Seq#Singleton(item)));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method list___iter__
// ==================================================

procedure list___iter__(_cthread_13: Ref, _caller_measures_13: (Seq Measure$DomainType), _residue_13: Perm, self: Ref) returns (_current_wait_level_13: Perm, _res: Ref)
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var _r_23_2: Ref;
  var _r_23_3: Ref;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[_cthread_13, $allocated];
    assume Heap[self, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Do welldefinedness check of the exhale part.
      if (*) {
        assume _cthread_13 != null;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_13, _cthread_13, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_13, _cthread_13, 1);
        assume state(Heap, Mask);
        assume (issubtype((typeof(_cthread_13): PyTypeDomainType), Thread_0): bool);
        assume state(Heap, Mask);
        assume (issubtype((typeof(self): PyTypeDomainType), (list((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
        assume state(Heap, Mask);
        perm := 1 / 10;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 10 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@961.12--961.38) [2779]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        Mask[self, list_acc] := Mask[self, list_acc] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        
        // -- Check definedness of Measure$check(_caller_measures_13, _cthread_13, 1)
          if (*) {
            // Stop execution
            assume false;
          }
        assume Measure$check(Heap, _caller_measures_13, _cthread_13, 1);
        assume state(Heap, Mask);
        assume false;
      }
    
    // -- Normally inhale the inhale part.
      assume _cthread_13 != null;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
      
      // -- Check definedness of Measure$check(_caller_measures_13, _cthread_13, 1)
        if (*) {
          // Stop execution
          assume false;
        }
      assume Measure$check(Heap, _caller_measures_13, _cthread_13, 1);
      assume state(Heap, Mask);
      assume (issubtype((typeof(_cthread_13): PyTypeDomainType), Thread_0): bool);
      assume state(Heap, Mask);
      assume (issubtype((typeof(self): PyTypeDomainType), (list((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
      assume state(Heap, Mask);
      perm := 1 / 10;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 10 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@961.12--961.38) [2780]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      Mask[self, list_acc] := Mask[self, list_acc] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
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
    
    // -- Do welldefinedness check of the inhale part.
      if (*) {
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_23: Ref [_r_23.MustReleaseBounded] :: Level(_r_23) <= _current_wait_level_13)
          if (*) {
            if (HasDirectPerm(PostMask, _r_23_2, MustReleaseBounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_23.MustReleaseBounded (testsfunctionalverificationexamplescav_example.py.vpr@963.11--963.246) [2781]"}
                HasDirectPerm(PostMask, _r_23_2, MustReleaseBounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_23_1: Ref ::
          { PostMask[_r_23_1, MustReleaseBounded] }
          HasDirectPerm(PostMask, _r_23_1, MustReleaseBounded) ==> Level(PostHeap, _r_23_1) <= _current_wait_level_13
        );
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of (forperm _r_23: Ref [_r_23.MustReleaseUnbounded] :: Level(_r_23) <= _current_wait_level_13)
          if (*) {
            if (HasDirectPerm(PostMask, _r_23_3, MustReleaseUnbounded)) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _r_23.MustReleaseUnbounded (testsfunctionalverificationexamplescav_example.py.vpr@963.11--963.246) [2782]"}
                HasDirectPerm(PostMask, _r_23_3, MustReleaseUnbounded);
              if (*) {
                // Stop execution
                assume false;
              }
            }
            assume false;
          }
        assume (forall _r_23_3_1: Ref ::
          { PostMask[_r_23_3_1, MustReleaseUnbounded] }
          HasDirectPerm(PostMask, _r_23_3_1, MustReleaseUnbounded) ==> Level(PostHeap, _r_23_3_1) <= _current_wait_level_13
        );
        assume _residue_13 <= _current_wait_level_13;
        assume state(PostHeap, PostMask);
        assume _res != self;
        assume state(PostHeap, PostMask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@965.11--965.37) [2783]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> _res != null;
        PostMask[_res, list_acc] := PostMask[_res, list_acc] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        perm := 1 / 20;
        assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@966.11--966.37) [2784]"}
          perm >= NoPerm;
        assume perm > NoPerm ==> self != null;
        PostMask[self, list_acc] := PostMask[self, list_acc] + perm;
        assume state(PostHeap, PostMask);
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of _res.list_acc == self.list_acc
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@967.11--967.41) [2785]"}
            HasDirectPerm(PostMask, _res, list_acc);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@967.11--967.41) [2786]"}
            HasDirectPerm(PostMask, self, list_acc);
        assume Seq#Equal(PostHeap[_res, list_acc], PostHeap[self, list_acc]);
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume _res != null;
        PostMask[_res, __container] := PostMask[_res, __container] + perm;
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of _res.__container == self
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.__container (testsfunctionalverificationexamplescav_example.py.vpr@968.11--968.67) [2787]"}
            HasDirectPerm(PostMask, _res, __container);
        assume PostHeap[_res, __container] == self;
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume _res != null;
        PostMask[_res, __iter_index] := PostMask[_res, __iter_index] + perm;
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of _res.__iter_index == 0
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@969.11--969.66) [2788]"}
            HasDirectPerm(PostMask, _res, __iter_index);
        assume PostHeap[_res, __iter_index] == 0;
        assume state(PostHeap, PostMask);
        perm := FullPerm;
        assume _res != null;
        PostMask[_res, __previous] := PostMask[_res, __previous] + perm;
        assume state(PostHeap, PostMask);
        
        // -- Check definedness of _res.__previous == Seq[Ref]()
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.__previous (testsfunctionalverificationexamplescav_example.py.vpr@970.11--970.71) [2789]"}
            HasDirectPerm(PostMask, _res, __previous);
        assume Seq#Equal(PostHeap[_res, __previous], (Seq#Empty(): Seq Ref));
        assume state(PostHeap, PostMask);
        assume (issubtype((typeof(_res): PyTypeDomainType), (Iterator((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
        assume state(PostHeap, PostMask);
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      assume state(PostHeap, PostMask);
      assume _res != self;
      assume state(PostHeap, PostMask);
      perm := 1 / 20;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@965.11--965.37) [2790]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> _res != null;
      PostMask[_res, list_acc] := PostMask[_res, list_acc] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      perm := 1 / 20;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@966.11--966.37) [2791]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> self != null;
      PostMask[self, list_acc] := PostMask[self, list_acc] + perm;
      assume state(PostHeap, PostMask);
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of _res.list_acc == self.list_acc
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@967.11--967.41) [2792]"}
          HasDirectPerm(PostMask, _res, list_acc);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@967.11--967.41) [2793]"}
          HasDirectPerm(PostMask, self, list_acc);
      assume Seq#Equal(PostHeap[_res, list_acc], PostHeap[self, list_acc]);
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume _res != null;
      PostMask[_res, __container] := PostMask[_res, __container] + perm;
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of _res.__container == self
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.__container (testsfunctionalverificationexamplescav_example.py.vpr@968.11--968.67) [2794]"}
          HasDirectPerm(PostMask, _res, __container);
      assume PostHeap[_res, __container] == self;
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume _res != null;
      PostMask[_res, __iter_index] := PostMask[_res, __iter_index] + perm;
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of _res.__iter_index == 0
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@969.11--969.66) [2795]"}
          HasDirectPerm(PostMask, _res, __iter_index);
      assume PostHeap[_res, __iter_index] == 0;
      assume state(PostHeap, PostMask);
      perm := FullPerm;
      assume _res != null;
      PostMask[_res, __previous] := PostMask[_res, __previous] + perm;
      assume state(PostHeap, PostMask);
      
      // -- Check definedness of _res.__previous == Seq[Ref]()
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access _res.__previous (testsfunctionalverificationexamplescav_example.py.vpr@970.11--970.71) [2796]"}
          HasDirectPerm(PostMask, _res, __previous);
      assume Seq#Equal(PostHeap[_res, __previous], (Seq#Empty(): Seq Ref));
      assume state(PostHeap, PostMask);
      assume (issubtype((typeof(_res): PyTypeDomainType), (Iterator((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale false -- testsfunctionalverificationexamplescav_example.py.vpr@974.3--974.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of list___iter__ might not hold. Assertion _res != self might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@964.11--964.23) [2797]"}
      _res != self;
    assert {:msg "  Postcondition of list___iter__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@965.11--965.37) [2798]"}
      1 / 20 >= NoPerm;
    perm := 1 / 20;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list___iter__ might not hold. There might be insufficient permission to access _res.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@965.11--965.37) [2799]"}
        perm <= Mask[_res, list_acc];
    }
    Mask[_res, list_acc] := Mask[_res, list_acc] - perm;
    assert {:msg "  Postcondition of list___iter__ might not hold. Fraction 1 / 20 might be negative. (testsfunctionalverificationexamplescav_example.py.vpr@966.11--966.37) [2800]"}
      1 / 20 >= NoPerm;
    perm := 1 / 20;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list___iter__ might not hold. There might be insufficient permission to access self.list_acc (testsfunctionalverificationexamplescav_example.py.vpr@966.11--966.37) [2801]"}
        perm <= Mask[self, list_acc];
    }
    Mask[self, list_acc] := Mask[self, list_acc] - perm;
    assert {:msg "  Postcondition of list___iter__ might not hold. Assertion _res.list_acc == self.list_acc might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@967.11--967.41) [2802]"}
      Seq#Equal(Heap[_res, list_acc], Heap[self, list_acc]);
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list___iter__ might not hold. There might be insufficient permission to access _res.__container (testsfunctionalverificationexamplescav_example.py.vpr@968.11--968.67) [2803]"}
        perm <= Mask[_res, __container];
    }
    Mask[_res, __container] := Mask[_res, __container] - perm;
    assert {:msg "  Postcondition of list___iter__ might not hold. Assertion _res.__container == self might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@968.11--968.67) [2804]"}
      Heap[_res, __container] == self;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list___iter__ might not hold. There might be insufficient permission to access _res.__iter_index (testsfunctionalverificationexamplescav_example.py.vpr@969.11--969.66) [2805]"}
        perm <= Mask[_res, __iter_index];
    }
    Mask[_res, __iter_index] := Mask[_res, __iter_index] - perm;
    assert {:msg "  Postcondition of list___iter__ might not hold. Assertion _res.__iter_index == 0 might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@969.11--969.66) [2806]"}
      Heap[_res, __iter_index] == 0;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of list___iter__ might not hold. There might be insufficient permission to access _res.__previous (testsfunctionalverificationexamplescav_example.py.vpr@970.11--970.71) [2807]"}
        perm <= Mask[_res, __previous];
    }
    Mask[_res, __previous] := Mask[_res, __previous] - perm;
    assert {:msg "  Postcondition of list___iter__ might not hold. Assertion _res.__previous == Seq[Ref]() might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@970.11--970.71) [2808]"}
      Seq#Equal(Heap[_res, __previous], (Seq#Empty(): Seq Ref));
    assert {:msg "  Postcondition of list___iter__ might not hold. Assertion issubtype(typeof(_res), Iterator(list_arg(typeof(self), 0))) might not hold. (testsfunctionalverificationexamplescav_example.py.vpr@971.11--971.71) [2809]"}
      (issubtype((typeof(_res): PyTypeDomainType), (Iterator((list_arg((typeof(self): PyTypeDomainType), 0): PyTypeDomainType)): PyTypeDomainType)): bool);
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}