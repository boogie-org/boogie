// RUN: %parallel-boogie /monomorphize /noVerify "%s" > "%t"

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

function  neverTriggered2(q$a_7: int, q$v_1: int): bool;
function  neverTriggered4(q$a_16: int, q$v_4: int): bool;
function  neverTriggered6(q$a_25: int, q$v_7: int): bool;
function  neverTriggered8(q$a_36: int, q$v_9: int): bool;
function  neverTriggered10(q$a_7: int, q$v_1: int): bool;
function  neverTriggered12(q$a_18: int, q$v_3: int): bool;
function  neverTriggered14(q$a_7: int, q$v_1: int): bool;
function  neverTriggered16(q$a_7: int, q$v_1: int): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function  invRecv1($tag: int, $to: int, $amount: int): int;
function  invRecv2($tag: int, $to: int, $amount: int): int;
function  invRecv3($tag_1: int, $to_1: int, $amount_1: int): int;
function  invRecv4($tag_1: int, $to_1: int, $amount_1: int): int;
function  invRecv5($tag_2: int, $to_2: int, $amount_2: int): int;
function  invRecv6($tag_2: int, $to_2: int, $amount_2: int): int;
function  invRecv7($tag_3: int, $to_3: int, $amount_3: int): int;
function  invRecv8($tag_3: int, $to_3: int, $amount_3: int): int;
function  invRecv9($tag: int, $to: int, $amount: int): int;
function  invRecv10($tag: int, $to: int, $amount: int): int;
function  invRecv11($tag_1: int, $to_1: int, $amount_1: int): int;
function  invRecv12($tag_1: int, $to_1: int, $amount_1: int): int;
function  invRecv13($tag: int, $to: int, $amount: int): int;
function  invRecv14($tag: int, $to: int, $amount: int): int;
function  invRecv15($tag: int, $to: int, $amount: int): int;
function  invRecv16($tag: int, $to: int, $amount: int): int;
// ==================================================
// Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale
// ==================================================

function  qpRange2($tag: int, $to: int, $amount: int): bool;
function  qpRange4($tag_1: int, $to_1: int, $amount_1: int): bool;
function  qpRange6($tag_2: int, $to_2: int, $amount_2: int): bool;
function  qpRange8($tag_3: int, $to_3: int, $amount_3: int): bool;
function  qpRange10($tag: int, $to: int, $amount: int): bool;
function  qpRange12($tag_1: int, $to_1: int, $amount_1: int): bool;
function  qpRange14($tag: int, $to: int, $amount: int): bool;
function  qpRange16($tag: int, $to: int, $amount: int): bool;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 2: $pure$success_get
// - height 1: $pure$return_get
// - height 0: $range_sum
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
// Translation of domain $Math
// ==================================================

// The type for domain $Math
type $MathDomainType;

// Translation of domain function $sign
function  $sign($a: int): int;

// Translation of domain function $div
function  $div($a: int, $b: int, $r: int): int;

// Translation of domain function $mod
function  $mod($a: int, $b: int, $r: int): int;

// Translation of domain function $pow
function  $pow($a: int, $b: int): int;

// Translation of domain function $sqrt
function  $sqrt($a: int): int;

// Translation of domain function $floor
function  $floor($a: int, $s: int): int;

// Translation of domain function $ceil
function  $ceil($a: int, $s: int): int;

// Translation of domain function $shift
function  $shift($a: int, $s: int): int;

// Translation of domain function $bitwise_not
function  $bitwise_not($a: int): int;

// Translation of domain function $bitwise_and
function  $bitwise_and($a: int, $b: int): int;

// Translation of domain function $bitwise_or
function  $bitwise_or($a: int, $b: int): int;

// Translation of domain function $bitwise_xor
function  $bitwise_xor($a: int, $b: int): int;

// Translation of domain axiom $sign_ax
axiom ($sign(0): int) == 0 && (forall $a_1: int ::
  { ($sign($a_1): int) }
  ($a_1 > 0 ==> ($sign($a_1): int) == 1) && ($a_1 < 0 ==> ($sign($a_1): int) == -1)
);

// Translation of domain axiom $div_ax
axiom (forall $a_1: int, $b_1: int, $r_1: int ::
  { ($div($a_1, $b_1, $r_1): int) }
  ($div($a_1, $b_1, $r_1): int) == $a_1 div $b_1 + (if $a_1 >= 0 || $a_1 mod $b_1 == 0 then 0 else ($sign($b_1): int))
);

// Translation of domain axiom $mod_ax
axiom (forall $a_1: int, $b_1: int, $r_1: int ::
  { ($mod($a_1, $b_1, $r_1): int) }
  ($mod($a_1, $b_1, $r_1): int) == $a_1 - ($div($a_1, $b_1, $r_1): int) * $b_1
);

// Translation of domain axiom $pow0N_ax
axiom (forall $a_1: int ::
  { ($pow(0, $a_1): int) }
  $a_1 != 0 ==> ($pow(0, $a_1): int) == 0
);

// Translation of domain axiom $powN0_ax
axiom (forall $a_1: int ::
  { ($pow($a_1, 0): int) }
  $a_1 != 0 ==> ($pow($a_1, 0): int) == 1
);

// Translation of domain axiom $pow_non_negative_ax
axiom (forall $a_1: int, $b_1: int ::
  { ($pow($a_1, $b_1): int) }
  $a_1 >= 0 ==> ($pow($a_1, $b_1): int) >= 0
);

// Translation of domain axiom $pow_non_negative_and_non_null_ax
axiom (forall $a_1: int, $b_1: int ::
  { ($pow($a_1, $b_1): int) }
  $a_1 > 0 && $b_1 >= 0 ==> ($pow($a_1, $b_1): int) > 0
);

// Translation of domain axiom $floor_ax
axiom (forall $a_1: int, $s_1: int ::
  { ($floor($a_1, $s_1): int) }
  $s_1 > 0 ==> ($floor($a_1, $s_1): int) == ($div((if $a_1 < 0 then $a_1 - ($s_1 - 1) else $a_1), $s_1, 0): int)
);

// Translation of domain axiom $ceil_ax
axiom (forall $a_1: int, $s_1: int ::
  { ($ceil($a_1, $s_1): int) }
  $s_1 > 0 ==> ($ceil($a_1, $s_1): int) == ($div((if $a_1 < 0 then $a_1 else $a_1 + $s_1 - 1), $s_1, 0): int)
);

// Translation of domain axiom $shift_ax
axiom (forall $a_1: int, $s_1: int ::
  { ($shift($a_1, $s_1): int) }
  ($shift($a_1, $s_1): int) >= 0
);

// Translation of domain axiom $bitwise_not_ax
axiom (forall $a_1: int ::
  { ($bitwise_not($a_1): int) }
  ($bitwise_not($a_1): int) >= 0
);

// Translation of domain axiom $bitwise_and_ax
axiom (forall $a_1: int, $b_1: int ::
  { ($bitwise_and($a_1, $b_1): int) }
  ($bitwise_and($a_1, $b_1): int) >= 0
);

// Translation of domain axiom $bitwise_or_ax
axiom (forall $a_1: int, $b_1: int ::
  { ($bitwise_or($a_1, $b_1): int) }
  ($bitwise_or($a_1, $b_1): int) >= 0
);

// Translation of domain axiom $bitwise_xor_ax
axiom (forall $a_1: int, $b_1: int ::
  { ($bitwise_xor($a_1, $b_1): int) }
  ($bitwise_xor($a_1, $b_1): int) >= 0
);

// ==================================================
// Translation of domain $Int
// ==================================================

// The type for domain $Int
type $IntDomainType;

// Translation of domain function $wrap
function  $wrap(x: int): $IntDomainType;

// Translation of domain function $unwrap
function  $unwrap(x: $IntDomainType): int;

// Translation of domain function $w_mul
function  $w_mul(x: $IntDomainType, y: $IntDomainType): $IntDomainType;

// Translation of domain function $w_mulI
function  $w_mulI(x: $IntDomainType, y: $IntDomainType): $IntDomainType;

// Translation of domain function $w_mulL
function  $w_mulL(x: $IntDomainType, y: $IntDomainType): $IntDomainType;

// Translation of domain function $w_abs
function  $w_abs(x: $IntDomainType): int;

// Translation of domain function $w_mod
function  $w_mod($a: $IntDomainType, $b: $IntDomainType): $IntDomainType;

// Translation of domain function $w_modL
function  $w_modL($a: $IntDomainType, $b: $IntDomainType): $IntDomainType;

// Translation of domain function $w_div
function  $w_div($a: $IntDomainType, $b: $IntDomainType): $IntDomainType;

// Translation of domain function $w_div_down
function  $w_div_down($a: $IntDomainType, $b: $IntDomainType): $IntDomainType;

// Translation of domain function $w_div_nat
function  $w_div_nat($a: $IntDomainType, $b: $IntDomainType): $IntDomainType;

// Translation of domain function $w_div_natL
function  $w_div_natL($a: $IntDomainType, $b: $IntDomainType): $IntDomainType;

// Translation of domain axiom $wrap_ax
axiom (forall i: int ::
  { ($wrap(i): $IntDomainType) }
  ($unwrap(($wrap(i): $IntDomainType)): int) == i
);

// Translation of domain axiom $unwrap_ax
axiom (forall i: $IntDomainType ::
  { ($wrap(($unwrap(i): int)): $IntDomainType) }
  ($wrap(($unwrap(i): int)): $IntDomainType) == i
);

// Translation of domain axiom $w_abs_ax_1
axiom (forall i: $IntDomainType ::
  { ($w_abs(i): int) }
  ($unwrap(i): int) < 0 ==> ($w_abs(i): int) == -($unwrap(i): int)
);

// Translation of domain axiom $w_abs_ax_2
axiom (forall i: $IntDomainType ::
  { ($w_abs(i): int) }
  ($unwrap(i): int) >= 0 ==> ($w_abs(i): int) == ($unwrap(i): int)
);

// Translation of domain axiom $w_mul_intermediate
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mul(i, j): $IntDomainType) }
  ($w_mul(i, j): $IntDomainType) == ($w_mulI(i, j): $IntDomainType)
);

// Translation of domain axiom $w_mul_limited
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mul(i, j): $IntDomainType) }
  ($w_mul(i, j): $IntDomainType) == ($w_mulL(i, j): $IntDomainType)
);

// Translation of domain axiom $w_mul_intermediate_to_limited
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  ($w_mulI(i, j): $IntDomainType) == ($w_mulL(i, j): $IntDomainType)
);

// Translation of domain axiom $w_mul_commutative
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mul(i, j): $IntDomainType) }
  ($w_mul(i, j): $IntDomainType) == ($w_mulI(j, i): $IntDomainType)
);

// Translation of domain axiom $w_mul_associative
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType ::
  { ($w_mulI(i, ($w_mulI(j, k): $IntDomainType)): $IntDomainType) }
  ($w_mulI(i, ($w_mulI(j, k): $IntDomainType)): $IntDomainType) == ($w_mulL(($w_mulL(i, j): $IntDomainType), k): $IntDomainType)
);

// Translation of domain axiom $w_mul_distributive
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType), ($w_mulI(i, k): $IntDomainType), ($w_mulI(i, l): $IntDomainType) }
  ($unwrap(j): int) == ($unwrap(k): int) + ($unwrap(l): int) ==> ($w_mulI(i, j): $IntDomainType) == ($wrap(($unwrap(($w_mulL(i, k): $IntDomainType)): int) + ($unwrap(($w_mulL(i, l): $IntDomainType)): int)): $IntDomainType)
);

// Translation of domain axiom $w_mul_basic_sign_1
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  ($w_mulI(i, j): $IntDomainType) == ($w_mulL(($wrap(-($unwrap(i): int)): $IntDomainType), ($wrap(-($unwrap(j): int)): $IntDomainType)): $IntDomainType)
);

// Translation of domain axiom $w_mul_basic_sign_2
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  ($w_mulI(i, j): $IntDomainType) == ($wrap(-($unwrap(($w_mulL(($wrap(-($unwrap(i): int)): $IntDomainType), j): $IntDomainType)): int)): $IntDomainType)
);

// Translation of domain axiom $w_mul_basic_zero_1
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  ($unwrap(i): int) == 0 || ($unwrap(j): int) == 0 ==> ($unwrap(($w_mulI(i, j): $IntDomainType)): int) == 0
);

// Translation of domain axiom $w_mul_basic_zero_2
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  (($unwrap(i): int) > 0 && ($unwrap(j): int) > 0) || (($unwrap(i): int) < 0 && ($unwrap(j): int) < 0) ==> ($unwrap(($w_mulI(i, j): $IntDomainType)): int) > 0
);

// Translation of domain axiom $w_mul_basic_neutral
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  ($unwrap(i): int) == 1 || ($unwrap(j): int) == 0 ==> ($w_mulI(i, j): $IntDomainType) == j
);

// Translation of domain axiom $w_mul_basic_proportional
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mulI(i, j): $IntDomainType) }
  (($w_abs(($w_mulI(i, j): $IntDomainType)): int) >= ($w_abs(j): int)) == (($w_abs(i): int) >= 1 || ($unwrap(j): int) == 0)
);

// Translation of domain axiom $w_mul_order_1
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, ($w_mulI(j, l): $IntDomainType)): $IntDomainType), ($w_mulI(k, l): $IntDomainType) }
  ($unwrap(($w_mulI(i, j): $IntDomainType)): int) > ($unwrap(k): int) && ($unwrap(l): int) > 0 ==> ($unwrap(($w_mulL(i, ($w_mulL(j, l): $IntDomainType)): $IntDomainType)): int) > ($unwrap(($w_mulI(k, l): $IntDomainType)): int)
);

// Translation of domain axiom $w_mul_order_2
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, ($w_mulI(j, l): $IntDomainType)): $IntDomainType), ($w_mulI(k, l): $IntDomainType) }
  ($unwrap(($w_mulI(i, j): $IntDomainType)): int) >= ($unwrap(k): int) && ($unwrap(l): int) > 0 ==> ($unwrap(($w_mulL(i, ($w_mulL(j, l): $IntDomainType)): $IntDomainType)): int) >= ($unwrap(($w_mulI(k, l): $IntDomainType)): int)
);

// Translation of domain axiom $w_mul_order_3
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, ($w_mulI(j, l): $IntDomainType)): $IntDomainType), ($w_mulI(k, l): $IntDomainType) }
  ($unwrap(($w_mulI(i, j): $IntDomainType)): int) > ($unwrap(k): int) && ($unwrap(l): int) < 0 ==> ($unwrap(($w_mulI(k, l): $IntDomainType)): int) > ($unwrap(($w_mulL(i, ($w_mulL(j, l): $IntDomainType)): $IntDomainType)): int)
);

// Translation of domain axiom $w_mul_order_4
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, ($w_mulI(j, l): $IntDomainType)): $IntDomainType), ($w_mulI(k, l): $IntDomainType) }
  ($unwrap(($w_mulI(i, j): $IntDomainType)): int) >= ($unwrap(k): int) && ($unwrap(l): int) < 0 ==> ($unwrap(($w_mulI(k, l): $IntDomainType)): int) >= ($unwrap(($w_mulL(i, ($w_mulL(j, l): $IntDomainType)): $IntDomainType)): int)
);

// Translation of domain axiom $w_mul_monotonicity_1
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, k): $IntDomainType), ($w_mulI(j, l): $IntDomainType) }
  ($w_abs(i): int) <= ($w_abs(j): int) && ($w_abs(k): int) <= ($w_abs(l): int) ==> ($w_abs(($w_mulI(i, k): $IntDomainType)): int) <= ($w_abs(($w_mulI(j, l): $IntDomainType)): int)
);

// Translation of domain axiom $w_mul_monotonicity_2
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, k): $IntDomainType), ($w_mulI(j, l): $IntDomainType) }
  ($w_abs(i): int) < ($w_abs(j): int) && (($w_abs(k): int) <= ($w_abs(l): int) && ($unwrap(l): int) != 0) ==> ($w_abs(($w_mulI(i, k): $IntDomainType)): int) < ($w_abs(($w_mulI(j, l): $IntDomainType)): int)
);

// Translation of domain axiom $w_mul_monotonicity_3
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mulI(i, k): $IntDomainType), ($w_mulI(j, l): $IntDomainType) }
  ($w_abs(i): int) <= ($w_abs(j): int) && (($w_abs(k): int) < ($w_abs(l): int) && ($unwrap(j): int) != 0) ==> ($w_abs(($w_mulI(i, k): $IntDomainType)): int) < ($w_abs(($w_mulI(j, l): $IntDomainType)): int)
);

// Translation of domain axiom $w_mod_limited
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  ($w_mod(i, j): $IntDomainType) == ($w_modL(i, j): $IntDomainType)
);

// Translation of domain axiom $w_mod_identity
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> i == j || i == ($wrap(0): $IntDomainType) ==> ($w_mod(i, j): $IntDomainType) == ($wrap(0): $IntDomainType)
);

// Translation of domain axiom $w_mod_basic_1
axiom (forall i: $IntDomainType, j: $IntDomainType, l: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType), ($w_mod(l, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($unwrap(i): int) == ($unwrap(l): int) + ($w_abs(j): int) && (($unwrap(l): int) >= 0 || ($unwrap(i): int) < 0) ==> ($w_mod(i, j): $IntDomainType) == ($w_modL(l, j): $IntDomainType)
);

// Translation of domain axiom $w_mod_basic_2
axiom (forall i: $IntDomainType, j: $IntDomainType, l: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType), ($w_mod(l, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($unwrap(i): int) == ($unwrap(l): int) - ($w_abs(j): int) && (($unwrap(l): int) <= 0 || ($unwrap(i): int) > 0) ==> ($w_mod(i, j): $IntDomainType) == ($w_modL(l, j): $IntDomainType)
);

// Translation of domain axiom $w_mod_basic_3
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> 0 <= ($w_abs(i): int) && ($w_abs(i): int) < ($w_abs(j): int) ==> ($w_mod(i, j): $IntDomainType) == i
);

// Translation of domain axiom $w_mod_basic_4
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_abs(($w_mod(i, j): $IntDomainType)): int) < ($w_abs(j): int)
);

// Translation of domain axiom $w_mod_sign_1
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($sign(($unwrap(($w_mod(i, j): $IntDomainType)): int)): int) == ($sign(($unwrap(i): int)): int) || ($sign(($unwrap(($w_mod(i, j): $IntDomainType)): int)): int) == 0
);

// Translation of domain axiom $w_mod_sign_2
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType), ($w_mod(k, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($unwrap(i): int) == -($unwrap(k): int) ==> ($w_mod(i, j): $IntDomainType) == ($wrap(-($unwrap(($w_modL(k, j): $IntDomainType)): int)): $IntDomainType)
);

// Translation of domain axiom $w_mod_sign_3
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_mod(i, j): $IntDomainType) == ($w_mod(i, ($wrap(-($unwrap(j): int)): $IntDomainType)): $IntDomainType)
);

// Translation of domain axiom $w_mod_mod
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_mod(i, j): $IntDomainType) == ($w_modL(($w_modL(i, j): $IntDomainType), j): $IntDomainType)
);

// Translation of domain axiom $w_mod_decrease
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_abs(($w_mod(i, j): $IntDomainType)): int) <= ($w_abs(i): int)
);

// Translation of domain axiom $w_mod_add
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType), ($w_mod(k, j): $IntDomainType), ($w_mod(l, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($unwrap(i): int) == ($unwrap(k): int) + ($unwrap(l): int) ==> ((($unwrap(i): int) >= 0 && ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) >= 0) || (($unwrap(i): int) <= 0 && ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) <= 0) ==> (($w_abs(j): int) <= ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) && (($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) < 2 * ($w_abs(j): int) && ($w_mod(i, j): $IntDomainType) == ($wrap(($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) - ($w_abs(j): int)): $IntDomainType))) || ((-($w_abs(j): int) < ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) && (($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) < ($w_abs(j): int) && ($w_mod(i, j): $IntDomainType) == ($wrap(($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int)): $IntDomainType))) || (-2 * ($w_abs(j): int) < ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) && (($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) <= -($w_abs(j): int) && ($w_mod(i, j): $IntDomainType) == ($wrap(($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) + ($w_abs(j): int)): $IntDomainType))))) && ((($unwrap(i): int) > 0 && ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) < 0) || (($unwrap(i): int) < 0 && ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) > 0) ==> (0 < ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) && (($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) < ($w_abs(j): int) && ($w_mod(i, j): $IntDomainType) == ($wrap(($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) - ($w_abs(j): int)): $IntDomainType))) || (-($w_abs(j): int) < ($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) && (($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) < 0 && ($w_mod(i, j): $IntDomainType) == ($wrap(($unwrap(($w_modL(k, j): $IntDomainType)): int) + ($unwrap(($w_modL(l, j): $IntDomainType)): int) + ($w_abs(j): int)): $IntDomainType))))
);

// Translation of domain axiom $w_mod_mul_basic
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_mod(($w_mul(i, j): $IntDomainType), j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_mod(($w_mul(i, j): $IntDomainType), j): $IntDomainType) == ($wrap(0): $IntDomainType)
);

// Translation of domain axiom $w_mod_mul_mod_noop
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType ::
  { ($w_mod(($w_mulI(i, k): $IntDomainType), j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_mod(($w_mulI(i, k): $IntDomainType), j): $IntDomainType) == ($w_modL(($w_mulL(($w_modL(i, j): $IntDomainType), k): $IntDomainType), j): $IntDomainType) && (($w_mod(($w_mulI(i, k): $IntDomainType), j): $IntDomainType) == ($w_modL(($w_mulL(i, ($w_modL(k, j): $IntDomainType)): $IntDomainType), j): $IntDomainType) && ($w_mod(($w_mulI(i, k): $IntDomainType), j): $IntDomainType) == ($w_modL(($w_mulL(($w_modL(i, j): $IntDomainType), ($w_modL(k, j): $IntDomainType)): $IntDomainType), j): $IntDomainType))
);

// Translation of domain axiom $w_mod_mul_vanish
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType ::
  { ($w_mod(i, j): $IntDomainType), ($w_mulI(k, j): $IntDomainType) }
  j != ($wrap(0): $IntDomainType) ==> ($w_mod(i, j): $IntDomainType) == ($w_modL(($wrap(($unwrap(($w_mulL(k, j): $IntDomainType)): int) + ($unwrap(i): int)): $IntDomainType), j): $IntDomainType)
);

// Translation of domain axiom $w_div_div_down
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div(i, j): $IntDomainType) }
  ($unwrap(j): int) != 0 ==> ($w_div(i, j): $IntDomainType) == (if ($unwrap(i): int) >= 0 then ($w_div_down(i, j): $IntDomainType) else ($wrap(-($unwrap(($w_div_down(($wrap(-($unwrap(i): int)): $IntDomainType), j): $IntDomainType)): int)): $IntDomainType))
);

// Translation of domain axiom $w_div_down_div_nat
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div_down(i, j): $IntDomainType) }
  ($w_div_down(i, j): $IntDomainType) == (if ($unwrap(j): int) >= 0 then ($w_div_nat(i, j): $IntDomainType) else ($wrap(-($unwrap(($w_div_nat(i, ($wrap(-($unwrap(j): int)): $IntDomainType)): $IntDomainType)): int)): $IntDomainType))
);

// Translation of domain axiom $w_div_nat_limited
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType) }
  ($w_div_nat(i, j): $IntDomainType) == ($w_div_natL(i, j): $IntDomainType)
);

// Translation of domain axiom $w_div_nat_neutral
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType) }
  ($unwrap(j): int) == 1 || ($unwrap(i): int) == 0 ==> ($w_div_nat(i, j): $IntDomainType) == i
);

// Translation of domain axiom $w_div_nat_self
axiom (forall i: $IntDomainType ::
  { ($w_div_nat(i, i): $IntDomainType) }
  ($unwrap(i): int) > 0 ==> ($w_div_nat(i, i): $IntDomainType) == ($wrap(1): $IntDomainType)
);

// Translation of domain axiom $w_div_nat_small
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType) }
  ($unwrap(i): int) >= 0 && ($unwrap(j): int) > 0 ==> (($unwrap(i): int) < ($unwrap(j): int)) == (($w_div_nat(i, j): $IntDomainType) == ($wrap(0): $IntDomainType))
);

// Translation of domain axiom $w_div_nat_dividend_add
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType, l: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType), ($w_div_nat(k, j): $IntDomainType), ($w_div_nat(l, j): $IntDomainType) }
  ($unwrap(i): int) >= 0 && (($unwrap(j): int) > 0 && (($unwrap(k): int) >= 0 && ($unwrap(l): int) >= 0)) ==> ($unwrap(i): int) == ($unwrap(k): int) + ($unwrap(l): int) ==> (0 <= ($unwrap(($w_mod(k, j): $IntDomainType)): int) + ($unwrap(($w_mod(l, j): $IntDomainType)): int) && (($unwrap(($w_mod(k, j): $IntDomainType)): int) + ($unwrap(($w_mod(l, j): $IntDomainType)): int) < ($unwrap(j): int) && ($w_div_nat(i, j): $IntDomainType) == ($wrap(($unwrap(($w_div_natL(k, j): $IntDomainType)): int) + ($unwrap(($w_div_natL(l, j): $IntDomainType)): int)): $IntDomainType))) || (($unwrap(j): int) <= ($unwrap(($w_mod(k, j): $IntDomainType)): int) + ($unwrap(($w_mod(l, j): $IntDomainType)): int) && (($unwrap(($w_mod(k, j): $IntDomainType)): int) + ($unwrap(($w_mod(l, j): $IntDomainType)): int) < 2 * ($unwrap(j): int) && ($w_div_nat(i, j): $IntDomainType) == ($wrap(($unwrap(($w_div_natL(k, j): $IntDomainType)): int) + ($unwrap(($w_div_natL(l, j): $IntDomainType)): int) + 1): $IntDomainType)))
);

// Translation of domain axiom $w_div_nat_ordered_by_dividend
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType), ($w_div_nat(k, j): $IntDomainType) }
  ($unwrap(i): int) >= 0 && (($unwrap(j): int) > 0 && ($unwrap(k): int) >= 0) ==> ($unwrap(i): int) <= ($unwrap(k): int) ==> ($unwrap(($w_div_nat(i, j): $IntDomainType)): int) <= ($unwrap(($w_div_natL(k, j): $IntDomainType)): int)
);

// Translation of domain axiom $w_div_nat_ordered_by_divisor
axiom (forall i: $IntDomainType, j: $IntDomainType, k: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType), ($w_div_nat(i, k): $IntDomainType) }
  ($unwrap(i): int) >= 0 && (($unwrap(j): int) > 0 && ($unwrap(k): int) > 0) ==> ($unwrap(j): int) <= ($unwrap(k): int) ==> ($unwrap(($w_div_nat(i, j): $IntDomainType)): int) >= ($unwrap(($w_div_natL(i, k): $IntDomainType)): int)
);

// Translation of domain axiom $w_div_nat_decrease
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType) }
  ($unwrap(i): int) > 0 && ($unwrap(j): int) > 1 ==> ($unwrap(($w_div_nat(i, j): $IntDomainType)): int) < ($unwrap(i): int)
);

// Translation of domain axiom $w_div_nat_nonincrease
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div_nat(i, j): $IntDomainType) }
  ($unwrap(i): int) >= 0 && ($unwrap(j): int) > 0 ==> ($unwrap(($w_div_nat(i, j): $IntDomainType)): int) <= ($unwrap(i): int)
);

// Translation of domain axiom $w_div_mul
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div(($w_mulI(i, j): $IntDomainType), j): $IntDomainType) }
  ($unwrap(j): int) != 0 ==> ($w_div(($w_mulI(i, j): $IntDomainType), j): $IntDomainType) == i
);

// Translation of domain axiom $w_div_sign
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div(i, j): $IntDomainType) }
  ($unwrap(j): int) != 0 ==> ($sign(($unwrap(($w_div(i, j): $IntDomainType)): int)): int) == ($sign(($unwrap(i): int)): int) * ($sign(($unwrap(j): int)): int) || ($sign(($unwrap(($w_div(i, j): $IntDomainType)): int)): int) == 0
);

// Translation of domain axiom $w_div_mod_mul
axiom (forall i: $IntDomainType, j: $IntDomainType ::
  { ($w_div(i, j): $IntDomainType), ($w_mod(i, j): $IntDomainType) }
  ($unwrap(j): int) != 0 ==> ($unwrap(i): int) == ($unwrap(($w_mulI(j, ($w_div(i, j): $IntDomainType)): $IntDomainType)): int) + ($unwrap(($w_mod(i, j): $IntDomainType)): int)
);

// ==================================================
// Translation of domain $Array
// ==================================================

// The type for domain $Array
type $ArrayDomainType $E;

// Translation of domain function $array_init
function  $array_init<$E>($e: $E, $c: int): Seq $E;

// Translation of domain axiom $array_init_len_ax
axiom (forall <$E> $e_1: $E, $c_1: int ::
  { ($array_init($e_1, $c_1): Seq $E) }
  Seq#Length(($array_init($e_1, $c_1): Seq $E)) == $c_1
);

// Translation of domain axiom $array_init_val_ax
axiom (forall <$E> $e_1: $E, $c_1: int, $i: int ::
  { (Seq#Index(($array_init($e_1, $c_1): Seq $E), $i): $E) }
  0 <= $i && $i < $c_1 ==> (Seq#Index(($array_init($e_1, $c_1): Seq $E), $i): $E) == $e_1
);

// ==================================================
// Translation of domain $Map
// ==================================================

// The type for domain $Map
type $MapDomainType $K $V;

// Translation of domain function $map_init
function  $map_init<$V, $K>($v: $V): $MapDomainType $K $V;

// Translation of domain function $map_eq
function  $map_eq<$K, $V>($m: ($MapDomainType $K $V), $n: ($MapDomainType $K $V)): bool;

// Translation of domain function $map_get
function  $map_get<$K, $V>($m: ($MapDomainType $K $V), $k: $K): $V;

// Translation of domain function $map_set
function  $map_set<$K, $V>($m: ($MapDomainType $K $V), $k: $K, $v: $V): $MapDomainType $K $V;

// Translation of domain axiom $map_init_ax
axiom (forall <$V, $K> $v_1: $V, $k_1: $K ::
  { ($map_get(($map_init($v_1): $MapDomainType $K $V), $k_1): $V) }
  ($map_get(($map_init($v_1): $MapDomainType $K $V), $k_1): $V) == $v_1
);

// Translation of domain axiom $map_eq_ax
axiom (forall <$K, $V> $m_1: ($MapDomainType $K $V), $n_1: ($MapDomainType $K $V) ::
  { ($map_eq($m_1, $n_1): bool) }
  ($map_eq($m_1, $n_1): bool) == ($m_1 == $n_1) && ($map_eq($m_1, $n_1): bool) == (forall $k_1: $K ::
    { ($map_get($m_1, $k_1): $V), ($map_get($n_1, $k_1): $V) }
    ($map_get($m_1, $k_1): $V) == ($map_get($n_1, $k_1): $V)
  )
);

// Translation of domain axiom $map_set_ax
axiom (forall <$K, $V> $m_1: ($MapDomainType $K $V), $k_1: $K, $v_1: $V, $kk: $K ::
  { ($map_get(($map_set($m_1, $k_1, $v_1): $MapDomainType $K $V), $kk): $V) }
  ($map_get(($map_set($m_1, $k_1, $v_1): $MapDomainType $K $V), $kk): $V) == (if $k_1 == $kk then $v_1 else ($map_get($m_1, $kk): $V))
);

// ==================================================
// Translation of domain $MapInt
// ==================================================

// The type for domain $MapInt
type $MapIntDomainType $K;

// Translation of domain function $map_sum
function  $map_sum<$K>($m: ($MapDomainType $K int)): int;

// Translation of domain axiom $map_sum_init_ax
axiom ($map_sum(($map_init(0): $MapDomainType int int)): int) == 0;

// Translation of domain axiom $map_sum_set_ax
axiom (forall <$K> $m_1: ($MapDomainType $K int), $k_1: $K, $v_1: int ::
  { ($map_sum(($map_set($m_1, $k_1, $v_1): $MapDomainType $K int)): int) }
  ($map_sum(($map_set($m_1, $k_1, $v_1): $MapDomainType $K int)): int) == ($map_sum($m_1): int) - ($map_get($m_1, $k_1): int) + $v_1
);

// ==================================================
// Translation of domain $Struct
// ==================================================

// The type for domain $Struct
type $StructDomainType;

// Translation of domain function $struct_loc
function  $struct_loc($s: $StructDomainType, $m: int): int;

// ==================================================
// Translation of domain $StructOps
// ==================================================

// The type for domain $StructOps
type $StructOpsDomainType $T;

// Translation of domain function $struct_get
function  $struct_get<$T>($l: int): $T;

// Translation of domain function $struct_set
function  $struct_set<$T>($s: $StructDomainType, $m: int, $t: $T): $StructDomainType;

// Translation of domain axiom $get_set_0_ax
axiom (forall <$T> $s_1: $StructDomainType, $m_1: int, $t_1: $T ::
  { ($struct_loc(($struct_set($s_1, $m_1, $t_1): $StructDomainType), $m_1): int) }
  ($struct_get(($struct_loc(($struct_set($s_1, $m_1, $t_1): $StructDomainType), $m_1): int)): $T) == $t_1
);

// Translation of domain axiom $get_set_1_ax
axiom (forall <$T> $s_1: $StructDomainType, $m_1: int, $n_1: int, $t_1: $T ::
  { ($struct_loc(($struct_set($s_1, $n_1, $t_1): $StructDomainType), $m_1): int) }
  $m_1 != $n_1 ==> ($struct_loc($s_1, $m_1): int) == ($struct_loc(($struct_set($s_1, $n_1, $t_1): $StructDomainType), $m_1): int)
);

// ==================================================
// Translation of domain $Convert
// ==================================================

// The type for domain $Convert
type $ConvertDomainType;

// Translation of domain function $bytes32_to_signed_int
function  $bytes32_to_signed_int($bb: (Seq int)): int;

// Translation of domain function $bytes32_to_unsigned_int
function  $bytes32_to_unsigned_int($bb: (Seq int)): int;

// Translation of domain function $signed_int_to_bytes32
function  $signed_int_to_bytes32($i_1: int): Seq int;

// Translation of domain function $unsigned_int_to_bytes32
function  $unsigned_int_to_bytes32($i_1: int): Seq int;

// Translation of domain function $pad32
function  $pad32($bb: (Seq int)): Seq int;

// Translation of domain axiom $bytes32_to_signed_int_ax
axiom (forall $bb_1: (Seq int) ::
  { ($bytes32_to_signed_int($bb_1): int) }
  Seq#Length($bb_1) <= 32 ==> -57896044618658097711785492504343953926634992332820282019728792003956564819968 <= ($bytes32_to_signed_int($bb_1): int) && ($bytes32_to_signed_int($bb_1): int) <= 57896044618658097711785492504343953926634992332820282019728792003956564819967
);

// Translation of domain axiom $bytes32_to_unsigned_int_ax
axiom (forall $bb_1: (Seq int) ::
  { ($bytes32_to_unsigned_int($bb_1): int) }
  Seq#Length($bb_1) <= 32 ==> 0 <= ($bytes32_to_unsigned_int($bb_1): int) && ($bytes32_to_unsigned_int($bb_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
);

// Translation of domain axiom $signed_int_to_bytes32_ax
axiom (forall $i: int ::
  { ($signed_int_to_bytes32($i): Seq int) }
  -57896044618658097711785492504343953926634992332820282019728792003956564819968 <= $i && $i <= 57896044618658097711785492504343953926634992332820282019728792003956564819967 ==> Seq#Length(($signed_int_to_bytes32($i): Seq int)) == 32
);

// Translation of domain axiom $unsigned_int_to_bytes32_ax
axiom (forall $i: int ::
  { ($unsigned_int_to_bytes32($i): Seq int) }
  -57896044618658097711785492504343953926634992332820282019728792003956564819968 <= $i && $i <= 57896044618658097711785492504343953926634992332820282019728792003956564819967 ==> Seq#Length(($unsigned_int_to_bytes32($i): Seq int)) == 32
);

// Translation of domain axiom $pad32_len_ax
axiom (forall $bb_1: (Seq int) ::
  { ($pad32($bb_1): Seq int) }
  Seq#Length(($pad32($bb_1): Seq int)) == 32
);

// Translation of domain axiom $pad32_vals_ax
axiom (forall $bb_1: (Seq int), $i: int ::
  { Seq#Index(($pad32($bb_1): Seq int), $i) }
  0 <= $i && $i < Seq#Length(($pad32($bb_1): Seq int)) ==> Seq#Index(($pad32($bb_1): Seq int), $i) == (if $i < 32 - Seq#Length($bb_1) then 0 else Seq#Index($bb_1, $i - (32 - Seq#Length($bb_1))))
);

// ==================================================
// Translation of domain $Range
// ==================================================

// The type for domain $Range
type $RangeDomainType;

// Translation of domain function $range
function  $range($f: int, $t: int): Seq int;

// Translation of domain axiom $range_len_ax
axiom (forall $f_1: int, $t_1: int ::
  { Seq#Length(($range($f_1, $t_1): Seq int)) }
  Seq#Length(($range($f_1, $t_1): Seq int)) == $t_1 - $f_1
);

// Translation of domain axiom $range_lookup_ax
axiom (forall $f_1: int, $t_1: int, $i: int ::
  { Seq#Index(($range($f_1, $t_1): Seq int), $i) }
  0 <= $i && $i < Seq#Length(($range($f_1, $t_1): Seq int)) ==> Seq#Index(($range($f_1, $t_1): Seq int), $i) == $f_1 + $i
);

// ==================================================
// Translation of domain $Blockchain
// ==================================================

// The type for domain $Blockchain
type $BlockchainDomainType;

// Translation of domain function $blockhash
function  $blockhash($no: int): Seq int;

// Translation of domain function $method_id
function  $method_id($bb: (Seq int), $l: int): Seq int;

// Translation of domain function $keccak256
function  $keccak256($s: (Seq int)): Seq int;

// Translation of domain function $sha256
function  $sha256($s: (Seq int)): Seq int;

// Translation of domain function $ecrecover
function  $ecrecover($s: (Seq int), v_2: int, r_1: int, s: int): int;

// Translation of domain function $ecadd
function  $ecadd($p: (Seq int), $q: (Seq int)): Seq int;

// Translation of domain function $ecmul
function  $ecmul($p: (Seq int), $s: int): Seq int;

// Translation of domain axiom $blockhash_ax
axiom (forall $no_1: int ::
  { ($blockhash($no_1): Seq int) }
  Seq#Length(($blockhash($no_1): Seq int)) == 32
);

// Translation of domain axiom $method_id_ax
axiom (forall $bb_1: (Seq int), $l_1: int ::
  { ($method_id($bb_1, $l_1): Seq int) }
  Seq#Length(($method_id($bb_1, $l_1): Seq int)) == $l_1
);

// Translation of domain axiom $keccak256_ax
axiom (forall $s_1: (Seq int) ::
  { ($keccak256($s_1): Seq int) }
  Seq#Length(($keccak256($s_1): Seq int)) == 32
);

// Translation of domain axiom $sha256_ax
axiom (forall $s_1: (Seq int) ::
  { ($sha256($s_1): Seq int) }
  Seq#Length(($sha256($s_1): Seq int)) == 32
);

// Translation of domain axiom $ecadd_ax
axiom (forall $p_1: (Seq int), $q_1: (Seq int) ::
  { ($ecadd($p_1, $q_1): Seq int) }
  Seq#Length(($ecadd($p_1, $q_1): Seq int)) == 2
);

// Translation of domain axiom $ecmul_ax
axiom (forall $p_1: (Seq int), $s_1: int ::
  { ($ecmul($p_1, $s_1): Seq int) }
  Seq#Length(($ecmul($p_1, $s_1): Seq int)) == 2
);

// ==================================================
// Translation of domain $Contract
// ==================================================

// The type for domain $Contract
type $ContractDomainType;

// Translation of domain function $self_address
function  $self_address(): int;

// Translation of domain function $implements
function  $implements($a: int, $i_1: int): bool;

// Translation of domain axiom $self_address_ax
axiom ($self_address(): int) != 0;

// ==================================================
// Translation of domain s$struct$self
// ==================================================

// The type for domain s$struct$self
type s$struct$selfDomainType;

// Translation of domain function s$struct$self$init
function  s$struct$self$init($arg_0: int, $arg_1: int, $arg_2: int, $arg_3: int, $arg_4: int, $arg_5: bool, $arg_6: ($MapDomainType int int), $arg_7: int, $arg_8: int, $arg_9: bool, $arg_10: ($MapDomainType int int), $arg_11: ($MapDomainType int int), $arg_12: bool): $StructDomainType;

// Translation of domain function s$struct$self$eq
function  s$struct$self$eq($l: $StructDomainType, $r: $StructDomainType): bool;

// Translation of domain axiom s$struct$self$init$ax
axiom (forall $arg_0_1: int, $arg_1_1: int, $arg_2_1: int, $arg_3_1: int, $arg_4_1: int, $arg_5_1: bool, $arg_6_1: ($MapDomainType int int), $arg_7_1: int, $arg_8_1: int, $arg_9_1: bool, $arg_10_1: ($MapDomainType int int), $arg_11_1: ($MapDomainType int int), $arg_12_1: bool ::
  { (s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType) }
  ($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), -1): int)): int) == 9122519725869122497593506884710 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 0): int)): int) == $arg_0_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 1): int)): int) == $arg_1_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 2): int)): int) == $arg_2_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 3): int)): int) == $arg_3_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 4): int)): int) == $arg_4_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 5): int)): bool) == $arg_5_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 6): int)): $MapDomainType int int) == $arg_6_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 7): int)): int) == $arg_7_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 8): int)): int) == $arg_8_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 9): int)): bool) == $arg_9_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 10): int)): $MapDomainType int int) == $arg_10_1 && (($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 11): int)): $MapDomainType int int) == $arg_11_1 && ($struct_get(($struct_loc((s$struct$self$init($arg_0_1, $arg_1_1, $arg_2_1, $arg_3_1, $arg_4_1, $arg_5_1, $arg_6_1, $arg_7_1, $arg_8_1, $arg_9_1, $arg_10_1, $arg_11_1, $arg_12_1): $StructDomainType), 12): int)): bool) == $arg_12_1))))))))))))
);

// Translation of domain axiom s$struct$self$eq$ax
axiom (forall $l_1: $StructDomainType, $r_1: $StructDomainType ::
  { (s$struct$self$eq($l_1, $r_1): bool) }
  (s$struct$self$eq($l_1, $r_1): bool) == ($l_1 == $r_1) && (s$struct$self$eq($l_1, $r_1): bool) == (($struct_get(($struct_loc($l_1, -1): int)): int) == ($struct_get(($struct_loc($r_1, -1): int)): int) && (($struct_get(($struct_loc($l_1, 0): int)): int) == ($struct_get(($struct_loc($r_1, 0): int)): int) && (($struct_get(($struct_loc($l_1, 1): int)): int) == ($struct_get(($struct_loc($r_1, 1): int)): int) && (($struct_get(($struct_loc($l_1, 2): int)): int) == ($struct_get(($struct_loc($r_1, 2): int)): int) && (($struct_get(($struct_loc($l_1, 3): int)): int) == ($struct_get(($struct_loc($r_1, 3): int)): int) && (($struct_get(($struct_loc($l_1, 4): int)): int) == ($struct_get(($struct_loc($r_1, 4): int)): int) && (($struct_get(($struct_loc($l_1, 5): int)): bool) == ($struct_get(($struct_loc($r_1, 5): int)): bool) && (($map_eq(($struct_get(($struct_loc($l_1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($r_1, 6): int)): $MapDomainType int int)): bool) && (($struct_get(($struct_loc($l_1, 7): int)): int) == ($struct_get(($struct_loc($r_1, 7): int)): int) && (($struct_get(($struct_loc($l_1, 8): int)): int) == ($struct_get(($struct_loc($r_1, 8): int)): int) && (($struct_get(($struct_loc($l_1, 9): int)): bool) == ($struct_get(($struct_loc($r_1, 9): int)): bool) && (($map_eq(($struct_get(($struct_loc($l_1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($r_1, 10): int)): $MapDomainType int int)): bool) && (($map_eq(($struct_get(($struct_loc($l_1, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($r_1, 11): int)): $MapDomainType int int)): bool) && ($struct_get(($struct_loc($l_1, 12): int)): bool) == ($struct_get(($struct_loc($r_1, 12): int)): bool))))))))))))))
);

// ==================================================
// Translation of domain s$resource$$creator
// ==================================================

// The type for domain s$resource$$creator
type s$resource$$creatorDomainType;

// Translation of domain function s$resource$$creator$init
function  s$resource$$creator$init($arg_0: $StructDomainType): $StructDomainType;

// Translation of domain function s$resource$$creator$eq
function  s$resource$$creator$eq($l: $StructDomainType, $r: $StructDomainType): bool;

// Translation of domain axiom s$resource$$creator$init$ax
axiom (forall $arg_0_1: $StructDomainType ::
  { (s$resource$$creator$init($arg_0_1): $StructDomainType) }
  ($struct_get(($struct_loc((s$resource$$creator$init($arg_0_1): $StructDomainType), -1): int)): int) == 2567760667165796382711201132846784524754120562 && ($struct_get(($struct_loc((s$resource$$creator$init($arg_0_1): $StructDomainType), 0): int)): $StructDomainType) == $arg_0_1
);

// Translation of domain axiom s$resource$$creator$eq$ax
axiom (forall $l_1: $StructDomainType, $r_1: $StructDomainType ::
  { (s$resource$$creator$eq($l_1, $r_1): bool) }
  (s$resource$$creator$eq($l_1, $r_1): bool) == ($l_1 == $r_1) && (s$resource$$creator$eq($l_1, $r_1): bool) == (($struct_get(($struct_loc($l_1, -1): int)): int) == ($struct_get(($struct_loc($r_1, -1): int)): int) && ($struct_get(($struct_loc($l_1, 0): int)): $StructDomainType) == ($struct_get(($struct_loc($r_1, 0): int)): $StructDomainType))
);

// ==================================================
// Translation of domain $Implements
// ==================================================

// The type for domain $Implements
type $ImplementsDomainType;

// Translation of domain axiom $Implements$ax
axiom true;

// ==================================================
// Translation of function $range_sum
// ==================================================

// Uninterpreted function definitions
function  $range_sum(Heap: HeapType, $x: int, $y: int): int;
function  $range_sum'(Heap: HeapType, $x: int, $y: int): int;
axiom (forall Heap: HeapType, $x: int, $y: int ::
  { $range_sum(Heap, $x, $y) }
  $range_sum(Heap, $x, $y) == $range_sum'(Heap, $x, $y) && dummyFunction($range_sum#triggerStateless($x, $y))
);
axiom (forall Heap: HeapType, $x: int, $y: int ::
  { $range_sum'(Heap, $x, $y) }
  dummyFunction($range_sum#triggerStateless($x, $y))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, $x: int, $y: int ::
  { state(Heap, Mask), $range_sum(Heap, $x, $y) }
  state(Heap, Mask) && AssumeFunctionsAbove < 0 ==> $x <= $y ==> $range_sum(Heap, $x, $y) == (if $x >= 0 && $y >= 0 then (if $y >= 0 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2) - (if $x >= 0 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2) else (if !($x >= 0) && $y >= 0 then (if $y >= 0 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2) - (if $x >= 0 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2) + $x else (if $y >= 0 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2) - $y - (if $x >= 0 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2) + $x))
);

// Framing axioms
function  $range_sum#frame(frame: FrameType, $x: int, $y: int): int;
axiom (forall Heap: HeapType, Mask: MaskType, $x: int, $y: int ::
  { state(Heap, Mask), $range_sum'(Heap, $x, $y) }
  state(Heap, Mask) ==> $range_sum'(Heap, $x, $y) == $range_sum#frame(EmptyFrame, $x, $y)
);

// Trigger function (controlling recursive postconditions)
function  $range_sum#trigger(frame: FrameType, $x: int, $y: int): bool;

// State-independent trigger function
function  $range_sum#triggerStateless($x: int, $y: int): int;

// Check contract well-formedness and postcondition
procedure $range_sum#definedness($x: int, $y: int) returns (Result: int)
  modifies Heap, Mask;
{
  var $x_ge_0_1: bool;
  var $y_ge_0_1: bool;
  var $x_exclusive_1: int;
  var $y_exclusive_1: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 0;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume $x <= $y;
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (let $x_ge_0 == ($x >= 0) in (let $y_ge_0 == ($y >= 0) in (let $x_exclusive == (($x_ge_0 ? ($x - 1) * $x / 2 : (-$x - 1) * -$x / 2)) in (let $y_exclusive == (($y_ge_0 ? ($y - 1) * $y / 2 : (-$y - 1) * -$y / 2)) in ($x_ge_0 && $y_ge_0 ? $y_exclusive - $x_exclusive : (!$x_ge_0 && $y_ge_0 ? $y_exclusive - $x_exclusive + $x : $y_exclusive - $y - $x_exclusive + $x))))))
      $x_ge_0_1 := $x >= 0;
      $y_ge_0_1 := $y >= 0;
      $x_exclusive_1 := (if $x_ge_0_1 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2);
      $y_exclusive_1 := (if $y_ge_0_1 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2);

  // -- Translate function body
    Result := (if $x >= 0 && $y >= 0 then (if $y >= 0 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2) - (if $x >= 0 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2) else (if !($x >= 0) && $y >= 0 then (if $y >= 0 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2) - (if $x >= 0 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2) + $x else (if $y >= 0 then ($y - 1) * $y div 2 else (-$y - 1) * -$y div 2) - $y - (if $x >= 0 then ($x - 1) * $x div 2 else (-$x - 1) * -$x div 2) + $x));
}

// ==================================================
// Translation of function $pure$success_get
// ==================================================

// Uninterpreted function definitions
function  $pure$success_get(Heap: HeapType, x_1: $StructDomainType): bool;
function  $pure$success_get'(Heap: HeapType, x_1: $StructDomainType): bool;
axiom (forall Heap: HeapType, x_1: $StructDomainType ::
  { $pure$success_get(Heap, x_1) }
  $pure$success_get(Heap, x_1) == $pure$success_get'(Heap, x_1) && dummyFunction($pure$success_get#triggerStateless(x_1))
);
axiom (forall Heap: HeapType, x_1: $StructDomainType ::
  { $pure$success_get'(Heap, x_1) }
  dummyFunction($pure$success_get#triggerStateless(x_1))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, x_1: $StructDomainType ::
  { state(Heap, Mask), $pure$success_get(Heap, x_1) }
  state(Heap, Mask) && AssumeFunctionsAbove < 2 ==> $pure$success_get(Heap, x_1) == ($struct_get(($struct_loc(x_1, 0): int)): bool)
);

// Framing axioms
function  $pure$success_get#frame(frame: FrameType, x_1: $StructDomainType): bool;
axiom (forall Heap: HeapType, Mask: MaskType, x_1: $StructDomainType ::
  { state(Heap, Mask), $pure$success_get'(Heap, x_1) }
  state(Heap, Mask) ==> $pure$success_get'(Heap, x_1) == $pure$success_get#frame(EmptyFrame, x_1)
);

// Trigger function (controlling recursive postconditions)
function  $pure$success_get#trigger(frame: FrameType, x_1: $StructDomainType): bool;

// State-independent trigger function
function  $pure$success_get#triggerStateless(x_1: $StructDomainType): bool;

// Check contract well-formedness and postcondition
procedure $pure$success_get#definedness(x_1: $StructDomainType) returns (Result: bool)
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 2;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Translate function body
    Result := ($struct_get(($struct_loc(x_1, 0): int)): bool);
}

// ==================================================
// Translation of function $pure$return_get
// ==================================================

// Uninterpreted function definitions
function  $pure$return_get(Heap: HeapType, x_1: $StructDomainType): int;
function  $pure$return_get'(Heap: HeapType, x_1: $StructDomainType): int;
axiom (forall Heap: HeapType, x_1: $StructDomainType ::
  { $pure$return_get(Heap, x_1) }
  $pure$return_get(Heap, x_1) == $pure$return_get'(Heap, x_1) && dummyFunction($pure$return_get#triggerStateless(x_1))
);
axiom (forall Heap: HeapType, x_1: $StructDomainType ::
  { $pure$return_get'(Heap, x_1) }
  dummyFunction($pure$return_get#triggerStateless(x_1))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, x_1: $StructDomainType ::
  { state(Heap, Mask), $pure$return_get(Heap, x_1) }
  state(Heap, Mask) && AssumeFunctionsAbove < 1 ==> $pure$success_get(Heap, x_1) ==> $pure$return_get(Heap, x_1) == ($struct_loc(x_1, 1): int)
);

// Framing axioms
function  $pure$return_get#frame(frame: FrameType, x_1: $StructDomainType): int;
axiom (forall Heap: HeapType, Mask: MaskType, x_1: $StructDomainType ::
  { state(Heap, Mask), $pure$return_get'(Heap, x_1) }
  state(Heap, Mask) ==> $pure$return_get'(Heap, x_1) == $pure$return_get#frame(EmptyFrame, x_1)
);

// Trigger function (controlling recursive postconditions)
function  $pure$return_get#trigger(frame: FrameType, x_1: $StructDomainType): bool;

// State-independent trigger function
function  $pure$return_get#triggerStateless(x_1: $StructDomainType): int;

// Check contract well-formedness and postcondition
procedure $pure$return_get#definedness(x_1: $StructDomainType) returns (Result: int)
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 1;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume state(Heap, Mask);

    // -- Check definedness of $pure$success_get(x)
      if (*) {
        // Stop execution
        assume false;
      }
    assume $pure$success_get(Heap, x_1);
    assume state(Heap, Mask);

  // -- Translate function body
    Result := ($struct_loc(x_1, 1): int);
}

// ==================================================
// Translation of predicate $failed
// ==================================================

type PredicateType_$failed;
function  $failed($address: int): Field PredicateType_$failed FrameType;
function  $failed#sm($address: int): Field PredicateType_$failed PMaskType;
axiom (forall $address: int ::
  { PredicateMaskField($failed($address)) }
  PredicateMaskField($failed($address)) == $failed#sm($address)
);
axiom (forall $address: int ::
  { $failed($address) }
  IsPredicateField($failed($address))
);
axiom (forall $address: int ::
  { $failed($address) }
  getPredicateId($failed($address)) == 0
);
function  $failed#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $failed#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $address: int, $address2: int ::
  { $failed($address), $failed($address2) }
  $failed($address) == $failed($address2) ==> $address == $address2
);
axiom (forall $address: int, $address2: int ::
  { $failed#sm($address), $failed#sm($address2) }
  $failed#sm($address) == $failed#sm($address2) ==> $address == $address2
);

axiom (forall Heap: HeapType, $address: int ::
  { $failed#trigger(Heap, $failed($address)) }
  $failed#everUsed($failed($address))
);

// ==================================================
// Translation of predicate $failed_0
// ==================================================

type PredicateType_$failed_0;
function  $failed_0($address: int): Field PredicateType_$failed_0 FrameType;
function  $failed_0#sm($address: int): Field PredicateType_$failed_0 PMaskType;
axiom (forall $address: int ::
  { PredicateMaskField($failed_0($address)) }
  PredicateMaskField($failed_0($address)) == $failed_0#sm($address)
);
axiom (forall $address: int ::
  { $failed_0($address) }
  IsPredicateField($failed_0($address))
);
axiom (forall $address: int ::
  { $failed_0($address) }
  getPredicateId($failed_0($address)) == 1
);
function  $failed_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $failed_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $address: int, $address2: int ::
  { $failed_0($address), $failed_0($address2) }
  $failed_0($address) == $failed_0($address2) ==> $address == $address2
);
axiom (forall $address: int, $address2: int ::
  { $failed_0#sm($address), $failed_0#sm($address2) }
  $failed_0#sm($address) == $failed_0#sm($address2) ==> $address == $address2
);

axiom (forall Heap: HeapType, $address: int ::
  { $failed_0#trigger(Heap, $failed_0($address)) }
  $failed_0#everUsed($failed_0($address))
);

// ==================================================
// Translation of predicate $allocation
// ==================================================

type PredicateType_$allocation;
function  $allocation($resource: $StructDomainType, $address: int): Field PredicateType_$allocation FrameType;
function  $allocation#sm($resource: $StructDomainType, $address: int): Field PredicateType_$allocation PMaskType;
axiom (forall $resource: $StructDomainType, $address: int ::
  { PredicateMaskField($allocation($resource, $address)) }
  PredicateMaskField($allocation($resource, $address)) == $allocation#sm($resource, $address)
);
axiom (forall $resource: $StructDomainType, $address: int ::
  { $allocation($resource, $address) }
  IsPredicateField($allocation($resource, $address))
);
axiom (forall $resource: $StructDomainType, $address: int ::
  { $allocation($resource, $address) }
  getPredicateId($allocation($resource, $address)) == 2
);
function  $allocation#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $allocation#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $address: int, $resource2: $StructDomainType, $address2: int ::
  { $allocation($resource, $address), $allocation($resource2, $address2) }
  $allocation($resource, $address) == $allocation($resource2, $address2) ==> $resource == $resource2 && $address == $address2
);
axiom (forall $resource: $StructDomainType, $address: int, $resource2: $StructDomainType, $address2: int ::
  { $allocation#sm($resource, $address), $allocation#sm($resource2, $address2) }
  $allocation#sm($resource, $address) == $allocation#sm($resource2, $address2) ==> $resource == $resource2 && $address == $address2
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $address: int ::
  { $allocation#trigger(Heap, $allocation($resource, $address)) }
  $allocation#everUsed($allocation($resource, $address))
);

// ==================================================
// Translation of predicate $allocation_0
// ==================================================

type PredicateType_$allocation_0;
function  $allocation_0($resource: $StructDomainType, $address: int): Field PredicateType_$allocation_0 FrameType;
function  $allocation_0#sm($resource: $StructDomainType, $address: int): Field PredicateType_$allocation_0 PMaskType;
axiom (forall $resource: $StructDomainType, $address: int ::
  { PredicateMaskField($allocation_0($resource, $address)) }
  PredicateMaskField($allocation_0($resource, $address)) == $allocation_0#sm($resource, $address)
);
axiom (forall $resource: $StructDomainType, $address: int ::
  { $allocation_0($resource, $address) }
  IsPredicateField($allocation_0($resource, $address))
);
axiom (forall $resource: $StructDomainType, $address: int ::
  { $allocation_0($resource, $address) }
  getPredicateId($allocation_0($resource, $address)) == 3
);
function  $allocation_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $allocation_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $address: int, $resource2: $StructDomainType, $address2: int ::
  { $allocation_0($resource, $address), $allocation_0($resource2, $address2) }
  $allocation_0($resource, $address) == $allocation_0($resource2, $address2) ==> $resource == $resource2 && $address == $address2
);
axiom (forall $resource: $StructDomainType, $address: int, $resource2: $StructDomainType, $address2: int ::
  { $allocation_0#sm($resource, $address), $allocation_0#sm($resource2, $address2) }
  $allocation_0#sm($resource, $address) == $allocation_0#sm($resource2, $address2) ==> $resource == $resource2 && $address == $address2
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $address: int ::
  { $allocation_0#trigger(Heap, $allocation_0($resource, $address)) }
  $allocation_0#everUsed($allocation_0($resource, $address))
);

// ==================================================
// Translation of predicate $offer
// ==================================================

type PredicateType_$offer;
function  $offer($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int): Field PredicateType_$offer FrameType;
function  $offer#sm($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int): Field PredicateType_$offer PMaskType;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { PredicateMaskField($offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) }
  PredicateMaskField($offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) == $offer#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { $offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) }
  IsPredicateField($offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { $offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) }
  getPredicateId($offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) == 4
);
function  $offer#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $offer#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int ::
  { $offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address), $offer($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) }
  $offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) == $offer($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_address == $to_address2))))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int ::
  { $offer#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address), $offer#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) }
  $offer#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) == $offer#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_address == $to_address2))))
);

axiom (forall Heap: HeapType, $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { $offer#trigger(Heap, $offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) }
  $offer#everUsed($offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address))
);

// ==================================================
// Translation of predicate $offer_0
// ==================================================

type PredicateType_$offer_0;
function  $offer_0($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int): Field PredicateType_$offer_0 FrameType;
function  $offer_0#sm($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int): Field PredicateType_$offer_0 PMaskType;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { PredicateMaskField($offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) }
  PredicateMaskField($offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) == $offer_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { $offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) }
  IsPredicateField($offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { $offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) }
  getPredicateId($offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) == 5
);
function  $offer_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $offer_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int ::
  { $offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address), $offer_0($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) }
  $offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) == $offer_0($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_address == $to_address2))))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int ::
  { $offer_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address), $offer_0#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) }
  $offer_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address) == $offer_0#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_address == $to_address2))))
);

axiom (forall Heap: HeapType, $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int ::
  { $offer_0#trigger(Heap, $offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address)) }
  $offer_0#everUsed($offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address))
);

// ==================================================
// Translation of predicate $trust
// ==================================================

type PredicateType_$trust;
function  $trust($address: int, $by_address: int): Field PredicateType_$trust FrameType;
function  $trust#sm($address: int, $by_address: int): Field PredicateType_$trust PMaskType;
axiom (forall $address: int, $by_address: int ::
  { PredicateMaskField($trust($address, $by_address)) }
  PredicateMaskField($trust($address, $by_address)) == $trust#sm($address, $by_address)
);
axiom (forall $address: int, $by_address: int ::
  { $trust($address, $by_address) }
  IsPredicateField($trust($address, $by_address))
);
axiom (forall $address: int, $by_address: int ::
  { $trust($address, $by_address) }
  getPredicateId($trust($address, $by_address)) == 6
);
function  $trust#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $trust#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $address: int, $by_address: int, $address2: int, $by_address2: int ::
  { $trust($address, $by_address), $trust($address2, $by_address2) }
  $trust($address, $by_address) == $trust($address2, $by_address2) ==> $address == $address2 && $by_address == $by_address2
);
axiom (forall $address: int, $by_address: int, $address2: int, $by_address2: int ::
  { $trust#sm($address, $by_address), $trust#sm($address2, $by_address2) }
  $trust#sm($address, $by_address) == $trust#sm($address2, $by_address2) ==> $address == $address2 && $by_address == $by_address2
);

axiom (forall Heap: HeapType, $address: int, $by_address: int ::
  { $trust#trigger(Heap, $trust($address, $by_address)) }
  $trust#everUsed($trust($address, $by_address))
);

// ==================================================
// Translation of predicate $trust_0
// ==================================================

type PredicateType_$trust_0;
function  $trust_0($address: int, $by_address: int): Field PredicateType_$trust_0 FrameType;
function  $trust_0#sm($address: int, $by_address: int): Field PredicateType_$trust_0 PMaskType;
axiom (forall $address: int, $by_address: int ::
  { PredicateMaskField($trust_0($address, $by_address)) }
  PredicateMaskField($trust_0($address, $by_address)) == $trust_0#sm($address, $by_address)
);
axiom (forall $address: int, $by_address: int ::
  { $trust_0($address, $by_address) }
  IsPredicateField($trust_0($address, $by_address))
);
axiom (forall $address: int, $by_address: int ::
  { $trust_0($address, $by_address) }
  getPredicateId($trust_0($address, $by_address)) == 7
);
function  $trust_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $trust_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $address: int, $by_address: int, $address2: int, $by_address2: int ::
  { $trust_0($address, $by_address), $trust_0($address2, $by_address2) }
  $trust_0($address, $by_address) == $trust_0($address2, $by_address2) ==> $address == $address2 && $by_address == $by_address2
);
axiom (forall $address: int, $by_address: int, $address2: int, $by_address2: int ::
  { $trust_0#sm($address, $by_address), $trust_0#sm($address2, $by_address2) }
  $trust_0#sm($address, $by_address) == $trust_0#sm($address2, $by_address2) ==> $address == $address2 && $by_address == $by_address2
);

axiom (forall Heap: HeapType, $address: int, $by_address: int ::
  { $trust_0#trigger(Heap, $trust_0($address, $by_address)) }
  $trust_0#everUsed($trust_0($address, $by_address))
);

// ==================================================
// Translation of predicate $performs$create
// ==================================================

type PredicateType_$performs$create;
function  $performs$create($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$create FrameType;
function  $performs$create#sm($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$create PMaskType;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { PredicateMaskField($performs$create($resource, $from_address, $to_address, $amount)) }
  PredicateMaskField($performs$create($resource, $from_address, $to_address, $amount)) == $performs$create#sm($resource, $from_address, $to_address, $amount)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$create($resource, $from_address, $to_address, $amount) }
  IsPredicateField($performs$create($resource, $from_address, $to_address, $amount))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$create($resource, $from_address, $to_address, $amount) }
  getPredicateId($performs$create($resource, $from_address, $to_address, $amount)) == 8
);
function  $performs$create#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$create#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$create($resource, $from_address, $to_address, $amount), $performs$create($resource2, $from_address2, $to_address2, $amount2) }
  $performs$create($resource, $from_address, $to_address, $amount) == $performs$create($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$create#sm($resource, $from_address, $to_address, $amount), $performs$create#sm($resource2, $from_address2, $to_address2, $amount2) }
  $performs$create#sm($resource, $from_address, $to_address, $amount) == $performs$create#sm($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$create#trigger(Heap, $performs$create($resource, $from_address, $to_address, $amount)) }
  $performs$create#everUsed($performs$create($resource, $from_address, $to_address, $amount))
);

// ==================================================
// Translation of predicate $performs$create_0
// ==================================================

type PredicateType_$performs$create_0;
function  $performs$create_0($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$create_0 FrameType;
function  $performs$create_0#sm($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$create_0 PMaskType;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { PredicateMaskField($performs$create_0($resource, $from_address, $to_address, $amount)) }
  PredicateMaskField($performs$create_0($resource, $from_address, $to_address, $amount)) == $performs$create_0#sm($resource, $from_address, $to_address, $amount)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$create_0($resource, $from_address, $to_address, $amount) }
  IsPredicateField($performs$create_0($resource, $from_address, $to_address, $amount))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$create_0($resource, $from_address, $to_address, $amount) }
  getPredicateId($performs$create_0($resource, $from_address, $to_address, $amount)) == 9
);
function  $performs$create_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$create_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$create_0($resource, $from_address, $to_address, $amount), $performs$create_0($resource2, $from_address2, $to_address2, $amount2) }
  $performs$create_0($resource, $from_address, $to_address, $amount) == $performs$create_0($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$create_0#sm($resource, $from_address, $to_address, $amount), $performs$create_0#sm($resource2, $from_address2, $to_address2, $amount2) }
  $performs$create_0#sm($resource, $from_address, $to_address, $amount) == $performs$create_0#sm($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$create_0#trigger(Heap, $performs$create_0($resource, $from_address, $to_address, $amount)) }
  $performs$create_0#everUsed($performs$create_0($resource, $from_address, $to_address, $amount))
);

// ==================================================
// Translation of predicate $performs$destroy
// ==================================================

type PredicateType_$performs$destroy;
function  $performs$destroy($resource: $StructDomainType, $from_address: int, $amount: int): Field PredicateType_$performs$destroy FrameType;
function  $performs$destroy#sm($resource: $StructDomainType, $from_address: int, $amount: int): Field PredicateType_$performs$destroy PMaskType;
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int ::
  { PredicateMaskField($performs$destroy($resource, $from_address, $amount)) }
  PredicateMaskField($performs$destroy($resource, $from_address, $amount)) == $performs$destroy#sm($resource, $from_address, $amount)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int ::
  { $performs$destroy($resource, $from_address, $amount) }
  IsPredicateField($performs$destroy($resource, $from_address, $amount))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int ::
  { $performs$destroy($resource, $from_address, $amount) }
  getPredicateId($performs$destroy($resource, $from_address, $amount)) == 10
);
function  $performs$destroy#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$destroy#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $amount2: int ::
  { $performs$destroy($resource, $from_address, $amount), $performs$destroy($resource2, $from_address2, $amount2) }
  $performs$destroy($resource, $from_address, $amount) == $performs$destroy($resource2, $from_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && $amount == $amount2)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $amount2: int ::
  { $performs$destroy#sm($resource, $from_address, $amount), $performs$destroy#sm($resource2, $from_address2, $amount2) }
  $performs$destroy#sm($resource, $from_address, $amount) == $performs$destroy#sm($resource2, $from_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $from_address: int, $amount: int ::
  { $performs$destroy#trigger(Heap, $performs$destroy($resource, $from_address, $amount)) }
  $performs$destroy#everUsed($performs$destroy($resource, $from_address, $amount))
);

// ==================================================
// Translation of predicate $performs$destroy_0
// ==================================================

type PredicateType_$performs$destroy_0;
function  $performs$destroy_0($resource: $StructDomainType, $from_address: int, $amount: int): Field PredicateType_$performs$destroy_0 FrameType;
function  $performs$destroy_0#sm($resource: $StructDomainType, $from_address: int, $amount: int): Field PredicateType_$performs$destroy_0 PMaskType;
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int ::
  { PredicateMaskField($performs$destroy_0($resource, $from_address, $amount)) }
  PredicateMaskField($performs$destroy_0($resource, $from_address, $amount)) == $performs$destroy_0#sm($resource, $from_address, $amount)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int ::
  { $performs$destroy_0($resource, $from_address, $amount) }
  IsPredicateField($performs$destroy_0($resource, $from_address, $amount))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int ::
  { $performs$destroy_0($resource, $from_address, $amount) }
  getPredicateId($performs$destroy_0($resource, $from_address, $amount)) == 11
);
function  $performs$destroy_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$destroy_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $amount2: int ::
  { $performs$destroy_0($resource, $from_address, $amount), $performs$destroy_0($resource2, $from_address2, $amount2) }
  $performs$destroy_0($resource, $from_address, $amount) == $performs$destroy_0($resource2, $from_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && $amount == $amount2)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $amount2: int ::
  { $performs$destroy_0#sm($resource, $from_address, $amount), $performs$destroy_0#sm($resource2, $from_address2, $amount2) }
  $performs$destroy_0#sm($resource, $from_address, $amount) == $performs$destroy_0#sm($resource2, $from_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $from_address: int, $amount: int ::
  { $performs$destroy_0#trigger(Heap, $performs$destroy_0($resource, $from_address, $amount)) }
  $performs$destroy_0#everUsed($performs$destroy_0($resource, $from_address, $amount))
);

// ==================================================
// Translation of predicate $performs$reallocate
// ==================================================

type PredicateType_$performs$reallocate;
function  $performs$reallocate($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$reallocate FrameType;
function  $performs$reallocate#sm($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$reallocate PMaskType;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { PredicateMaskField($performs$reallocate($resource, $from_address, $to_address, $amount)) }
  PredicateMaskField($performs$reallocate($resource, $from_address, $to_address, $amount)) == $performs$reallocate#sm($resource, $from_address, $to_address, $amount)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$reallocate($resource, $from_address, $to_address, $amount) }
  IsPredicateField($performs$reallocate($resource, $from_address, $to_address, $amount))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$reallocate($resource, $from_address, $to_address, $amount) }
  getPredicateId($performs$reallocate($resource, $from_address, $to_address, $amount)) == 12
);
function  $performs$reallocate#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$reallocate#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$reallocate($resource, $from_address, $to_address, $amount), $performs$reallocate($resource2, $from_address2, $to_address2, $amount2) }
  $performs$reallocate($resource, $from_address, $to_address, $amount) == $performs$reallocate($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$reallocate#sm($resource, $from_address, $to_address, $amount), $performs$reallocate#sm($resource2, $from_address2, $to_address2, $amount2) }
  $performs$reallocate#sm($resource, $from_address, $to_address, $amount) == $performs$reallocate#sm($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$reallocate#trigger(Heap, $performs$reallocate($resource, $from_address, $to_address, $amount)) }
  $performs$reallocate#everUsed($performs$reallocate($resource, $from_address, $to_address, $amount))
);

// ==================================================
// Translation of predicate $performs$reallocate_0
// ==================================================

type PredicateType_$performs$reallocate_0;
function  $performs$reallocate_0($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$reallocate_0 FrameType;
function  $performs$reallocate_0#sm($resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int): Field PredicateType_$performs$reallocate_0 PMaskType;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { PredicateMaskField($performs$reallocate_0($resource, $from_address, $to_address, $amount)) }
  PredicateMaskField($performs$reallocate_0($resource, $from_address, $to_address, $amount)) == $performs$reallocate_0#sm($resource, $from_address, $to_address, $amount)
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$reallocate_0($resource, $from_address, $to_address, $amount) }
  IsPredicateField($performs$reallocate_0($resource, $from_address, $to_address, $amount))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$reallocate_0($resource, $from_address, $to_address, $amount) }
  getPredicateId($performs$reallocate_0($resource, $from_address, $to_address, $amount)) == 13
);
function  $performs$reallocate_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$reallocate_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$reallocate_0($resource, $from_address, $to_address, $amount), $performs$reallocate_0($resource2, $from_address2, $to_address2, $amount2) }
  $performs$reallocate_0($resource, $from_address, $to_address, $amount) == $performs$reallocate_0($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);
axiom (forall $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int, $resource2: $StructDomainType, $from_address2: int, $to_address2: int, $amount2: int ::
  { $performs$reallocate_0#sm($resource, $from_address, $to_address, $amount), $performs$reallocate_0#sm($resource2, $from_address2, $to_address2, $amount2) }
  $performs$reallocate_0#sm($resource, $from_address, $to_address, $amount) == $performs$reallocate_0#sm($resource2, $from_address2, $to_address2, $amount2) ==> $resource == $resource2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $amount == $amount2))
);

axiom (forall Heap: HeapType, $resource: $StructDomainType, $from_address: int, $to_address: int, $amount: int ::
  { $performs$reallocate_0#trigger(Heap, $performs$reallocate_0($resource, $from_address, $to_address, $amount)) }
  $performs$reallocate_0#everUsed($performs$reallocate_0($resource, $from_address, $to_address, $amount))
);

// ==================================================
// Translation of predicate $performs$offer
// ==================================================

type PredicateType_$performs$offer;
function  $performs$offer($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int): Field PredicateType_$performs$offer FrameType;
function  $performs$offer#sm($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int): Field PredicateType_$performs$offer PMaskType;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { PredicateMaskField($performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) }
  PredicateMaskField($performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) == $performs$offer#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { $performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) }
  IsPredicateField($performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { $performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) }
  getPredicateId($performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) == 14
);
function  $performs$offer#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$offer#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int, $times2: int ::
  { $performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times), $performs$offer($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) }
  $performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) == $performs$offer($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $times == $times2)))))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int, $times2: int ::
  { $performs$offer#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times), $performs$offer#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) }
  $performs$offer#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) == $performs$offer#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $times == $times2)))))
);

axiom (forall Heap: HeapType, $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { $performs$offer#trigger(Heap, $performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) }
  $performs$offer#everUsed($performs$offer($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times))
);

// ==================================================
// Translation of predicate $performs$offer_0
// ==================================================

type PredicateType_$performs$offer_0;
function  $performs$offer_0($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int): Field PredicateType_$performs$offer_0 FrameType;
function  $performs$offer_0#sm($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int): Field PredicateType_$performs$offer_0 PMaskType;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { PredicateMaskField($performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) }
  PredicateMaskField($performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) == $performs$offer_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { $performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) }
  IsPredicateField($performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { $performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) }
  getPredicateId($performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) == 15
);
function  $performs$offer_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$offer_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int, $times2: int ::
  { $performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times), $performs$offer_0($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) }
  $performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) == $performs$offer_0($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $times == $times2)))))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_address2: int, $times2: int ::
  { $performs$offer_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times), $performs$offer_0#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) }
  $performs$offer_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times) == $performs$offer_0#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_address2, $times2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && ($to_address == $to_address2 && $times == $times2)))))
);

axiom (forall Heap: HeapType, $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_address: int, $times: int ::
  { $performs$offer_0#trigger(Heap, $performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times)) }
  $performs$offer_0#everUsed($performs$offer_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_address, $times))
);

// ==================================================
// Translation of predicate $performs$revoke
// ==================================================

type PredicateType_$performs$revoke;
function  $performs$revoke($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int): Field PredicateType_$performs$revoke FrameType;
function  $performs$revoke#sm($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int): Field PredicateType_$performs$revoke PMaskType;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { PredicateMaskField($performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) }
  PredicateMaskField($performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) == $performs$revoke#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { $performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) }
  IsPredicateField($performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { $performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) }
  getPredicateId($performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) == 16
);
function  $performs$revoke#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$revoke#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_adress2: int ::
  { $performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress), $performs$revoke($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) }
  $performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) == $performs$revoke($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_adress == $to_adress2))))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_adress2: int ::
  { $performs$revoke#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress), $performs$revoke#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) }
  $performs$revoke#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) == $performs$revoke#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_adress == $to_adress2))))
);

axiom (forall Heap: HeapType, $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { $performs$revoke#trigger(Heap, $performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) }
  $performs$revoke#everUsed($performs$revoke($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress))
);

// ==================================================
// Translation of predicate $performs$revoke_0
// ==================================================

type PredicateType_$performs$revoke_0;
function  $performs$revoke_0($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int): Field PredicateType_$performs$revoke_0 FrameType;
function  $performs$revoke_0#sm($from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int): Field PredicateType_$performs$revoke_0 PMaskType;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { PredicateMaskField($performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) }
  PredicateMaskField($performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) == $performs$revoke_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { $performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) }
  IsPredicateField($performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { $performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) }
  getPredicateId($performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) == 17
);
function  $performs$revoke_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$revoke_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_adress2: int ::
  { $performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress), $performs$revoke_0($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) }
  $performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) == $performs$revoke_0($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_adress == $to_adress2))))
);
axiom (forall $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int, $from_resource2: $StructDomainType, $to_resource2: $StructDomainType, $from_amount2: int, $to_amount2: int, $from_address2: int, $to_adress2: int ::
  { $performs$revoke_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress), $performs$revoke_0#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) }
  $performs$revoke_0#sm($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress) == $performs$revoke_0#sm($from_resource2, $to_resource2, $from_amount2, $to_amount2, $from_address2, $to_adress2) ==> $from_resource == $from_resource2 && ($to_resource == $to_resource2 && ($from_amount == $from_amount2 && ($to_amount == $to_amount2 && ($from_address == $from_address2 && $to_adress == $to_adress2))))
);

axiom (forall Heap: HeapType, $from_resource: $StructDomainType, $to_resource: $StructDomainType, $from_amount: int, $to_amount: int, $from_address: int, $to_adress: int ::
  { $performs$revoke_0#trigger(Heap, $performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress)) }
  $performs$revoke_0#everUsed($performs$revoke_0($from_resource, $to_resource, $from_amount, $to_amount, $from_address, $to_adress))
);

// ==================================================
// Translation of predicate $performs$trust
// ==================================================

type PredicateType_$performs$trust;
function  $performs$trust($address: int, $by_address: int, $value: bool): Field PredicateType_$performs$trust FrameType;
function  $performs$trust#sm($address: int, $by_address: int, $value: bool): Field PredicateType_$performs$trust PMaskType;
axiom (forall $address: int, $by_address: int, $value: bool ::
  { PredicateMaskField($performs$trust($address, $by_address, $value)) }
  PredicateMaskField($performs$trust($address, $by_address, $value)) == $performs$trust#sm($address, $by_address, $value)
);
axiom (forall $address: int, $by_address: int, $value: bool ::
  { $performs$trust($address, $by_address, $value) }
  IsPredicateField($performs$trust($address, $by_address, $value))
);
axiom (forall $address: int, $by_address: int, $value: bool ::
  { $performs$trust($address, $by_address, $value) }
  getPredicateId($performs$trust($address, $by_address, $value)) == 18
);
function  $performs$trust#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$trust#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $address: int, $by_address: int, $value: bool, $address2: int, $by_address2: int, $value2: bool ::
  { $performs$trust($address, $by_address, $value), $performs$trust($address2, $by_address2, $value2) }
  $performs$trust($address, $by_address, $value) == $performs$trust($address2, $by_address2, $value2) ==> $address == $address2 && ($by_address == $by_address2 && $value == $value2)
);
axiom (forall $address: int, $by_address: int, $value: bool, $address2: int, $by_address2: int, $value2: bool ::
  { $performs$trust#sm($address, $by_address, $value), $performs$trust#sm($address2, $by_address2, $value2) }
  $performs$trust#sm($address, $by_address, $value) == $performs$trust#sm($address2, $by_address2, $value2) ==> $address == $address2 && ($by_address == $by_address2 && $value == $value2)
);

axiom (forall Heap: HeapType, $address: int, $by_address: int, $value: bool ::
  { $performs$trust#trigger(Heap, $performs$trust($address, $by_address, $value)) }
  $performs$trust#everUsed($performs$trust($address, $by_address, $value))
);

// ==================================================
// Translation of predicate $performs$trust_0
// ==================================================

type PredicateType_$performs$trust_0;
function  $performs$trust_0($address: int, $by_address: int, $value: bool): Field PredicateType_$performs$trust_0 FrameType;
function  $performs$trust_0#sm($address: int, $by_address: int, $value: bool): Field PredicateType_$performs$trust_0 PMaskType;
axiom (forall $address: int, $by_address: int, $value: bool ::
  { PredicateMaskField($performs$trust_0($address, $by_address, $value)) }
  PredicateMaskField($performs$trust_0($address, $by_address, $value)) == $performs$trust_0#sm($address, $by_address, $value)
);
axiom (forall $address: int, $by_address: int, $value: bool ::
  { $performs$trust_0($address, $by_address, $value) }
  IsPredicateField($performs$trust_0($address, $by_address, $value))
);
axiom (forall $address: int, $by_address: int, $value: bool ::
  { $performs$trust_0($address, $by_address, $value) }
  getPredicateId($performs$trust_0($address, $by_address, $value)) == 19
);
function  $performs$trust_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $performs$trust_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $address: int, $by_address: int, $value: bool, $address2: int, $by_address2: int, $value2: bool ::
  { $performs$trust_0($address, $by_address, $value), $performs$trust_0($address2, $by_address2, $value2) }
  $performs$trust_0($address, $by_address, $value) == $performs$trust_0($address2, $by_address2, $value2) ==> $address == $address2 && ($by_address == $by_address2 && $value == $value2)
);
axiom (forall $address: int, $by_address: int, $value: bool, $address2: int, $by_address2: int, $value2: bool ::
  { $performs$trust_0#sm($address, $by_address, $value), $performs$trust_0#sm($address2, $by_address2, $value2) }
  $performs$trust_0#sm($address, $by_address, $value) == $performs$trust_0#sm($address2, $by_address2, $value2) ==> $address == $address2 && ($by_address == $by_address2 && $value == $value2)
);

axiom (forall Heap: HeapType, $address: int, $by_address: int, $value: bool ::
  { $performs$trust_0#trigger(Heap, $performs$trust_0($address, $by_address, $value)) }
  $performs$trust_0#everUsed($performs$trust_0($address, $by_address, $value))
);

// ==================================================
// Translation of predicate $accessible$__init__
// ==================================================

type PredicateType_$accessible$__init__;
function  $accessible$__init__($tag: int, $to: int, $amount: int, $arg0: int, $arg1: int): Field PredicateType_$accessible$__init__ FrameType;
function  $accessible$__init__#sm($tag: int, $to: int, $amount: int, $arg0: int, $arg1: int): Field PredicateType_$accessible$__init__ PMaskType;
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { PredicateMaskField($accessible$__init__($tag, $to, $amount, $arg0, $arg1)) }
  PredicateMaskField($accessible$__init__($tag, $to, $amount, $arg0, $arg1)) == $accessible$__init__#sm($tag, $to, $amount, $arg0, $arg1)
);
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { $accessible$__init__($tag, $to, $amount, $arg0, $arg1) }
  IsPredicateField($accessible$__init__($tag, $to, $amount, $arg0, $arg1))
);
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { $accessible$__init__($tag, $to, $amount, $arg0, $arg1) }
  getPredicateId($accessible$__init__($tag, $to, $amount, $arg0, $arg1)) == 20
);
function  $accessible$__init__#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$__init__#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int, $tag2: int, $to2: int, $amount2: int, $arg02: int, $arg12: int ::
  { $accessible$__init__($tag, $to, $amount, $arg0, $arg1), $accessible$__init__($tag2, $to2, $amount2, $arg02, $arg12) }
  $accessible$__init__($tag, $to, $amount, $arg0, $arg1) == $accessible$__init__($tag2, $to2, $amount2, $arg02, $arg12) ==> $tag == $tag2 && ($to == $to2 && ($amount == $amount2 && ($arg0 == $arg02 && $arg1 == $arg12)))
);
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int, $tag2: int, $to2: int, $amount2: int, $arg02: int, $arg12: int ::
  { $accessible$__init__#sm($tag, $to, $amount, $arg0, $arg1), $accessible$__init__#sm($tag2, $to2, $amount2, $arg02, $arg12) }
  $accessible$__init__#sm($tag, $to, $amount, $arg0, $arg1) == $accessible$__init__#sm($tag2, $to2, $amount2, $arg02, $arg12) ==> $tag == $tag2 && ($to == $to2 && ($amount == $amount2 && ($arg0 == $arg02 && $arg1 == $arg12)))
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { $accessible$__init__#trigger(Heap, $accessible$__init__($tag, $to, $amount, $arg0, $arg1)) }
  $accessible$__init__#everUsed($accessible$__init__($tag, $to, $amount, $arg0, $arg1))
);

// ==================================================
// Translation of predicate $accessible$__init___0
// ==================================================

type PredicateType_$accessible$__init___0;
function  $accessible$__init___0($tag: int, $to: int, $amount: int, $arg0: int, $arg1: int): Field PredicateType_$accessible$__init___0 FrameType;
function  $accessible$__init___0#sm($tag: int, $to: int, $amount: int, $arg0: int, $arg1: int): Field PredicateType_$accessible$__init___0 PMaskType;
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { PredicateMaskField($accessible$__init___0($tag, $to, $amount, $arg0, $arg1)) }
  PredicateMaskField($accessible$__init___0($tag, $to, $amount, $arg0, $arg1)) == $accessible$__init___0#sm($tag, $to, $amount, $arg0, $arg1)
);
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { $accessible$__init___0($tag, $to, $amount, $arg0, $arg1) }
  IsPredicateField($accessible$__init___0($tag, $to, $amount, $arg0, $arg1))
);
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { $accessible$__init___0($tag, $to, $amount, $arg0, $arg1) }
  getPredicateId($accessible$__init___0($tag, $to, $amount, $arg0, $arg1)) == 21
);
function  $accessible$__init___0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$__init___0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int, $tag2: int, $to2: int, $amount2: int, $arg02: int, $arg12: int ::
  { $accessible$__init___0($tag, $to, $amount, $arg0, $arg1), $accessible$__init___0($tag2, $to2, $amount2, $arg02, $arg12) }
  $accessible$__init___0($tag, $to, $amount, $arg0, $arg1) == $accessible$__init___0($tag2, $to2, $amount2, $arg02, $arg12) ==> $tag == $tag2 && ($to == $to2 && ($amount == $amount2 && ($arg0 == $arg02 && $arg1 == $arg12)))
);
axiom (forall $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int, $tag2: int, $to2: int, $amount2: int, $arg02: int, $arg12: int ::
  { $accessible$__init___0#sm($tag, $to, $amount, $arg0, $arg1), $accessible$__init___0#sm($tag2, $to2, $amount2, $arg02, $arg12) }
  $accessible$__init___0#sm($tag, $to, $amount, $arg0, $arg1) == $accessible$__init___0#sm($tag2, $to2, $amount2, $arg02, $arg12) ==> $tag == $tag2 && ($to == $to2 && ($amount == $amount2 && ($arg0 == $arg02 && $arg1 == $arg12)))
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int, $arg0: int, $arg1: int ::
  { $accessible$__init___0#trigger(Heap, $accessible$__init___0($tag, $to, $amount, $arg0, $arg1)) }
  $accessible$__init___0#everUsed($accessible$__init___0($tag, $to, $amount, $arg0, $arg1))
);

// ==================================================
// Translation of predicate $accessible$bid
// ==================================================

type PredicateType_$accessible$bid;
function  $accessible$bid($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$bid FrameType;
function  $accessible$bid#sm($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$bid PMaskType;
axiom (forall $tag: int, $to: int, $amount: int ::
  { PredicateMaskField($accessible$bid($tag, $to, $amount)) }
  PredicateMaskField($accessible$bid($tag, $to, $amount)) == $accessible$bid#sm($tag, $to, $amount)
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$bid($tag, $to, $amount) }
  IsPredicateField($accessible$bid($tag, $to, $amount))
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$bid($tag, $to, $amount) }
  getPredicateId($accessible$bid($tag, $to, $amount)) == 22
);
function  $accessible$bid#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$bid#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$bid($tag, $to, $amount), $accessible$bid($tag2, $to2, $amount2) }
  $accessible$bid($tag, $to, $amount) == $accessible$bid($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$bid#sm($tag, $to, $amount), $accessible$bid#sm($tag2, $to2, $amount2) }
  $accessible$bid#sm($tag, $to, $amount) == $accessible$bid#sm($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int ::
  { $accessible$bid#trigger(Heap, $accessible$bid($tag, $to, $amount)) }
  $accessible$bid#everUsed($accessible$bid($tag, $to, $amount))
);

// ==================================================
// Translation of predicate $accessible$bid_0
// ==================================================

type PredicateType_$accessible$bid_0;
function  $accessible$bid_0($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$bid_0 FrameType;
function  $accessible$bid_0#sm($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$bid_0 PMaskType;
axiom (forall $tag: int, $to: int, $amount: int ::
  { PredicateMaskField($accessible$bid_0($tag, $to, $amount)) }
  PredicateMaskField($accessible$bid_0($tag, $to, $amount)) == $accessible$bid_0#sm($tag, $to, $amount)
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$bid_0($tag, $to, $amount) }
  IsPredicateField($accessible$bid_0($tag, $to, $amount))
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$bid_0($tag, $to, $amount) }
  getPredicateId($accessible$bid_0($tag, $to, $amount)) == 23
);
function  $accessible$bid_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$bid_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$bid_0($tag, $to, $amount), $accessible$bid_0($tag2, $to2, $amount2) }
  $accessible$bid_0($tag, $to, $amount) == $accessible$bid_0($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$bid_0#sm($tag, $to, $amount), $accessible$bid_0#sm($tag2, $to2, $amount2) }
  $accessible$bid_0#sm($tag, $to, $amount) == $accessible$bid_0#sm($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int ::
  { $accessible$bid_0#trigger(Heap, $accessible$bid_0($tag, $to, $amount)) }
  $accessible$bid_0#everUsed($accessible$bid_0($tag, $to, $amount))
);

// ==================================================
// Translation of predicate $accessible$withdraw
// ==================================================

type PredicateType_$accessible$withdraw;
function  $accessible$withdraw($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$withdraw FrameType;
function  $accessible$withdraw#sm($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$withdraw PMaskType;
axiom (forall $tag: int, $to: int, $amount: int ::
  { PredicateMaskField($accessible$withdraw($tag, $to, $amount)) }
  PredicateMaskField($accessible$withdraw($tag, $to, $amount)) == $accessible$withdraw#sm($tag, $to, $amount)
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$withdraw($tag, $to, $amount) }
  IsPredicateField($accessible$withdraw($tag, $to, $amount))
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$withdraw($tag, $to, $amount) }
  getPredicateId($accessible$withdraw($tag, $to, $amount)) == 24
);
function  $accessible$withdraw#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$withdraw#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$withdraw($tag, $to, $amount), $accessible$withdraw($tag2, $to2, $amount2) }
  $accessible$withdraw($tag, $to, $amount) == $accessible$withdraw($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$withdraw#sm($tag, $to, $amount), $accessible$withdraw#sm($tag2, $to2, $amount2) }
  $accessible$withdraw#sm($tag, $to, $amount) == $accessible$withdraw#sm($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int ::
  { $accessible$withdraw#trigger(Heap, $accessible$withdraw($tag, $to, $amount)) }
  $accessible$withdraw#everUsed($accessible$withdraw($tag, $to, $amount))
);

// ==================================================
// Translation of predicate $accessible$withdraw_0
// ==================================================

type PredicateType_$accessible$withdraw_0;
function  $accessible$withdraw_0($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$withdraw_0 FrameType;
function  $accessible$withdraw_0#sm($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$withdraw_0 PMaskType;
axiom (forall $tag: int, $to: int, $amount: int ::
  { PredicateMaskField($accessible$withdraw_0($tag, $to, $amount)) }
  PredicateMaskField($accessible$withdraw_0($tag, $to, $amount)) == $accessible$withdraw_0#sm($tag, $to, $amount)
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$withdraw_0($tag, $to, $amount) }
  IsPredicateField($accessible$withdraw_0($tag, $to, $amount))
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$withdraw_0($tag, $to, $amount) }
  getPredicateId($accessible$withdraw_0($tag, $to, $amount)) == 25
);
function  $accessible$withdraw_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$withdraw_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$withdraw_0($tag, $to, $amount), $accessible$withdraw_0($tag2, $to2, $amount2) }
  $accessible$withdraw_0($tag, $to, $amount) == $accessible$withdraw_0($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$withdraw_0#sm($tag, $to, $amount), $accessible$withdraw_0#sm($tag2, $to2, $amount2) }
  $accessible$withdraw_0#sm($tag, $to, $amount) == $accessible$withdraw_0#sm($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int ::
  { $accessible$withdraw_0#trigger(Heap, $accessible$withdraw_0($tag, $to, $amount)) }
  $accessible$withdraw_0#everUsed($accessible$withdraw_0($tag, $to, $amount))
);

// ==================================================
// Translation of predicate $accessible$endAuction
// ==================================================

type PredicateType_$accessible$endAuction;
function  $accessible$endAuction($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$endAuction FrameType;
function  $accessible$endAuction#sm($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$endAuction PMaskType;
axiom (forall $tag: int, $to: int, $amount: int ::
  { PredicateMaskField($accessible$endAuction($tag, $to, $amount)) }
  PredicateMaskField($accessible$endAuction($tag, $to, $amount)) == $accessible$endAuction#sm($tag, $to, $amount)
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$endAuction($tag, $to, $amount) }
  IsPredicateField($accessible$endAuction($tag, $to, $amount))
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$endAuction($tag, $to, $amount) }
  getPredicateId($accessible$endAuction($tag, $to, $amount)) == 26
);
function  $accessible$endAuction#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$endAuction#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$endAuction($tag, $to, $amount), $accessible$endAuction($tag2, $to2, $amount2) }
  $accessible$endAuction($tag, $to, $amount) == $accessible$endAuction($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$endAuction#sm($tag, $to, $amount), $accessible$endAuction#sm($tag2, $to2, $amount2) }
  $accessible$endAuction#sm($tag, $to, $amount) == $accessible$endAuction#sm($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int ::
  { $accessible$endAuction#trigger(Heap, $accessible$endAuction($tag, $to, $amount)) }
  $accessible$endAuction#everUsed($accessible$endAuction($tag, $to, $amount))
);

// ==================================================
// Translation of predicate $accessible$endAuction_0
// ==================================================

type PredicateType_$accessible$endAuction_0;
function  $accessible$endAuction_0($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$endAuction_0 FrameType;
function  $accessible$endAuction_0#sm($tag: int, $to: int, $amount: int): Field PredicateType_$accessible$endAuction_0 PMaskType;
axiom (forall $tag: int, $to: int, $amount: int ::
  { PredicateMaskField($accessible$endAuction_0($tag, $to, $amount)) }
  PredicateMaskField($accessible$endAuction_0($tag, $to, $amount)) == $accessible$endAuction_0#sm($tag, $to, $amount)
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$endAuction_0($tag, $to, $amount) }
  IsPredicateField($accessible$endAuction_0($tag, $to, $amount))
);
axiom (forall $tag: int, $to: int, $amount: int ::
  { $accessible$endAuction_0($tag, $to, $amount) }
  getPredicateId($accessible$endAuction_0($tag, $to, $amount)) == 27
);
function  $accessible$endAuction_0#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  $accessible$endAuction_0#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$endAuction_0($tag, $to, $amount), $accessible$endAuction_0($tag2, $to2, $amount2) }
  $accessible$endAuction_0($tag, $to, $amount) == $accessible$endAuction_0($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);
axiom (forall $tag: int, $to: int, $amount: int, $tag2: int, $to2: int, $amount2: int ::
  { $accessible$endAuction_0#sm($tag, $to, $amount), $accessible$endAuction_0#sm($tag2, $to2, $amount2) }
  $accessible$endAuction_0#sm($tag, $to, $amount) == $accessible$endAuction_0#sm($tag2, $to2, $amount2) ==> $tag == $tag2 && ($to == $to2 && $amount == $amount2)
);

axiom (forall Heap: HeapType, $tag: int, $to: int, $amount: int ::
  { $accessible$endAuction_0#trigger(Heap, $accessible$endAuction_0($tag, $to, $amount)) }
  $accessible$endAuction_0#everUsed($accessible$endAuction_0($tag, $to, $amount))
);

// ==================================================
// Translation of method $transitivity_check
// ==================================================

procedure $transitivity_check() returns ()
  modifies Heap, Mask;
{
  var $self$0: $StructDomainType;
  var $self$1: $StructDomainType;
  var $self$2: $StructDomainType;
  var block: $StructDomainType;
  var QPMask: MaskType;
  var q$a_28: int;
  var q$a_31: int;
  var q$a_34: int;
  var AssertHeap: HeapType;
  var AssertMask: MaskType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 0)): Int) &&
  //   ($struct_get($struct_loc($self$0, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@610.3--610.158
    assume 0 <= ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume ($struct_get(($struct_loc($self$0, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 1)): Int) &&
  //   ($struct_get($struct_loc($self$0, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@611.3--611.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 1): int)): int);
    assume ($struct_get(($struct_loc($self$0, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 2)): Int) &&
  //   ($struct_get($struct_loc($self$0, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@612.3--612.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 2): int)): int);
    assume ($struct_get(($struct_loc($self$0, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 3)): Int) &&
  //   ($struct_get($struct_loc($self$0, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@613.3--613.158
    assume 0 <= ($struct_get(($struct_loc($self$0, 3): int)): int);
    assume ($struct_get(($struct_loc($self$0, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 4)): Int) &&
  //   ($struct_get($struct_loc($self$0, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@614.3--614.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 4): int)): int);
    assume ($struct_get(($struct_loc($self$0, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@615.3--615.355

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@616.3--616.263

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 7)): Int) &&
  //   ($struct_get($struct_loc($self$0, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@617.3--617.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 7): int)): int);
    assume ($struct_get(($struct_loc($self$0, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc($self$0, 8)): Int) &&
  //   ($struct_get($struct_loc($self$0, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@618.3--618.187
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc($self$0, 8): int)): int);
    assume ($struct_get(($struct_loc($self$0, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@619.3--619.358

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@620.3--620.266

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@621.3--621.358

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@622.3--622.266

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@623.3--623.89
    assume ($struct_get(($struct_loc($self$0, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 0)): Int) &&
  //   ($struct_get($struct_loc($self$1, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@624.3--624.158
    assume 0 <= ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume ($struct_get(($struct_loc($self$1, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 1)): Int) &&
  //   ($struct_get($struct_loc($self$1, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@625.3--625.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 1): int)): int);
    assume ($struct_get(($struct_loc($self$1, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 2)): Int) &&
  //   ($struct_get($struct_loc($self$1, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@626.3--626.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 2): int)): int);
    assume ($struct_get(($struct_loc($self$1, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 3)): Int) &&
  //   ($struct_get($struct_loc($self$1, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@627.3--627.158
    assume 0 <= ($struct_get(($struct_loc($self$1, 3): int)): int);
    assume ($struct_get(($struct_loc($self$1, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 4)): Int) &&
  //   ($struct_get($struct_loc($self$1, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@628.3--628.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 4): int)): int);
    assume ($struct_get(($struct_loc($self$1, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@629.3--629.355

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_5): int) && ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@630.3--630.263

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_7: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_7): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_7): int) <= ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 7)): Int) &&
  //   ($struct_get($struct_loc($self$1, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@631.3--631.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    assume ($struct_get(($struct_loc($self$1, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc($self$1, 8)): Int) &&
  //   ($struct_get($struct_loc($self$1, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@632.3--632.187
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc($self$1, 8): int)): int);
    assume ($struct_get(($struct_loc($self$1, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@633.3--633.358

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_5): int) && ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@634.3--634.266

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_7: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_7): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_7): int) <= ($map_sum(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@635.3--635.358

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_5): int) && ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@636.3--636.266

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_7: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_7): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_7): int) <= ($map_sum(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@637.3--637.89
    assume ($struct_get(($struct_loc($self$1, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$2, 0)): Int) &&
  //   ($struct_get($struct_loc($self$2, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@638.3--638.158
    assume 0 <= ($struct_get(($struct_loc($self$2, 0): int)): int);
    assume ($struct_get(($struct_loc($self$2, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$2, 1)): Int) &&
  //   ($struct_get($struct_loc($self$2, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@639.3--639.187
    assume 0 <= ($struct_get(($struct_loc($self$2, 1): int)): int);
    assume ($struct_get(($struct_loc($self$2, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$2, 2)): Int) &&
  //   ($struct_get($struct_loc($self$2, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@640.3--640.187
    assume 0 <= ($struct_get(($struct_loc($self$2, 2): int)): int);
    assume ($struct_get(($struct_loc($self$2, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$2, 3)): Int) &&
  //   ($struct_get($struct_loc($self$2, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@641.3--641.158
    assume 0 <= ($struct_get(($struct_loc($self$2, 3): int)): int);
    assume ($struct_get(($struct_loc($self$2, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$2, 4)): Int) &&
  //   ($struct_get($struct_loc($self$2, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@642.3--642.187
    assume 0 <= ($struct_get(($struct_loc($self$2, 4): int)): int);
    assume ($struct_get(($struct_loc($self$2, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@643.3--643.355

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_9: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), $q0_9): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), $q0_9): int) && ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), $q0_9): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@644.3--644.263

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_11: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), $q0_11): int) }
      ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), $q0_11): int) <= ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$2, 7)): Int) &&
  //   ($struct_get($struct_loc($self$2, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@645.3--645.187
    assume 0 <= ($struct_get(($struct_loc($self$2, 7): int)): int);
    assume ($struct_get(($struct_loc($self$2, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc($self$2, 8)): Int) &&
  //   ($struct_get($struct_loc($self$2, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@646.3--646.187
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc($self$2, 8): int)): int);
    assume ($struct_get(($struct_loc($self$2, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@647.3--647.358

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_9: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $q1_9): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $q1_9): int) && ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $q1_9): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@648.3--648.266

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_11: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $q1_11): int) }
      ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $q1_11): int) <= ($map_sum(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@649.3--649.358

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_9: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), $q2_9): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), $q2_9): int) && ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), $q2_9): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@650.3--650.266

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_11: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), $q2_11): int) }
      ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), $q2_11): int) <= ($map_sum(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@651.3--651.89
    assume ($struct_get(($struct_loc($self$2, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@652.3--652.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@653.3--653.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@654.3--654.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@655.3--655.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@656.3--656.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@657.3--657.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@658.3--658.267

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_1_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $a_1_1): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $a_1_1): int) >= ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $a_1_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc($self$0, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@659.3--659.111
    if (($struct_get(($struct_loc($self$0, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc($self$0, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 0)): Int) ==
  //   ($struct_get($struct_loc($self$0, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@660.3--660.100
    assume ($struct_get(($struct_loc($self$0, 0): int)): int) == ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$0, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@661.3--661.103
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$0, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$0, 4)): Int) <=
  //   ($struct_get($struct_loc($self$0, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@662.3--662.224
    if (!($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$0, 4): int)): int) <= ($struct_get(($struct_loc($self$0, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$0, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@663.3--663.328
    if (!($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$0, 4): int)): int) == ($map_sum(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc($self$0, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@664.3--664.177
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc($self$0, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 4)): Int) >=
  //   ($struct_get($struct_loc($self$0, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@665.3--665.100
    assume ($struct_get(($struct_loc($self$0, 4): int)): int) >= ($struct_get(($struct_loc($self$0, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$0, 4)): Int) ==
  //   ($struct_get($struct_loc($self$0, 4)): Int) &&
  //   ($struct_get($struct_loc($self$0, 3)): Int) ==
  //   ($struct_get($struct_loc($self$0, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@666.3--666.243
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$0, 4): int)): int) == ($struct_get(($struct_loc($self$0, 4): int)): int);
      assume ($struct_get(($struct_loc($self$0, 3): int)): int) == ($struct_get(($struct_loc($self$0, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@667.3--667.58
    assume ($struct_get(($struct_loc($self$0, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 3)): Int) !=
  //   ($struct_get($struct_loc($self$0, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@668.3--668.100
    assume ($struct_get(($struct_loc($self$0, 3): int)): int) != ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$0,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@669.3--669.131
    assume ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$0, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$0,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@670.3--670.182
    if (!($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$0, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$0,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc($self$0, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@671.3--671.223
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$0, 0): int)): int)): int) == ($struct_get(($struct_loc($self$0, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$0,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc($self$0, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$0,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$0,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@672.3--672.413
    assume ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$0, 3): int)): int)): int) + ($struct_get(($struct_loc($self$0, 4): int)): int) + ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$0, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$0, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$0, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc($self$0, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@673.3--673.532

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$0, 3)): Int) && q$a != ($struct_get($struct_loc($self$0, 0)): Int) ==> ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), q$a_1): int) }
      0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_1 != ($struct_get(($struct_loc($self$0, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc($self$0, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), q$a_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@674.3--674.90
    assume ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@675.3--675.353

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), q$a_3): int) }
      0 <= q$a_3 && q$a_3 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), q$a_3): int) != 0 ==> ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), q$a_3): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$0, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@676.3--676.409

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$0, 0)): Int) && ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), q$a_5): int) }
      0 <= q$a_5 && q$a_5 <= 1461501637330902918203684832716283019655932542975 ==> q$a_5 != ($struct_get(($struct_loc($self$0, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), q$a_5): int) == 0 ==> ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), q$a_5): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@677.3--677.397

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    havoc QPMask;

    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Inhale might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@677.10--677.397) [203]"}
        (forall q$a_7: int, q$v_1: int, q$a_7_1: int, q$v_1_1: int ::
        { neverTriggered2(q$a_7, q$v_1), neverTriggered2(q$a_7_1, q$v_1_1) }
        ((((q$a_7 != q$a_7_1 && q$v_1 != q$v_1_1) && (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), q$a_7): int))))) && (0 <= q$a_7_1 && (q$a_7_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1_1 && q$v_1_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1_1 == ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), q$a_7_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_7 != q$a_7_1 || q$v_1 != q$v_1_1
      );

    // -- Define Inverse Function
      assume (forall q$a_7: int, q$v_1: int ::
        { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Mask[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] }
        (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), q$a_7): int)))) && NoPerm < FullPerm ==> (invRecv1(18, q$a_7, q$v_1) == q$a_7 && invRecv2(18, q$a_7, q$v_1) == q$v_1) && qpRange2(18, q$a_7, q$v_1)
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { invRecv1($tag, $to, $amount), invRecv2($tag, $to, $amount) }
        ((0 <= invRecv1($tag, $to, $amount) && (invRecv1($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv2($tag, $to, $amount) && invRecv2($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv2($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), invRecv1($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange2($tag, $to, $amount) ==> (18 == $tag && invRecv1($tag, $to, $amount) == $to) && invRecv2($tag, $to, $amount) == $amount
      );

    // -- Define updated permissions
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        ((0 <= invRecv1($tag, $to, $amount) && (invRecv1($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv2($tag, $to, $amount) && invRecv2($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv2($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), invRecv1($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange2($tag, $to, $amount) ==> (NoPerm < FullPerm ==> (18 == $tag && invRecv1($tag, $to, $amount) == $to) && invRecv2($tag, $to, $amount) == $amount) && QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)] + FullPerm
      );

    // -- Define independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        !(((0 <= invRecv1($tag, $to, $amount) && (invRecv1($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv2($tag, $to, $amount) && invRecv2($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv2($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), invRecv1($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange2($tag, $to, $amount)) ==> QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@678.3--678.267

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $a_3): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $a_3): int) >= ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $a_3): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc($self$1, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@679.3--679.111
    if (($struct_get(($struct_loc($self$1, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc($self$1, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 0)): Int) ==
  //   ($struct_get($struct_loc($self$0, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@680.3--680.100
    assume ($struct_get(($struct_loc($self$1, 0): int)): int) == ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$1, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@681.3--681.103
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$1, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) <=
  //   ($struct_get($struct_loc($self$1, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@682.3--682.224
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@683.3--683.328
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) == ($map_sum(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc($self$1, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@684.3--684.177
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 4)): Int) >=
  //   ($struct_get($struct_loc($self$0, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@685.3--685.100
    assume ($struct_get(($struct_loc($self$1, 4): int)): int) >= ($struct_get(($struct_loc($self$0, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$1, 4)): Int) ==
  //   ($struct_get($struct_loc($self$0, 4)): Int) &&
  //   ($struct_get($struct_loc($self$1, 3)): Int) ==
  //   ($struct_get($struct_loc($self$0, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@686.3--686.243
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$1, 4): int)): int) == ($struct_get(($struct_loc($self$0, 4): int)): int);
      assume ($struct_get(($struct_loc($self$1, 3): int)): int) == ($struct_get(($struct_loc($self$0, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@687.3--687.58
    assume ($struct_get(($struct_loc($self$1, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 3)): Int) !=
  //   ($struct_get($struct_loc($self$1, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@688.3--688.100
    assume ($struct_get(($struct_loc($self$1, 3): int)): int) != ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@689.3--689.131
    assume ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@690.3--690.182
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc($self$1, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@691.3--691.223
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == ($struct_get(($struct_loc($self$1, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@692.3--692.413
    assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$1, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc($self$1, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@693.3--693.532

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$1, 3)): Int) && q$a != ($struct_get($struct_loc($self$1, 0)): Int) ==> ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_10: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_10): int) }
      0 <= q$a_10 && q$a_10 <= 1461501637330902918203684832716283019655932542975 ==> q$a_10 != ($struct_get(($struct_loc($self$1, 3): int)): int) && q$a_10 != ($struct_get(($struct_loc($self$1, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_10): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_10): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_10): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@694.3--694.90
    assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@695.3--695.353

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_12: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_12): int) }
      0 <= q$a_12 && q$a_12 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_12): int) != 0 ==> ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_12): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$1, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@696.3--696.409

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$1, 0)): Int) && ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_14: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_14): int) }
      0 <= q$a_14 && q$a_14 <= 1461501637330902918203684832716283019655932542975 ==> q$a_14 != ($struct_get(($struct_loc($self$1, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_14): int) == 0 ==> ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_14): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@697.3--697.397

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    havoc QPMask;

    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Inhale might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@697.10--697.397) [204]"}
        (forall q$a_16: int, q$v_4: int, q$a_16_1: int, q$v_4_1: int ::
        { neverTriggered4(q$a_16, q$v_4), neverTriggered4(q$a_16_1, q$v_4_1) }
        ((((q$a_16 != q$a_16_1 && q$v_4 != q$v_4_1) && (0 <= q$a_16 && (q$a_16 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_4 && q$v_4 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_4 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_16): int))))) && (0 <= q$a_16_1 && (q$a_16_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_4_1 && q$v_4_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_4_1 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_16_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_16 != q$a_16_1 || q$v_4 != q$v_4_1
      );

    // -- Define Inverse Function
      assume (forall q$a_16: int, q$v_4: int ::
        { Heap[null, $accessible$withdraw(18, q$a_16, q$v_4)] } { Mask[null, $accessible$withdraw(18, q$a_16, q$v_4)] } { Heap[null, $accessible$withdraw(18, q$a_16, q$v_4)] }
        (0 <= q$a_16 && (q$a_16 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_4 && q$v_4 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_4 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_16): int)))) && NoPerm < FullPerm ==> (invRecv3(18, q$a_16, q$v_4) == q$a_16 && invRecv4(18, q$a_16, q$v_4) == q$v_4) && qpRange4(18, q$a_16, q$v_4)
      );
      assume (forall $tag_1: int, $to_1: int, $amount_1: int ::
        { invRecv3($tag_1, $to_1, $amount_1), invRecv4($tag_1, $to_1, $amount_1) }
        ((0 <= invRecv3($tag_1, $to_1, $amount_1) && (invRecv3($tag_1, $to_1, $amount_1) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv4($tag_1, $to_1, $amount_1) && invRecv4($tag_1, $to_1, $amount_1) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv4($tag_1, $to_1, $amount_1) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv3($tag_1, $to_1, $amount_1)): int)))) && NoPerm < FullPerm) && qpRange4($tag_1, $to_1, $amount_1) ==> (18 == $tag_1 && invRecv3($tag_1, $to_1, $amount_1) == $to_1) && invRecv4($tag_1, $to_1, $amount_1) == $amount_1
      );

    // -- Define updated permissions
      assume (forall $tag_1: int, $to_1: int, $amount_1: int ::
        { QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] }
        ((0 <= invRecv3($tag_1, $to_1, $amount_1) && (invRecv3($tag_1, $to_1, $amount_1) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv4($tag_1, $to_1, $amount_1) && invRecv4($tag_1, $to_1, $amount_1) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv4($tag_1, $to_1, $amount_1) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv3($tag_1, $to_1, $amount_1)): int)))) && NoPerm < FullPerm) && qpRange4($tag_1, $to_1, $amount_1) ==> (NoPerm < FullPerm ==> (18 == $tag_1 && invRecv3($tag_1, $to_1, $amount_1) == $to_1) && invRecv4($tag_1, $to_1, $amount_1) == $amount_1) && QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] == Mask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] + FullPerm
      );

    // -- Define independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
      );
      assume (forall $tag_1: int, $to_1: int, $amount_1: int ::
        { QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] }
        !(((0 <= invRecv3($tag_1, $to_1, $amount_1) && (invRecv3($tag_1, $to_1, $amount_1) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv4($tag_1, $to_1, $amount_1) && invRecv4($tag_1, $to_1, $amount_1) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv4($tag_1, $to_1, $amount_1) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv3($tag_1, $to_1, $amount_1)): int)))) && NoPerm < FullPerm) && qpRange4($tag_1, $to_1, $amount_1)) ==> QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] == Mask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@698.3--698.267

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $a_5): int) }
      ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), $a_5): int) >= ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $a_5): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc($self$2, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@699.3--699.111
    if (($struct_get(($struct_loc($self$2, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc($self$2, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 0)): Int) ==
  //   ($struct_get($struct_loc($self$1, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@700.3--700.100
    assume ($struct_get(($struct_loc($self$2, 0): int)): int) == ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$2, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@701.3--701.103
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$2, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$2, 4)): Int) <=
  //   ($struct_get($struct_loc($self$2, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@702.3--702.224
    if (!($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$2, 4): int)): int) <= ($struct_get(($struct_loc($self$2, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$2, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@703.3--703.328
    if (!($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$2, 4): int)): int) == ($map_sum(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc($self$2, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@704.3--704.177
    if (($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc($self$2, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 4)): Int) >=
  //   ($struct_get($struct_loc($self$1, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@705.3--705.100
    assume ($struct_get(($struct_loc($self$2, 4): int)): int) >= ($struct_get(($struct_loc($self$1, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$2, 4)): Int) ==
  //   ($struct_get($struct_loc($self$1, 4)): Int) &&
  //   ($struct_get($struct_loc($self$2, 3)): Int) ==
  //   ($struct_get($struct_loc($self$1, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@706.3--706.243
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$2, 4): int)): int) == ($struct_get(($struct_loc($self$1, 4): int)): int);
      assume ($struct_get(($struct_loc($self$2, 3): int)): int) == ($struct_get(($struct_loc($self$1, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@707.3--707.58
    assume ($struct_get(($struct_loc($self$2, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 3)): Int) !=
  //   ($struct_get($struct_loc($self$2, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@708.3--708.100
    assume ($struct_get(($struct_loc($self$2, 3): int)): int) != ($struct_get(($struct_loc($self$2, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@709.3--709.131
    assume ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@710.3--710.182
    if (!($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc($self$2, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@711.3--711.223
    if (($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 0): int)): int)): int) == ($struct_get(($struct_loc($self$2, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc($self$2, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@712.3--712.413
    assume ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 3): int)): int)): int) + ($struct_get(($struct_loc($self$2, 4): int)): int) + ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$2, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc($self$2, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@713.3--713.532

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$2, 3)): Int) && q$a != ($struct_get($struct_loc($self$2, 0)): Int) ==> ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_19: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_19): int) }
      0 <= q$a_19 && q$a_19 <= 1461501637330902918203684832716283019655932542975 ==> q$a_19 != ($struct_get(($struct_loc($self$2, 3): int)): int) && q$a_19 != ($struct_get(($struct_loc($self$2, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), q$a_19): int) + ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_19): int) == ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_19): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@714.3--714.90
    assume ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@715.3--715.353

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_21: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_21): int) }
      0 <= q$a_21 && q$a_21 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_21): int) != 0 ==> ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_21): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$2, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@716.3--716.409

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$2, 0)): Int) && ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_23: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_23): int) }
      0 <= q$a_23 && q$a_23 <= 1461501637330902918203684832716283019655932542975 ==> q$a_23 != ($struct_get(($struct_loc($self$2, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_23): int) == 0 ==> ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), q$a_23): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@717.3--717.397

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    havoc QPMask;

    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Inhale might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@717.10--717.397) [205]"}
        (forall q$a_25: int, q$v_7: int, q$a_25_1: int, q$v_7_1: int ::
        { neverTriggered6(q$a_25, q$v_7), neverTriggered6(q$a_25_1, q$v_7_1) }
        ((((q$a_25 != q$a_25_1 && q$v_7 != q$v_7_1) && (0 <= q$a_25 && (q$a_25 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_7 && q$v_7 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_7 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_25): int))))) && (0 <= q$a_25_1 && (q$a_25_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_7_1 && q$v_7_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_7_1 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_25_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_25 != q$a_25_1 || q$v_7 != q$v_7_1
      );

    // -- Define Inverse Function
      assume (forall q$a_25: int, q$v_7: int ::
        { Heap[null, $accessible$withdraw(18, q$a_25, q$v_7)] } { Mask[null, $accessible$withdraw(18, q$a_25, q$v_7)] } { Heap[null, $accessible$withdraw(18, q$a_25, q$v_7)] }
        (0 <= q$a_25 && (q$a_25 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_7 && q$v_7 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_7 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_25): int)))) && NoPerm < FullPerm ==> (invRecv5(18, q$a_25, q$v_7) == q$a_25 && invRecv6(18, q$a_25, q$v_7) == q$v_7) && qpRange6(18, q$a_25, q$v_7)
      );
      assume (forall $tag_2: int, $to_2: int, $amount_2: int ::
        { invRecv5($tag_2, $to_2, $amount_2), invRecv6($tag_2, $to_2, $amount_2) }
        ((0 <= invRecv5($tag_2, $to_2, $amount_2) && (invRecv5($tag_2, $to_2, $amount_2) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv6($tag_2, $to_2, $amount_2) && invRecv6($tag_2, $to_2, $amount_2) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv6($tag_2, $to_2, $amount_2) == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), invRecv5($tag_2, $to_2, $amount_2)): int)))) && NoPerm < FullPerm) && qpRange6($tag_2, $to_2, $amount_2) ==> (18 == $tag_2 && invRecv5($tag_2, $to_2, $amount_2) == $to_2) && invRecv6($tag_2, $to_2, $amount_2) == $amount_2
      );

    // -- Define updated permissions
      assume (forall $tag_2: int, $to_2: int, $amount_2: int ::
        { QPMask[null, $accessible$withdraw($tag_2, $to_2, $amount_2)] }
        ((0 <= invRecv5($tag_2, $to_2, $amount_2) && (invRecv5($tag_2, $to_2, $amount_2) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv6($tag_2, $to_2, $amount_2) && invRecv6($tag_2, $to_2, $amount_2) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv6($tag_2, $to_2, $amount_2) == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), invRecv5($tag_2, $to_2, $amount_2)): int)))) && NoPerm < FullPerm) && qpRange6($tag_2, $to_2, $amount_2) ==> (NoPerm < FullPerm ==> (18 == $tag_2 && invRecv5($tag_2, $to_2, $amount_2) == $to_2) && invRecv6($tag_2, $to_2, $amount_2) == $amount_2) && QPMask[null, $accessible$withdraw($tag_2, $to_2, $amount_2)] == Mask[null, $accessible$withdraw($tag_2, $to_2, $amount_2)] + FullPerm
      );

    // -- Define independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
      );
      assume (forall $tag_2: int, $to_2: int, $amount_2: int ::
        { QPMask[null, $accessible$withdraw($tag_2, $to_2, $amount_2)] }
        !(((0 <= invRecv5($tag_2, $to_2, $amount_2) && (invRecv5($tag_2, $to_2, $amount_2) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv6($tag_2, $to_2, $amount_2) && invRecv6($tag_2, $to_2, $amount_2) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv6($tag_2, $to_2, $amount_2) == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), invRecv5($tag_2, $to_2, $amount_2)): int)))) && NoPerm < FullPerm) && qpRange6($tag_2, $to_2, $amount_2)) ==> QPMask[null, $accessible$withdraw($tag_2, $to_2, $amount_2)] == Mask[null, $accessible$withdraw($tag_2, $to_2, $amount_2)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc($self$2, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@718.3--718.111
    if (($struct_get(($struct_loc($self$2, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@718.10--718.111) [206]"}
        ($struct_get(($struct_loc($self$2, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 0)): Int) ==
  //   ($struct_get($struct_loc($self$0, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@719.3--719.100
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 0)): Int) == ($struct_get($struct_loc($self$0, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@719.10--719.100) [207]"}
      ($struct_get(($struct_loc($self$2, 0): int)): int) == ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$2, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@720.3--720.103
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@720.10--720.103) [208]"}
        ($struct_get(($struct_loc($self$2, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert !($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$2, 4)): Int) <=
  //   ($struct_get($struct_loc($self$2, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@721.3--721.224
    if (!($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc($self$2, 4)): Int) <= ($struct_get($struct_loc($self$2, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@721.10--721.224) [209]"}
        ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$2, 4): int)): int) <= ($struct_get(($struct_loc($self$2, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert !($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$2, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@722.3--722.328
    if (!($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc($self$2, 4)): Int) == ($map_sum(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@722.10--722.328) [210]"}
        ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$2, 4): int)): int) == ($map_sum(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc($self$2, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@723.3--723.177
    if (($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc($self$2, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@723.10--723.177) [211]"}
        ($map_sum(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc($self$2, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 4)): Int) >=
  //   ($struct_get($struct_loc($self$0, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@724.3--724.100
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 4)): Int) >= ($struct_get($struct_loc($self$0, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@724.10--724.100) [212]"}
      ($struct_get(($struct_loc($self$2, 4): int)): int) >= ($struct_get(($struct_loc($self$0, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$2, 4)): Int) ==
  //   ($struct_get($struct_loc($self$0, 4)): Int) &&
  //   ($struct_get($struct_loc($self$2, 3)): Int) ==
  //   ($struct_get($struct_loc($self$0, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@725.3--725.243
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 4)): Int) == ($struct_get($struct_loc($self$0, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@725.10--725.243) [213]"}
        ($struct_get(($struct_loc($self$2, 4): int)): int) == ($struct_get(($struct_loc($self$0, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 3)): Int) == ($struct_get($struct_loc($self$0, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@725.10--725.243) [214]"}
        ($struct_get(($struct_loc($self$2, 3): int)): int) == ($struct_get(($struct_loc($self$0, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@726.3--726.58
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@726.10--726.58) [215]"}
      ($struct_get(($struct_loc($self$2, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 3)): Int) !=
  //   ($struct_get($struct_loc($self$2, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@727.3--727.100
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$2, 3)): Int) != ($struct_get($struct_loc($self$2, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@727.10--727.100) [216]"}
      ($struct_get(($struct_loc($self$2, 3): int)): int) != ($struct_get(($struct_loc($self$2, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@728.3--728.131
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$2, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@728.10--728.131) [217]"}
      ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert !($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@729.3--729.182
    if (!($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@729.10--729.182) [218]"}
        ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$2, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc($self$2, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@730.3--730.223
    if (($struct_get(($struct_loc($self$2, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2, 0)): Int)): Int) == ($struct_get($struct_loc($self$2, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@730.10--730.223) [219]"}
        ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 0): int)): int)): int) == ($struct_get(($struct_loc($self$2, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc($self$2, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$2,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@731.3--731.413
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$2, 3)): Int)): Int) + ($struct_get($struct_loc($self$2, 4)): Int) + ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$2, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$2, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@731.10--731.413) [220]"}
      ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 3): int)): int)): int) + ($struct_get(($struct_loc($self$2, 4): int)): int) + ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$2, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$2, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc($self$2, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@732.3--732.532

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$2, 3)): Int) && q$a != ($struct_get($struct_loc($self$2, 0)): Int) ==> ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_28 && q$a_28 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_28 != ($struct_get(($struct_loc($self$2, 3): int)): int) && q$a_28 != ($struct_get(($struct_loc($self$2, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@732.11--732.531) [221]"}
            ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), q$a_28): int) + ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_28): int) == ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_28): int);
        }
      }
      assume false;
    }
    assume (forall q$a_29_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_29_1): int) }
      0 <= q$a_29_1 && q$a_29_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_29_1 != ($struct_get(($struct_loc($self$2, 3): int)): int) && q$a_29_1 != ($struct_get(($struct_loc($self$2, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), q$a_29_1): int) + ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_29_1): int) == ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_29_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: assert ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@733.3--733.90
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@733.10--733.90) [222]"}
      ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@734.3--734.353

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_31 && q$a_31 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_31): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@734.11--734.352) [223]"}
            ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_31): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_32_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_32_1): int) }
      0 <= q$a_32_1 && q$a_32_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_32_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_32_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$2, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@735.3--735.409

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$2, 0)): Int) && ($map_get(($struct_get($struct_loc($self$2, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_34 && q$a_34 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_34 != ($struct_get(($struct_loc($self$2, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_34): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$2, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@735.11--735.408) [224]"}
            ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), q$a_34): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_35_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_35_1): int) }
      0 <= q$a_35_1 && q$a_35_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_35_1 != ($struct_get(($struct_loc($self$2, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$2, 11): int)): $MapDomainType int int), q$a_35_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc($self$2, 10): int)): $MapDomainType int int), q$a_35_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: assert true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@736.3--736.397

    // -- Check definedness of true && (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc($self$2, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    AssertHeap := Heap;
    AssertMask := Mask;
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Assert might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@736.10--736.397) [227]"}
        (forall q$a_36: int, q$v_9: int, q$a_36_1: int, q$v_9_1: int ::
        { neverTriggered8(q$a_36, q$v_9), neverTriggered8(q$a_36_1, q$v_9_1) }
        ((((q$a_36 != q$a_36_1 && q$v_9 != q$v_9_1) && (0 <= q$a_36 && (q$a_36 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_9 && q$v_9 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_9 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_36): int))))) && (0 <= q$a_36_1 && (q$a_36_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_9_1 && q$v_9_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_9_1 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_36_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_36 != q$a_36_1 || q$v_9 != q$v_9_1
      );

    // -- check if sufficient permission is held
      assert {:msg "  Assert might fail. There might be insufficient permission to access $accessible$withdraw(18, q$a, q$v) (testsresourcesexamplesauction.vy.vpr@736.10--736.397) [228]"}
        (forall q$a_36: int, q$v_9: int ::
        { AssertHeap[null, $accessible$withdraw(18, q$a_36, q$v_9)] } { AssertMask[null, $accessible$withdraw(18, q$a_36, q$v_9)] } { AssertHeap[null, $accessible$withdraw(18, q$a_36, q$v_9)] }
        0 <= q$a_36 && (q$a_36 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_9 && q$v_9 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_9 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_36): int))) ==> AssertMask[null, $accessible$withdraw(18, q$a_36, q$v_9)] >= FullPerm
      );

    // -- assumptions for inverse of receiver acc($accessible$withdraw(18, q$a, q$v), write)
      assume (forall q$a_36: int, q$v_9: int ::
        { AssertHeap[null, $accessible$withdraw(18, q$a_36, q$v_9)] } { AssertMask[null, $accessible$withdraw(18, q$a_36, q$v_9)] } { AssertHeap[null, $accessible$withdraw(18, q$a_36, q$v_9)] }
        (0 <= q$a_36 && (q$a_36 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_9 && q$v_9 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_9 == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), q$a_36): int)))) && NoPerm < FullPerm ==> (invRecv7(18, q$a_36, q$v_9) == q$a_36 && invRecv8(18, q$a_36, q$v_9) == q$v_9) && qpRange8(18, q$a_36, q$v_9)
      );
      assume (forall $tag_3: int, $to_3: int, $amount_3: int ::
        { invRecv7($tag_3, $to_3, $amount_3), invRecv8($tag_3, $to_3, $amount_3) }
        ((0 <= invRecv7($tag_3, $to_3, $amount_3) && (invRecv7($tag_3, $to_3, $amount_3) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv8($tag_3, $to_3, $amount_3) && invRecv8($tag_3, $to_3, $amount_3) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv8($tag_3, $to_3, $amount_3) == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), invRecv7($tag_3, $to_3, $amount_3)): int)))) && NoPerm < FullPerm) && qpRange8($tag_3, $to_3, $amount_3) ==> (18 == $tag_3 && invRecv7($tag_3, $to_3, $amount_3) == $to_3) && invRecv8($tag_3, $to_3, $amount_3) == $amount_3
      );

    // -- assume permission updates for predicate $accessible$withdraw
      assume (forall $tag_3: int, $to_3: int, $amount_3: int ::
        { QPMask[null, $accessible$withdraw($tag_3, $to_3, $amount_3)] }
        ((0 <= invRecv7($tag_3, $to_3, $amount_3) && (invRecv7($tag_3, $to_3, $amount_3) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv8($tag_3, $to_3, $amount_3) && invRecv8($tag_3, $to_3, $amount_3) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv8($tag_3, $to_3, $amount_3) == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), invRecv7($tag_3, $to_3, $amount_3)): int)))) && NoPerm < FullPerm) && qpRange8($tag_3, $to_3, $amount_3) ==> ((18 == $tag_3 && invRecv7($tag_3, $to_3, $amount_3) == $to_3) && invRecv8($tag_3, $to_3, $amount_3) == $amount_3) && QPMask[null, $accessible$withdraw($tag_3, $to_3, $amount_3)] == AssertMask[null, $accessible$withdraw($tag_3, $to_3, $amount_3)] - FullPerm
      );
      assume (forall $tag_3: int, $to_3: int, $amount_3: int ::
        { QPMask[null, $accessible$withdraw($tag_3, $to_3, $amount_3)] }
        !(((0 <= invRecv7($tag_3, $to_3, $amount_3) && (invRecv7($tag_3, $to_3, $amount_3) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv8($tag_3, $to_3, $amount_3) && invRecv8($tag_3, $to_3, $amount_3) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv8($tag_3, $to_3, $amount_3) == ($map_get(($struct_get(($struct_loc($self$2, 6): int)): $MapDomainType int int), invRecv7($tag_3, $to_3, $amount_3)): int)))) && NoPerm < FullPerm) && qpRange8($tag_3, $to_3, $amount_3)) ==> QPMask[null, $accessible$withdraw($tag_3, $to_3, $amount_3)] == AssertMask[null, $accessible$withdraw($tag_3, $to_3, $amount_3)]
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { AssertMask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> AssertMask[o_4, f_6] == QPMask[o_4, f_6]
      );
    AssertMask := QPMask;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method $reflexivity_check
// ==================================================

procedure $reflexivity_check() returns ()
  modifies Heap, Mask;
{
  var $self$0: $StructDomainType;
  var $self$1: $StructDomainType;
  var block: $StructDomainType;
  var QPMask: MaskType;
  var q$a_10: int;
  var q$a_13: int;
  var q$a_16: int;
  var AssertHeap: HeapType;
  var AssertMask: MaskType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 0)): Int) &&
  //   ($struct_get($struct_loc($self$0, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@747.3--747.158
    assume 0 <= ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume ($struct_get(($struct_loc($self$0, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 1)): Int) &&
  //   ($struct_get($struct_loc($self$0, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@748.3--748.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 1): int)): int);
    assume ($struct_get(($struct_loc($self$0, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 2)): Int) &&
  //   ($struct_get($struct_loc($self$0, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@749.3--749.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 2): int)): int);
    assume ($struct_get(($struct_loc($self$0, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 3)): Int) &&
  //   ($struct_get($struct_loc($self$0, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@750.3--750.158
    assume 0 <= ($struct_get(($struct_loc($self$0, 3): int)): int);
    assume ($struct_get(($struct_loc($self$0, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 4)): Int) &&
  //   ($struct_get($struct_loc($self$0, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@751.3--751.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 4): int)): int);
    assume ($struct_get(($struct_loc($self$0, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@752.3--752.355

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@753.3--753.263

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc($self$0, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc($self$0, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$0, 7)): Int) &&
  //   ($struct_get($struct_loc($self$0, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@754.3--754.187
    assume 0 <= ($struct_get(($struct_loc($self$0, 7): int)): int);
    assume ($struct_get(($struct_loc($self$0, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc($self$0, 8)): Int) &&
  //   ($struct_get($struct_loc($self$0, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@755.3--755.187
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc($self$0, 8): int)): int);
    assume ($struct_get(($struct_loc($self$0, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@756.3--756.358

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@757.3--757.266

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@758.3--758.358

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@759.3--759.266

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc($self$0, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc($self$0, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@760.3--760.89
    assume ($struct_get(($struct_loc($self$0, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 0)): Int) &&
  //   ($struct_get($struct_loc($self$1, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@761.3--761.158
    assume 0 <= ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume ($struct_get(($struct_loc($self$1, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 1)): Int) &&
  //   ($struct_get($struct_loc($self$1, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@762.3--762.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 1): int)): int);
    assume ($struct_get(($struct_loc($self$1, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 2)): Int) &&
  //   ($struct_get($struct_loc($self$1, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@763.3--763.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 2): int)): int);
    assume ($struct_get(($struct_loc($self$1, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 3)): Int) &&
  //   ($struct_get($struct_loc($self$1, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@764.3--764.158
    assume 0 <= ($struct_get(($struct_loc($self$1, 3): int)): int);
    assume ($struct_get(($struct_loc($self$1, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 4)): Int) &&
  //   ($struct_get($struct_loc($self$1, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@765.3--765.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 4): int)): int);
    assume ($struct_get(($struct_loc($self$1, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@766.3--766.355

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_5): int) && ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@767.3--767.263

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_7: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_7): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), $q0_7): int) <= ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($self$1, 7)): Int) &&
  //   ($struct_get($struct_loc($self$1, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@768.3--768.187
    assume 0 <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    assume ($struct_get(($struct_loc($self$1, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc($self$1, 8)): Int) &&
  //   ($struct_get($struct_loc($self$1, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@769.3--769.187
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc($self$1, 8): int)): int);
    assume ($struct_get(($struct_loc($self$1, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@770.3--770.358

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_5): int) && ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@771.3--771.266

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_7: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_7): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $q1_7): int) <= ($map_sum(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@772.3--772.358

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_5): int) && ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@773.3--773.266

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_7: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_7): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), $q2_7): int) <= ($map_sum(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@774.3--774.89
    assume ($struct_get(($struct_loc($self$1, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@775.3--775.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@776.3--776.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@777.3--777.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@778.3--778.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@779.3--779.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@780.3--780.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@781.3--781.267

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc($self$0, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_1_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $a_1_1): int) }
      ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), $a_1_1): int) >= ($map_get(($struct_get(($struct_loc($self$0, 10): int)): $MapDomainType int int), $a_1_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc($self$1, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@782.3--782.111
    if (($struct_get(($struct_loc($self$1, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc($self$1, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 0)): Int) ==
  //   ($struct_get($struct_loc($self$0, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@783.3--783.100
    assume ($struct_get(($struct_loc($self$1, 0): int)): int) == ($struct_get(($struct_loc($self$0, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$1, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@784.3--784.103
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$1, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) <=
  //   ($struct_get($struct_loc($self$1, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@785.3--785.224
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@786.3--786.328
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) == ($map_sum(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc($self$1, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@787.3--787.177
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 4)): Int) >=
  //   ($struct_get($struct_loc($self$0, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@788.3--788.100
    assume ($struct_get(($struct_loc($self$1, 4): int)): int) >= ($struct_get(($struct_loc($self$0, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$0, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$1, 4)): Int) ==
  //   ($struct_get($struct_loc($self$0, 4)): Int) &&
  //   ($struct_get($struct_loc($self$1, 3)): Int) ==
  //   ($struct_get($struct_loc($self$0, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@789.3--789.243
    if (($struct_get(($struct_loc($self$0, 5): int)): bool)) {
      assume ($struct_get(($struct_loc($self$1, 4): int)): int) == ($struct_get(($struct_loc($self$0, 4): int)): int);
      assume ($struct_get(($struct_loc($self$1, 3): int)): int) == ($struct_get(($struct_loc($self$0, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@790.3--790.58
    assume ($struct_get(($struct_loc($self$1, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 3)): Int) !=
  //   ($struct_get($struct_loc($self$1, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@791.3--791.100
    assume ($struct_get(($struct_loc($self$1, 3): int)): int) != ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@792.3--792.131
    assume ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@793.3--793.182
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc($self$1, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@794.3--794.223
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == ($struct_get(($struct_loc($self$1, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@795.3--795.413
    assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$1, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc($self$1, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@796.3--796.532

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$1, 3)): Int) && q$a != ($struct_get($struct_loc($self$1, 0)): Int) ==> ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_1): int) }
      0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_1 != ($struct_get(($struct_loc($self$1, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc($self$1, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@797.3--797.90
    assume ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@798.3--798.353

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_3: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_3): int) }
      0 <= q$a_3 && q$a_3 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_3): int) != 0 ==> ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_3): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$1, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@799.3--799.409

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$1, 0)): Int) && ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_5: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_5): int) }
      0 <= q$a_5 && q$a_5 <= 1461501637330902918203684832716283019655932542975 ==> q$a_5 != ($struct_get(($struct_loc($self$1, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_5): int) == 0 ==> ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_5): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@800.3--800.397

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    havoc QPMask;

    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Inhale might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@800.10--800.397) [229]"}
        (forall q$a_7: int, q$v_1: int, q$a_7_1: int, q$v_1_1: int ::
        { neverTriggered10(q$a_7, q$v_1), neverTriggered10(q$a_7_1, q$v_1_1) }
        ((((q$a_7 != q$a_7_1 && q$v_1 != q$v_1_1) && (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_7): int))))) && (0 <= q$a_7_1 && (q$a_7_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1_1 && q$v_1_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1_1 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_7_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_7 != q$a_7_1 || q$v_1 != q$v_1_1
      );

    // -- Define Inverse Function
      assume (forall q$a_7: int, q$v_1: int ::
        { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Mask[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] }
        (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_7): int)))) && NoPerm < FullPerm ==> (invRecv9(18, q$a_7, q$v_1) == q$a_7 && invRecv10(18, q$a_7, q$v_1) == q$v_1) && qpRange10(18, q$a_7, q$v_1)
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { invRecv9($tag, $to, $amount), invRecv10($tag, $to, $amount) }
        ((0 <= invRecv9($tag, $to, $amount) && (invRecv9($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv10($tag, $to, $amount) && invRecv10($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv10($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv9($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange10($tag, $to, $amount) ==> (18 == $tag && invRecv9($tag, $to, $amount) == $to) && invRecv10($tag, $to, $amount) == $amount
      );

    // -- Define updated permissions
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        ((0 <= invRecv9($tag, $to, $amount) && (invRecv9($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv10($tag, $to, $amount) && invRecv10($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv10($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv9($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange10($tag, $to, $amount) ==> (NoPerm < FullPerm ==> (18 == $tag && invRecv9($tag, $to, $amount) == $to) && invRecv10($tag, $to, $amount) == $amount) && QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)] + FullPerm
      );

    // -- Define independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        !(((0 <= invRecv9($tag, $to, $amount) && (invRecv9($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv10($tag, $to, $amount) && invRecv10($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv10($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv9($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange10($tag, $to, $amount)) ==> QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc($self$1, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@801.3--801.111
    if (($struct_get(($struct_loc($self$1, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@801.10--801.111) [230]"}
        ($struct_get(($struct_loc($self$1, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 0)): Int) ==
  //   ($struct_get($struct_loc($self$1, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@802.3--802.100
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 0)): Int) == ($struct_get($struct_loc($self$1, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@802.10--802.100) [231]"}
      ($struct_get(($struct_loc($self$1, 0): int)): int) == ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$1, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@803.3--803.103
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@803.10--803.103) [232]"}
        ($struct_get(($struct_loc($self$1, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) <=
  //   ($struct_get($struct_loc($self$1, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@804.3--804.224
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc($self$1, 4)): Int) <= ($struct_get($struct_loc($self$1, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@804.10--804.224) [233]"}
        ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@805.3--805.328
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc($self$1, 4)): Int) == ($map_sum(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@805.10--805.328) [234]"}
        ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) == ($map_sum(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc($self$1, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@806.3--806.177
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc($self$1, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@806.10--806.177) [235]"}
        ($map_sum(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc($self$1, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 4)): Int) >=
  //   ($struct_get($struct_loc($self$1, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@807.3--807.100
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 4)): Int) >= ($struct_get($struct_loc($self$1, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@807.10--807.100) [236]"}
      ($struct_get(($struct_loc($self$1, 4): int)): int) >= ($struct_get(($struct_loc($self$1, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($struct_get($struct_loc($self$1, 4)): Int) ==
  //   ($struct_get($struct_loc($self$1, 4)): Int) &&
  //   ($struct_get($struct_loc($self$1, 3)): Int) ==
  //   ($struct_get($struct_loc($self$1, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@808.3--808.243
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 4)): Int) == ($struct_get($struct_loc($self$1, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@808.10--808.243) [237]"}
        ($struct_get(($struct_loc($self$1, 4): int)): int) == ($struct_get(($struct_loc($self$1, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 3)): Int) == ($struct_get($struct_loc($self$1, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@808.10--808.243) [238]"}
        ($struct_get(($struct_loc($self$1, 3): int)): int) == ($struct_get(($struct_loc($self$1, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@809.3--809.58
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@809.10--809.58) [239]"}
      ($struct_get(($struct_loc($self$1, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 3)): Int) !=
  //   ($struct_get($struct_loc($self$1, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@810.3--810.100
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc($self$1, 3)): Int) != ($struct_get($struct_loc($self$1, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@810.10--810.100) [240]"}
      ($struct_get(($struct_loc($self$1, 3): int)): int) != ($struct_get(($struct_loc($self$1, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@811.3--811.131
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@811.10--811.131) [241]"}
      ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert !($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@812.3--812.182
    if (!($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@812.10--812.182) [242]"}
        ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($struct_get($struct_loc($self$1, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc($self$1, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@813.3--813.223
    if (($struct_get(($struct_loc($self$1, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1, 0)): Int)): Int) == ($struct_get($struct_loc($self$1, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@813.10--813.223) [243]"}
        ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 0): int)): int)): int) == ($struct_get(($struct_loc($self$1, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: assert ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc($self$1, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$1,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@814.3--814.413
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), ($struct_get($struct_loc($self$1, 3)): Int)): Int) + ($struct_get($struct_loc($self$1, 4)): Int) + ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), ($struct_get($struct_loc($self$1, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), ($struct_get($struct_loc($self$1, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@814.10--814.413) [244]"}
      ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int) + ($struct_get(($struct_loc($self$1, 4): int)): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc($self$1, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$1, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc($self$1, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@815.3--815.532

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$1, 3)): Int) && q$a != ($struct_get($struct_loc($self$1, 0)): Int) ==> ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_10 && q$a_10 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_10 != ($struct_get(($struct_loc($self$1, 3): int)): int) && q$a_10 != ($struct_get(($struct_loc($self$1, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@815.11--815.531) [245]"}
            ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_10): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_10): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_10): int);
        }
      }
      assume false;
    }
    assume (forall q$a_11_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_11_1): int) }
      0 <= q$a_11_1 && q$a_11_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_11_1 != ($struct_get(($struct_loc($self$1, 3): int)): int) && q$a_11_1 != ($struct_get(($struct_loc($self$1, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_11_1): int) + ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_11_1): int) == ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_11_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: assert ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@816.3--816.90
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@816.10--816.90) [246]"}
      ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@817.3--817.353

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_13 && q$a_13 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_13): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@817.11--817.352) [247]"}
            ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_13): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_14_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_14_1): int) }
      0 <= q$a_14_1 && q$a_14_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_14_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_14_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc($self$1, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@818.3--818.409

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc($self$1, 0)): Int) && ($map_get(($struct_get($struct_loc($self$1, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_16 && q$a_16 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_16 != ($struct_get(($struct_loc($self$1, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_16): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc($self$1, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@818.11--818.408) [248]"}
            ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_16): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_17_1: int ::
      { ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_17_1): int) }
      0 <= q$a_17_1 && q$a_17_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_17_1 != ($struct_get(($struct_loc($self$1, 0): int)): int) && ($map_get(($struct_get(($struct_loc($self$1, 11): int)): $MapDomainType int int), q$a_17_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc($self$1, 10): int)): $MapDomainType int int), q$a_17_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: assert true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@819.3--819.397

    // -- Check definedness of true && (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc($self$1, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    AssertHeap := Heap;
    AssertMask := Mask;
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Assert might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@819.10--819.397) [251]"}
        (forall q$a_18: int, q$v_3: int, q$a_18_1: int, q$v_3_1: int ::
        { neverTriggered12(q$a_18, q$v_3), neverTriggered12(q$a_18_1, q$v_3_1) }
        ((((q$a_18 != q$a_18_1 && q$v_3 != q$v_3_1) && (0 <= q$a_18 && (q$a_18 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_3 && q$v_3 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_3 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_18): int))))) && (0 <= q$a_18_1 && (q$a_18_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_3_1 && q$v_3_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_3_1 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_18_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_18 != q$a_18_1 || q$v_3 != q$v_3_1
      );

    // -- check if sufficient permission is held
      assert {:msg "  Assert might fail. There might be insufficient permission to access $accessible$withdraw(18, q$a, q$v) (testsresourcesexamplesauction.vy.vpr@819.10--819.397) [252]"}
        (forall q$a_18: int, q$v_3: int ::
        { AssertHeap[null, $accessible$withdraw(18, q$a_18, q$v_3)] } { AssertMask[null, $accessible$withdraw(18, q$a_18, q$v_3)] } { AssertHeap[null, $accessible$withdraw(18, q$a_18, q$v_3)] }
        0 <= q$a_18 && (q$a_18 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_3 && q$v_3 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_3 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_18): int))) ==> AssertMask[null, $accessible$withdraw(18, q$a_18, q$v_3)] >= FullPerm
      );

    // -- assumptions for inverse of receiver acc($accessible$withdraw(18, q$a, q$v), write)
      assume (forall q$a_18: int, q$v_3: int ::
        { AssertHeap[null, $accessible$withdraw(18, q$a_18, q$v_3)] } { AssertMask[null, $accessible$withdraw(18, q$a_18, q$v_3)] } { AssertHeap[null, $accessible$withdraw(18, q$a_18, q$v_3)] }
        (0 <= q$a_18 && (q$a_18 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_3 && q$v_3 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_3 == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), q$a_18): int)))) && NoPerm < FullPerm ==> (invRecv11(18, q$a_18, q$v_3) == q$a_18 && invRecv12(18, q$a_18, q$v_3) == q$v_3) && qpRange12(18, q$a_18, q$v_3)
      );
      assume (forall $tag_1: int, $to_1: int, $amount_1: int ::
        { invRecv11($tag_1, $to_1, $amount_1), invRecv12($tag_1, $to_1, $amount_1) }
        ((0 <= invRecv11($tag_1, $to_1, $amount_1) && (invRecv11($tag_1, $to_1, $amount_1) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv12($tag_1, $to_1, $amount_1) && invRecv12($tag_1, $to_1, $amount_1) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv12($tag_1, $to_1, $amount_1) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv11($tag_1, $to_1, $amount_1)): int)))) && NoPerm < FullPerm) && qpRange12($tag_1, $to_1, $amount_1) ==> (18 == $tag_1 && invRecv11($tag_1, $to_1, $amount_1) == $to_1) && invRecv12($tag_1, $to_1, $amount_1) == $amount_1
      );

    // -- assume permission updates for predicate $accessible$withdraw
      assume (forall $tag_1: int, $to_1: int, $amount_1: int ::
        { QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] }
        ((0 <= invRecv11($tag_1, $to_1, $amount_1) && (invRecv11($tag_1, $to_1, $amount_1) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv12($tag_1, $to_1, $amount_1) && invRecv12($tag_1, $to_1, $amount_1) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv12($tag_1, $to_1, $amount_1) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv11($tag_1, $to_1, $amount_1)): int)))) && NoPerm < FullPerm) && qpRange12($tag_1, $to_1, $amount_1) ==> ((18 == $tag_1 && invRecv11($tag_1, $to_1, $amount_1) == $to_1) && invRecv12($tag_1, $to_1, $amount_1) == $amount_1) && QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] == AssertMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] - FullPerm
      );
      assume (forall $tag_1: int, $to_1: int, $amount_1: int ::
        { QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] }
        !(((0 <= invRecv11($tag_1, $to_1, $amount_1) && (invRecv11($tag_1, $to_1, $amount_1) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv12($tag_1, $to_1, $amount_1) && invRecv12($tag_1, $to_1, $amount_1) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv12($tag_1, $to_1, $amount_1) == ($map_get(($struct_get(($struct_loc($self$1, 6): int)): $MapDomainType int int), invRecv11($tag_1, $to_1, $amount_1)): int)))) && NoPerm < FullPerm) && qpRange12($tag_1, $to_1, $amount_1)) ==> QPMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)] == AssertMask[null, $accessible$withdraw($tag_1, $to_1, $amount_1)]
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { AssertMask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> AssertMask[o_4, f_6] == QPMask[o_4, f_6]
      );
    AssertMask := QPMask;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method $forced_ether_check
// ==================================================

procedure $forced_ether_check() returns ()
  modifies Heap, Mask;
{
  var self: $StructDomainType;
  var $pre_self: $StructDomainType;
  var block: $StructDomainType;
  var $havoc: int;
  var QPMask: MaskType;
  var $pre_$contracts: ($MapDomainType int $StructDomainType);
  var $contracts: ($MapDomainType int $StructDomainType);

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@831.3--831.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@832.3--832.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@833.3--833.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@834.3--834.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@835.3--835.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@836.3--836.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@837.3--837.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@838.3--838.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@839.3--839.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@840.3--840.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@841.3--841.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@842.3--842.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@843.3--843.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@844.3--844.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($pre_self, 0)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@845.3--845.162
    assume 0 <= ($struct_get(($struct_loc($pre_self, 0): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($pre_self, 1)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@846.3--846.191
    assume 0 <= ($struct_get(($struct_loc($pre_self, 1): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($pre_self, 2)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@847.3--847.191
    assume 0 <= ($struct_get(($struct_loc($pre_self, 2): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($pre_self, 3)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@848.3--848.162
    assume 0 <= ($struct_get(($struct_loc($pre_self, 3): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($pre_self, 4)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@849.3--849.191
    assume 0 <= ($struct_get(($struct_loc($pre_self, 4): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@850.3--850.361

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_5: int ::
      { ($map_get(($struct_get(($struct_loc($pre_self, 6): int)): $MapDomainType int int), $q0_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($pre_self, 6): int)): $MapDomainType int int), $q0_5): int) && ($map_get(($struct_get(($struct_loc($pre_self, 6): int)): $MapDomainType int int), $q0_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@851.3--851.269

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc($pre_self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_7: int ::
      { ($map_get(($struct_get(($struct_loc($pre_self, 6): int)): $MapDomainType int int), $q0_7): int) }
      ($map_get(($struct_get(($struct_loc($pre_self, 6): int)): $MapDomainType int int), $q0_7): int) <= ($map_sum(($struct_get(($struct_loc($pre_self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc($pre_self, 7)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@852.3--852.191
    assume 0 <= ($struct_get(($struct_loc($pre_self, 7): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc($pre_self, 8)): Int) &&
  //   ($struct_get($struct_loc($pre_self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@853.3--853.191
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc($pre_self, 8): int)): int);
    assume ($struct_get(($struct_loc($pre_self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@854.3--854.364

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_5: int ::
      { ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), $q1_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), $q1_5): int) && ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), $q1_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@855.3--855.272

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_7: int ::
      { ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), $q1_7): int) }
      ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), $q1_7): int) <= ($map_sum(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@856.3--856.364

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_5: int ::
      { ($map_get(($struct_get(($struct_loc($pre_self, 11): int)): $MapDomainType int int), $q2_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc($pre_self, 11): int)): $MapDomainType int int), $q2_5): int) && ($map_get(($struct_get(($struct_loc($pre_self, 11): int)): $MapDomainType int int), $q2_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@857.3--857.272

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc($pre_self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_7: int ::
      { ($map_get(($struct_get(($struct_loc($pre_self, 11): int)): $MapDomainType int int), $q2_7): int) }
      ($map_get(($struct_get(($struct_loc($pre_self, 11): int)): $MapDomainType int int), $q2_7): int) <= ($map_sum(($struct_get(($struct_loc($pre_self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc($pre_self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@858.3--858.91
    assume ($struct_get(($struct_loc($pre_self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@859.3--859.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@860.3--860.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@861.3--861.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@862.3--862.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@863.3--863.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@864.3--864.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale $havoc >= 0 -- testsresourcesexamplesauction.vy.vpr@865.3--865.21
    assume $havoc >= 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@866.3--866.258

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) >= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@867.3--867.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@868.3--868.94
    assume ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@869.3--869.97
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@870.3--870.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@871.3--871.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@872.3--872.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@873.3--873.94
    assume ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc(self, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@874.3--874.228
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
      assume ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@875.3--875.55
    assume ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@876.3--876.94
    assume ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@877.3--877.125
    assume ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@878.3--878.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@879.3--879.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@880.3--880.392
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@881.3--881.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int) }
      0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@882.3--882.87
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@883.3--883.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) }
      0 <= q$a_3 && q$a_3 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_3): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@884.3--884.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) }
      0 <= q$a_5 && q$a_5 <= 1461501637330902918203684832716283019655932542975 ==> q$a_5 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_5): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@885.3--885.394

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    havoc QPMask;

    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Inhale might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@885.10--885.394) [253]"}
        (forall q$a_7: int, q$v_1: int, q$a_7_1: int, q$v_1_1: int ::
        { neverTriggered14(q$a_7, q$v_1), neverTriggered14(q$a_7_1, q$v_1_1) }
        ((((q$a_7 != q$a_7_1 && q$v_1 != q$v_1_1) && (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_7): int))))) && (0 <= q$a_7_1 && (q$a_7_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1_1 && q$v_1_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1_1 == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_7_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_7 != q$a_7_1 || q$v_1 != q$v_1_1
      );

    // -- Define Inverse Function
      assume (forall q$a_7: int, q$v_1: int ::
        { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Mask[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] }
        (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_7): int)))) && NoPerm < FullPerm ==> (invRecv13(18, q$a_7, q$v_1) == q$a_7 && invRecv14(18, q$a_7, q$v_1) == q$v_1) && qpRange14(18, q$a_7, q$v_1)
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { invRecv13($tag, $to, $amount), invRecv14($tag, $to, $amount) }
        ((0 <= invRecv13($tag, $to, $amount) && (invRecv13($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv14($tag, $to, $amount) && invRecv14($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv14($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), invRecv13($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange14($tag, $to, $amount) ==> (18 == $tag && invRecv13($tag, $to, $amount) == $to) && invRecv14($tag, $to, $amount) == $amount
      );

    // -- Define updated permissions
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        ((0 <= invRecv13($tag, $to, $amount) && (invRecv13($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv14($tag, $to, $amount) && invRecv14($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv14($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), invRecv13($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange14($tag, $to, $amount) ==> (NoPerm < FullPerm ==> (18 == $tag && invRecv13($tag, $to, $amount) == $to) && invRecv14($tag, $to, $amount) == $amount) && QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)] + FullPerm
      );

    // -- Define independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        !(((0 <= invRecv13($tag, $to, $amount) && (invRecv13($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv14($tag, $to, $amount) && invRecv14($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv14($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), invRecv13($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange14($tag, $to, $amount)) ==> QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: $pre_self := self -- testsresourcesexamplesauction.vy.vpr@887.3--887.20
    $pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: $pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@888.3--888.32
    $pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   $havoc): $Struct) -- testsresourcesexamplesauction.vy.vpr@889.3--889.93
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + $havoc): $StructDomainType);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method f$__init__
// ==================================================

procedure f$__init__(l$_beneficiary: int, l$_bidding_time: $IntDomainType) returns ($succ: bool)
  modifies Heap, Mask;
{
  var revert_lblGuard: bool;
  var end_lblGuard: bool;
  var return_lblGuard: bool;
  var self: $StructDomainType;
  var block: $StructDomainType;
  var msg: $StructDomainType;
  var $pre_self: $StructDomainType;
  var $pre_$contracts: ($MapDomainType int $StructDomainType);
  var $contracts: ($MapDomainType int $StructDomainType);
  var $old_self: $StructDomainType;
  var $old_$contracts: ($MapDomainType int $StructDomainType);
  var $overflow: bool;
  var $first_public_state: bool;
  var l$havoc: int;
  var LabelreturnMask: MaskType;
  var LabelreturnHeap: HeapType;
  var $out_of_gas: bool;
  var LabelrevertMask: MaskType;
  var LabelrevertHeap: HeapType;
  var LabelendMask: MaskType;
  var LabelendHeap: HeapType;
  var l$havoc$1: int;
  var l$havoc$2: ($MapDomainType int $StructDomainType);
  var q$a_1: int;
  var q$a_4: int;
  var q$a_7: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    revert_lblGuard := false;
    end_lblGuard := false;
    return_lblGuard := false;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

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
  // inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@913.3--913.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 37
  // inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@914.3--914.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 38
  // inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@915.3--915.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 39
  // inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@916.3--916.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 40
  // inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@917.3--917.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 41
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@918.3--918.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 42
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@919.3--919.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 43
  // inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@920.3--920.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 44
  // inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@921.3--921.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 45
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@922.3--922.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 46
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@923.3--923.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 47
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@924.3--924.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 48
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@925.3--925.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 49
  // inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@926.3--926.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 50
  // inhale 0 <= $self_address() &&
  //   $self_address() <= 1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@928.3--928.102
    assume 0 <= ($self_address(): int);
    assume ($self_address(): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 51
  // inhale 0 <= l$_beneficiary &&
  //   l$_beneficiary <= 1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@930.3--930.100
    assume 0 <= l$_beneficiary;
    assume l$_beneficiary <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 52
  // inhale 0 <= $unwrap(l$_bidding_time) &&
  //   $unwrap(l$_bidding_time) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@931.3--931.149
    assume 0 <= ($unwrap(l$_bidding_time): int);
    assume ($unwrap(l$_bidding_time): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 53
  // inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@933.3--933.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 54
  // inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@934.3--934.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 55
  // inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@935.3--935.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 56
  // inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@936.3--936.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 57
  // inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@937.3--937.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 58
  // inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@938.3--938.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 59
  // inhale 0 <= ($struct_get($struct_loc(msg, 0)): Int) &&
  //   ($struct_get($struct_loc(msg, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@940.3--940.150
    assume 0 <= ($struct_get(($struct_loc(msg, 0): int)): int);
    assume ($struct_get(($struct_loc(msg, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 60
  // inhale 0 <= ($struct_get($struct_loc(msg, 1)): Int) &&
  //   ($struct_get($struct_loc(msg, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@941.3--941.179
    assume 0 <= ($struct_get(($struct_loc(msg, 1): int)): int);
    assume ($struct_get(($struct_loc(msg, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 61
  // inhale 0 <= ($struct_get($struct_loc(msg, 2)): Int) &&
  //   ($struct_get($struct_loc(msg, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@942.3--942.179
    assume 0 <= ($struct_get(($struct_loc(msg, 2): int)): int);
    assume ($struct_get(($struct_loc(msg, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 62
  // inhale ($struct_get($struct_loc(msg, -1)): Int) ==
  //   35634842679176259756224246631 -- testsresourcesexamplesauction.vy.vpr@943.3--943.83
    assume ($struct_get(($struct_loc(msg, -1): int)): int) == 35634842679176259756224246631;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 63
  // inhale ($struct_get($struct_loc(msg, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@944.3--944.54
    assume ($struct_get(($struct_loc(msg, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 64
  // $pre_self := self -- testsresourcesexamplesauction.vy.vpr@946.3--946.20
    $pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 65
  // $pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@947.3--947.32
    $pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 66
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@949.3--949.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 67
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@950.3--950.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 68
  // $succ := true -- testsresourcesexamplesauction.vy.vpr@951.3--951.16
    $succ := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 69
  // $overflow := false -- testsresourcesexamplesauction.vy.vpr@952.3--952.21
    $overflow := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 70
  // $first_public_state := true -- testsresourcesexamplesauction.vy.vpr@953.3--953.30
    $first_public_state := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 71
  // self := s$struct$self$init(0, 0, 0, 0, 0, false, ($map_init(0): $Map[Int, Int]),
  //   0, 0, false, ($map_init(0): $Map[Int, Int]), ($map_init(0): $Map[Int, Int]),
  //   false) -- testsresourcesexamplesauction.vy.vpr@954.3--954.167
    self := (s$struct$self$init(0, 0, 0, 0, 0, false, ($map_init(0): $MapDomainType int int), 0, 0, false, ($map_init(0): $MapDomainType int int), ($map_init(0): $MapDomainType int int), false): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 72
  // inhale l$havoc >= 0 -- testsresourcesexamplesauction.vy.vpr@955.3--955.22
    assume l$havoc >= 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 73
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   l$havoc): $Struct) -- testsresourcesexamplesauction.vy.vpr@956.3--956.94
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + l$havoc): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 74
  // inhale ($struct_get($struct_loc(msg, 1)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@958.3--958.54
    assume ($struct_get(($struct_loc(msg, 1): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: if (!(l$_beneficiary != 0)) -- testsresourcesexamplesauction.vy.vpr@960.3--962.4
    if (!(l$_beneficiary != 0)) {

      // -- Translating statement: // id = 75
  // goto revert -- testsresourcesexamplesauction.vy.vpr@961.5--961.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 76
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 77
  // self := ($struct_set(self, 0, l$_beneficiary): $Struct) -- testsresourcesexamplesauction.vy.vpr@963.3--963.58
    self := ($struct_set(self, 0, l$_beneficiary): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 78
  // self := ($struct_set(self, 1, $unwrap($wrap(($struct_get($struct_loc(block,
  //   4)): Int)))): $Struct) -- testsresourcesexamplesauction.vy.vpr@964.3--964.101
    self := ($struct_set(self, 1, ($unwrap(($wrap(($struct_get(($struct_loc(block, 4): int)): int)): $IntDomainType)): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: if (($struct_get($struct_loc(self, 1)): Int) + $unwrap(l$_bidding_time) < 0) -- testsresourcesexamplesauction.vy.vpr@965.3--967.4
    if (($struct_get(($struct_loc(self, 1): int)): int) + ($unwrap(l$_bidding_time): int) < 0) {

      // -- Translating statement: // id = 79
  // goto revert -- testsresourcesexamplesauction.vy.vpr@966.5--966.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 80
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 81
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if (($struct_get($struct_loc(self, 1)): Int) + $unwrap(l$_bidding_time) > 115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@968.3--971.4
    if (($struct_get(($struct_loc(self, 1): int)): int) + ($unwrap(l$_bidding_time): int) > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {

      // -- Translating statement: // id = 82
  // $overflow := true -- testsresourcesexamplesauction.vy.vpr@969.5--969.22
        $overflow := true;
        assume state(Heap, Mask);

      // -- Translating statement: // id = 83
  // goto revert -- testsresourcesexamplesauction.vy.vpr@970.5--970.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 84
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 85
  // self := ($struct_set(self, 2, $unwrap($wrap(($struct_get($struct_loc(self, 1)): Int) +
  //   $unwrap(l$_bidding_time)))): $Struct) -- testsresourcesexamplesauction.vy.vpr@972.3--972.127
    self := ($struct_set(self, 2, ($unwrap(($wrap(($struct_get(($struct_loc(self, 1): int)): int) + ($unwrap(l$_bidding_time): int)): $IntDomainType)): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 86
  // label return -- testsresourcesexamplesauction.vy.vpr@973.3--973.15
    vreturn:
    LabelreturnMask := Mask;
    LabelreturnHeap := Heap;
    return_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: if ($out_of_gas) -- testsresourcesexamplesauction.vy.vpr@974.3--976.4
    if ($out_of_gas) {

      // -- Translating statement: // id = 87
  // goto revert -- testsresourcesexamplesauction.vy.vpr@975.5--975.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 88
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 89
  // goto end -- testsresourcesexamplesauction.vy.vpr@977.3--977.11
    goto end;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 90
  // label revert -- testsresourcesexamplesauction.vy.vpr@978.3--978.15
    revert:
    LabelrevertMask := Mask;
    LabelrevertHeap := Heap;
    revert_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 91
  // $succ := false -- testsresourcesexamplesauction.vy.vpr@979.3--979.17
    $succ := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 92
  // self := $pre_self -- testsresourcesexamplesauction.vy.vpr@981.3--981.20
    self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 93
  // $contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@982.3--982.32
    $contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 94
  // $old_self := $pre_self -- testsresourcesexamplesauction.vy.vpr@984.3--984.25
    $old_self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 95
  // $old_$contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@985.3--985.37
    $old_$contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 96
  // label end -- testsresourcesexamplesauction.vy.vpr@986.3--986.12
    end:
    LabelendMask := Mask;
    LabelendHeap := Heap;
    end_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: if ($first_public_state) -- testsresourcesexamplesauction.vy.vpr@987.3--989.4
    if ($first_public_state) {

      // -- Translating statement: // id = 97
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@988.5--988.22
        $old_self := self;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 98
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 99
  // assert $succ ==>
  //   $succ &&
  //   (($struct_get($struct_loc(msg, 1)): Int) >
  //   ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) != 0) ==>
  //   ($struct_get($struct_loc(msg, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@991.3--991.248
    if ($succ) {
      if ($succ && (($struct_get(($struct_loc(msg, 1): int)): int) > ($struct_get(($struct_loc(self, 4): int)): int) && ($struct_get(($struct_loc(self, 3): int)): int) != 0)) {
        assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(msg, 0)): Int) == ($struct_get($struct_loc(self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@991.10--991.248) [254]"}
          ($struct_get(($struct_loc(msg, 0): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: if ($succ) -- testsresourcesexamplesauction.vy.vpr@993.3--995.4
    if ($succ) {

      // -- Translating statement: // id = 100
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 101
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 102
  // inhale l$havoc$1 >= 0 -- testsresourcesexamplesauction.vy.vpr@996.3--996.24
    assume l$havoc$1 >= 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 103
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   l$havoc$1): $Struct) -- testsresourcesexamplesauction.vy.vpr@997.3--997.96
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + l$havoc$1): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 104
  // $contracts := l$havoc$2 -- testsresourcesexamplesauction.vy.vpr@999.3--999.26
    $contracts := l$havoc$2;
    assume state(Heap, Mask);

  // -- Translating statement: if ($first_public_state) -- testsresourcesexamplesauction.vy.vpr@1000.3--1002.4
    if ($first_public_state) {

      // -- Translating statement: // id = 105
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1001.5--1001.22
        $old_self := self;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 106
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 107
  // assert $succ ==>
  //   ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1004.3--1004.115
    if ($succ) {
      if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
        assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1004.10--1004.115) [255]"}
          ($struct_get(($struct_loc(self, 4): int)): int) == 0;
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 108
  // assert $succ ==>
  //   ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1005.3--1005.109
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) == ($struct_get($struct_loc($old_self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1005.10--1005.109) [256]"}
        ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 109
  // assert $succ ==>
  //   ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1006.3--1006.112
    if ($succ) {
      if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@1006.10--1006.112) [257]"}
          ($struct_get(($struct_loc(self, 5): int)): bool);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 110
  // assert $succ ==>
  //   !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1007.3--1007.222
    if ($succ) {
      if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1007.10--1007.222) [258]"}
          ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 111
  // assert $succ ==>
  //   !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1008.3--1008.323
    if ($succ) {
      if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) == ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1008.10--1008.323) [259]"}
          ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 112
  // assert $succ ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1009.3--1009.178
    if ($succ) {
      if (($struct_get(($struct_loc(self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1009.10--1009.178) [260]"}
          ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 113
  // assert $succ ==>
  //   ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1010.3--1010.109
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) >= ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1010.10--1010.109) [261]"}
        ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 114
  // assert $succ ==>
  //   ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1011.3--1011.253
    if ($succ) {
      if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1011.10--1011.253) [262]"}
          ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
        assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) == ($struct_get($struct_loc($old_self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1011.10--1011.253) [263]"}
          ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 115
  // assert $succ ==> ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1012.3--1012.65
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1012.10--1012.65) [264]"}
        ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 116
  // assert $succ ==>
  //   ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1013.3--1013.104
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) != ($struct_get($struct_loc(self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1013.10--1013.104) [265]"}
        ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 117
  // assert $succ ==>
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1014.3--1014.135
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1014.10--1014.135) [266]"}
        ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 118
  // assert $succ ==>
  //   !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1015.3--1015.183
    if ($succ) {
      if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1015.10--1015.183) [267]"}
          ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 119
  // assert $succ ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1016.3--1016.221
    if ($succ) {
      if (($struct_get(($struct_loc(self, 5): int)): bool)) {
        assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == ($struct_get($struct_loc(self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1016.10--1016.221) [268]"}
          ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
      }
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 120
  // assert $succ ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1017.3--1017.402
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) + ($struct_get($struct_loc(self, 4)): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1017.10--1017.402) [269]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 121
  // assert $succ ==>
  //   (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1018.3--1018.524

    // -- Check definedness of $succ ==> (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if ($succ) {
        if (*) {
          assume false;
        }
      }
    if ($succ) {
      if (*) {
        if (0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975) {
          if (q$a_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc(self, 0): int)): int)) {
            assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1018.10--1018.524) [270]"}
              ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int);
          }
        }
        assume false;
      }
      assume (forall q$a_2_1: int ::
        { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_2_1): int) }
        0 <= q$a_2_1 && q$a_2_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_2_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_2_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_2_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_2_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_2_1): int)
      );
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 122
  // assert $succ ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1019.3--1019.97
    if ($succ) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1019.10--1019.97) [271]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 123
  // assert $succ ==>
  //   (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1020.3--1020.354

    // -- Check definedness of $succ ==> (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if ($succ) {
        if (*) {
          assume false;
        }
      }
    if ($succ) {
      if (*) {
        if (0 <= q$a_4 && q$a_4 <= 1461501637330902918203684832716283019655932542975) {
          if (($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_4): int) != 0) {
            assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1020.10--1020.354) [272]"}
              ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_4): int) != 0;
          }
        }
        assume false;
      }
      assume (forall q$a_5_1: int ::
        { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_5_1): int) }
        0 <= q$a_5_1 && q$a_5_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_5_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5_1): int) != 0
      );
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 124
  // assert $succ ==>
  //   (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1021.3--1021.407

    // -- Check definedness of $succ ==> (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if ($succ) {
        if (*) {
          assume false;
        }
      }
    if ($succ) {
      if (*) {
        if (0 <= q$a_7 && q$a_7 <= 1461501637330902918203684832716283019655932542975) {
          if (q$a_7 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_7): int) == 0) {
            assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1021.10--1021.407) [273]"}
              ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_7): int) == 0;
          }
        }
        assume false;
      }
      assume (forall q$a_8_1: int ::
        { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_8_1): int) }
        0 <= q$a_8_1 && q$a_8_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_8_1 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_8_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_8_1): int) == 0
      );
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 125
  // assert $succ ==>
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1022.3--1022.355

    // -- Check definedness of $succ ==> (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if ($succ) {
        if (*) {
          assume false;
        }
      }
    if ($succ) {
      if (*) {
        assume false;
      }
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method f$bid
// ==================================================

procedure f$bid() returns ($succ: bool)
  modifies Heap, Mask;
{
  var revert_lblGuard: bool;
  var end_lblGuard: bool;
  var return_lblGuard: bool;
  var self: $StructDomainType;
  var block: $StructDomainType;
  var msg: $StructDomainType;
  var $pre_self: $StructDomainType;
  var $pre_$contracts: ($MapDomainType int $StructDomainType);
  var $contracts: ($MapDomainType int $StructDomainType);
  var $old_self: $StructDomainType;
  var $old_$contracts: ($MapDomainType int $StructDomainType);
  var $overflow: bool;
  var LabelreturnMask: MaskType;
  var LabelreturnHeap: HeapType;
  var $out_of_gas: bool;
  var LabelrevertMask: MaskType;
  var LabelrevertHeap: HeapType;
  var LabelendMask: MaskType;
  var LabelendHeap: HeapType;
  var l$havoc: int;
  var l$havoc$1: ($MapDomainType int $StructDomainType);
  var q$a_9: int;
  var q$a_12: int;
  var q$a_15: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    revert_lblGuard := false;
    end_lblGuard := false;
    return_lblGuard := false;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

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
  // inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1044.3--1044.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 33
  // inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1045.3--1045.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 34
  // inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1046.3--1046.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 35
  // inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1047.3--1047.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 36
  // inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1048.3--1048.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 37
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1049.3--1049.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 38
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1050.3--1050.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 39
  // inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1051.3--1051.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 40
  // inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@1052.3--1052.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 41
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1053.3--1053.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 42
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1054.3--1054.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 43
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1055.3--1055.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 44
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1056.3--1056.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 45
  // inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@1057.3--1057.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 46
  // inhale 0 <= $self_address() &&
  //   $self_address() <= 1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1059.3--1059.102
    assume 0 <= ($self_address(): int);
    assume ($self_address(): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 47
  // inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1061.3--1061.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 48
  // inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1062.3--1062.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 49
  // inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1063.3--1063.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 50
  // inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@1064.3--1064.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 51
  // inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1065.3--1065.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 52
  // inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@1066.3--1066.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 53
  // inhale 0 <= ($struct_get($struct_loc(msg, 0)): Int) &&
  //   ($struct_get($struct_loc(msg, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1068.3--1068.150
    assume 0 <= ($struct_get(($struct_loc(msg, 0): int)): int);
    assume ($struct_get(($struct_loc(msg, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 54
  // inhale 0 <= ($struct_get($struct_loc(msg, 1)): Int) &&
  //   ($struct_get($struct_loc(msg, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1069.3--1069.179
    assume 0 <= ($struct_get(($struct_loc(msg, 1): int)): int);
    assume ($struct_get(($struct_loc(msg, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 55
  // inhale 0 <= ($struct_get($struct_loc(msg, 2)): Int) &&
  //   ($struct_get($struct_loc(msg, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1070.3--1070.179
    assume 0 <= ($struct_get(($struct_loc(msg, 2): int)): int);
    assume ($struct_get(($struct_loc(msg, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 56
  // inhale ($struct_get($struct_loc(msg, -1)): Int) ==
  //   35634842679176259756224246631 -- testsresourcesexamplesauction.vy.vpr@1071.3--1071.83
    assume ($struct_get(($struct_loc(msg, -1): int)): int) == 35634842679176259756224246631;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 57
  // inhale ($struct_get($struct_loc(msg, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1072.3--1072.54
    assume ($struct_get(($struct_loc(msg, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 58
  // inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@1074.3--1074.258

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) >= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 59
  // inhale ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1075.3--1075.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 60
  // inhale ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1076.3--1076.94
    assume ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 61
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1077.3--1077.97
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 62
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1078.3--1078.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 63
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1079.3--1079.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 64
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1080.3--1080.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 65
  // inhale ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1081.3--1081.94
    assume ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc(self, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 66
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1082.3--1082.228
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
      assume ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 67
  // inhale ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1083.3--1083.55
    assume ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 68
  // inhale ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1084.3--1084.94
    assume ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 69
  // inhale ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1085.3--1085.125
    assume ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 70
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1086.3--1086.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 71
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1087.3--1087.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 72
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1088.3--1088.392
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 73
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1089.3--1089.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int) }
      0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 74
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1090.3--1090.87
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 75
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1091.3--1091.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) }
      0 <= q$a_3 && q$a_3 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_3): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 76
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1092.3--1092.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) }
      0 <= q$a_5 && q$a_5 <= 1461501637330902918203684832716283019655932542975 ==> q$a_5 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_5): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 77
  // inhale (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1093.3--1093.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 78
  // $pre_self := self -- testsresourcesexamplesauction.vy.vpr@1095.3--1095.20
    $pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 79
  // $pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1096.3--1096.32
    $pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 80
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1098.3--1098.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 81
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1099.3--1099.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 82
  // $succ := true -- testsresourcesexamplesauction.vy.vpr@1100.3--1100.16
    $succ := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 83
  // $overflow := false -- testsresourcesexamplesauction.vy.vpr@1101.3--1101.21
    $overflow := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 84
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   ($struct_get($struct_loc(msg, 1)): Int)): $Struct) -- testsresourcesexamplesauction.vy.vpr@1103.3--1103.126
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + ($struct_get(($struct_loc(msg, 1): int)): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 85
  // self := ($struct_set(self, 11, ($map_set(($struct_get($struct_loc(self, 11)): $Map[Int, Int]),
  //   ($struct_get($struct_loc(msg, 0)): Int), ($map_get(($struct_get($struct_loc(self,
  //   11)): $Map[Int, Int]), ($struct_get($struct_loc(msg, 0)): Int)): Int) +
  //   ($struct_get($struct_loc(msg, 1)): Int)): $Map[Int, Int])): $Struct) -- testsresourcesexamplesauction.vy.vpr@1104.3--1104.320
    self := ($struct_set(self, 11, ($map_set(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int), ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int) + ($struct_get(($struct_loc(msg, 1): int)): int)): $MapDomainType int int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: if (!(($struct_get($struct_loc(block, 4)): Int) < ($struct_get($struct_loc(self, 2)): Int))) -- testsresourcesexamplesauction.vy.vpr@1106.3--1108.4
    if (!(($struct_get(($struct_loc(block, 4): int)): int) < ($struct_get(($struct_loc(self, 2): int)): int))) {

      // -- Translating statement: // id = 86
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1107.5--1107.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 87
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 88
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if (!!($struct_get($struct_loc(self, 5)): Bool)) -- testsresourcesexamplesauction.vy.vpr@1109.3--1111.4
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {

      // -- Translating statement: // id = 89
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1110.5--1110.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 90
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 91
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if (!(($struct_get($struct_loc(msg, 1)): Int) > ($struct_get($struct_loc(self, 4)): Int))) -- testsresourcesexamplesauction.vy.vpr@1112.3--1114.4
    if (!(($struct_get(($struct_loc(msg, 1): int)): int) > ($struct_get(($struct_loc(self, 4): int)): int))) {

      // -- Translating statement: // id = 92
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1113.5--1113.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 93
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 94
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if (!(($struct_get($struct_loc(msg, 0)): Int) != ($struct_get($struct_loc(self, 0)): Int))) -- testsresourcesexamplesauction.vy.vpr@1115.3--1117.4
    if (!(($struct_get(($struct_loc(msg, 0): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int))) {

      // -- Translating statement: // id = 95
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1116.5--1116.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 96
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 97
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if ($unwrap($wrap(($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int))) + $unwrap($wrap(($struct_get($struct_loc(self, 4)): Int))) < 0) -- testsresourcesexamplesauction.vy.vpr@1118.3--1120.4
    if (($unwrap(($wrap(($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int)): $IntDomainType)): int) + ($unwrap(($wrap(($struct_get(($struct_loc(self, 4): int)): int)): $IntDomainType)): int) < 0) {

      // -- Translating statement: // id = 98
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1119.5--1119.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 99
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 100
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if ($unwrap($wrap(($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int))) + $unwrap($wrap(($struct_get($struct_loc(self, 4)): Int))) > 115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1121.3--1124.4
    if (($unwrap(($wrap(($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int)): $IntDomainType)): int) + ($unwrap(($wrap(($struct_get(($struct_loc(self, 4): int)): int)): $IntDomainType)): int) > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {

      // -- Translating statement: // id = 101
  // $overflow := true -- testsresourcesexamplesauction.vy.vpr@1122.5--1122.22
        $overflow := true;
        assume state(Heap, Mask);

      // -- Translating statement: // id = 102
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1123.5--1123.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 103
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 104
  // self := ($struct_set(self, 6, ($map_set(($struct_get($struct_loc(self, 6)): $Map[Int, Int]),
  //   ($struct_get($struct_loc(self, 3)): Int), $unwrap($wrap(($map_get(($struct_get($struct_loc(self,
  //   6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int))) +
  //   $unwrap($wrap(($struct_get($struct_loc(self, 4)): Int)))): $Map[Int, Int])): $Struct) -- testsresourcesexamplesauction.vy.vpr@1125.3--1125.352
    self := ($struct_set(self, 6, ($map_set(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int), ($unwrap(($wrap(($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int)): $IntDomainType)): int) + ($unwrap(($wrap(($struct_get(($struct_loc(self, 4): int)): int)): $IntDomainType)): int)): $MapDomainType int int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 105
  // self := ($struct_set(self, 3, ($struct_get($struct_loc(msg, 0)): Int)): $Struct) -- testsresourcesexamplesauction.vy.vpr@1126.3--1126.83
    self := ($struct_set(self, 3, ($struct_get(($struct_loc(msg, 0): int)): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 106
  // self := ($struct_set(self, 4, $unwrap($wrap(($struct_get($struct_loc(msg, 1)): Int)))): $Struct) -- testsresourcesexamplesauction.vy.vpr@1127.3--1127.99
    self := ($struct_set(self, 4, ($unwrap(($wrap(($struct_get(($struct_loc(msg, 1): int)): int)): $IntDomainType)): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 107
  // label return -- testsresourcesexamplesauction.vy.vpr@1128.3--1128.15
    vreturn:
    LabelreturnMask := Mask;
    LabelreturnHeap := Heap;
    return_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: if ($out_of_gas) -- testsresourcesexamplesauction.vy.vpr@1129.3--1131.4
    if ($out_of_gas) {

      // -- Translating statement: // id = 108
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1130.5--1130.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 109
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 110
  // goto end -- testsresourcesexamplesauction.vy.vpr@1132.3--1132.11
    goto end;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 111
  // label revert -- testsresourcesexamplesauction.vy.vpr@1133.3--1133.15
    revert:
    LabelrevertMask := Mask;
    LabelrevertHeap := Heap;
    revert_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 112
  // $succ := false -- testsresourcesexamplesauction.vy.vpr@1134.3--1134.17
    $succ := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 113
  // self := $pre_self -- testsresourcesexamplesauction.vy.vpr@1136.3--1136.20
    self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 114
  // $contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1137.3--1137.32
    $contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 115
  // $old_self := $pre_self -- testsresourcesexamplesauction.vy.vpr@1139.3--1139.25
    $old_self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 116
  // $old_$contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1140.3--1140.37
    $old_$contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 117
  // label end -- testsresourcesexamplesauction.vy.vpr@1141.3--1141.12
    end:
    LabelendMask := Mask;
    LabelendHeap := Heap;
    end_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 118
  // exhale $succ ==>
  //   ($struct_get($struct_loc(self, 4)): Int) >
  //   ($struct_get($struct_loc($pre_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1143.3--1143.108
    if ($succ) {
      assert {:msg "  Exhale might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) > ($struct_get($struct_loc($pre_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1143.10--1143.108) [275]"}
        ($struct_get(($struct_loc(self, 4): int)): int) > ($struct_get(($struct_loc($pre_self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 119
  // assert $succ &&
  //   (($struct_get($struct_loc(msg, 1)): Int) >
  //   ($struct_get($struct_loc($pre_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) != 0) ==>
  //   ($struct_get($struct_loc(msg, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1144.3--1144.243
    if ($succ && (($struct_get(($struct_loc(msg, 1): int)): int) > ($struct_get(($struct_loc($pre_self, 4): int)): int) && ($struct_get(($struct_loc(self, 3): int)): int) != 0)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(msg, 0)): Int) == ($struct_get($struct_loc(self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1144.10--1144.243) [276]"}
        ($struct_get(($struct_loc(msg, 0): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: if ($succ) -- testsresourcesexamplesauction.vy.vpr@1146.3--1148.4
    if ($succ) {

      // -- Translating statement: // id = 120
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 121
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 122
  // inhale l$havoc >= 0 -- testsresourcesexamplesauction.vy.vpr@1149.3--1149.22
    assume l$havoc >= 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 123
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   l$havoc): $Struct) -- testsresourcesexamplesauction.vy.vpr@1150.3--1150.94
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + l$havoc): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 124
  // $contracts := l$havoc$1 -- testsresourcesexamplesauction.vy.vpr@1152.3--1152.26
    $contracts := l$havoc$1;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 125
  // assert ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1154.3--1154.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1154.10--1154.105) [277]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 126
  // assert ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1155.3--1155.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) == ($struct_get($struct_loc($old_self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1155.10--1155.99) [278]"}
      ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 127
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1156.3--1156.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@1156.10--1156.102) [279]"}
        ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 128
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1157.3--1157.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1157.10--1157.212) [280]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 129
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1158.3--1158.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) == ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1158.10--1158.313) [281]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 130
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1159.3--1159.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1159.10--1159.168) [282]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 131
  // assert ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1160.3--1160.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) >= ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1160.10--1160.99) [283]"}
      ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 132
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1161.3--1161.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1161.10--1161.243) [284]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) == ($struct_get($struct_loc($old_self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1161.10--1161.243) [285]"}
        ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 133
  // assert ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1162.3--1162.55
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1162.10--1162.55) [286]"}
      ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 134
  // assert ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1163.3--1163.94
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) != ($struct_get($struct_loc(self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1163.10--1163.94) [287]"}
      ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 135
  // assert ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1164.3--1164.125
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1164.10--1164.125) [288]"}
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 136
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1165.3--1165.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1165.10--1165.173) [289]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 137
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1166.3--1166.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == ($struct_get($struct_loc(self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1166.10--1166.211) [290]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 138
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1167.3--1167.392
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) + ($struct_get($struct_loc(self, 4)): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1167.10--1167.392) [291]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 139
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1168.3--1168.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_9 && q$a_9 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_9 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_9 != ($struct_get(($struct_loc(self, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1168.11--1168.513) [292]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_9): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_9): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_9): int);
        }
      }
      assume false;
    }
    assume (forall q$a_10_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_10_1): int) }
      0 <= q$a_10_1 && q$a_10_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_10_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_10_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_10_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_10_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_10_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 140
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1169.3--1169.87
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1169.10--1169.87) [293]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 141
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1170.3--1170.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_12 && q$a_12 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_12): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1170.11--1170.343) [294]"}
            ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_12): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_13_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_13_1): int) }
      0 <= q$a_13_1 && q$a_13_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_13_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_13_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 142
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1171.3--1171.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_15 && q$a_15 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_15 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_15): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1171.11--1171.396) [295]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_15): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_16_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_16_1_1): int) }
      0 <= q$a_16_1_1 && q$a_16_1_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_16_1_1 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_16_1_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_16_1_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 143
  // assert (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1172.3--1172.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    if (*) {
      assume false;
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method f$withdraw
// ==================================================

procedure f$withdraw() returns ($succ: bool)
  modifies Heap, Mask;
{
  var revert_lblGuard: bool;
  var end_lblGuard: bool;
  var return_lblGuard: bool;
  var self: $StructDomainType;
  var block: $StructDomainType;
  var msg: $StructDomainType;
  var QPMask: MaskType;
  var $pre_self: $StructDomainType;
  var $pre_$contracts: ($MapDomainType int $StructDomainType);
  var $contracts: ($MapDomainType int $StructDomainType);
  var $old_self: $StructDomainType;
  var $old_$contracts: ($MapDomainType int $StructDomainType);
  var $overflow: bool;
  var l$pending_amount: $IntDomainType;
  var l$havoc: ($MapDomainType int $StructDomainType);
  var q$a_10: int;
  var q$a_13: int;
  var q$a_16: int;
  var l$send_fail: bool;
  var perm: Perm;
  var i0$$pre_self: $StructDomainType;
  var i0$$pre_$contracts: ($MapDomainType int $StructDomainType);
  var l$havoc$1: ($MapDomainType int $StructDomainType);
  var l$havoc$2: $StructDomainType;
  var l$havoc$3: ($MapDomainType int $StructDomainType);
  var l$no_reentrant_call: bool;
  var l$havoc$4: ($MapDomainType int $StructDomainType);
  var l$havoc$5: ($MapDomainType int $StructDomainType);
  var LabelreturnMask: MaskType;
  var LabelreturnHeap: HeapType;
  var $out_of_gas: bool;
  var LabelrevertMask: MaskType;
  var LabelrevertHeap: HeapType;
  var LabelendMask: MaskType;
  var LabelendHeap: HeapType;
  var l$havoc$6: int;
  var l$havoc$7: ($MapDomainType int $StructDomainType);
  var q$a_30: int;
  var q$a_33: int;
  var q$a_36: int;
  var $a_5: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    revert_lblGuard := false;
    end_lblGuard := false;
    return_lblGuard := false;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

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
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 47
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 48
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 49
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 50
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 51
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 52
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 53
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 54
  // inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1205.3--1205.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 55
  // inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1206.3--1206.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 56
  // inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1207.3--1207.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 57
  // inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1208.3--1208.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 58
  // inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1209.3--1209.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 59
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1210.3--1210.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 60
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1211.3--1211.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 61
  // inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1212.3--1212.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 62
  // inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@1213.3--1213.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 63
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1214.3--1214.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 64
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1215.3--1215.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 65
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1216.3--1216.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 66
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1217.3--1217.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 67
  // inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@1218.3--1218.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 68
  // inhale 0 <= $self_address() &&
  //   $self_address() <= 1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1220.3--1220.102
    assume 0 <= ($self_address(): int);
    assume ($self_address(): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 69
  // inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1222.3--1222.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 70
  // inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1223.3--1223.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 71
  // inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1224.3--1224.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 72
  // inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@1225.3--1225.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 73
  // inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1226.3--1226.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 74
  // inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@1227.3--1227.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 75
  // inhale 0 <= ($struct_get($struct_loc(msg, 0)): Int) &&
  //   ($struct_get($struct_loc(msg, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1229.3--1229.150
    assume 0 <= ($struct_get(($struct_loc(msg, 0): int)): int);
    assume ($struct_get(($struct_loc(msg, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 76
  // inhale 0 <= ($struct_get($struct_loc(msg, 1)): Int) &&
  //   ($struct_get($struct_loc(msg, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1230.3--1230.179
    assume 0 <= ($struct_get(($struct_loc(msg, 1): int)): int);
    assume ($struct_get(($struct_loc(msg, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 77
  // inhale 0 <= ($struct_get($struct_loc(msg, 2)): Int) &&
  //   ($struct_get($struct_loc(msg, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1231.3--1231.179
    assume 0 <= ($struct_get(($struct_loc(msg, 2): int)): int);
    assume ($struct_get(($struct_loc(msg, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 78
  // inhale ($struct_get($struct_loc(msg, -1)): Int) ==
  //   35634842679176259756224246631 -- testsresourcesexamplesauction.vy.vpr@1232.3--1232.83
    assume ($struct_get(($struct_loc(msg, -1): int)): int) == 35634842679176259756224246631;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 79
  // inhale ($struct_get($struct_loc(msg, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1233.3--1233.54
    assume ($struct_get(($struct_loc(msg, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 80
  // inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@1235.3--1235.258

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) >= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 81
  // inhale ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1236.3--1236.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 82
  // inhale ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1237.3--1237.94
    assume ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 83
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1238.3--1238.97
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 84
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1239.3--1239.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 85
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1240.3--1240.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 86
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1241.3--1241.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 87
  // inhale ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1242.3--1242.94
    assume ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc(self, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 88
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1243.3--1243.228
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
      assume ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 89
  // inhale ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1244.3--1244.55
    assume ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 90
  // inhale ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1245.3--1245.94
    assume ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 91
  // inhale ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1246.3--1246.125
    assume ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 92
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1247.3--1247.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 93
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1248.3--1248.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 94
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1249.3--1249.392
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 95
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1250.3--1250.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int) }
      0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 96
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1251.3--1251.87
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 97
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1252.3--1252.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) }
      0 <= q$a_3 && q$a_3 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_3): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 98
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1253.3--1253.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) }
      0 <= q$a_5 && q$a_5 <= 1461501637330902918203684832716283019655932542975 ==> q$a_5 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_5): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 99
  // inhale true &&
  //   (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int))) ==>
  //     acc($accessible$withdraw(18, q$a, q$v), write)) -- testsresourcesexamplesauction.vy.vpr@1254.3--1254.394

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 && q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int))) ==> acc($accessible$withdraw(18, q$a, q$v), write))
      if (*) {
        assume false;
      }
    havoc QPMask;

    // -- check if receiver acc($accessible$withdraw(18, q$a, q$v), write) is injective
      assert {:msg "  Inhale might fail. Quantified resource $accessible$withdraw(18, q$a, q$v) might not be injective. (testsresourcesexamplesauction.vy.vpr@1254.10--1254.394) [297]"}
        (forall q$a_7: int, q$v_1: int, q$a_7_1: int, q$v_1_1: int ::
        { neverTriggered16(q$a_7, q$v_1), neverTriggered16(q$a_7_1, q$v_1_1) }
        ((((q$a_7 != q$a_7_1 && q$v_1 != q$v_1_1) && (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_7): int))))) && (0 <= q$a_7_1 && (q$a_7_1 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1_1 && q$v_1_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1_1 == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_7_1): int))))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> q$a_7 != q$a_7_1 || q$v_1 != q$v_1_1
      );

    // -- Define Inverse Function
      assume (forall q$a_7: int, q$v_1: int ::
        { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Mask[null, $accessible$withdraw(18, q$a_7, q$v_1)] } { Heap[null, $accessible$withdraw(18, q$a_7, q$v_1)] }
        (0 <= q$a_7 && (q$a_7 <= 1461501637330902918203684832716283019655932542975 && ((0 <= q$v_1 && q$v_1 <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && q$v_1 == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_7): int)))) && NoPerm < FullPerm ==> (invRecv15(18, q$a_7, q$v_1) == q$a_7 && invRecv16(18, q$a_7, q$v_1) == q$v_1) && qpRange16(18, q$a_7, q$v_1)
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { invRecv15($tag, $to, $amount), invRecv16($tag, $to, $amount) }
        ((0 <= invRecv15($tag, $to, $amount) && (invRecv15($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv16($tag, $to, $amount) && invRecv16($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv16($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), invRecv15($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange16($tag, $to, $amount) ==> (18 == $tag && invRecv15($tag, $to, $amount) == $to) && invRecv16($tag, $to, $amount) == $amount
      );

    // -- Define updated permissions
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        ((0 <= invRecv15($tag, $to, $amount) && (invRecv15($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv16($tag, $to, $amount) && invRecv16($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv16($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), invRecv15($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange16($tag, $to, $amount) ==> (NoPerm < FullPerm ==> (18 == $tag && invRecv15($tag, $to, $amount) == $to) && invRecv16($tag, $to, $amount) == $amount) && QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)] + FullPerm
      );

    // -- Define independent locations
      assume (forall <A, B> o_4: Ref, f_6: (Field A B) ::
        { Mask[o_4, f_6] } { QPMask[o_4, f_6] }
        (o_4 != null || !IsPredicateField(f_6)) || getPredicateId(f_6) != 24 ==> Mask[o_4, f_6] == QPMask[o_4, f_6]
      );
      assume (forall $tag: int, $to: int, $amount: int ::
        { QPMask[null, $accessible$withdraw($tag, $to, $amount)] }
        !(((0 <= invRecv15($tag, $to, $amount) && (invRecv15($tag, $to, $amount) <= 1461501637330902918203684832716283019655932542975 && ((0 <= invRecv16($tag, $to, $amount) && invRecv16($tag, $to, $amount) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) && invRecv16($tag, $to, $amount) == ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), invRecv15($tag, $to, $amount)): int)))) && NoPerm < FullPerm) && qpRange16($tag, $to, $amount)) ==> QPMask[null, $accessible$withdraw($tag, $to, $amount)] == Mask[null, $accessible$withdraw($tag, $to, $amount)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 100
  // $pre_self := self -- testsresourcesexamplesauction.vy.vpr@1256.3--1256.20
    $pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 101
  // $pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1257.3--1257.32
    $pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 102
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1259.3--1259.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 103
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1260.3--1260.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 104
  // $succ := true -- testsresourcesexamplesauction.vy.vpr@1261.3--1261.16
    $succ := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 105
  // $overflow := false -- testsresourcesexamplesauction.vy.vpr@1262.3--1262.21
    $overflow := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 106
  // inhale ($struct_get($struct_loc(msg, 1)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1264.3--1264.54
    assume ($struct_get(($struct_loc(msg, 1): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 107
  // l$pending_amount := $wrap(($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]),
  //   ($struct_get($struct_loc(msg, 0)): Int)): Int)) -- testsresourcesexamplesauction.vy.vpr@1266.3--1266.139
    l$pending_amount := ($wrap(($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int)): $IntDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 108
  // self := ($struct_set(self, 6, ($map_set(($struct_get($struct_loc(self, 6)): $Map[Int, Int]),
  //   ($struct_get($struct_loc(msg, 0)): Int), 0): $Map[Int, Int])): $Struct) -- testsresourcesexamplesauction.vy.vpr@1267.3--1267.167
    self := ($struct_set(self, 6, ($map_set(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int), 0): $MapDomainType int int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: if (($struct_get($struct_loc(self, 7)): Int) < $unwrap(l$pending_amount)) -- testsresourcesexamplesauction.vy.vpr@1268.3--1270.4
    if (($struct_get(($struct_loc(self, 7): int)): int) < ($unwrap(l$pending_amount): int)) {

      // -- Translating statement: // id = 109
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1269.5--1269.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 110
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 111
  // self := ($struct_set(self, 10, ($map_set(($struct_get($struct_loc(self, 10)): $Map[Int, Int]),
  //   ($struct_get($struct_loc(msg, 0)): Int), ($map_get(($struct_get($struct_loc(self,
  //   10)): $Map[Int, Int]), ($struct_get($struct_loc(msg, 0)): Int)): Int) +
  //   $unwrap(l$pending_amount)): $Map[Int, Int])): $Struct) -- testsresourcesexamplesauction.vy.vpr@1271.3--1271.306
    self := ($struct_set(self, 10, ($map_set(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int), ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int) + ($unwrap(l$pending_amount): int)): $MapDomainType int int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 112
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) -
  //   $unwrap(l$pending_amount)): $Struct) -- testsresourcesexamplesauction.vy.vpr@1272.3--1272.112
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) - ($unwrap(l$pending_amount): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 113
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1274.3--1274.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 114
  // $contracts := l$havoc -- testsresourcesexamplesauction.vy.vpr@1276.3--1276.24
    $contracts := l$havoc;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 115
  // assert ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1278.3--1278.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1278.10--1278.105) [298]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 116
  // assert ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1279.3--1279.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) == ($struct_get($struct_loc($old_self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1279.10--1279.99) [299]"}
      ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 117
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1280.3--1280.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@1280.10--1280.102) [300]"}
        ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 118
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1281.3--1281.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1281.10--1281.212) [301]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 119
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1282.3--1282.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) == ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1282.10--1282.313) [302]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 120
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1283.3--1283.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1283.10--1283.168) [303]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 121
  // assert ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1284.3--1284.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) >= ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1284.10--1284.99) [304]"}
      ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 122
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1285.3--1285.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1285.10--1285.243) [305]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) == ($struct_get($struct_loc($old_self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1285.10--1285.243) [306]"}
        ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 123
  // assert ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1286.3--1286.55
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1286.10--1286.55) [307]"}
      ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 124
  // assert ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1287.3--1287.94
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) != ($struct_get($struct_loc(self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1287.10--1287.94) [308]"}
      ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 125
  // assert ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1288.3--1288.125
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1288.10--1288.125) [309]"}
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 126
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1289.3--1289.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1289.10--1289.173) [310]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 127
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1290.3--1290.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == ($struct_get($struct_loc(self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1290.10--1290.211) [311]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 128
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1291.3--1291.392
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) + ($struct_get($struct_loc(self, 4)): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1291.10--1291.392) [312]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 129
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1292.3--1292.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_10 && q$a_10 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_10 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_10 != ($struct_get(($struct_loc(self, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1292.11--1292.513) [313]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_10): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_10): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_10): int);
        }
      }
      assume false;
    }
    assume (forall q$a_11_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_11_1): int) }
      0 <= q$a_11_1 && q$a_11_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_11_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_11_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_11_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_11_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_11_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 130
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1293.3--1293.87
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1293.10--1293.87) [314]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 131
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1294.3--1294.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_13 && q$a_13 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_13): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1294.11--1294.343) [315]"}
            ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_13): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_14_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_14_1): int) }
      0 <= q$a_14_1 && q$a_14_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_14_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_14_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 132
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1295.3--1295.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_16 && q$a_16 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_16 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_16): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1295.11--1295.396) [316]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_16): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_17_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_17_1): int) }
      0 <= q$a_17_1 && q$a_17_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_17_1 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_17_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_17_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 133
  // assert (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1296.3--1296.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    if (*) {
      assume false;
    }
    assume state(Heap, Mask);

  // -- Translating statement: if (l$send_fail) -- testsresourcesexamplesauction.vy.vpr@1297.3--1300.4
    if (l$send_fail) {

      // -- Translating statement: // id = 134
  // inhale acc($failed(($struct_get($struct_loc(msg, 0)): Int)), write) -- testsresourcesexamplesauction.vy.vpr@1298.5--1298.72
        perm := FullPerm;
        Mask[null, $failed(($struct_get(($struct_loc(msg, 0): int)): int))] := Mask[null, $failed(($struct_get(($struct_loc(msg, 0): int)): int))] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);

      // -- Translating statement: // id = 135
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1299.5--1299.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 136
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 137
  // $contracts := $old_$contracts -- testsresourcesexamplesauction.vy.vpr@1302.3--1302.32
    $contracts := $old_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 138
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1304.3--1304.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 139
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1305.3--1305.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 140
  // i0$$pre_self := self -- testsresourcesexamplesauction.vy.vpr@1307.3--1307.23
    i0$$pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 141
  // i0$$pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1308.3--1308.35
    i0$$pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 142
  // $contracts := l$havoc$1 -- testsresourcesexamplesauction.vy.vpr@1310.3--1310.26
    $contracts := l$havoc$1;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 143
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1312.3--1312.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 144
  // self := l$havoc$2 -- testsresourcesexamplesauction.vy.vpr@1314.3--1314.20
    self := l$havoc$2;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 145
  // $contracts := l$havoc$3 -- testsresourcesexamplesauction.vy.vpr@1315.3--1315.26
    $contracts := l$havoc$3;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 146
  // inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1317.3--1317.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 147
  // inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1318.3--1318.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 148
  // inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1319.3--1319.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 149
  // inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1320.3--1320.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 150
  // inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1321.3--1321.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 151
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1322.3--1322.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_5): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 152
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1323.3--1323.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_7: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_7): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_7): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 153
  // inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1324.3--1324.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 154
  // inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@1325.3--1325.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 155
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1326.3--1326.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_5): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 156
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1327.3--1327.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_7: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_7): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_7): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 157
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1328.3--1328.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_5): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 158
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1329.3--1329.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_7: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_7): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_7): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 159
  // inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@1330.3--1330.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 160
  // inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc($old_self, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@1332.3--1332.263

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc($old_self, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_3): int) >= ($map_get(($struct_get(($struct_loc($old_self, 10): int)): $MapDomainType int int), $a_3): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 161
  // inhale ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1333.3--1333.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 162
  // inhale ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1334.3--1334.99
    assume ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 163
  // inhale ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1335.3--1335.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 164
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1336.3--1336.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 165
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1337.3--1337.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 166
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1338.3--1338.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 167
  // inhale ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1339.3--1339.99
    assume ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 168
  // inhale ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1340.3--1340.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assume ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 169
  // inhale ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1341.3--1341.55
    assume ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 170
  // inhale ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1342.3--1342.94
    assume ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 171
  // inhale ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1343.3--1343.125
    assume ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 172
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1344.3--1344.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 173
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1345.3--1345.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 174
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1346.3--1346.392
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 175
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1347.3--1347.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_22: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_22): int) }
      0 <= q$a_22 && q$a_22 <= 1461501637330902918203684832716283019655932542975 ==> q$a_22 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_22 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_22): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_22): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_22): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 176
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1348.3--1348.87
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 177
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1349.3--1349.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_24: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_24): int) }
      0 <= q$a_24 && q$a_24 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_24): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_24): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 178
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1350.3--1350.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_26: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_26): int) }
      0 <= q$a_26 && q$a_26 <= 1461501637330902918203684832716283019655932542975 ==> q$a_26 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_26): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_26): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 179
  // inhale (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1351.3--1351.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: if (l$no_reentrant_call) -- testsresourcesexamplesauction.vy.vpr@1352.3--1356.4
    if (l$no_reentrant_call) {

      // -- Translating statement: // id = 180
  // self := $old_self -- testsresourcesexamplesauction.vy.vpr@1354.5--1354.22
        self := $old_self;
        assume state(Heap, Mask);

      // -- Translating statement: // id = 181
  // $contracts := $old_$contracts -- testsresourcesexamplesauction.vy.vpr@1355.5--1355.34
        $contracts := $old_$contracts;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 182
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 183
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1358.3--1358.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 184
  // $contracts := l$havoc$4 -- testsresourcesexamplesauction.vy.vpr@1360.3--1360.26
    $contracts := l$havoc$4;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 185
  // $old_$contracts := i0$$pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1362.3--1362.40
    $old_$contracts := i0$$pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 186
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1364.3--1364.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 187
  // $contracts := l$havoc$5 -- testsresourcesexamplesauction.vy.vpr@1366.3--1366.26
    $contracts := l$havoc$5;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 188
  // $old_$contracts := i0$$pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1368.3--1368.40
    $old_$contracts := i0$$pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 189
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1370.3--1370.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 190
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1371.3--1371.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 191
  // label return -- testsresourcesexamplesauction.vy.vpr@1372.3--1372.15
    vreturn:
    LabelreturnMask := Mask;
    LabelreturnHeap := Heap;
    return_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: if ($out_of_gas) -- testsresourcesexamplesauction.vy.vpr@1373.3--1375.4
    if ($out_of_gas) {

      // -- Translating statement: // id = 192
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1374.5--1374.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 193
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 194
  // goto end -- testsresourcesexamplesauction.vy.vpr@1376.3--1376.11
    goto end;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 195
  // label revert -- testsresourcesexamplesauction.vy.vpr@1377.3--1377.15
    revert:
    LabelrevertMask := Mask;
    LabelrevertHeap := Heap;
    revert_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 196
  // $succ := false -- testsresourcesexamplesauction.vy.vpr@1378.3--1378.17
    $succ := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 197
  // self := $pre_self -- testsresourcesexamplesauction.vy.vpr@1380.3--1380.20
    self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 198
  // $contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1381.3--1381.32
    $contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 199
  // $old_self := $pre_self -- testsresourcesexamplesauction.vy.vpr@1383.3--1383.25
    $old_self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 200
  // $old_$contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1384.3--1384.37
    $old_$contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 201
  // label end -- testsresourcesexamplesauction.vy.vpr@1385.3--1385.12
    end:
    LabelendMask := Mask;
    LabelendHeap := Heap;
    end_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 202
  // exhale !($out_of_gas ||
  //   ($out_of_gas ||
  //   perm($failed(($struct_get($struct_loc(msg, 0)): Int))) > none)) ==>
  //   $succ -- testsresourcesexamplesauction.vy.vpr@1387.3--1387.116
    if (!($out_of_gas || ($out_of_gas || NoPerm < Mask[null, $failed(($struct_get(($struct_loc(msg, 0): int)): int))]))) {
      assert {:msg "  Exhale might fail. Assertion $succ might not hold. (testsresourcesexamplesauction.vy.vpr@1387.10--1387.116) [319]"}
        $succ;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 203
  // assert $succ &&
  //   (($struct_get($struct_loc(msg, 1)): Int) >
  //   ($struct_get($struct_loc($pre_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) != 0) ==>
  //   ($struct_get($struct_loc(msg, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1388.3--1388.243
    if ($succ && (($struct_get(($struct_loc(msg, 1): int)): int) > ($struct_get(($struct_loc($pre_self, 4): int)): int) && ($struct_get(($struct_loc(self, 3): int)): int) != 0)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(msg, 0)): Int) == ($struct_get($struct_loc(self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1388.10--1388.243) [320]"}
        ($struct_get(($struct_loc(msg, 0): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: if ($succ) -- testsresourcesexamplesauction.vy.vpr@1390.3--1392.4
    if ($succ) {

      // -- Translating statement: // id = 204
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 205
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 206
  // inhale l$havoc$6 >= 0 -- testsresourcesexamplesauction.vy.vpr@1393.3--1393.24
    assume l$havoc$6 >= 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 207
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   l$havoc$6): $Struct) -- testsresourcesexamplesauction.vy.vpr@1394.3--1394.96
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + l$havoc$6): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 208
  // $contracts := l$havoc$7 -- testsresourcesexamplesauction.vy.vpr@1396.3--1396.26
    $contracts := l$havoc$7;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 209
  // assert ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1398.3--1398.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1398.10--1398.105) [321]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 210
  // assert ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1399.3--1399.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) == ($struct_get($struct_loc($old_self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1399.10--1399.99) [322]"}
      ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 211
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1400.3--1400.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@1400.10--1400.102) [323]"}
        ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 212
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1401.3--1401.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1401.10--1401.212) [324]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 213
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1402.3--1402.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) == ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1402.10--1402.313) [325]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 214
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1403.3--1403.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1403.10--1403.168) [326]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 215
  // assert ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1404.3--1404.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) >= ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1404.10--1404.99) [327]"}
      ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 216
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1405.3--1405.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1405.10--1405.243) [328]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) == ($struct_get($struct_loc($old_self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1405.10--1405.243) [329]"}
        ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 217
  // assert ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1406.3--1406.55
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1406.10--1406.55) [330]"}
      ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 218
  // assert ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1407.3--1407.94
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) != ($struct_get($struct_loc(self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1407.10--1407.94) [331]"}
      ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 219
  // assert ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1408.3--1408.125
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1408.10--1408.125) [332]"}
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 220
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1409.3--1409.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1409.10--1409.173) [333]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 221
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1410.3--1410.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == ($struct_get($struct_loc(self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1410.10--1410.211) [334]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 222
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1411.3--1411.392
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) + ($struct_get($struct_loc(self, 4)): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1411.10--1411.392) [335]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 223
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1412.3--1412.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_30 && q$a_30 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_30 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_30 != ($struct_get(($struct_loc(self, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1412.11--1412.513) [336]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_30): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_30): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_30): int);
        }
      }
      assume false;
    }
    assume (forall q$a_31_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_31_1): int) }
      0 <= q$a_31_1 && q$a_31_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_31_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_31_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_31_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_31_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_31_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 224
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1413.3--1413.87
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1413.10--1413.87) [337]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 225
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1414.3--1414.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_33 && q$a_33 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_33): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1414.11--1414.343) [338]"}
            ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_33): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_34_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_34_1): int) }
      0 <= q$a_34_1 && q$a_34_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_34_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_34_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 226
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1415.3--1415.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_36 && q$a_36 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_36 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_36): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1415.11--1415.396) [339]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_36): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_37_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_37_1): int) }
      0 <= q$a_37_1 && q$a_37_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_37_1 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_37_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_37_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 227
  // assert (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1416.3--1416.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    if (*) {
      assume false;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 228
  // assert (forall $a: Int ::
  //     { $accessible$withdraw(18, ($struct_get($struct_loc(msg, 0)): Int), $a) }
  //     perm($accessible$withdraw(18, ($struct_get($struct_loc(msg, 0)): Int), $a)) >
  //     none ==>
  //     (!(perm($failed(($struct_get($struct_loc(msg, 0)): Int))) > none ||
  //     $out_of_gas) ==>
  //     $succ) &&
  //     ($succ ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(msg,
  //     0)): Int)): Int) -
  //     ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(msg,
  //     0)): Int)): Int) >=
  //     $a)) -- testsresourcesexamplesauction.vy.vpr@1418.3--1418.532

    // -- Check definedness of (forall $a: Int :: { $accessible$withdraw(18, ($struct_get($struct_loc(msg, 0)): Int), $a) } perm($accessible$withdraw(18, ($struct_get($struct_loc(msg, 0)): Int), $a)) > none ==> (!(perm($failed(($struct_get($struct_loc(msg, 0)): Int))) > none || $out_of_gas) ==> $succ) && ($succ ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(msg, 0)): Int)): Int) - ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(msg, 0)): Int)): Int) >= $a))
      if (*) {
        assume false;
      }
    if (*) {
      if (NoPerm < Mask[null, $accessible$withdraw(18, ($struct_get(($struct_loc(msg, 0): int)): int), $a_5)]) {
        if (!(NoPerm < Mask[null, $failed(($struct_get(($struct_loc(msg, 0): int)): int))] || $out_of_gas)) {
          assert {:msg "  Assert might fail. Assertion $succ might not hold. (testsresourcesexamplesauction.vy.vpr@1418.11--1418.531) [341]"}
            $succ;
        }
        if ($succ) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(msg, 0)): Int)): Int) - ($map_get(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(msg, 0)): Int)): Int) >= $a might not hold. (testsresourcesexamplesauction.vy.vpr@1418.11--1418.531) [342]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int) - ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int) >= $a_5;
        }
      }
      assume false;
    }
    assume (forall $a_6_1: int ::
      { Heap[null, $accessible$withdraw(18, ($struct_get(($struct_loc(msg, 0): int)): int), $a_6_1)] }
      NoPerm < Mask[null, $accessible$withdraw(18, ($struct_get(($struct_loc(msg, 0): int)): int), $a_6_1)] ==> (!(NoPerm < Mask[null, $failed(($struct_get(($struct_loc(msg, 0): int)): int))] || $out_of_gas) ==> $succ) && ($succ ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int) - ($map_get(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(msg, 0): int)): int)): int) >= $a_6_1)
    );
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method f$endAuction
// ==================================================

procedure f$endAuction() returns ($succ: bool)
  modifies Heap, Mask;
{
  var revert_lblGuard: bool;
  var end_lblGuard: bool;
  var return_lblGuard: bool;
  var self: $StructDomainType;
  var block: $StructDomainType;
  var msg: $StructDomainType;
  var $pre_self: $StructDomainType;
  var $pre_$contracts: ($MapDomainType int $StructDomainType);
  var $contracts: ($MapDomainType int $StructDomainType);
  var $old_self: $StructDomainType;
  var $old_$contracts: ($MapDomainType int $StructDomainType);
  var $overflow: bool;
  var l$havoc: ($MapDomainType int $StructDomainType);
  var q$a_9: int;
  var q$a_12: int;
  var q$a_15: int;
  var l$send_fail: bool;
  var perm: Perm;
  var i0$$pre_self: $StructDomainType;
  var i0$$pre_$contracts: ($MapDomainType int $StructDomainType);
  var l$havoc$1: ($MapDomainType int $StructDomainType);
  var l$havoc$2: $StructDomainType;
  var l$havoc$3: ($MapDomainType int $StructDomainType);
  var l$no_reentrant_call: bool;
  var l$havoc$4: ($MapDomainType int $StructDomainType);
  var l$havoc$5: ($MapDomainType int $StructDomainType);
  var LabelreturnMask: MaskType;
  var LabelreturnHeap: HeapType;
  var $out_of_gas: bool;
  var LabelrevertMask: MaskType;
  var LabelrevertHeap: HeapType;
  var LabelendMask: MaskType;
  var LabelendHeap: HeapType;
  var l$havoc$6: int;
  var l$havoc$7: ($MapDomainType int $StructDomainType);
  var q$a_29: int;
  var q$a_32: int;
  var q$a_35: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    revert_lblGuard := false;
    end_lblGuard := false;
    return_lblGuard := false;

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

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
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 47
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 48
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 49
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 50
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 51
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: // id = 52
  // inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1450.3--1450.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 53
  // inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1451.3--1451.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 54
  // inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1452.3--1452.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 55
  // inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1453.3--1453.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 56
  // inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1454.3--1454.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 57
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1455.3--1455.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 58
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1456.3--1456.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 59
  // inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1457.3--1457.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 60
  // inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@1458.3--1458.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 61
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1459.3--1459.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 62
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1460.3--1460.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 63
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1461.3--1461.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_1): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 64
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1462.3--1462.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_3): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 65
  // inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@1463.3--1463.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 66
  // inhale 0 <= $self_address() &&
  //   $self_address() <= 1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1465.3--1465.102
    assume 0 <= ($self_address(): int);
    assume ($self_address(): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 67
  // inhale 0 <= ($struct_get($struct_loc(block, 0)): Int) &&
  //   ($struct_get($struct_loc(block, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1467.3--1467.154
    assume 0 <= ($struct_get(($struct_loc(block, 0): int)): int);
    assume ($struct_get(($struct_loc(block, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 68
  // inhale 0 <= ($struct_get($struct_loc(block, 1)): Int) &&
  //   ($struct_get($struct_loc(block, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1468.3--1468.183
    assume 0 <= ($struct_get(($struct_loc(block, 1): int)): int);
    assume ($struct_get(($struct_loc(block, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 69
  // inhale 0 <= ($struct_get($struct_loc(block, 2)): Int) &&
  //   ($struct_get($struct_loc(block, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1469.3--1469.183
    assume 0 <= ($struct_get(($struct_loc(block, 2): int)): int);
    assume ($struct_get(($struct_loc(block, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 70
  // inhale |($struct_get($struct_loc(block, 3)): Seq[Int])| == 32 -- testsresourcesexamplesauction.vy.vpr@1470.3--1470.64
    assume Seq#Length(($struct_get(($struct_loc(block, 3): int)): Seq int)) == 32;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 71
  // inhale 0 <= ($struct_get($struct_loc(block, 4)): Int) &&
  //   ($struct_get($struct_loc(block, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1471.3--1471.183
    assume 0 <= ($struct_get(($struct_loc(block, 4): int)): int);
    assume ($struct_get(($struct_loc(block, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 72
  // inhale ($struct_get($struct_loc(block, -1)): Int) ==
  //   2335365049822495359383864865678187 -- testsresourcesexamplesauction.vy.vpr@1472.3--1472.90
    assume ($struct_get(($struct_loc(block, -1): int)): int) == 2335365049822495359383864865678187;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 73
  // inhale 0 <= ($struct_get($struct_loc(msg, 0)): Int) &&
  //   ($struct_get($struct_loc(msg, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1474.3--1474.150
    assume 0 <= ($struct_get(($struct_loc(msg, 0): int)): int);
    assume ($struct_get(($struct_loc(msg, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 74
  // inhale 0 <= ($struct_get($struct_loc(msg, 1)): Int) &&
  //   ($struct_get($struct_loc(msg, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1475.3--1475.179
    assume 0 <= ($struct_get(($struct_loc(msg, 1): int)): int);
    assume ($struct_get(($struct_loc(msg, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 75
  // inhale 0 <= ($struct_get($struct_loc(msg, 2)): Int) &&
  //   ($struct_get($struct_loc(msg, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1476.3--1476.179
    assume 0 <= ($struct_get(($struct_loc(msg, 2): int)): int);
    assume ($struct_get(($struct_loc(msg, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 76
  // inhale ($struct_get($struct_loc(msg, -1)): Int) ==
  //   35634842679176259756224246631 -- testsresourcesexamplesauction.vy.vpr@1477.3--1477.83
    assume ($struct_get(($struct_loc(msg, -1): int)): int) == 35634842679176259756224246631;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 77
  // inhale ($struct_get($struct_loc(msg, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1478.3--1478.54
    assume ($struct_get(($struct_loc(msg, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 78
  // inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@1480.3--1480.258

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int) >= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_1_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 79
  // inhale ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1481.3--1481.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 80
  // inhale ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1482.3--1482.94
    assume ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 81
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1483.3--1483.97
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 82
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1484.3--1484.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 83
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1485.3--1485.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 84
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1486.3--1486.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 85
  // inhale ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1487.3--1487.94
    assume ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc(self, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 86
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1488.3--1488.228
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
      assume ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 87
  // inhale ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1489.3--1489.55
    assume ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 88
  // inhale ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1490.3--1490.94
    assume ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 89
  // inhale ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1491.3--1491.125
    assume ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 90
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1492.3--1492.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 91
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1493.3--1493.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 92
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1494.3--1494.392
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 93
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1495.3--1495.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int) }
      0 <= q$a_1 && q$a_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_1): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 94
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1496.3--1496.87
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 95
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1497.3--1497.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) }
      0 <= q$a_3 && q$a_3 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_3): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_3): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 96
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1498.3--1498.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) }
      0 <= q$a_5 && q$a_5 <= 1461501637330902918203684832716283019655932542975 ==> q$a_5 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_5): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_5): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 97
  // inhale (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1499.3--1499.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 98
  // $pre_self := self -- testsresourcesexamplesauction.vy.vpr@1501.3--1501.20
    $pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 99
  // $pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1502.3--1502.32
    $pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 100
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1504.3--1504.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 101
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1505.3--1505.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 102
  // $succ := true -- testsresourcesexamplesauction.vy.vpr@1506.3--1506.16
    $succ := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 103
  // $overflow := false -- testsresourcesexamplesauction.vy.vpr@1507.3--1507.21
    $overflow := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 104
  // inhale ($struct_get($struct_loc(msg, 1)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1509.3--1509.54
    assume ($struct_get(($struct_loc(msg, 1): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: if (!(($struct_get($struct_loc(block, 4)): Int) >= ($struct_get($struct_loc(self, 2)): Int))) -- testsresourcesexamplesauction.vy.vpr@1511.3--1513.4
    if (!(($struct_get(($struct_loc(block, 4): int)): int) >= ($struct_get(($struct_loc(self, 2): int)): int))) {

      // -- Translating statement: // id = 105
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1512.5--1512.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 106
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 107
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
    assume state(Heap, Mask);

  // -- Translating statement: if (!!($struct_get($struct_loc(self, 5)): Bool)) -- testsresourcesexamplesauction.vy.vpr@1514.3--1516.4
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {

      // -- Translating statement: // id = 108
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1515.5--1515.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 109
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 110
  // self := ($struct_set(self, 5, true): $Struct) -- testsresourcesexamplesauction.vy.vpr@1517.3--1517.48
    self := ($struct_set(self, 5, true): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: if (($struct_get($struct_loc(self, 7)): Int) < ($struct_get($struct_loc(self, 4)): Int)) -- testsresourcesexamplesauction.vy.vpr@1518.3--1520.4
    if (($struct_get(($struct_loc(self, 7): int)): int) < ($struct_get(($struct_loc(self, 4): int)): int)) {

      // -- Translating statement: // id = 111
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1519.5--1519.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 112
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 113
  // self := ($struct_set(self, 10, ($map_set(($struct_get($struct_loc(self, 10)): $Map[Int, Int]),
  //   ($struct_get($struct_loc(self, 0)): Int), ($map_get(($struct_get($struct_loc(self,
  //   10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int)): $Map[Int, Int])): $Struct) -- testsresourcesexamplesauction.vy.vpr@1521.3--1521.323
    self := ($struct_set(self, 10, ($map_set(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int), ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int)): $MapDomainType int int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 114
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) -
  //   ($struct_get($struct_loc(self, 4)): Int)): $Struct) -- testsresourcesexamplesauction.vy.vpr@1522.3--1522.127
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) - ($struct_get(($struct_loc(self, 4): int)): int)): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 115
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1524.3--1524.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 116
  // $contracts := l$havoc -- testsresourcesexamplesauction.vy.vpr@1526.3--1526.24
    $contracts := l$havoc;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 117
  // assert ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1528.3--1528.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1528.10--1528.105) [343]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 118
  // assert ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1529.3--1529.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) == ($struct_get($struct_loc($old_self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1529.10--1529.99) [344]"}
      ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 119
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1530.3--1530.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@1530.10--1530.102) [345]"}
        ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 120
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1531.3--1531.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1531.10--1531.212) [346]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 121
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1532.3--1532.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) == ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1532.10--1532.313) [347]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 122
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1533.3--1533.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1533.10--1533.168) [348]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 123
  // assert ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1534.3--1534.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) >= ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1534.10--1534.99) [349]"}
      ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 124
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1535.3--1535.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1535.10--1535.243) [350]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) == ($struct_get($struct_loc($old_self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1535.10--1535.243) [351]"}
        ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 125
  // assert ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1536.3--1536.55
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1536.10--1536.55) [352]"}
      ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 126
  // assert ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1537.3--1537.94
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) != ($struct_get($struct_loc(self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1537.10--1537.94) [353]"}
      ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 127
  // assert ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1538.3--1538.125
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1538.10--1538.125) [354]"}
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 128
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1539.3--1539.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1539.10--1539.173) [355]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 129
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1540.3--1540.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == ($struct_get($struct_loc(self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1540.10--1540.211) [356]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 130
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1541.3--1541.392
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) + ($struct_get($struct_loc(self, 4)): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1541.10--1541.392) [357]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 131
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1542.3--1542.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_9 && q$a_9 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_9 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_9 != ($struct_get(($struct_loc(self, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1542.11--1542.513) [358]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_9): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_9): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_9): int);
        }
      }
      assume false;
    }
    assume (forall q$a_10_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_10_1): int) }
      0 <= q$a_10_1 && q$a_10_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_10_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_10_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_10_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_10_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_10_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 132
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1543.3--1543.87
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1543.10--1543.87) [359]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 133
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1544.3--1544.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_12 && q$a_12 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_12): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1544.11--1544.343) [360]"}
            ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_12): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_13_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_13_1): int) }
      0 <= q$a_13_1 && q$a_13_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_13_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_13_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 134
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1545.3--1545.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_15 && q$a_15 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_15 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_15): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1545.11--1545.396) [361]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_15): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_16_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_16_1_1): int) }
      0 <= q$a_16_1_1 && q$a_16_1_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_16_1_1 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_16_1_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_16_1_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 135
  // assert (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1546.3--1546.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    if (*) {
      assume false;
    }
    assume state(Heap, Mask);

  // -- Translating statement: if (l$send_fail) -- testsresourcesexamplesauction.vy.vpr@1547.3--1550.4
    if (l$send_fail) {

      // -- Translating statement: // id = 136
  // inhale acc($failed(($struct_get($struct_loc(self, 0)): Int)), write) -- testsresourcesexamplesauction.vy.vpr@1548.5--1548.73
        perm := FullPerm;
        Mask[null, $failed(($struct_get(($struct_loc(self, 0): int)): int))] := Mask[null, $failed(($struct_get(($struct_loc(self, 0): int)): int))] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume state(Heap, Mask);

      // -- Translating statement: // id = 137
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1549.5--1549.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 138
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 139
  // $contracts := $old_$contracts -- testsresourcesexamplesauction.vy.vpr@1552.3--1552.32
    $contracts := $old_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 140
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1554.3--1554.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 141
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1555.3--1555.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 142
  // i0$$pre_self := self -- testsresourcesexamplesauction.vy.vpr@1557.3--1557.23
    i0$$pre_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 143
  // i0$$pre_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1558.3--1558.35
    i0$$pre_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 144
  // $contracts := l$havoc$1 -- testsresourcesexamplesauction.vy.vpr@1560.3--1560.26
    $contracts := l$havoc$1;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 145
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1562.3--1562.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 146
  // self := l$havoc$2 -- testsresourcesexamplesauction.vy.vpr@1564.3--1564.20
    self := l$havoc$2;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 147
  // $contracts := l$havoc$3 -- testsresourcesexamplesauction.vy.vpr@1565.3--1565.26
    $contracts := l$havoc$3;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 148
  // inhale 0 <= ($struct_get($struct_loc(self, 0)): Int) &&
  //   ($struct_get($struct_loc(self, 0)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1567.3--1567.152
    assume 0 <= ($struct_get(($struct_loc(self, 0): int)): int);
    assume ($struct_get(($struct_loc(self, 0): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 149
  // inhale 0 <= ($struct_get($struct_loc(self, 1)): Int) &&
  //   ($struct_get($struct_loc(self, 1)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1568.3--1568.181
    assume 0 <= ($struct_get(($struct_loc(self, 1): int)): int);
    assume ($struct_get(($struct_loc(self, 1): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 150
  // inhale 0 <= ($struct_get($struct_loc(self, 2)): Int) &&
  //   ($struct_get($struct_loc(self, 2)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1569.3--1569.181
    assume 0 <= ($struct_get(($struct_loc(self, 2): int)): int);
    assume ($struct_get(($struct_loc(self, 2): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 151
  // inhale 0 <= ($struct_get($struct_loc(self, 3)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) <=
  //   1461501637330902918203684832716283019655932542975 -- testsresourcesexamplesauction.vy.vpr@1570.3--1570.152
    assume 0 <= ($struct_get(($struct_loc(self, 3): int)): int);
    assume ($struct_get(($struct_loc(self, 3): int)): int) <= 1461501637330902918203684832716283019655932542975;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 152
  // inhale 0 <= ($struct_get($struct_loc(self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1571.3--1571.181
    assume 0 <= ($struct_get(($struct_loc(self, 4): int)): int);
    assume ($struct_get(($struct_loc(self, 4): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 153
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1572.3--1572.346

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) && ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q0_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_5): int) && ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 154
  // inhale (forall $q0: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1573.3--1573.254

    // -- Check definedness of (forall $q0: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) } ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), $q0): Int) <= ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q0_7: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_7): int) }
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), $q0_7): int) <= ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 155
  // inhale 0 <= ($struct_get($struct_loc(self, 7)): Int) &&
  //   ($struct_get($struct_loc(self, 7)): Int) <=
  //   115792089237316195423570985008687907853269984665640564039457584007913129639935 -- testsresourcesexamplesauction.vy.vpr@1574.3--1574.181
    assume 0 <= ($struct_get(($struct_loc(self, 7): int)): int);
    assume ($struct_get(($struct_loc(self, 7): int)): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 156
  // inhale -170141183460469231731687303715884105728 <=
  //   ($struct_get($struct_loc(self, 8)): Int) &&
  //   ($struct_get($struct_loc(self, 8)): Int) <=
  //   170141183460469231731687303715884105727 -- testsresourcesexamplesauction.vy.vpr@1575.3--1575.181
    assume -170141183460469231731687303715884105728 <= ($struct_get(($struct_loc(self, 8): int)): int);
    assume ($struct_get(($struct_loc(self, 8): int)): int) <= 170141183460469231731687303715884105727;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 157
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1576.3--1576.349

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) && ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q1_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_5): int) && ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 158
  // inhale (forall $q1: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1577.3--1577.257

    // -- Check definedness of (forall $q1: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $q1): Int) <= ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q1_7: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_7): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $q1_7): int) <= ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 159
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     0 <=
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935) -- testsresourcesexamplesauction.vy.vpr@1578.3--1578.349

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } 0 <= ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      if (*) {
        assume false;
      }
    assume (forall $q2_5: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_5): int) }
      0 <= ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_5): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_5): int) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 160
  // inhale (forall $q2: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <=
  //     ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int)) -- testsresourcesexamplesauction.vy.vpr@1579.3--1579.257

    // -- Check definedness of (forall $q2: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) } ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), $q2): Int) <= ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int))
      if (*) {
        assume false;
      }
    assume (forall $q2_7: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_7): int) }
      ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), $q2_7): int) <= ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 161
  // inhale ($struct_get($struct_loc(self, -1)): Int) ==
  //   9122519725869122497593506884710 -- testsresourcesexamplesauction.vy.vpr@1580.3--1580.86
    assume ($struct_get(($struct_loc(self, -1): int)): int) == 9122519725869122497593506884710;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 162
  // inhale (forall $a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) }
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >=
  //     ($map_get(($struct_get($struct_loc($old_self, 10)): $Map[Int, Int]), $a): Int)) -- testsresourcesexamplesauction.vy.vpr@1582.3--1582.263

    // -- Check definedness of (forall $a: Int :: { ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) } ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), $a): Int) >= ($map_get(($struct_get($struct_loc($old_self, 10)): $Map[Int, Int]), $a): Int))
      if (*) {
        assume false;
      }
    assume (forall $a_3: int ::
      { ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_3): int) }
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), $a_3): int) >= ($map_get(($struct_get(($struct_loc($old_self, 10): int)): $MapDomainType int int), $a_3): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 163
  // inhale ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1583.3--1583.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 164
  // inhale ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1584.3--1584.99
    assume ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 165
  // inhale ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1585.3--1585.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 166
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1586.3--1586.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 167
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1587.3--1587.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 168
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1588.3--1588.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 169
  // inhale ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1589.3--1589.99
    assume ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 170
  // inhale ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1590.3--1590.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assume ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assume ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 171
  // inhale ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1591.3--1591.55
    assume ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 172
  // inhale ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1592.3--1592.94
    assume ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 173
  // inhale ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1593.3--1593.125
    assume ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 174
  // inhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1594.3--1594.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 175
  // inhale ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1595.3--1595.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 176
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1596.3--1596.392
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 177
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1597.3--1597.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    assume (forall q$a_21: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_21): int) }
      0 <= q$a_21 && q$a_21 <= 1461501637330902918203684832716283019655932542975 ==> q$a_21 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_21 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_21): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_21): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_21): int)
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 178
  // inhale ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1598.3--1598.87
    assume ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 179
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1599.3--1599.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_23: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_23): int) }
      0 <= q$a_23 && q$a_23 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_23): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_23): int) != 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 180
  // inhale (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1600.3--1600.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    assume (forall q$a_25: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_25): int) }
      0 <= q$a_25 && q$a_25 <= 1461501637330902918203684832716283019655932542975 ==> q$a_25 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_25): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_25): int) == 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 181
  // inhale (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1601.3--1601.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: if (l$no_reentrant_call) -- testsresourcesexamplesauction.vy.vpr@1602.3--1606.4
    if (l$no_reentrant_call) {

      // -- Translating statement: // id = 182
  // self := $old_self -- testsresourcesexamplesauction.vy.vpr@1604.5--1604.22
        self := $old_self;
        assume state(Heap, Mask);

      // -- Translating statement: // id = 183
  // $contracts := $old_$contracts -- testsresourcesexamplesauction.vy.vpr@1605.5--1605.34
        $contracts := $old_$contracts;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 184
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 185
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1608.3--1608.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 186
  // $contracts := l$havoc$4 -- testsresourcesexamplesauction.vy.vpr@1610.3--1610.26
    $contracts := l$havoc$4;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 187
  // $old_$contracts := i0$$pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1612.3--1612.40
    $old_$contracts := i0$$pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 188
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1614.3--1614.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 189
  // $contracts := l$havoc$5 -- testsresourcesexamplesauction.vy.vpr@1616.3--1616.26
    $contracts := l$havoc$5;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 190
  // $old_$contracts := i0$$pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1618.3--1618.40
    $old_$contracts := i0$$pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 191
  // $old_self := self -- testsresourcesexamplesauction.vy.vpr@1620.3--1620.20
    $old_self := self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 192
  // $old_$contracts := $contracts -- testsresourcesexamplesauction.vy.vpr@1621.3--1621.32
    $old_$contracts := $contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 193
  // label return -- testsresourcesexamplesauction.vy.vpr@1622.3--1622.15
    vreturn:
    LabelreturnMask := Mask;
    LabelreturnHeap := Heap;
    return_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: if ($out_of_gas) -- testsresourcesexamplesauction.vy.vpr@1623.3--1625.4
    if ($out_of_gas) {

      // -- Translating statement: // id = 194
  // goto revert -- testsresourcesexamplesauction.vy.vpr@1624.5--1624.16
        goto revert;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 195
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 196
  // goto end -- testsresourcesexamplesauction.vy.vpr@1626.3--1626.11
    goto end;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 197
  // label revert -- testsresourcesexamplesauction.vy.vpr@1627.3--1627.15
    revert:
    LabelrevertMask := Mask;
    LabelrevertHeap := Heap;
    revert_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 198
  // $succ := false -- testsresourcesexamplesauction.vy.vpr@1628.3--1628.17
    $succ := false;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 199
  // self := $pre_self -- testsresourcesexamplesauction.vy.vpr@1630.3--1630.20
    self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 200
  // $contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1631.3--1631.32
    $contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 201
  // $old_self := $pre_self -- testsresourcesexamplesauction.vy.vpr@1633.3--1633.25
    $old_self := $pre_self;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 202
  // $old_$contracts := $pre_$contracts -- testsresourcesexamplesauction.vy.vpr@1634.3--1634.37
    $old_$contracts := $pre_$contracts;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 203
  // label end -- testsresourcesexamplesauction.vy.vpr@1635.3--1635.12
    end:
    LabelendMask := Mask;
    LabelendHeap := Heap;
    end_lblGuard := true;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 204
  // exhale !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) ==
  //   ($map_sum(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1637.3--1637.204
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Exhale might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) == ($map_sum(($struct_get($struct_loc($pre_self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1637.10--1637.204) [364]"}
        ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int) == ($map_sum(($struct_get(($struct_loc($pre_self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 205
  // assert $succ &&
  //   (($struct_get($struct_loc(msg, 1)): Int) >
  //   ($struct_get($struct_loc($pre_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) != 0) ==>
  //   ($struct_get($struct_loc(msg, 0)): Int) ==
  //   ($struct_get($struct_loc(self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1638.3--1638.243
    if ($succ && (($struct_get(($struct_loc(msg, 1): int)): int) > ($struct_get(($struct_loc($pre_self, 4): int)): int) && ($struct_get(($struct_loc(self, 3): int)): int) != 0)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(msg, 0)): Int) == ($struct_get($struct_loc(self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1638.10--1638.243) [365]"}
        ($struct_get(($struct_loc(msg, 0): int)): int) == ($struct_get(($struct_loc(self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: if ($succ) -- testsresourcesexamplesauction.vy.vpr@1640.3--1642.4
    if ($succ) {

      // -- Translating statement: // id = 206
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: // id = 207
  // // LoopDummyStmtInfo()
  // inhale true -- <no position>
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 208
  // inhale l$havoc$6 >= 0 -- testsresourcesexamplesauction.vy.vpr@1643.3--1643.24
    assume l$havoc$6 >= 0;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 209
  // self := ($struct_set(self, 7, ($struct_get($struct_loc(self, 7)): Int) +
  //   l$havoc$6): $Struct) -- testsresourcesexamplesauction.vy.vpr@1644.3--1644.96
    self := ($struct_set(self, 7, ($struct_get(($struct_loc(self, 7): int)): int) + l$havoc$6): $StructDomainType);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 210
  // $contracts := l$havoc$7 -- testsresourcesexamplesauction.vy.vpr@1646.3--1646.26
    $contracts := l$havoc$7;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 211
  // assert ($struct_get($struct_loc(self, 3)): Int) == 0 ==>
  //   ($struct_get($struct_loc(self, 4)): Int) == 0 -- testsresourcesexamplesauction.vy.vpr@1648.3--1648.105
    if (($struct_get(($struct_loc(self, 3): int)): int) == 0) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1648.10--1648.105) [366]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 212
  // assert ($struct_get($struct_loc(self, 0)): Int) ==
  //   ($struct_get($struct_loc($old_self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1649.3--1649.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) == ($struct_get($struct_loc($old_self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1649.10--1649.99) [367]"}
      ($struct_get(($struct_loc(self, 0): int)): int) == ($struct_get(($struct_loc($old_self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 213
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 5)): Bool) -- testsresourcesexamplesauction.vy.vpr@1650.3--1650.102
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 5)): Bool) might not hold. (testsresourcesexamplesauction.vy.vpr@1650.10--1650.102) [368]"}
        ($struct_get(($struct_loc(self, 5): int)): bool);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 214
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1651.3--1651.212
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1651.10--1651.212) [369]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 215
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) -
  //   ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) -- testsresourcesexamplesauction.vy.vpr@1652.3--1652.313
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) + ($struct_get($struct_loc(self, 4)): Int) == ($map_sum(($struct_get($struct_loc(self, 11)): $Map[Int, Int])): Int) - ($map_sum(($struct_get($struct_loc(self, 10)): $Map[Int, Int])): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1652.10--1652.313) [370]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) == ($map_sum(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int)): int) - ($map_sum(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 216
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <=
  //   ($struct_get($struct_loc(self, 7)): Int) -- testsresourcesexamplesauction.vy.vpr@1653.3--1653.168
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_sum(($struct_get($struct_loc(self, 6)): $Map[Int, Int])): Int) <= ($struct_get($struct_loc(self, 7)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1653.10--1653.168) [371]"}
        ($map_sum(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int)): int) <= ($struct_get(($struct_loc(self, 7): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 217
  // assert ($struct_get($struct_loc(self, 4)): Int) >=
  //   ($struct_get($struct_loc($old_self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1654.3--1654.99
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) >= ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1654.10--1654.99) [372]"}
      ($struct_get(($struct_loc(self, 4): int)): int) >= ($struct_get(($struct_loc($old_self, 4): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 218
  // assert ($struct_get($struct_loc($old_self, 5)): Bool) ==>
  //   ($struct_get($struct_loc(self, 4)): Int) ==
  //   ($struct_get($struct_loc($old_self, 4)): Int) &&
  //   ($struct_get($struct_loc(self, 3)): Int) ==
  //   ($struct_get($struct_loc($old_self, 3)): Int) -- testsresourcesexamplesauction.vy.vpr@1655.3--1655.243
    if (($struct_get(($struct_loc($old_self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 4)): Int) == ($struct_get($struct_loc($old_self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1655.10--1655.243) [373]"}
        ($struct_get(($struct_loc(self, 4): int)): int) == ($struct_get(($struct_loc($old_self, 4): int)): int);
      assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) == ($struct_get($struct_loc($old_self, 3)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1655.10--1655.243) [374]"}
        ($struct_get(($struct_loc(self, 3): int)): int) == ($struct_get(($struct_loc($old_self, 3): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 219
  // assert ($struct_get($struct_loc(self, 0)): Int) != 0 -- testsresourcesexamplesauction.vy.vpr@1656.3--1656.55
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 0)): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1656.10--1656.55) [375]"}
      ($struct_get(($struct_loc(self, 0): int)): int) != 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 220
  // assert ($struct_get($struct_loc(self, 3)): Int) !=
  //   ($struct_get($struct_loc(self, 0)): Int) -- testsresourcesexamplesauction.vy.vpr@1657.3--1657.94
    assert {:msg "  Assert might fail. Assertion ($struct_get($struct_loc(self, 3)): Int) != ($struct_get($struct_loc(self, 0)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1657.10--1657.94) [376]"}
      ($struct_get(($struct_loc(self, 3): int)): int) != ($struct_get(($struct_loc(self, 0): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 221
  // assert ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1658.3--1658.125
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1658.10--1658.125) [377]"}
      ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 222
  // assert !($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1659.3--1659.173
    if (!($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1659.10--1659.173) [378]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == 0;
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 223
  // assert ($struct_get($struct_loc(self, 5)): Bool) ==>
  //   ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   0)): Int)): Int) ==
  //   ($struct_get($struct_loc(self, 4)): Int) -- testsresourcesexamplesauction.vy.vpr@1660.3--1660.211
    if (($struct_get(($struct_loc(self, 5): int)): bool)) {
      assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 0)): Int)): Int) == ($struct_get($struct_loc(self, 4)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1660.10--1660.211) [379]"}
        ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 0): int)): int)): int) == ($struct_get(($struct_loc(self, 4): int)): int);
    }
    assume state(Heap, Mask);

  // -- Translating statement: // id = 224
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) +
  //   ($struct_get($struct_loc(self, 4)): Int) +
  //   ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) ==
  //   ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self,
  //   3)): Int)): Int) -- testsresourcesexamplesauction.vy.vpr@1661.3--1661.392
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) + ($struct_get($struct_loc(self, 4)): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), ($struct_get($struct_loc(self, 3)): Int)): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1661.10--1661.392) [380]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) + ($struct_get(($struct_loc(self, 4): int)): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), ($struct_get(($struct_loc(self, 3): int)): int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: // id = 225
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 3)): Int) &&
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) +
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int)) -- testsresourcesexamplesauction.vy.vpr@1662.3--1662.514

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 3)): Int) && q$a != ($struct_get($struct_loc(self, 0)): Int) ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int))
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_29 && q$a_29 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_29 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_29 != ($struct_get(($struct_loc(self, 0): int)): int)) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) + ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) == ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) might not hold. (testsresourcesexamplesauction.vy.vpr@1662.11--1662.513) [381]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_29): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_29): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_29): int);
        }
      }
      assume false;
    }
    assume (forall q$a_30_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_30_1): int) }
      0 <= q$a_30_1 && q$a_30_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_30_1 != ($struct_get(($struct_loc(self, 3): int)): int) && q$a_30_1 != ($struct_get(($struct_loc(self, 0): int)): int) ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_30_1): int) + ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_30_1): int) == ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_30_1): int)
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 226
  // assert ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) ==
  //   0 -- testsresourcesexamplesauction.vy.vpr@1663.3--1663.87
    assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), 0): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1663.10--1663.87) [382]"}
      ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), 0): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: // id = 227
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) !=
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) !=
  //     0) -- testsresourcesexamplesauction.vy.vpr@1664.3--1664.344

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) != 0 ==> ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_32 && q$a_32 <= 1461501637330902918203684832716283019655932542975) {
        if (($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_32): int) != 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) != 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1664.11--1664.343) [383]"}
            ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_32): int) != 0;
        }
      }
      assume false;
    }
    assume (forall q$a_33_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_33_1): int) }
      0 <= q$a_33_1 && q$a_33_1 <= 1461501637330902918203684832716283019655932542975 ==> ($map_get(($struct_get(($struct_loc(self, 6): int)): $MapDomainType int int), q$a_33_1): int) != 0 ==> ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_33_1): int) != 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 228
  // assert (forall q$a: Int ::
  //     { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) }
  //     0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==>
  //     q$a != ($struct_get($struct_loc(self, 0)): Int) &&
  //     ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) ==
  //     0 ==>
  //     ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) ==
  //     0) -- testsresourcesexamplesauction.vy.vpr@1665.3--1665.397

    // -- Check definedness of (forall q$a: Int :: { ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) } 0 <= q$a && q$a <= 1461501637330902918203684832716283019655932542975 ==> q$a != ($struct_get($struct_loc(self, 0)): Int) && ($map_get(($struct_get($struct_loc(self, 11)): $Map[Int, Int]), q$a): Int) == 0 ==> ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0)
      if (*) {
        assume false;
      }
    if (*) {
      if (0 <= q$a_35 && q$a_35 <= 1461501637330902918203684832716283019655932542975) {
        if (q$a_35 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_35): int) == 0) {
          assert {:msg "  Assert might fail. Assertion ($map_get(($struct_get($struct_loc(self, 10)): $Map[Int, Int]), q$a): Int) == 0 might not hold. (testsresourcesexamplesauction.vy.vpr@1665.11--1665.396) [384]"}
            ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_35): int) == 0;
        }
      }
      assume false;
    }
    assume (forall q$a_36_1_1: int ::
      { ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_36_1_1): int) }
      0 <= q$a_36_1_1 && q$a_36_1_1 <= 1461501637330902918203684832716283019655932542975 ==> q$a_36_1_1 != ($struct_get(($struct_loc(self, 0): int)): int) && ($map_get(($struct_get(($struct_loc(self, 11): int)): $MapDomainType int int), q$a_36_1_1): int) == 0 ==> ($map_get(($struct_get(($struct_loc(self, 10): int)): $MapDomainType int int), q$a_36_1_1): int) == 0
    );
    assume state(Heap, Mask);

  // -- Translating statement: // id = 229
  // assert (forall q$a: Int, q$v: Int ::
  //     { $accessible$withdraw(18, q$a, q$v) }
  //     0 <= q$a &&
  //     (q$a <= 1461501637330902918203684832716283019655932542975 &&
  //     (0 <= q$v &&
  //     q$v <=
  //     115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==>
  //     q$v ==
  //     ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==>
  //     true) -- testsresourcesexamplesauction.vy.vpr@1666.3--1666.345

    // -- Check definedness of (forall q$a: Int, q$v: Int :: { $accessible$withdraw(18, q$a, q$v) } 0 <= q$a && (q$a <= 1461501637330902918203684832716283019655932542975 && (0 <= q$v && q$v <= 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==> q$v == ($map_get(($struct_get($struct_loc(self, 6)): $Map[Int, Int]), q$a): Int) ==> true)
      if (*) {
        assume false;
      }
    if (*) {
      assume false;
    }
    assume state(Heap, Mask);
}
