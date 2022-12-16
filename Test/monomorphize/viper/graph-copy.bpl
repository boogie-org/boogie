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

function  neverTriggered1(x_1: Ref): bool;
function  neverTriggered2(x_3: Ref): bool;
function  neverTriggered3(x_9: Ref): bool;
function  neverTriggered4(x_11: Ref): bool;
function  neverTriggered5(x_13: Ref): bool;
function  neverTriggered6(x_17: Ref): bool;
function  neverTriggered7(x_25: Ref): bool;
function  neverTriggered8(x_27: Ref): bool;
function  neverTriggered9(x_28: Ref): bool;
function  neverTriggered10(x_31: Ref): bool;
function  neverTriggered11(x_38: Ref): bool;
function  neverTriggered12(x_39: Ref): bool;
function  neverTriggered13(x_40: Ref): bool;
function  neverTriggered14(x_43: Ref): bool;
function  neverTriggered15(r_4: Ref): bool;
function  neverTriggered16(r_5: Ref): bool;
function  neverTriggered17(x_47: Ref): bool;
function  neverTriggered18(x_51: Ref): bool;
function  neverTriggered19(r_11: Ref): bool;
function  neverTriggered20(r_13: Ref): bool;
function  neverTriggered21(x_54: Ref): bool;
function  neverTriggered22(x_56: Ref): bool;
function  neverTriggered23(r_16: Ref): bool;
function  neverTriggered24(r_17: Ref): bool;
function  neverTriggered25(x_58: Ref): bool;
function  neverTriggered26(x_59: Ref): bool;
function  neverTriggered27(x_64: Ref): bool;
function  neverTriggered28(x_65: Ref): bool;
function  neverTriggered29(x_66: Ref): bool;
function  neverTriggered30(x_68: Ref): bool;
function  neverTriggered31(x_72: Ref): bool;
function  neverTriggered32(x_73: Ref): bool;
function  neverTriggered33(x_74: Ref): bool;
function  neverTriggered34(x_77: Ref): bool;
function  neverTriggered35(r_22: Ref): bool;
function  neverTriggered36(r_23: Ref): bool;
function  neverTriggered37(x_80: Ref): bool;
function  neverTriggered38(x_82: Ref): bool;
function  neverTriggered39(r_26: Ref): bool;
function  neverTriggered40(r_27: Ref): bool;
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

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

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
// Translation of domain IEdges
// ==================================================

// The type for domain IEdges
type IEdgesDomainType;

// Translation of domain function edge_lookup
function  edge_lookup(e: IEdgesDomainType, i: int): Ref;

// Translation of domain function has_edge
function  has_edge(e: IEdgesDomainType, i: int): bool;

// Translation of domain function insert_edge
function  insert_edge(e: IEdgesDomainType, i: int, node: Ref): IEdgesDomainType;

// Translation of domain function edges_domain
function  edges_domain(e: IEdgesDomainType): Set int;

// Translation of domain function empty_edges
function  empty_edges(): IEdgesDomainType;

// Translation of domain axiom inserted_edge_present
axiom (forall e_1: IEdgesDomainType, i_1: int, node_1: Ref ::
  { (edge_lookup((insert_edge(e_1, i_1, node_1): IEdgesDomainType), i_1): Ref) }
  (edge_lookup((insert_edge(e_1, i_1, node_1): IEdgesDomainType), i_1): Ref) == node_1
);

// Translation of domain axiom other_edges_preserved_after_insertion
axiom (forall e_1: IEdgesDomainType, i_1: int, node_1: Ref, j: int ::
  { (edge_lookup(e_1, j): Ref), (insert_edge(e_1, i_1, node_1): IEdgesDomainType) } { (edge_lookup(e_1, j): Ref), (edge_lookup((insert_edge(e_1, i_1, node_1): IEdgesDomainType), j): Ref) } { (edge_lookup((insert_edge(e_1, i_1, node_1): IEdgesDomainType), j): Ref) }
  i_1 != j ==> (edge_lookup(e_1, j): Ref) == (edge_lookup((insert_edge(e_1, i_1, node_1): IEdgesDomainType), j): Ref)
);

// Translation of domain axiom inserted_edge_defined
axiom (forall e_1: IEdgesDomainType, i_1: int, node_1: Ref ::
  { (has_edge((insert_edge(e_1, i_1, node_1): IEdgesDomainType), i_1): bool) }
  (has_edge((insert_edge(e_1, i_1, node_1): IEdgesDomainType), i_1): bool)
);

// Translation of domain axiom has_edge_complete
axiom (forall e_1: IEdgesDomainType, i_1: int ::
  { (has_edge(e_1, i_1): bool) } { (edge_lookup(e_1, i_1): Ref) }
  (has_edge(e_1, i_1): bool) == ((edge_lookup(e_1, i_1): Ref) != null)
);

// Translation of domain axiom edges_domain_defined
axiom (forall e_1: IEdgesDomainType, i_1: int ::
  { (edges_domain(e_1): Set int), (has_edge(e_1, i_1): bool) } { (edges_domain(e_1): Set int)[i_1] } { (has_edge(e_1, i_1): bool) }
  (edges_domain(e_1): Set int)[i_1] == (has_edge(e_1, i_1): bool)
);

// Translation of domain axiom empty_edges_has_no_nodes
axiom (forall i_1: int ::
  { (has_edge((empty_edges(): IEdgesDomainType), i_1): bool) }
  !(has_edge((empty_edges(): IEdgesDomainType), i_1): bool)
);

// ==================================================
// Translation of domain INodeMap
// ==================================================

// The type for domain INodeMap
type INodeMapDomainType;

// Translation of domain function lookup
function  lookup(node_map: INodeMapDomainType, node: Ref): Ref;

// Translation of domain function has_node
function  has_node(node_map: INodeMapDomainType, node: Ref): bool;

// Translation of domain function insert
function  insert(node_map: INodeMapDomainType, key_node: Ref, val_node: Ref): INodeMapDomainType;

// Translation of domain function map_domain
function  map_domain(node_map: INodeMapDomainType): Seq Ref;

// Translation of domain function empty_map
function  empty_map(): INodeMapDomainType;

// Translation of domain axiom inserted_node_present
axiom (forall node_map_1: INodeMapDomainType, key_node_1: Ref, val_node_1: Ref ::
  { (lookup((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), key_node_1): Ref) }
  (lookup((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), key_node_1): Ref) == val_node_1
);

// Translation of domain axiom other_nodes_preserved_after_insertion
axiom (forall node_map_1: INodeMapDomainType, key_node_1: Ref, val_node_1: Ref, node_1: Ref ::
  { (lookup(node_map_1, node_1): Ref), (insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType) } { (lookup(node_map_1, node_1): Ref), (lookup((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), node_1): Ref) } { (lookup((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), node_1): Ref) }
  node_1 != key_node_1 ==> (lookup(node_map_1, node_1): Ref) == (lookup((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), node_1): Ref)
);

// Translation of domain axiom inserted_node_defined
axiom (forall node_map_1: INodeMapDomainType, key_node_1: Ref, val_node_1: Ref ::
  { (has_node((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), key_node_1): bool) }
  (has_node((insert(node_map_1, key_node_1, val_node_1): INodeMapDomainType), key_node_1): bool)
);

// Translation of domain axiom has_node_complete
axiom (forall node_map_1: INodeMapDomainType, node_1: Ref ::
  { (has_node(node_map_1, node_1): bool) } { (lookup(node_map_1, node_1): Ref) }
  (has_node(node_map_1, node_1): bool) == ((lookup(node_map_1, node_1): Ref) != null)
);

// Translation of domain axiom domain_is_defined
axiom (forall node_map_1: INodeMapDomainType, key: Ref ::
  { (map_domain(node_map_1): Seq Ref), (has_node(node_map_1, key): bool) } { Seq#ContainsTrigger((map_domain(node_map_1): Seq Ref), key) } { Seq#Contains((map_domain(node_map_1): Seq Ref), key) } { (has_node(node_map_1, key): bool) }
  Seq#Contains((map_domain(node_map_1): Seq Ref), key) == (has_node(node_map_1, key): bool)
);

// Translation of domain axiom empty_map_has_no_nodes
axiom (forall node_1: Ref ::
  { (has_node((empty_map(): INodeMapDomainType), node_1): bool) }
  !(has_node((empty_map(): INodeMapDomainType), node_1): bool)
);

// ==================================================
// Translation of all fields
// ==================================================

const unique val: Field NormalField int;
axiom !IsPredicateField(val);
axiom !IsWandField(val);
const unique edges: Field NormalField IEdgesDomainType;
axiom !IsPredicateField(edges);
axiom !IsWandField(edges);

// ==================================================
// Translation of method graph_copy_rec
// ==================================================

procedure graph_copy_rec(this: Ref, node_map_1: INodeMapDomainType, setOfRef: (Set Ref), node_map_image: (Set Ref), rd: Perm) returns (nodeCopy: Ref, res_node_map: INodeMapDomainType, res_copy_nodes: (Set Ref))
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var x: Ref;
  var i_2: int;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var x_2: Ref;
  var x_4: Ref;
  var x_6: Ref;
  var i_3: int;
  var freshObj: Ref;
  var S: (Set int);
  var x_41: Ref;
  var x_44: Ref;
  var j: int;
  var r_1: Ref;
  var j_2: int;
  var r_2: Ref;
  var ExhaleHeap: HeapType;
  var i_6: int;
  var x_8: Ref;
  var x_10: Ref;
  var j_1: int;
  var r_3: Ref;
  var j_3: int;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var newNode: Ref;
  var nodeForId: Ref;
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var arg_s1: (Set int);
  var arg_node_map: INodeMapDomainType;
  var arg_node_map_image: (Set Ref);
  var arg_rd: Perm;
  var x_60: Ref;
  var i$0: int;
  var x_62: Ref;
  var x_75: Ref;
  var x_78: Ref;
  var j_10: int;
  var r_18: Ref;
  var j_12: int;
  var r_20: Ref;
  var x_29: Ref;
  var x_32: Ref;
  var x_34: Ref;
  var i_4: int;
  var x_36: Ref;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume Heap[this, $allocated];
  
  // -- Checked inhaling of precondition
    assume NoPerm < rd;
    assume state(Heap, Mask);
    assume this != null;
    assume state(Heap, Mask);
    assume setOfRef[this];
    assume state(Heap, Mask);
    assume Set#Card(Set#Intersection(setOfRef, node_map_image)) == 0;
    assume state(Heap, Mask);
    
    // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@96.12--96.61) [443]"}
      (forall x_1: Ref, x_1_1: Ref ::
      
      (((x_1 != x_1_1 && setOfRef[x_1]) && setOfRef[x_1_1]) && NoPerm < rd) && NoPerm < rd ==> x_1 != x_1_1
    );
    
    // -- Define Inverse Function
      assume (forall x_1: Ref ::
        { Heap[x_1, val] } { QPMask[x_1, val] } { setOfRef[x_1] }
        setOfRef[x_1] && NoPerm < rd ==> qpRange1(x_1) && invRecv1(x_1) == x_1
      );
      assume (forall o_3: Ref ::
        { invRecv1(o_3) }
        (setOfRef[invRecv1(o_3)] && NoPerm < rd) && qpRange1(o_3) ==> invRecv1(o_3) == o_3
      );
    // Check that permission expression is non-negative for all fields
    assert {:msg "  Contract might not be well-formed. Fraction rd might be negative. (graph-copy.vpr@96.12--96.61) [444]"}
      (forall x_1: Ref ::
      { Heap[x_1, val] } { QPMask[x_1, val] } { setOfRef[x_1] }
      setOfRef[x_1] ==> rd >= NoPerm
    );
    
    // -- Assume set of fields is nonNull
      assume (forall x_1: Ref ::
        { Heap[x_1, val] } { QPMask[x_1, val] } { setOfRef[x_1] }
        setOfRef[x_1] && rd > NoPerm ==> x_1 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        ((setOfRef[invRecv1(o_3)] && NoPerm < rd) && qpRange1(o_3) ==> (NoPerm < rd ==> invRecv1(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + rd) && (!((setOfRef[invRecv1(o_3)] && NoPerm < rd) && qpRange1(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@97.12--97.63) [445]"}
      (forall x_3: Ref, x_3_1: Ref ::
      
      (((x_3 != x_3_1 && setOfRef[x_3]) && setOfRef[x_3_1]) && NoPerm < rd) && NoPerm < rd ==> x_3 != x_3_1
    );
    
    // -- Define Inverse Function
      assume (forall x_3: Ref ::
        { Heap[x_3, edges] } { QPMask[x_3, edges] } { setOfRef[x_3] }
        setOfRef[x_3] && NoPerm < rd ==> qpRange2(x_3) && invRecv2(x_3) == x_3
      );
      assume (forall o_3: Ref ::
        { invRecv2(o_3) }
        (setOfRef[invRecv2(o_3)] && NoPerm < rd) && qpRange2(o_3) ==> invRecv2(o_3) == o_3
      );
    // Check that permission expression is non-negative for all fields
    assert {:msg "  Contract might not be well-formed. Fraction rd might be negative. (graph-copy.vpr@97.12--97.63) [446]"}
      (forall x_3: Ref ::
      { Heap[x_3, edges] } { QPMask[x_3, edges] } { setOfRef[x_3] }
      setOfRef[x_3] ==> rd >= NoPerm
    );
    
    // -- Assume set of fields is nonNull
      assume (forall x_3: Ref ::
        { Heap[x_3, edges] } { QPMask[x_3, edges] } { setOfRef[x_3] }
        setOfRef[x_3] && rd > NoPerm ==> x_3 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, edges] }
        ((setOfRef[invRecv2(o_3)] && NoPerm < rd) && qpRange2(o_3) ==> (NoPerm < rd ==> invRecv2(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + rd) && (!((setOfRef[invRecv2(o_3)] && NoPerm < rd) && qpRange2(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of (forall x: Ref, i: Int :: { (x in setOfRef), (i in edges_domain(x.edges)) } { (x in setOfRef), edge_lookup(x.edges, i) } { (x in setOfRef), (edge_lookup(x.edges, i) in setOfRef) } { edges_domain(x.edges), edge_lookup(x.edges, i) } { edges_domain(x.edges), (edge_lookup(x.edges, i) in setOfRef) } { (i in edges_domain(x.edges)) } { (edge_lookup(x.edges, i) in setOfRef) } (x in setOfRef) && (i in edges_domain(x.edges)) ==> (edge_lookup(x.edges, i) in setOfRef))
      if (*) {
        if (setOfRef[x]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@98.12--98.120) [447]"}
            HasDirectPerm(Mask, x, edges);
        }
        if (setOfRef[x] && (edges_domain(Heap[x, edges]): Set int)[i_2]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@98.12--98.120) [448]"}
            HasDirectPerm(Mask, x, edges);
        }
        assume false;
      }
    assume (forall x_5: Ref, i_1_1: int ::
      { setOfRef[x_5], (edges_domain(Heap[x_5, edges]): Set int)[i_1_1] } { setOfRef[x_5], (edge_lookup(Heap[x_5, edges], i_1_1): Ref) } { setOfRef[x_5], setOfRef[(edge_lookup(Heap[x_5, edges], i_1_1): Ref)] } { (edges_domain(Heap[x_5, edges]): Set int), (edge_lookup(Heap[x_5, edges], i_1_1): Ref) } { (edges_domain(Heap[x_5, edges]): Set int), setOfRef[(edge_lookup(Heap[x_5, edges], i_1_1): Ref)] } { (edges_domain(Heap[x_5, edges]): Set int)[i_1_1] } { setOfRef[(edge_lookup(Heap[x_5, edges], i_1_1): Ref)] }
      setOfRef[x_5] && (edges_domain(Heap[x_5, edges]): Set int)[i_1_1] ==> setOfRef[(edge_lookup(Heap[x_5, edges], i_1_1): Ref)]
    );
    assume state(Heap, Mask);
    
    // -- Check definedness of (forall x: Ref :: { (x in map_domain(node_map)) } { (lookup(node_map, x) in node_map_image) } (x in map_domain(node_map)) ==> (lookup(node_map, x) in node_map_image))
      if (*) {
        assume false;
      }
    assume (forall x_7: Ref ::
      { Seq#ContainsTrigger((map_domain(node_map_1): Seq Ref), x_7) } { Seq#Contains((map_domain(node_map_1): Seq Ref), x_7) } { node_map_image[(lookup(node_map_1, x_7): Ref)] }
      Seq#Contains((map_domain(node_map_1): Seq Ref), x_7) ==> node_map_image[(lookup(node_map_1, x_7): Ref)]
    );
    assume state(Heap, Mask);
    
    // -- Check definedness of (forall x: Ref :: { (x in node_map_image) } (x in node_map_image) ==> acc(x.val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@101.12--101.63) [449]"}
      (forall x_9: Ref, x_9_1: Ref ::
      
      (((x_9 != x_9_1 && node_map_image[x_9]) && node_map_image[x_9_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_9 != x_9_1
    );
    
    // -- Define Inverse Function
      assume (forall x_9: Ref ::
        { Heap[x_9, val] } { QPMask[x_9, val] } { node_map_image[x_9] }
        node_map_image[x_9] && NoPerm < FullPerm ==> qpRange3(x_9) && invRecv3(x_9) == x_9
      );
      assume (forall o_3: Ref ::
        { invRecv3(o_3) }
        (node_map_image[invRecv3(o_3)] && NoPerm < FullPerm) && qpRange3(o_3) ==> invRecv3(o_3) == o_3
      );
    
    // -- Assume set of fields is nonNull
      assume (forall x_9: Ref ::
        { Heap[x_9, val] } { QPMask[x_9, val] } { node_map_image[x_9] }
        node_map_image[x_9] ==> x_9 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        ((node_map_image[invRecv3(o_3)] && NoPerm < FullPerm) && qpRange3(o_3) ==> (NoPerm < FullPerm ==> invRecv3(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!((node_map_image[invRecv3(o_3)] && NoPerm < FullPerm) && qpRange3(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of (forall x: Ref :: { (x in node_map_image) } (x in node_map_image) ==> acc(x.edges, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@102.12--102.65) [450]"}
      (forall x_11: Ref, x_11_1: Ref ::
      
      (((x_11 != x_11_1 && node_map_image[x_11]) && node_map_image[x_11_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_11 != x_11_1
    );
    
    // -- Define Inverse Function
      assume (forall x_11: Ref ::
        { Heap[x_11, edges] } { QPMask[x_11, edges] } { node_map_image[x_11] }
        node_map_image[x_11] && NoPerm < FullPerm ==> qpRange4(x_11) && invRecv4(x_11) == x_11
      );
      assume (forall o_3: Ref ::
        { invRecv4(o_3) }
        (node_map_image[invRecv4(o_3)] && NoPerm < FullPerm) && qpRange4(o_3) ==> invRecv4(o_3) == o_3
      );
    
    // -- Assume set of fields is nonNull
      assume (forall x_11: Ref ::
        { Heap[x_11, edges] } { QPMask[x_11, edges] } { node_map_image[x_11] }
        node_map_image[x_11] ==> x_11 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, edges] }
        ((node_map_image[invRecv4(o_3)] && NoPerm < FullPerm) && qpRange4(o_3) ==> (NoPerm < FullPerm ==> invRecv4(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + FullPerm) && (!((node_map_image[invRecv4(o_3)] && NoPerm < FullPerm) && qpRange4(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
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
    assume nodeCopy != null;
    assume res_copy_nodes[nodeCopy];
    assume state(PostHeap, PostMask);
    assume Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@106.11--106.60) [451]"}
      (forall x_13: Ref, x_13_1: Ref ::
      
      (((x_13 != x_13_1 && setOfRef[x_13]) && setOfRef[x_13_1]) && NoPerm < rd) && NoPerm < rd ==> x_13 != x_13_1
    );
    
    // -- Define Inverse Function
      assume (forall x_13: Ref ::
        { PostHeap[x_13, val] } { QPMask[x_13, val] } { setOfRef[x_13] }
        setOfRef[x_13] && NoPerm < rd ==> qpRange5(x_13) && invRecv5(x_13) == x_13
      );
      assume (forall o_3: Ref ::
        { invRecv5(o_3) }
        (setOfRef[invRecv5(o_3)] && NoPerm < rd) && qpRange5(o_3) ==> invRecv5(o_3) == o_3
      );
    // Check that permission expression is non-negative for all fields
    assert {:msg "  Contract might not be well-formed. Fraction rd might be negative. (graph-copy.vpr@106.11--106.60) [452]"}
      (forall x_13: Ref ::
      { PostHeap[x_13, val] } { QPMask[x_13, val] } { setOfRef[x_13] }
      setOfRef[x_13] ==> rd >= NoPerm
    );
    
    // -- Assume set of fields is nonNull
      assume (forall x_13: Ref ::
        { PostHeap[x_13, val] } { QPMask[x_13, val] } { setOfRef[x_13] }
        setOfRef[x_13] && rd > NoPerm ==> x_13 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        ((setOfRef[invRecv5(o_3)] && NoPerm < rd) && qpRange5(o_3) ==> (NoPerm < rd ==> invRecv5(o_3) == o_3) && QPMask[o_3, val] == PostMask[o_3, val] + rd) && (!((setOfRef[invRecv5(o_3)] && NoPerm < rd) && qpRange5(o_3)) ==> QPMask[o_3, val] == PostMask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.val == old(x.val))
      if (*) {
        if (setOfRef[x_2]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.val (graph-copy.vpr@107.11--107.65) [453]"}
            HasDirectPerm(PostMask, x_2, val);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.val (graph-copy.vpr@107.11--107.65) [454]"}
            HasDirectPerm(old(Mask), x_2, val);
        }
        assume false;
      }
    assume (forall x_15: Ref ::
      { setOfRef[x_15] }
      setOfRef[x_15] ==> PostHeap[x_15, val] == old(Heap)[x_15, val]
    );
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@108.11--108.62) [455]"}
      (forall x_17: Ref, x_17_1: Ref ::
      
      (((x_17 != x_17_1 && setOfRef[x_17]) && setOfRef[x_17_1]) && NoPerm < rd) && NoPerm < rd ==> x_17 != x_17_1
    );
    
    // -- Define Inverse Function
      assume (forall x_17: Ref ::
        { PostHeap[x_17, edges] } { QPMask[x_17, edges] } { setOfRef[x_17] }
        setOfRef[x_17] && NoPerm < rd ==> qpRange6(x_17) && invRecv6(x_17) == x_17
      );
      assume (forall o_3: Ref ::
        { invRecv6(o_3) }
        (setOfRef[invRecv6(o_3)] && NoPerm < rd) && qpRange6(o_3) ==> invRecv6(o_3) == o_3
      );
    // Check that permission expression is non-negative for all fields
    assert {:msg "  Contract might not be well-formed. Fraction rd might be negative. (graph-copy.vpr@108.11--108.62) [456]"}
      (forall x_17: Ref ::
      { PostHeap[x_17, edges] } { QPMask[x_17, edges] } { setOfRef[x_17] }
      setOfRef[x_17] ==> rd >= NoPerm
    );
    
    // -- Assume set of fields is nonNull
      assume (forall x_17: Ref ::
        { PostHeap[x_17, edges] } { QPMask[x_17, edges] } { setOfRef[x_17] }
        setOfRef[x_17] && rd > NoPerm ==> x_17 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, edges] }
        ((setOfRef[invRecv6(o_3)] && NoPerm < rd) && qpRange6(o_3) ==> (NoPerm < rd ==> invRecv6(o_3) == o_3) && QPMask[o_3, edges] == PostMask[o_3, edges] + rd) && (!((setOfRef[invRecv6(o_3)] && NoPerm < rd) && qpRange6(o_3)) ==> QPMask[o_3, edges] == PostMask[o_3, edges])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != edges ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.edges == old(x.edges))
      if (*) {
        if (setOfRef[x_4]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@109.11--109.69) [457]"}
            HasDirectPerm(PostMask, x_4, edges);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@109.11--109.69) [458]"}
            HasDirectPerm(old(Mask), x_4, edges);
        }
        assume false;
      }
    assume (forall x_19: Ref ::
      { setOfRef[x_19] }
      setOfRef[x_19] ==> PostHeap[x_19, edges] == old(Heap)[x_19, edges]
    );
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref, i: Int :: { (x in setOfRef), (i in edges_domain(x.edges)) } { (x in setOfRef), edge_lookup(x.edges, i) } { (x in setOfRef), (edge_lookup(x.edges, i) in setOfRef) } { edges_domain(x.edges), edge_lookup(x.edges, i) } { edges_domain(x.edges), (edge_lookup(x.edges, i) in setOfRef) } { (i in edges_domain(x.edges)) } { (edge_lookup(x.edges, i) in setOfRef) } (x in setOfRef) && (i in edges_domain(x.edges)) ==> (edge_lookup(x.edges, i) in setOfRef))
      if (*) {
        if (setOfRef[x_6]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@110.11--110.119) [459]"}
            HasDirectPerm(PostMask, x_6, edges);
        }
        if (setOfRef[x_6] && (edges_domain(PostHeap[x_6, edges]): Set int)[i_3]) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@110.11--110.119) [460]"}
            HasDirectPerm(PostMask, x_6, edges);
        }
        assume false;
      }
    assume (forall x_21: Ref, i_3_1: int ::
      { setOfRef[x_21], (edges_domain(PostHeap[x_21, edges]): Set int)[i_3_1] } { setOfRef[x_21], (edge_lookup(PostHeap[x_21, edges], i_3_1): Ref) } { setOfRef[x_21], setOfRef[(edge_lookup(PostHeap[x_21, edges], i_3_1): Ref)] } { (edges_domain(PostHeap[x_21, edges]): Set int), (edge_lookup(PostHeap[x_21, edges], i_3_1): Ref) } { (edges_domain(PostHeap[x_21, edges]): Set int), setOfRef[(edge_lookup(PostHeap[x_21, edges], i_3_1): Ref)] } { (edges_domain(PostHeap[x_21, edges]): Set int)[i_3_1] } { setOfRef[(edge_lookup(PostHeap[x_21, edges], i_3_1): Ref)] }
      setOfRef[x_21] && (edges_domain(PostHeap[x_21, edges]): Set int)[i_3_1] ==> setOfRef[(edge_lookup(PostHeap[x_21, edges], i_3_1): Ref)]
    );
    assume state(PostHeap, PostMask);
    assume Set#Equal(res_copy_nodes, Set#Union(res_copy_nodes, node_map_image));
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in map_domain(res_node_map)) } { (lookup(res_node_map, x) in res_copy_nodes) } (x in map_domain(res_node_map)) ==> (lookup(res_node_map, x) in res_copy_nodes))
      if (*) {
        assume false;
      }
    assume (forall x_23: Ref ::
      { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), x_23) } { Seq#Contains((map_domain(res_node_map): Seq Ref), x_23) } { res_copy_nodes[(lookup(res_node_map, x_23): Ref)] }
      Seq#Contains((map_domain(res_node_map): Seq Ref), x_23) ==> res_copy_nodes[(lookup(res_node_map, x_23): Ref)]
    );
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in res_copy_nodes) } (x in res_copy_nodes) ==> acc(x.val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@113.11--113.62) [461]"}
      (forall x_25: Ref, x_25_1: Ref ::
      
      (((x_25 != x_25_1 && res_copy_nodes[x_25]) && res_copy_nodes[x_25_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_25 != x_25_1
    );
    
    // -- Define Inverse Function
      assume (forall x_25: Ref ::
        { PostHeap[x_25, val] } { QPMask[x_25, val] } { res_copy_nodes[x_25] }
        res_copy_nodes[x_25] && NoPerm < FullPerm ==> qpRange7(x_25) && invRecv7(x_25) == x_25
      );
      assume (forall o_3: Ref ::
        { invRecv7(o_3) }
        (res_copy_nodes[invRecv7(o_3)] && NoPerm < FullPerm) && qpRange7(o_3) ==> invRecv7(o_3) == o_3
      );
    
    // -- Assume set of fields is nonNull
      assume (forall x_25: Ref ::
        { PostHeap[x_25, val] } { QPMask[x_25, val] } { res_copy_nodes[x_25] }
        res_copy_nodes[x_25] ==> x_25 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        ((res_copy_nodes[invRecv7(o_3)] && NoPerm < FullPerm) && qpRange7(o_3) ==> (NoPerm < FullPerm ==> invRecv7(o_3) == o_3) && QPMask[o_3, val] == PostMask[o_3, val] + FullPerm) && (!((res_copy_nodes[invRecv7(o_3)] && NoPerm < FullPerm) && qpRange7(o_3)) ==> QPMask[o_3, val] == PostMask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of (forall x: Ref :: { (x in res_copy_nodes) } (x in res_copy_nodes) ==> acc(x.edges, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@114.11--114.64) [462]"}
      (forall x_27: Ref, x_27_1: Ref ::
      
      (((x_27 != x_27_1 && res_copy_nodes[x_27]) && res_copy_nodes[x_27_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_27 != x_27_1
    );
    
    // -- Define Inverse Function
      assume (forall x_27: Ref ::
        { PostHeap[x_27, edges] } { QPMask[x_27, edges] } { res_copy_nodes[x_27] }
        res_copy_nodes[x_27] && NoPerm < FullPerm ==> qpRange8(x_27) && invRecv8(x_27) == x_27
      );
      assume (forall o_3: Ref ::
        { invRecv8(o_3) }
        (res_copy_nodes[invRecv8(o_3)] && NoPerm < FullPerm) && qpRange8(o_3) ==> invRecv8(o_3) == o_3
      );
    
    // -- Assume set of fields is nonNull
      assume (forall x_27: Ref ::
        { PostHeap[x_27, edges] } { QPMask[x_27, edges] } { res_copy_nodes[x_27] }
        res_copy_nodes[x_27] ==> x_27 != null
      );
    
    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, edges] }
        ((res_copy_nodes[invRecv8(o_3)] && NoPerm < FullPerm) && qpRange8(o_3) ==> (NoPerm < FullPerm ==> invRecv8(o_3) == o_3) && QPMask[o_3, edges] == PostMask[o_3, edges] + FullPerm) && (!((res_copy_nodes[invRecv8(o_3)] && NoPerm < FullPerm) && qpRange8(o_3)) ==> QPMask[o_3, edges] == PostMask[o_3, edges])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != edges ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: if (has_node(node_map, this)) -- graph-copy.vpr@119.3--169.4
    if ((has_node(node_map_1, this): bool)) {
      
      // -- Translating statement: nodeCopy := lookup(node_map, this) -- graph-copy.vpr@120.5--120.39
        nodeCopy := (lookup(node_map_1, this): Ref);
        assume state(Heap, Mask);
      
      // -- Translating statement: res_node_map := node_map -- graph-copy.vpr@121.5--121.29
        res_node_map := node_map_1;
        assume state(Heap, Mask);
      
      // -- Translating statement: res_copy_nodes := node_map_image -- graph-copy.vpr@122.5--122.37
        res_copy_nodes := node_map_image;
        assume state(Heap, Mask);
    } else {
      
      // -- Translating statement: nodeCopy := new(val, edges) -- graph-copy.vpr@124.5--124.32
        havoc freshObj;
        assume freshObj != null && !Heap[freshObj, $allocated];
        Heap[freshObj, $allocated] := true;
        nodeCopy := freshObj;
        Mask[nodeCopy, val] := Mask[nodeCopy, val] + FullPerm;
        Mask[nodeCopy, edges] := Mask[nodeCopy, edges] + FullPerm;
        assume state(Heap, Mask);
      
      // -- Translating statement: nodeCopy.val := this.val -- graph-copy.vpr@125.5--125.29
        
        // -- Check definedness of this.val
          assert {:msg "  Assignment might fail. There might be insufficient permission to access this.val (graph-copy.vpr@125.5--125.29) [463]"}
            HasDirectPerm(Mask, this, val);
        assert {:msg "  Assignment might fail. There might be insufficient permission to access nodeCopy.val (graph-copy.vpr@125.5--125.29) [464]"}
          FullPerm == Mask[nodeCopy, val];
        Heap[nodeCopy, val] := Heap[this, val];
        assume state(Heap, Mask);
      
      // -- Translating statement: res_node_map := insert(node_map, this, nodeCopy) -- graph-copy.vpr@127.5--127.53
        res_node_map := (insert(node_map_1, this, nodeCopy): INodeMapDomainType);
        assume state(Heap, Mask);
      
      // -- Translating statement: res_copy_nodes := (node_map_image union Set(nodeCopy)) -- graph-copy.vpr@129.5--129.57
        res_copy_nodes := Set#Union(node_map_image, Set#Singleton(nodeCopy));
        assume state(Heap, Mask);
      
      // -- Translating statement: assert ((setOfRef intersection node_map_image) union
  //   (setOfRef intersection Set(nodeCopy))) ==
  //   (setOfRef intersection res_copy_nodes) -- graph-copy.vpr@137.5--138.51
        assert {:msg "  Assert might fail. Assertion ((setOfRef intersection node_map_image) union (setOfRef intersection Set(nodeCopy))) == (setOfRef intersection res_copy_nodes) might not hold. (graph-copy.vpr@137.12--138.51) [465]"}
          Set#Equal(Set#Union(Set#Intersection(setOfRef, node_map_image), Set#Intersection(setOfRef, Set#Singleton(nodeCopy))), Set#Intersection(setOfRef, res_copy_nodes));
        assume state(Heap, Mask);
      
      // -- Translating statement: S := edges_domain(this.edges) -- graph-copy.vpr@140.5--140.34
        
        // -- Check definedness of edges_domain(this.edges)
          assert {:msg "  Assignment might fail. There might be insufficient permission to access this.edges (graph-copy.vpr@140.5--140.34) [466]"}
            HasDirectPerm(Mask, this, edges);
        S := (edges_domain(Heap[this, edges]): Set int);
        assume state(Heap, Mask);
      
      // -- Translating statement: while (|S| > 0) -- graph-copy.vpr@142.5--168.6
        
        // -- Before loop head
          
          // -- Exhale loop invariant before loop
            assert {:msg "  Loop invariant (nodeCopy in res_copy_nodes) might not hold on entry. Assertion (nodeCopy in res_copy_nodes) might not hold. (graph-copy.vpr@143.17--143.43) [467]"}
              res_copy_nodes[nodeCopy];
            assert {:msg "  Loop invariant (this in setOfRef) might not hold on entry. Assertion (this in setOfRef) might not hold. (graph-copy.vpr@144.17--144.33) [468]"}
              setOfRef[this];
            havoc QPMask;
            
            // -- check that the permission amount is positive
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd)) might not hold on entry. Fraction rd might be negative. (graph-copy.vpr@145.17--145.66) [469]"}
                (forall x_40: Ref ::
                { Heap[x_40, val] } { QPMask[x_40, val] } { setOfRef[x_40] }
                setOfRef[x_40] && dummyFunction(Heap[x_40, val]) ==> rd >= NoPerm
              );
            
            // -- check if receiver x is injective
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd)) might not hold on entry. Quantified resource x.val might not be injective. (graph-copy.vpr@145.17--145.66) [470]"}
                (forall x_40: Ref, x_40_1: Ref ::
                { neverTriggered13(x_40), neverTriggered13(x_40_1) }
                (((x_40 != x_40_1 && setOfRef[x_40]) && setOfRef[x_40_1]) && NoPerm < rd) && NoPerm < rd ==> x_40 != x_40_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd)) might not hold on entry. There might be insufficient permission to access x.val (graph-copy.vpr@145.17--145.66) [471]"}
                (forall x_40: Ref ::
                { Heap[x_40, val] } { QPMask[x_40, val] } { setOfRef[x_40] }
                setOfRef[x_40] ==> Mask[x_40, val] >= rd
              );
            
            // -- assumptions for inverse of receiver x
              assume (forall x_40: Ref ::
                { Heap[x_40, val] } { QPMask[x_40, val] } { setOfRef[x_40] }
                setOfRef[x_40] && NoPerm < rd ==> qpRange13(x_40) && invRecv13(x_40) == x_40
              );
              assume (forall o_3: Ref ::
                { invRecv13(o_3) }
                setOfRef[invRecv13(o_3)] && (NoPerm < rd && qpRange13(o_3)) ==> invRecv13(o_3) == o_3
              );
            
            // -- assume permission updates for field val
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                (setOfRef[invRecv13(o_3)] && (NoPerm < rd && qpRange13(o_3)) ==> invRecv13(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - rd) && (!(setOfRef[invRecv13(o_3)] && (NoPerm < rd && qpRange13(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            if (*) {
              if (setOfRef[x_41]) {
                assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.val == old(x.val)) might not hold on entry. Assertion x.val == old(x.val) might not hold. (graph-copy.vpr@146.17--146.71) [472]"}
                  Heap[x_41, val] == old(Heap)[x_41, val];
              }
              assume false;
            }
            assume (forall x_42_1: Ref ::
              { setOfRef[x_42_1] }
              setOfRef[x_42_1] ==> Heap[x_42_1, val] == old(Heap)[x_42_1, val]
            );
            havoc QPMask;
            
            // -- check that the permission amount is positive
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd)) might not hold on entry. Fraction rd might be negative. (graph-copy.vpr@147.17--147.68) [473]"}
                (forall x_43: Ref ::
                { Heap[x_43, edges] } { QPMask[x_43, edges] } { setOfRef[x_43] }
                setOfRef[x_43] && dummyFunction(Heap[x_43, edges]) ==> rd >= NoPerm
              );
            
            // -- check if receiver x is injective
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd)) might not hold on entry. Quantified resource x.edges might not be injective. (graph-copy.vpr@147.17--147.68) [474]"}
                (forall x_43: Ref, x_43_1: Ref ::
                { neverTriggered14(x_43), neverTriggered14(x_43_1) }
                (((x_43 != x_43_1 && setOfRef[x_43]) && setOfRef[x_43_1]) && NoPerm < rd) && NoPerm < rd ==> x_43 != x_43_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd)) might not hold on entry. There might be insufficient permission to access x.edges (graph-copy.vpr@147.17--147.68) [475]"}
                (forall x_43: Ref ::
                { Heap[x_43, edges] } { QPMask[x_43, edges] } { setOfRef[x_43] }
                setOfRef[x_43] ==> Mask[x_43, edges] >= rd
              );
            
            // -- assumptions for inverse of receiver x
              assume (forall x_43: Ref ::
                { Heap[x_43, edges] } { QPMask[x_43, edges] } { setOfRef[x_43] }
                setOfRef[x_43] && NoPerm < rd ==> qpRange14(x_43) && invRecv14(x_43) == x_43
              );
              assume (forall o_3: Ref ::
                { invRecv14(o_3) }
                setOfRef[invRecv14(o_3)] && (NoPerm < rd && qpRange14(o_3)) ==> invRecv14(o_3) == o_3
              );
            
            // -- assume permission updates for field edges
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                (setOfRef[invRecv14(o_3)] && (NoPerm < rd && qpRange14(o_3)) ==> invRecv14(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - rd) && (!(setOfRef[invRecv14(o_3)] && (NoPerm < rd && qpRange14(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            if (*) {
              if (setOfRef[x_44]) {
                assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.edges == old(x.edges)) might not hold on entry. Assertion x.edges == old(x.edges) might not hold. (graph-copy.vpr@148.17--148.75) [476]"}
                  Heap[x_44, edges] == old(Heap)[x_44, edges];
              }
              assume false;
            }
            assume (forall x_45_1: Ref ::
              { setOfRef[x_45_1] }
              setOfRef[x_45_1] ==> Heap[x_45_1, edges] == old(Heap)[x_45_1, edges]
            );
            if (*) {
              if (S[j]) {
                assert {:msg "  Loop invariant (forall j: Int :: { (j in S) } { (edge_lookup(this.edges, j) in setOfRef) } (j in S) ==> (edge_lookup(this.edges, j) in setOfRef)) might not hold on entry. Assertion (edge_lookup(this.edges, j) in setOfRef) might not hold. (graph-copy.vpr@149.17--149.83) [477]"}
                  setOfRef[(edge_lookup(Heap[this, edges], j): Ref)];
              }
              assume false;
            }
            assume (forall j_1_1: int ::
              { S[j_1_1] } { setOfRef[(edge_lookup(Heap[this, edges], j_1_1): Ref)] }
              S[j_1_1] ==> setOfRef[(edge_lookup(Heap[this, edges], j_1_1): Ref)]
            );
            if (*) {
              if (setOfRef[r_1] && (edges_domain(Heap[r_1, edges]): Set int)[j_2]) {
                assert {:msg "  Loop invariant (forall r: Ref, j: Int :: { (r in setOfRef), (j in edges_domain(r.edges)) } { (r in setOfRef), edge_lookup(r.edges, j) } { (r in setOfRef), (edge_lookup(r.edges, j) in setOfRef) } { edges_domain(r.edges), edge_lookup(r.edges, j) } { edges_domain(r.edges), (edge_lookup(r.edges, j) in setOfRef) } { (j in edges_domain(r.edges)) } { (edge_lookup(r.edges, j) in setOfRef) } (r in setOfRef) && (j in edges_domain(r.edges)) ==> (edge_lookup(r.edges, j) in setOfRef)) might not hold on entry. Assertion (edge_lookup(r.edges, j) in setOfRef) might not hold. (graph-copy.vpr@150.17--150.125) [478]"}
                  setOfRef[(edge_lookup(Heap[r_1, edges], j_2): Ref)];
              }
              assume false;
            }
            assume (forall r_1_1: Ref, j_3_1: int ::
              { setOfRef[r_1_1], (edges_domain(Heap[r_1_1, edges]): Set int)[j_3_1] } { setOfRef[r_1_1], (edge_lookup(Heap[r_1_1, edges], j_3_1): Ref) } { setOfRef[r_1_1], setOfRef[(edge_lookup(Heap[r_1_1, edges], j_3_1): Ref)] } { (edges_domain(Heap[r_1_1, edges]): Set int), (edge_lookup(Heap[r_1_1, edges], j_3_1): Ref) } { (edges_domain(Heap[r_1_1, edges]): Set int), setOfRef[(edge_lookup(Heap[r_1_1, edges], j_3_1): Ref)] } { (edges_domain(Heap[r_1_1, edges]): Set int)[j_3_1] } { setOfRef[(edge_lookup(Heap[r_1_1, edges], j_3_1): Ref)] }
              setOfRef[r_1_1] && (edges_domain(Heap[r_1_1, edges]): Set int)[j_3_1] ==> setOfRef[(edge_lookup(Heap[r_1_1, edges], j_3_1): Ref)]
            );
            assert {:msg "  Loop invariant (node_map_image subset res_copy_nodes) might not hold on entry. Assertion (node_map_image subset res_copy_nodes) might not hold. (graph-copy.vpr@151.32--151.53) [479]"}
              Set#Subset(node_map_image, res_copy_nodes);
            assert {:msg "  Loop invariant |(setOfRef intersection res_copy_nodes)| == 0 might not hold on entry. Assertion |(setOfRef intersection res_copy_nodes)| == 0 might not hold. (graph-copy.vpr@152.17--152.60) [480]"}
              Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
            if (*) {
              if (Seq#Contains((map_domain(res_node_map): Seq Ref), r_2)) {
                assert {:msg "  Loop invariant (forall r: Ref :: { (r in map_domain(res_node_map)) } { (lookup(res_node_map, r) in res_copy_nodes) } (r in map_domain(res_node_map)) ==> (lookup(res_node_map, r) in res_copy_nodes)) might not hold on entry. Assertion (lookup(res_node_map, r) in res_copy_nodes) might not hold. (graph-copy.vpr@153.17--153.108) [481]"}
                  res_copy_nodes[(lookup(res_node_map, r_2): Ref)];
              }
              assume false;
            }
            assume (forall r_3_1: Ref ::
              { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), r_3_1) } { Seq#Contains((map_domain(res_node_map): Seq Ref), r_3_1) } { res_copy_nodes[(lookup(res_node_map, r_3_1): Ref)] }
              Seq#Contains((map_domain(res_node_map): Seq Ref), r_3_1) ==> res_copy_nodes[(lookup(res_node_map, r_3_1): Ref)]
            );
            havoc QPMask;
            
            // -- check that the permission amount is positive
              
            
            // -- check if receiver r is injective
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.val, write)) might not hold on entry. Quantified resource r.val might not be injective. (graph-copy.vpr@154.17--154.68) [482]"}
                (forall r_4: Ref, r_4_1: Ref ::
                { neverTriggered15(r_4), neverTriggered15(r_4_1) }
                (((r_4 != r_4_1 && res_copy_nodes[r_4]) && res_copy_nodes[r_4_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_4 != r_4_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.val, write)) might not hold on entry. There might be insufficient permission to access r.val (graph-copy.vpr@154.17--154.68) [483]"}
                (forall r_4: Ref ::
                { Heap[r_4, val] } { QPMask[r_4, val] } { res_copy_nodes[r_4] }
                res_copy_nodes[r_4] ==> Mask[r_4, val] >= FullPerm
              );
            
            // -- assumptions for inverse of receiver r
              assume (forall r_4: Ref ::
                { Heap[r_4, val] } { QPMask[r_4, val] } { res_copy_nodes[r_4] }
                res_copy_nodes[r_4] && NoPerm < FullPerm ==> qpRange15(r_4) && invRecv15(r_4) == r_4
              );
              assume (forall o_3: Ref ::
                { invRecv15(o_3) }
                res_copy_nodes[invRecv15(o_3)] && (NoPerm < FullPerm && qpRange15(o_3)) ==> invRecv15(o_3) == o_3
              );
            
            // -- assume permission updates for field val
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                (res_copy_nodes[invRecv15(o_3)] && (NoPerm < FullPerm && qpRange15(o_3)) ==> invRecv15(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!(res_copy_nodes[invRecv15(o_3)] && (NoPerm < FullPerm && qpRange15(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            havoc QPMask;
            
            // -- check that the permission amount is positive
              
            
            // -- check if receiver r is injective
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.edges, write)) might not hold on entry. Quantified resource r.edges might not be injective. (graph-copy.vpr@155.17--155.70) [484]"}
                (forall r_5: Ref, r_5_1: Ref ::
                { neverTriggered16(r_5), neverTriggered16(r_5_1) }
                (((r_5 != r_5_1 && res_copy_nodes[r_5]) && res_copy_nodes[r_5_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_5 != r_5_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.edges, write)) might not hold on entry. There might be insufficient permission to access r.edges (graph-copy.vpr@155.17--155.70) [485]"}
                (forall r_5: Ref ::
                { Heap[r_5, edges] } { QPMask[r_5, edges] } { res_copy_nodes[r_5] }
                res_copy_nodes[r_5] ==> Mask[r_5, edges] >= FullPerm
              );
            
            // -- assumptions for inverse of receiver r
              assume (forall r_5: Ref ::
                { Heap[r_5, edges] } { QPMask[r_5, edges] } { res_copy_nodes[r_5] }
                res_copy_nodes[r_5] && NoPerm < FullPerm ==> qpRange16(r_5) && invRecv16(r_5) == r_5
              );
              assume (forall o_3: Ref ::
                { invRecv16(o_3) }
                res_copy_nodes[invRecv16(o_3)] && (NoPerm < FullPerm && qpRange16(o_3)) ==> invRecv16(o_3) == o_3
              );
            
            // -- assume permission updates for field edges
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                (res_copy_nodes[invRecv16(o_3)] && (NoPerm < FullPerm && qpRange16(o_3)) ==> invRecv16(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - FullPerm) && (!(res_copy_nodes[invRecv16(o_3)] && (NoPerm < FullPerm && qpRange16(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
        
        // -- Havoc loop written variables (except locals)
          havoc S, i_6, res_node_map, res_copy_nodes;
        
        // -- Check definedness of invariant
          if (*) {
            assume res_copy_nodes[nodeCopy];
            assume state(Heap, Mask);
            assume setOfRef[this];
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd))
              if (*) {
                assume false;
              }
            havoc QPMask;
            assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@145.17--145.66) [486]"}
              (forall x_47: Ref, x_47_1: Ref ::
              
              (((x_47 != x_47_1 && setOfRef[x_47]) && setOfRef[x_47_1]) && NoPerm < rd) && NoPerm < rd ==> x_47 != x_47_1
            );
            
            // -- Define Inverse Function
              assume (forall x_47: Ref ::
                { Heap[x_47, val] } { QPMask[x_47, val] } { setOfRef[x_47] }
                setOfRef[x_47] && NoPerm < rd ==> qpRange17(x_47) && invRecv17(x_47) == x_47
              );
              assume (forall o_3: Ref ::
                { invRecv17(o_3) }
                (setOfRef[invRecv17(o_3)] && NoPerm < rd) && qpRange17(o_3) ==> invRecv17(o_3) == o_3
              );
            // Check that permission expression is non-negative for all fields
            assert {:msg "  Contract might not be well-formed. Fraction rd might be negative. (graph-copy.vpr@145.17--145.66) [487]"}
              (forall x_47: Ref ::
              { Heap[x_47, val] } { QPMask[x_47, val] } { setOfRef[x_47] }
              setOfRef[x_47] ==> rd >= NoPerm
            );
            
            // -- Assume set of fields is nonNull
              assume (forall x_47: Ref ::
                { Heap[x_47, val] } { QPMask[x_47, val] } { setOfRef[x_47] }
                setOfRef[x_47] && rd > NoPerm ==> x_47 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                ((setOfRef[invRecv17(o_3)] && NoPerm < rd) && qpRange17(o_3) ==> (NoPerm < rd ==> invRecv17(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + rd) && (!((setOfRef[invRecv17(o_3)] && NoPerm < rd) && qpRange17(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.val == old(x.val))
              if (*) {
                if (setOfRef[x_8]) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.val (graph-copy.vpr@146.17--146.71) [488]"}
                    HasDirectPerm(Mask, x_8, val);
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.val (graph-copy.vpr@146.17--146.71) [489]"}
                    HasDirectPerm(old(Mask), x_8, val);
                }
                assume false;
              }
            assume (forall x_49: Ref ::
              { setOfRef[x_49] }
              setOfRef[x_49] ==> Heap[x_49, val] == old(Heap)[x_49, val]
            );
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd))
              if (*) {
                assume false;
              }
            havoc QPMask;
            assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@147.17--147.68) [490]"}
              (forall x_51: Ref, x_51_1: Ref ::
              
              (((x_51 != x_51_1 && setOfRef[x_51]) && setOfRef[x_51_1]) && NoPerm < rd) && NoPerm < rd ==> x_51 != x_51_1
            );
            
            // -- Define Inverse Function
              assume (forall x_51: Ref ::
                { Heap[x_51, edges] } { QPMask[x_51, edges] } { setOfRef[x_51] }
                setOfRef[x_51] && NoPerm < rd ==> qpRange18(x_51) && invRecv18(x_51) == x_51
              );
              assume (forall o_3: Ref ::
                { invRecv18(o_3) }
                (setOfRef[invRecv18(o_3)] && NoPerm < rd) && qpRange18(o_3) ==> invRecv18(o_3) == o_3
              );
            // Check that permission expression is non-negative for all fields
            assert {:msg "  Contract might not be well-formed. Fraction rd might be negative. (graph-copy.vpr@147.17--147.68) [491]"}
              (forall x_51: Ref ::
              { Heap[x_51, edges] } { QPMask[x_51, edges] } { setOfRef[x_51] }
              setOfRef[x_51] ==> rd >= NoPerm
            );
            
            // -- Assume set of fields is nonNull
              assume (forall x_51: Ref ::
                { Heap[x_51, edges] } { QPMask[x_51, edges] } { setOfRef[x_51] }
                setOfRef[x_51] && rd > NoPerm ==> x_51 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                ((setOfRef[invRecv18(o_3)] && NoPerm < rd) && qpRange18(o_3) ==> (NoPerm < rd ==> invRecv18(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + rd) && (!((setOfRef[invRecv18(o_3)] && NoPerm < rd) && qpRange18(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.edges == old(x.edges))
              if (*) {
                if (setOfRef[x_10]) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@148.17--148.75) [492]"}
                    HasDirectPerm(Mask, x_10, edges);
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access x.edges (graph-copy.vpr@148.17--148.75) [493]"}
                    HasDirectPerm(old(Mask), x_10, edges);
                }
                assume false;
              }
            assume (forall x_53: Ref ::
              { setOfRef[x_53] }
              setOfRef[x_53] ==> Heap[x_53, edges] == old(Heap)[x_53, edges]
            );
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall j: Int :: { (j in S) } { (edge_lookup(this.edges, j) in setOfRef) } (j in S) ==> (edge_lookup(this.edges, j) in setOfRef))
              if (*) {
                if (S[j_1]) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.edges (graph-copy.vpr@149.17--149.83) [494]"}
                    HasDirectPerm(Mask, this, edges);
                }
                assume false;
              }
            assume (forall j_5: int ::
              { S[j_5] } { setOfRef[(edge_lookup(Heap[this, edges], j_5): Ref)] }
              S[j_5] ==> setOfRef[(edge_lookup(Heap[this, edges], j_5): Ref)]
            );
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall r: Ref, j: Int :: { (r in setOfRef), (j in edges_domain(r.edges)) } { (r in setOfRef), edge_lookup(r.edges, j) } { (r in setOfRef), (edge_lookup(r.edges, j) in setOfRef) } { edges_domain(r.edges), edge_lookup(r.edges, j) } { edges_domain(r.edges), (edge_lookup(r.edges, j) in setOfRef) } { (j in edges_domain(r.edges)) } { (edge_lookup(r.edges, j) in setOfRef) } (r in setOfRef) && (j in edges_domain(r.edges)) ==> (edge_lookup(r.edges, j) in setOfRef))
              if (*) {
                if (setOfRef[r_3]) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access r.edges (graph-copy.vpr@150.17--150.125) [495]"}
                    HasDirectPerm(Mask, r_3, edges);
                }
                if (setOfRef[r_3] && (edges_domain(Heap[r_3, edges]): Set int)[j_3]) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access r.edges (graph-copy.vpr@150.17--150.125) [496]"}
                    HasDirectPerm(Mask, r_3, edges);
                }
                assume false;
              }
            assume (forall r_7: Ref, j_7: int ::
              { setOfRef[r_7], (edges_domain(Heap[r_7, edges]): Set int)[j_7] } { setOfRef[r_7], (edge_lookup(Heap[r_7, edges], j_7): Ref) } { setOfRef[r_7], setOfRef[(edge_lookup(Heap[r_7, edges], j_7): Ref)] } { (edges_domain(Heap[r_7, edges]): Set int), (edge_lookup(Heap[r_7, edges], j_7): Ref) } { (edges_domain(Heap[r_7, edges]): Set int), setOfRef[(edge_lookup(Heap[r_7, edges], j_7): Ref)] } { (edges_domain(Heap[r_7, edges]): Set int)[j_7] } { setOfRef[(edge_lookup(Heap[r_7, edges], j_7): Ref)] }
              setOfRef[r_7] && (edges_domain(Heap[r_7, edges]): Set int)[j_7] ==> setOfRef[(edge_lookup(Heap[r_7, edges], j_7): Ref)]
            );
            assume state(Heap, Mask);
            assume Set#Subset(node_map_image, res_copy_nodes);
            assume state(Heap, Mask);
            assume Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall r: Ref :: { (r in map_domain(res_node_map)) } { (lookup(res_node_map, r) in res_copy_nodes) } (r in map_domain(res_node_map)) ==> (lookup(res_node_map, r) in res_copy_nodes))
              if (*) {
                assume false;
              }
            assume (forall r_9: Ref ::
              { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), r_9) } { Seq#Contains((map_domain(res_node_map): Seq Ref), r_9) } { res_copy_nodes[(lookup(res_node_map, r_9): Ref)] }
              Seq#Contains((map_domain(res_node_map): Seq Ref), r_9) ==> res_copy_nodes[(lookup(res_node_map, r_9): Ref)]
            );
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.val, write))
              if (*) {
                assume false;
              }
            havoc QPMask;
            assert {:msg "  Contract might not be well-formed. Quantified resource r.val might not be injective. (graph-copy.vpr@154.17--154.68) [497]"}
              (forall r_11: Ref, r_11_1: Ref ::
              
              (((r_11 != r_11_1 && res_copy_nodes[r_11]) && res_copy_nodes[r_11_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_11 != r_11_1
            );
            
            // -- Define Inverse Function
              assume (forall r_11: Ref ::
                { Heap[r_11, val] } { QPMask[r_11, val] } { res_copy_nodes[r_11] }
                res_copy_nodes[r_11] && NoPerm < FullPerm ==> qpRange19(r_11) && invRecv19(r_11) == r_11
              );
              assume (forall o_3: Ref ::
                { invRecv19(o_3) }
                (res_copy_nodes[invRecv19(o_3)] && NoPerm < FullPerm) && qpRange19(o_3) ==> invRecv19(o_3) == o_3
              );
            
            // -- Assume set of fields is nonNull
              assume (forall r_11: Ref ::
                { Heap[r_11, val] } { QPMask[r_11, val] } { res_copy_nodes[r_11] }
                res_copy_nodes[r_11] ==> r_11 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                ((res_copy_nodes[invRecv19(o_3)] && NoPerm < FullPerm) && qpRange19(o_3) ==> (NoPerm < FullPerm ==> invRecv19(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!((res_copy_nodes[invRecv19(o_3)] && NoPerm < FullPerm) && qpRange19(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.edges, write))
              if (*) {
                assume false;
              }
            havoc QPMask;
            assert {:msg "  Contract might not be well-formed. Quantified resource r.edges might not be injective. (graph-copy.vpr@155.17--155.70) [498]"}
              (forall r_13: Ref, r_13_1: Ref ::
              
              (((r_13 != r_13_1 && res_copy_nodes[r_13]) && res_copy_nodes[r_13_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_13 != r_13_1
            );
            
            // -- Define Inverse Function
              assume (forall r_13: Ref ::
                { Heap[r_13, edges] } { QPMask[r_13, edges] } { res_copy_nodes[r_13] }
                res_copy_nodes[r_13] && NoPerm < FullPerm ==> qpRange20(r_13) && invRecv20(r_13) == r_13
              );
              assume (forall o_3: Ref ::
                { invRecv20(o_3) }
                (res_copy_nodes[invRecv20(o_3)] && NoPerm < FullPerm) && qpRange20(o_3) ==> invRecv20(o_3) == o_3
              );
            
            // -- Assume set of fields is nonNull
              assume (forall r_13: Ref ::
                { Heap[r_13, edges] } { QPMask[r_13, edges] } { res_copy_nodes[r_13] }
                res_copy_nodes[r_13] ==> r_13 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                ((res_copy_nodes[invRecv20(o_3)] && NoPerm < FullPerm) && qpRange20(o_3) ==> (NoPerm < FullPerm ==> invRecv20(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + FullPerm) && (!((res_copy_nodes[invRecv20(o_3)] && NoPerm < FullPerm) && qpRange20(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
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
            assume res_copy_nodes[nodeCopy];
            assume setOfRef[this];
            havoc QPMask;
            assert {:msg "  While statement might fail. Quantified resource x.val might not be injective. (graph-copy.vpr@145.17--145.66) [499]"}
              (forall x_54: Ref, x_54_1: Ref ::
              
              (((x_54 != x_54_1 && setOfRef[x_54]) && setOfRef[x_54_1]) && NoPerm < rd) && NoPerm < rd ==> x_54 != x_54_1
            );
            
            // -- Define Inverse Function
              assume (forall x_54: Ref ::
                { Heap[x_54, val] } { QPMask[x_54, val] } { setOfRef[x_54] }
                setOfRef[x_54] && NoPerm < rd ==> qpRange21(x_54) && invRecv21(x_54) == x_54
              );
              assume (forall o_3: Ref ::
                { invRecv21(o_3) }
                (setOfRef[invRecv21(o_3)] && NoPerm < rd) && qpRange21(o_3) ==> invRecv21(o_3) == o_3
              );
            // Check that permission expression is non-negative for all fields
            assert {:msg "  While statement might fail. Fraction rd might be negative. (graph-copy.vpr@145.17--145.66) [500]"}
              (forall x_54: Ref ::
              { Heap[x_54, val] } { QPMask[x_54, val] } { setOfRef[x_54] }
              setOfRef[x_54] ==> rd >= NoPerm
            );
            
            // -- Assume set of fields is nonNull
              assume (forall x_54: Ref ::
                { Heap[x_54, val] } { QPMask[x_54, val] } { setOfRef[x_54] }
                setOfRef[x_54] && rd > NoPerm ==> x_54 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                ((setOfRef[invRecv21(o_3)] && NoPerm < rd) && qpRange21(o_3) ==> (NoPerm < rd ==> invRecv21(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + rd) && (!((setOfRef[invRecv21(o_3)] && NoPerm < rd) && qpRange21(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            assume (forall x_55: Ref ::
              { setOfRef[x_55] }
              setOfRef[x_55] ==> Heap[x_55, val] == old(Heap)[x_55, val]
            );
            havoc QPMask;
            assert {:msg "  While statement might fail. Quantified resource x.edges might not be injective. (graph-copy.vpr@147.17--147.68) [501]"}
              (forall x_56: Ref, x_56_1: Ref ::
              
              (((x_56 != x_56_1 && setOfRef[x_56]) && setOfRef[x_56_1]) && NoPerm < rd) && NoPerm < rd ==> x_56 != x_56_1
            );
            
            // -- Define Inverse Function
              assume (forall x_56: Ref ::
                { Heap[x_56, edges] } { QPMask[x_56, edges] } { setOfRef[x_56] }
                setOfRef[x_56] && NoPerm < rd ==> qpRange22(x_56) && invRecv22(x_56) == x_56
              );
              assume (forall o_3: Ref ::
                { invRecv22(o_3) }
                (setOfRef[invRecv22(o_3)] && NoPerm < rd) && qpRange22(o_3) ==> invRecv22(o_3) == o_3
              );
            // Check that permission expression is non-negative for all fields
            assert {:msg "  While statement might fail. Fraction rd might be negative. (graph-copy.vpr@147.17--147.68) [502]"}
              (forall x_56: Ref ::
              { Heap[x_56, edges] } { QPMask[x_56, edges] } { setOfRef[x_56] }
              setOfRef[x_56] ==> rd >= NoPerm
            );
            
            // -- Assume set of fields is nonNull
              assume (forall x_56: Ref ::
                { Heap[x_56, edges] } { QPMask[x_56, edges] } { setOfRef[x_56] }
                setOfRef[x_56] && rd > NoPerm ==> x_56 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                ((setOfRef[invRecv22(o_3)] && NoPerm < rd) && qpRange22(o_3) ==> (NoPerm < rd ==> invRecv22(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + rd) && (!((setOfRef[invRecv22(o_3)] && NoPerm < rd) && qpRange22(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            assume (forall x_57: Ref ::
              { setOfRef[x_57] }
              setOfRef[x_57] ==> Heap[x_57, edges] == old(Heap)[x_57, edges]
            );
            assume (forall j_8: int ::
              { S[j_8] } { setOfRef[(edge_lookup(Heap[this, edges], j_8): Ref)] }
              S[j_8] ==> setOfRef[(edge_lookup(Heap[this, edges], j_8): Ref)]
            );
            assume (forall r_14: Ref, j_9: int ::
              { setOfRef[r_14], (edges_domain(Heap[r_14, edges]): Set int)[j_9] } { setOfRef[r_14], (edge_lookup(Heap[r_14, edges], j_9): Ref) } { setOfRef[r_14], setOfRef[(edge_lookup(Heap[r_14, edges], j_9): Ref)] } { (edges_domain(Heap[r_14, edges]): Set int), (edge_lookup(Heap[r_14, edges], j_9): Ref) } { (edges_domain(Heap[r_14, edges]): Set int), setOfRef[(edge_lookup(Heap[r_14, edges], j_9): Ref)] } { (edges_domain(Heap[r_14, edges]): Set int)[j_9] } { setOfRef[(edge_lookup(Heap[r_14, edges], j_9): Ref)] }
              setOfRef[r_14] && (edges_domain(Heap[r_14, edges]): Set int)[j_9] ==> setOfRef[(edge_lookup(Heap[r_14, edges], j_9): Ref)]
            );
            assume Set#Subset(node_map_image, res_copy_nodes);
            assume Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
            assume (forall r_15: Ref ::
              { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), r_15) } { Seq#Contains((map_domain(res_node_map): Seq Ref), r_15) } { res_copy_nodes[(lookup(res_node_map, r_15): Ref)] }
              Seq#Contains((map_domain(res_node_map): Seq Ref), r_15) ==> res_copy_nodes[(lookup(res_node_map, r_15): Ref)]
            );
            havoc QPMask;
            assert {:msg "  While statement might fail. Quantified resource r.val might not be injective. (graph-copy.vpr@154.17--154.68) [503]"}
              (forall r_16: Ref, r_16_1: Ref ::
              
              (((r_16 != r_16_1 && res_copy_nodes[r_16]) && res_copy_nodes[r_16_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_16 != r_16_1
            );
            
            // -- Define Inverse Function
              assume (forall r_16: Ref ::
                { Heap[r_16, val] } { QPMask[r_16, val] } { res_copy_nodes[r_16] }
                res_copy_nodes[r_16] && NoPerm < FullPerm ==> qpRange23(r_16) && invRecv23(r_16) == r_16
              );
              assume (forall o_3: Ref ::
                { invRecv23(o_3) }
                (res_copy_nodes[invRecv23(o_3)] && NoPerm < FullPerm) && qpRange23(o_3) ==> invRecv23(o_3) == o_3
              );
            
            // -- Assume set of fields is nonNull
              assume (forall r_16: Ref ::
                { Heap[r_16, val] } { QPMask[r_16, val] } { res_copy_nodes[r_16] }
                res_copy_nodes[r_16] ==> r_16 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                ((res_copy_nodes[invRecv23(o_3)] && NoPerm < FullPerm) && qpRange23(o_3) ==> (NoPerm < FullPerm ==> invRecv23(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!((res_copy_nodes[invRecv23(o_3)] && NoPerm < FullPerm) && qpRange23(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            havoc QPMask;
            assert {:msg "  While statement might fail. Quantified resource r.edges might not be injective. (graph-copy.vpr@155.17--155.70) [504]"}
              (forall r_17: Ref, r_17_1: Ref ::
              
              (((r_17 != r_17_1 && res_copy_nodes[r_17]) && res_copy_nodes[r_17_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_17 != r_17_1
            );
            
            // -- Define Inverse Function
              assume (forall r_17: Ref ::
                { Heap[r_17, edges] } { QPMask[r_17, edges] } { res_copy_nodes[r_17] }
                res_copy_nodes[r_17] && NoPerm < FullPerm ==> qpRange24(r_17) && invRecv24(r_17) == r_17
              );
              assume (forall o_3: Ref ::
                { invRecv24(o_3) }
                (res_copy_nodes[invRecv24(o_3)] && NoPerm < FullPerm) && qpRange24(o_3) ==> invRecv24(o_3) == o_3
              );
            
            // -- Assume set of fields is nonNull
              assume (forall r_17: Ref ::
                { Heap[r_17, edges] } { QPMask[r_17, edges] } { res_copy_nodes[r_17] }
                res_copy_nodes[r_17] ==> r_17 != null
              );
            
            // -- Define permissions
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                ((res_copy_nodes[invRecv24(o_3)] && NoPerm < FullPerm) && qpRange24(o_3) ==> (NoPerm < FullPerm ==> invRecv24(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + FullPerm) && (!((res_copy_nodes[invRecv24(o_3)] && NoPerm < FullPerm) && qpRange24(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            // Check and assume guard
            assume Set#Card(S) > 0;
            assume state(Heap, Mask);
            
            // -- Translate loop body
              
              // -- Assumptions about local variables
                assume Heap[newNode, $allocated];
                assume Heap[nodeForId, $allocated];
              
              // -- Translating statement: S, i := pop(S) -- graph-copy.vpr@157.7--157.21
                PreCallHeap := Heap;
                PreCallMask := Mask;
                arg_s1 := S;
                havoc S, i_6;
                
                // -- Exhaling precondition
                  assert {:msg "  The precondition of method pop might not hold. Assertion 0 < |S| might not hold. (graph-copy.vpr@157.7--157.21) [505]"}
                    0 < Set#Card(arg_s1);
                
                // -- Inhaling postcondition
                  assume arg_s1[i_6];
                  assume Set#Equal(S, Set#Difference(arg_s1, Set#Singleton(i_6)));
                  assume state(Heap, Mask);
                assume state(Heap, Mask);
              
              // -- Translating statement: nodeForId := edge_lookup(this.edges, i) -- graph-copy.vpr@163.7--163.46
                
                // -- Check definedness of edge_lookup(this.edges, i)
                  assert {:msg "  Assignment might fail. There might be insufficient permission to access this.edges (graph-copy.vpr@163.7--163.46) [506]"}
                    HasDirectPerm(Mask, this, edges);
                nodeForId := (edge_lookup(Heap[this, edges], i_6): Ref);
                assume state(Heap, Mask);
              
              // -- Translating statement: newNode, res_node_map, res_copy_nodes := graph_copy_rec(nodeForId, res_node_map,
  //   setOfRef, res_copy_nodes, rd / 2) -- graph-copy.vpr@165.7--165.119
                PreCallHeap := Heap;
                PreCallMask := Mask;
                arg_node_map := res_node_map;
                arg_node_map_image := res_copy_nodes;
                arg_rd := rd / 2;
                havoc newNode, res_node_map, res_copy_nodes;
                
                // -- Exhaling precondition
                  assert {:msg "  The precondition of method graph_copy_rec might not hold. Assertion none < rd / 2 might not hold. (graph-copy.vpr@165.7--165.119) [507]"}
                    NoPerm < arg_rd;
                  assert {:msg "  The precondition of method graph_copy_rec might not hold. Assertion nodeForId != null might not hold. (graph-copy.vpr@165.7--165.119) [508]"}
                    nodeForId != null;
                  assert {:msg "  The precondition of method graph_copy_rec might not hold. Assertion (nodeForId in setOfRef) might not hold. (graph-copy.vpr@165.7--165.119) [509]"}
                    setOfRef[nodeForId];
                  assert {:msg "  The precondition of method graph_copy_rec might not hold. Assertion |(setOfRef intersection res_copy_nodes)| == 0 might not hold. (graph-copy.vpr@165.7--165.119) [510]"}
                    Set#Card(Set#Intersection(setOfRef, arg_node_map_image)) == 0;
                  havoc QPMask;
                  
                  // -- check that the permission amount is positive
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. Fraction rd / 2 might be negative. (graph-copy.vpr@165.7--165.119) [511]"}
                      (forall x_58: Ref ::
                      { Heap[x_58, val] } { QPMask[x_58, val] } { setOfRef[x_58] }
                      setOfRef[x_58] && dummyFunction(Heap[x_58, val]) ==> arg_rd >= NoPerm
                    );
                  
                  // -- check if receiver x is injective
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. Quantified resource x.val might not be injective. (graph-copy.vpr@165.7--165.119) [512]"}
                      (forall x_58: Ref, x_58_1: Ref ::
                      { neverTriggered25(x_58), neverTriggered25(x_58_1) }
                      (((x_58 != x_58_1 && setOfRef[x_58]) && setOfRef[x_58_1]) && NoPerm < arg_rd) && NoPerm < arg_rd ==> x_58 != x_58_1
                    );
                  
                  // -- check if sufficient permission is held
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. There might be insufficient permission to access x.val (graph-copy.vpr@165.7--165.119) [513]"}
                      (forall x_58: Ref ::
                      { Heap[x_58, val] } { QPMask[x_58, val] } { setOfRef[x_58] }
                      setOfRef[x_58] ==> Mask[x_58, val] >= arg_rd
                    );
                  
                  // -- assumptions for inverse of receiver x
                    assume (forall x_58: Ref ::
                      { Heap[x_58, val] } { QPMask[x_58, val] } { setOfRef[x_58] }
                      setOfRef[x_58] && NoPerm < arg_rd ==> qpRange25(x_58) && invRecv25(x_58) == x_58
                    );
                    assume (forall o_3: Ref ::
                      { invRecv25(o_3) }
                      setOfRef[invRecv25(o_3)] && (NoPerm < arg_rd && qpRange25(o_3)) ==> invRecv25(o_3) == o_3
                    );
                  
                  // -- assume permission updates for field val
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, val] }
                      (setOfRef[invRecv25(o_3)] && (NoPerm < arg_rd && qpRange25(o_3)) ==> invRecv25(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - arg_rd) && (!(setOfRef[invRecv25(o_3)] && (NoPerm < arg_rd && qpRange25(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
                    );
                  
                  // -- assume permission updates for independent locations
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { QPMask[o_3, f_5] }
                      f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  havoc QPMask;
                  
                  // -- check that the permission amount is positive
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. Fraction rd / 2 might be negative. (graph-copy.vpr@165.7--165.119) [514]"}
                      (forall x_59: Ref ::
                      { Heap[x_59, edges] } { QPMask[x_59, edges] } { setOfRef[x_59] }
                      setOfRef[x_59] && dummyFunction(Heap[x_59, edges]) ==> arg_rd >= NoPerm
                    );
                  
                  // -- check if receiver x is injective
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. Quantified resource x.edges might not be injective. (graph-copy.vpr@165.7--165.119) [515]"}
                      (forall x_59: Ref, x_59_1: Ref ::
                      { neverTriggered26(x_59), neverTriggered26(x_59_1) }
                      (((x_59 != x_59_1 && setOfRef[x_59]) && setOfRef[x_59_1]) && NoPerm < arg_rd) && NoPerm < arg_rd ==> x_59 != x_59_1
                    );
                  
                  // -- check if sufficient permission is held
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. There might be insufficient permission to access x.edges (graph-copy.vpr@165.7--165.119) [516]"}
                      (forall x_59: Ref ::
                      { Heap[x_59, edges] } { QPMask[x_59, edges] } { setOfRef[x_59] }
                      setOfRef[x_59] ==> Mask[x_59, edges] >= arg_rd
                    );
                  
                  // -- assumptions for inverse of receiver x
                    assume (forall x_59: Ref ::
                      { Heap[x_59, edges] } { QPMask[x_59, edges] } { setOfRef[x_59] }
                      setOfRef[x_59] && NoPerm < arg_rd ==> qpRange26(x_59) && invRecv26(x_59) == x_59
                    );
                    assume (forall o_3: Ref ::
                      { invRecv26(o_3) }
                      setOfRef[invRecv26(o_3)] && (NoPerm < arg_rd && qpRange26(o_3)) ==> invRecv26(o_3) == o_3
                    );
                  
                  // -- assume permission updates for field edges
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, edges] }
                      (setOfRef[invRecv26(o_3)] && (NoPerm < arg_rd && qpRange26(o_3)) ==> invRecv26(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - arg_rd) && (!(setOfRef[invRecv26(o_3)] && (NoPerm < arg_rd && qpRange26(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
                    );
                  
                  // -- assume permission updates for independent locations
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { QPMask[o_3, f_5] }
                      f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  if (*) {
                    if (setOfRef[x_60] && (edges_domain(Heap[x_60, edges]): Set int)[i$0]) {
                      assert {:msg "  The precondition of method graph_copy_rec might not hold. Assertion (edge_lookup(x.edges, i$0) in setOfRef) might not hold. (graph-copy.vpr@165.7--165.119) [517]"}
                        setOfRef[(edge_lookup(Heap[x_60, edges], i$0): Ref)];
                    }
                    assume false;
                  }
                  assume (forall x_61_1: Ref, i$0_1_1: int ::
                    { setOfRef[x_61_1], (edges_domain(Heap[x_61_1, edges]): Set int)[i$0_1_1] } { setOfRef[x_61_1], (edge_lookup(Heap[x_61_1, edges], i$0_1_1): Ref) } { setOfRef[x_61_1], setOfRef[(edge_lookup(Heap[x_61_1, edges], i$0_1_1): Ref)] } { (edges_domain(Heap[x_61_1, edges]): Set int), (edge_lookup(Heap[x_61_1, edges], i$0_1_1): Ref) } { (edges_domain(Heap[x_61_1, edges]): Set int), setOfRef[(edge_lookup(Heap[x_61_1, edges], i$0_1_1): Ref)] } { (edges_domain(Heap[x_61_1, edges]): Set int)[i$0_1_1] } { setOfRef[(edge_lookup(Heap[x_61_1, edges], i$0_1_1): Ref)] }
                    setOfRef[x_61_1] && (edges_domain(Heap[x_61_1, edges]): Set int)[i$0_1_1] ==> setOfRef[(edge_lookup(Heap[x_61_1, edges], i$0_1_1): Ref)]
                  );
                  if (*) {
                    if (Seq#Contains((map_domain(arg_node_map): Seq Ref), x_62)) {
                      assert {:msg "  The precondition of method graph_copy_rec might not hold. Assertion (lookup(res_node_map, x) in res_copy_nodes) might not hold. (graph-copy.vpr@165.7--165.119) [518]"}
                        arg_node_map_image[(lookup(arg_node_map, x_62): Ref)];
                    }
                    assume false;
                  }
                  assume (forall x_63_1: Ref ::
                    { Seq#ContainsTrigger((map_domain(arg_node_map): Seq Ref), x_63_1) } { Seq#Contains((map_domain(arg_node_map): Seq Ref), x_63_1) } { arg_node_map_image[(lookup(arg_node_map, x_63_1): Ref)] }
                    Seq#Contains((map_domain(arg_node_map): Seq Ref), x_63_1) ==> arg_node_map_image[(lookup(arg_node_map, x_63_1): Ref)]
                  );
                  havoc QPMask;
                  
                  // -- check that the permission amount is positive
                    
                  
                  // -- check if receiver x is injective
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. Quantified resource x.val might not be injective. (graph-copy.vpr@165.7--165.119) [519]"}
                      (forall x_64: Ref, x_64_1: Ref ::
                      { neverTriggered27(x_64), neverTriggered27(x_64_1) }
                      (((x_64 != x_64_1 && arg_node_map_image[x_64]) && arg_node_map_image[x_64_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_64 != x_64_1
                    );
                  
                  // -- check if sufficient permission is held
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. There might be insufficient permission to access x.val (graph-copy.vpr@165.7--165.119) [520]"}
                      (forall x_64: Ref ::
                      { Heap[x_64, val] } { QPMask[x_64, val] } { arg_node_map_image[x_64] }
                      arg_node_map_image[x_64] ==> Mask[x_64, val] >= FullPerm
                    );
                  
                  // -- assumptions for inverse of receiver x
                    assume (forall x_64: Ref ::
                      { Heap[x_64, val] } { QPMask[x_64, val] } { arg_node_map_image[x_64] }
                      arg_node_map_image[x_64] && NoPerm < FullPerm ==> qpRange27(x_64) && invRecv27(x_64) == x_64
                    );
                    assume (forall o_3: Ref ::
                      { invRecv27(o_3) }
                      arg_node_map_image[invRecv27(o_3)] && (NoPerm < FullPerm && qpRange27(o_3)) ==> invRecv27(o_3) == o_3
                    );
                  
                  // -- assume permission updates for field val
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, val] }
                      (arg_node_map_image[invRecv27(o_3)] && (NoPerm < FullPerm && qpRange27(o_3)) ==> invRecv27(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!(arg_node_map_image[invRecv27(o_3)] && (NoPerm < FullPerm && qpRange27(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
                    );
                  
                  // -- assume permission updates for independent locations
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { QPMask[o_3, f_5] }
                      f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  havoc QPMask;
                  
                  // -- check that the permission amount is positive
                    
                  
                  // -- check if receiver x is injective
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. Quantified resource x.edges might not be injective. (graph-copy.vpr@165.7--165.119) [521]"}
                      (forall x_65: Ref, x_65_1: Ref ::
                      { neverTriggered28(x_65), neverTriggered28(x_65_1) }
                      (((x_65 != x_65_1 && arg_node_map_image[x_65]) && arg_node_map_image[x_65_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_65 != x_65_1
                    );
                  
                  // -- check if sufficient permission is held
                    assert {:msg "  The precondition of method graph_copy_rec might not hold. There might be insufficient permission to access x.edges (graph-copy.vpr@165.7--165.119) [522]"}
                      (forall x_65: Ref ::
                      { Heap[x_65, edges] } { QPMask[x_65, edges] } { arg_node_map_image[x_65] }
                      arg_node_map_image[x_65] ==> Mask[x_65, edges] >= FullPerm
                    );
                  
                  // -- assumptions for inverse of receiver x
                    assume (forall x_65: Ref ::
                      { Heap[x_65, edges] } { QPMask[x_65, edges] } { arg_node_map_image[x_65] }
                      arg_node_map_image[x_65] && NoPerm < FullPerm ==> qpRange28(x_65) && invRecv28(x_65) == x_65
                    );
                    assume (forall o_3: Ref ::
                      { invRecv28(o_3) }
                      arg_node_map_image[invRecv28(o_3)] && (NoPerm < FullPerm && qpRange28(o_3)) ==> invRecv28(o_3) == o_3
                    );
                  
                  // -- assume permission updates for field edges
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, edges] }
                      (arg_node_map_image[invRecv28(o_3)] && (NoPerm < FullPerm && qpRange28(o_3)) ==> invRecv28(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - FullPerm) && (!(arg_node_map_image[invRecv28(o_3)] && (NoPerm < FullPerm && qpRange28(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
                    );
                  
                  // -- assume permission updates for independent locations
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { QPMask[o_3, f_5] }
                      f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  // Finish exhale
                  havoc ExhaleHeap;
                  assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                  Heap := ExhaleHeap;
                
                // -- Inhaling postcondition
                  assume newNode != null;
                  assume res_copy_nodes[newNode];
                  assume Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
                  havoc QPMask;
                  assert {:msg "  Method call might fail. Quantified resource x.val might not be injective. (graph-copy.vpr@165.7--165.119) [523]"}
                    (forall x_66: Ref, x_66_1: Ref ::
                    
                    (((x_66 != x_66_1 && setOfRef[x_66]) && setOfRef[x_66_1]) && NoPerm < arg_rd) && NoPerm < arg_rd ==> x_66 != x_66_1
                  );
                  
                  // -- Define Inverse Function
                    assume (forall x_66: Ref ::
                      { Heap[x_66, val] } { QPMask[x_66, val] } { setOfRef[x_66] }
                      setOfRef[x_66] && NoPerm < arg_rd ==> qpRange29(x_66) && invRecv29(x_66) == x_66
                    );
                    assume (forall o_3: Ref ::
                      { invRecv29(o_3) }
                      (setOfRef[invRecv29(o_3)] && NoPerm < arg_rd) && qpRange29(o_3) ==> invRecv29(o_3) == o_3
                    );
                  // Check that permission expression is non-negative for all fields
                  assert {:msg "  Method call might fail. Fraction rd / 2 might be negative. (graph-copy.vpr@165.7--165.119) [524]"}
                    (forall x_66: Ref ::
                    { Heap[x_66, val] } { QPMask[x_66, val] } { setOfRef[x_66] }
                    setOfRef[x_66] ==> arg_rd >= NoPerm
                  );
                  
                  // -- Assume set of fields is nonNull
                    assume (forall x_66: Ref ::
                      { Heap[x_66, val] } { QPMask[x_66, val] } { setOfRef[x_66] }
                      setOfRef[x_66] && arg_rd > NoPerm ==> x_66 != null
                    );
                  
                  // -- Define permissions
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, val] }
                      ((setOfRef[invRecv29(o_3)] && NoPerm < arg_rd) && qpRange29(o_3) ==> (NoPerm < arg_rd ==> invRecv29(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + arg_rd) && (!((setOfRef[invRecv29(o_3)] && NoPerm < arg_rd) && qpRange29(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
                    );
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                      f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  assume state(Heap, Mask);
                  assume (forall x_67: Ref ::
                    { setOfRef[x_67] }
                    setOfRef[x_67] ==> Heap[x_67, val] == old(PreCallHeap)[x_67, val]
                  );
                  havoc QPMask;
                  assert {:msg "  Method call might fail. Quantified resource x.edges might not be injective. (graph-copy.vpr@165.7--165.119) [525]"}
                    (forall x_68: Ref, x_68_1: Ref ::
                    
                    (((x_68 != x_68_1 && setOfRef[x_68]) && setOfRef[x_68_1]) && NoPerm < arg_rd) && NoPerm < arg_rd ==> x_68 != x_68_1
                  );
                  
                  // -- Define Inverse Function
                    assume (forall x_68: Ref ::
                      { Heap[x_68, edges] } { QPMask[x_68, edges] } { setOfRef[x_68] }
                      setOfRef[x_68] && NoPerm < arg_rd ==> qpRange30(x_68) && invRecv30(x_68) == x_68
                    );
                    assume (forall o_3: Ref ::
                      { invRecv30(o_3) }
                      (setOfRef[invRecv30(o_3)] && NoPerm < arg_rd) && qpRange30(o_3) ==> invRecv30(o_3) == o_3
                    );
                  // Check that permission expression is non-negative for all fields
                  assert {:msg "  Method call might fail. Fraction rd / 2 might be negative. (graph-copy.vpr@165.7--165.119) [526]"}
                    (forall x_68: Ref ::
                    { Heap[x_68, edges] } { QPMask[x_68, edges] } { setOfRef[x_68] }
                    setOfRef[x_68] ==> arg_rd >= NoPerm
                  );
                  
                  // -- Assume set of fields is nonNull
                    assume (forall x_68: Ref ::
                      { Heap[x_68, edges] } { QPMask[x_68, edges] } { setOfRef[x_68] }
                      setOfRef[x_68] && arg_rd > NoPerm ==> x_68 != null
                    );
                  
                  // -- Define permissions
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, edges] }
                      ((setOfRef[invRecv30(o_3)] && NoPerm < arg_rd) && qpRange30(o_3) ==> (NoPerm < arg_rd ==> invRecv30(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + arg_rd) && (!((setOfRef[invRecv30(o_3)] && NoPerm < arg_rd) && qpRange30(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
                    );
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                      f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  assume state(Heap, Mask);
                  assume (forall x_69: Ref ::
                    { setOfRef[x_69] }
                    setOfRef[x_69] ==> Heap[x_69, edges] == old(PreCallHeap)[x_69, edges]
                  );
                  assume (forall x_70: Ref, i$0_2: int ::
                    { setOfRef[x_70], (edges_domain(Heap[x_70, edges]): Set int)[i$0_2] } { setOfRef[x_70], (edge_lookup(Heap[x_70, edges], i$0_2): Ref) } { setOfRef[x_70], setOfRef[(edge_lookup(Heap[x_70, edges], i$0_2): Ref)] } { (edges_domain(Heap[x_70, edges]): Set int), (edge_lookup(Heap[x_70, edges], i$0_2): Ref) } { (edges_domain(Heap[x_70, edges]): Set int), setOfRef[(edge_lookup(Heap[x_70, edges], i$0_2): Ref)] } { (edges_domain(Heap[x_70, edges]): Set int)[i$0_2] } { setOfRef[(edge_lookup(Heap[x_70, edges], i$0_2): Ref)] }
                    setOfRef[x_70] && (edges_domain(Heap[x_70, edges]): Set int)[i$0_2] ==> setOfRef[(edge_lookup(Heap[x_70, edges], i$0_2): Ref)]
                  );
                  assume Set#Equal(res_copy_nodes, Set#Union(res_copy_nodes, arg_node_map_image));
                  assume (forall x_71: Ref ::
                    { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), x_71) } { Seq#Contains((map_domain(res_node_map): Seq Ref), x_71) } { res_copy_nodes[(lookup(res_node_map, x_71): Ref)] }
                    Seq#Contains((map_domain(res_node_map): Seq Ref), x_71) ==> res_copy_nodes[(lookup(res_node_map, x_71): Ref)]
                  );
                  havoc QPMask;
                  assert {:msg "  Method call might fail. Quantified resource x.val might not be injective. (graph-copy.vpr@165.7--165.119) [527]"}
                    (forall x_72: Ref, x_72_1: Ref ::
                    
                    (((x_72 != x_72_1 && res_copy_nodes[x_72]) && res_copy_nodes[x_72_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_72 != x_72_1
                  );
                  
                  // -- Define Inverse Function
                    assume (forall x_72: Ref ::
                      { Heap[x_72, val] } { QPMask[x_72, val] } { res_copy_nodes[x_72] }
                      res_copy_nodes[x_72] && NoPerm < FullPerm ==> qpRange31(x_72) && invRecv31(x_72) == x_72
                    );
                    assume (forall o_3: Ref ::
                      { invRecv31(o_3) }
                      (res_copy_nodes[invRecv31(o_3)] && NoPerm < FullPerm) && qpRange31(o_3) ==> invRecv31(o_3) == o_3
                    );
                  
                  // -- Assume set of fields is nonNull
                    assume (forall x_72: Ref ::
                      { Heap[x_72, val] } { QPMask[x_72, val] } { res_copy_nodes[x_72] }
                      res_copy_nodes[x_72] ==> x_72 != null
                    );
                  
                  // -- Define permissions
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, val] }
                      ((res_copy_nodes[invRecv31(o_3)] && NoPerm < FullPerm) && qpRange31(o_3) ==> (NoPerm < FullPerm ==> invRecv31(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!((res_copy_nodes[invRecv31(o_3)] && NoPerm < FullPerm) && qpRange31(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
                    );
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                      f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  assume state(Heap, Mask);
                  havoc QPMask;
                  assert {:msg "  Method call might fail. Quantified resource x.edges might not be injective. (graph-copy.vpr@165.7--165.119) [528]"}
                    (forall x_73: Ref, x_73_1: Ref ::
                    
                    (((x_73 != x_73_1 && res_copy_nodes[x_73]) && res_copy_nodes[x_73_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_73 != x_73_1
                  );
                  
                  // -- Define Inverse Function
                    assume (forall x_73: Ref ::
                      { Heap[x_73, edges] } { QPMask[x_73, edges] } { res_copy_nodes[x_73] }
                      res_copy_nodes[x_73] && NoPerm < FullPerm ==> qpRange32(x_73) && invRecv32(x_73) == x_73
                    );
                    assume (forall o_3: Ref ::
                      { invRecv32(o_3) }
                      (res_copy_nodes[invRecv32(o_3)] && NoPerm < FullPerm) && qpRange32(o_3) ==> invRecv32(o_3) == o_3
                    );
                  
                  // -- Assume set of fields is nonNull
                    assume (forall x_73: Ref ::
                      { Heap[x_73, edges] } { QPMask[x_73, edges] } { res_copy_nodes[x_73] }
                      res_copy_nodes[x_73] ==> x_73 != null
                    );
                  
                  // -- Define permissions
                    assume (forall o_3: Ref ::
                      { QPMask[o_3, edges] }
                      ((res_copy_nodes[invRecv32(o_3)] && NoPerm < FullPerm) && qpRange32(o_3) ==> (NoPerm < FullPerm ==> invRecv32(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + FullPerm) && (!((res_copy_nodes[invRecv32(o_3)] && NoPerm < FullPerm) && qpRange32(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
                    );
                    assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                      { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
                      f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
                    );
                  Mask := QPMask;
                  assume state(Heap, Mask);
                  assume state(Heap, Mask);
                assume Heap[newNode, $allocated];
                assume state(Heap, Mask);
              
              // -- Translating statement: nodeCopy.edges := insert_edge(nodeCopy.edges, i, newNode) -- graph-copy.vpr@167.7--167.64
                
                // -- Check definedness of insert_edge(nodeCopy.edges, i, newNode)
                  assert {:msg "  Assignment might fail. There might be insufficient permission to access nodeCopy.edges (graph-copy.vpr@167.7--167.64) [529]"}
                    HasDirectPerm(Mask, nodeCopy, edges);
                assert {:msg "  Assignment might fail. There might be insufficient permission to access nodeCopy.edges (graph-copy.vpr@167.7--167.64) [530]"}
                  FullPerm == Mask[nodeCopy, edges];
                Heap[nodeCopy, edges] := (insert_edge(Heap[nodeCopy, edges], i_6, newNode): IEdgesDomainType);
                assume state(Heap, Mask);
            // Exhale invariant
            assert {:msg "  Loop invariant (nodeCopy in res_copy_nodes) might not be preserved. Assertion (nodeCopy in res_copy_nodes) might not hold. (graph-copy.vpr@143.17--143.43) [531]"}
              res_copy_nodes[nodeCopy];
            assert {:msg "  Loop invariant (this in setOfRef) might not be preserved. Assertion (this in setOfRef) might not hold. (graph-copy.vpr@144.17--144.33) [532]"}
              setOfRef[this];
            havoc QPMask;
            
            // -- check that the permission amount is positive
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd)) might not be preserved. Fraction rd might be negative. (graph-copy.vpr@145.17--145.66) [533]"}
                (forall x_74: Ref ::
                { Heap[x_74, val] } { QPMask[x_74, val] } { setOfRef[x_74] }
                setOfRef[x_74] && dummyFunction(Heap[x_74, val]) ==> rd >= NoPerm
              );
            
            // -- check if receiver x is injective
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd)) might not be preserved. Quantified resource x.val might not be injective. (graph-copy.vpr@145.17--145.66) [534]"}
                (forall x_74: Ref, x_74_1: Ref ::
                { neverTriggered33(x_74), neverTriggered33(x_74_1) }
                (((x_74 != x_74_1 && setOfRef[x_74]) && setOfRef[x_74_1]) && NoPerm < rd) && NoPerm < rd ==> x_74 != x_74_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.val, rd)) might not be preserved. There might be insufficient permission to access x.val (graph-copy.vpr@145.17--145.66) [535]"}
                (forall x_74: Ref ::
                { Heap[x_74, val] } { QPMask[x_74, val] } { setOfRef[x_74] }
                setOfRef[x_74] ==> Mask[x_74, val] >= rd
              );
            
            // -- assumptions for inverse of receiver x
              assume (forall x_74: Ref ::
                { Heap[x_74, val] } { QPMask[x_74, val] } { setOfRef[x_74] }
                setOfRef[x_74] && NoPerm < rd ==> qpRange33(x_74) && invRecv33(x_74) == x_74
              );
              assume (forall o_3: Ref ::
                { invRecv33(o_3) }
                setOfRef[invRecv33(o_3)] && (NoPerm < rd && qpRange33(o_3)) ==> invRecv33(o_3) == o_3
              );
            
            // -- assume permission updates for field val
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                (setOfRef[invRecv33(o_3)] && (NoPerm < rd && qpRange33(o_3)) ==> invRecv33(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - rd) && (!(setOfRef[invRecv33(o_3)] && (NoPerm < rd && qpRange33(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            if (*) {
              if (setOfRef[x_75]) {
                assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.val == old(x.val)) might not be preserved. Assertion x.val == old(x.val) might not hold. (graph-copy.vpr@146.17--146.71) [536]"}
                  Heap[x_75, val] == old(Heap)[x_75, val];
              }
              assume false;
            }
            assume (forall x_76_1: Ref ::
              { setOfRef[x_76_1] }
              setOfRef[x_76_1] ==> Heap[x_76_1, val] == old(Heap)[x_76_1, val]
            );
            havoc QPMask;
            
            // -- check that the permission amount is positive
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd)) might not be preserved. Fraction rd might be negative. (graph-copy.vpr@147.17--147.68) [537]"}
                (forall x_77: Ref ::
                { Heap[x_77, edges] } { QPMask[x_77, edges] } { setOfRef[x_77] }
                setOfRef[x_77] && dummyFunction(Heap[x_77, edges]) ==> rd >= NoPerm
              );
            
            // -- check if receiver x is injective
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd)) might not be preserved. Quantified resource x.edges might not be injective. (graph-copy.vpr@147.17--147.68) [538]"}
                (forall x_77: Ref, x_77_1: Ref ::
                { neverTriggered34(x_77), neverTriggered34(x_77_1) }
                (((x_77 != x_77_1 && setOfRef[x_77]) && setOfRef[x_77_1]) && NoPerm < rd) && NoPerm < rd ==> x_77 != x_77_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> acc(x.edges, rd)) might not be preserved. There might be insufficient permission to access x.edges (graph-copy.vpr@147.17--147.68) [539]"}
                (forall x_77: Ref ::
                { Heap[x_77, edges] } { QPMask[x_77, edges] } { setOfRef[x_77] }
                setOfRef[x_77] ==> Mask[x_77, edges] >= rd
              );
            
            // -- assumptions for inverse of receiver x
              assume (forall x_77: Ref ::
                { Heap[x_77, edges] } { QPMask[x_77, edges] } { setOfRef[x_77] }
                setOfRef[x_77] && NoPerm < rd ==> qpRange34(x_77) && invRecv34(x_77) == x_77
              );
              assume (forall o_3: Ref ::
                { invRecv34(o_3) }
                setOfRef[invRecv34(o_3)] && (NoPerm < rd && qpRange34(o_3)) ==> invRecv34(o_3) == o_3
              );
            
            // -- assume permission updates for field edges
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                (setOfRef[invRecv34(o_3)] && (NoPerm < rd && qpRange34(o_3)) ==> invRecv34(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - rd) && (!(setOfRef[invRecv34(o_3)] && (NoPerm < rd && qpRange34(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            if (*) {
              if (setOfRef[x_78]) {
                assert {:msg "  Loop invariant (forall x: Ref :: { (x in setOfRef) } (x in setOfRef) ==> x.edges == old(x.edges)) might not be preserved. Assertion x.edges == old(x.edges) might not hold. (graph-copy.vpr@148.17--148.75) [540]"}
                  Heap[x_78, edges] == old(Heap)[x_78, edges];
              }
              assume false;
            }
            assume (forall x_79_1: Ref ::
              { setOfRef[x_79_1] }
              setOfRef[x_79_1] ==> Heap[x_79_1, edges] == old(Heap)[x_79_1, edges]
            );
            if (*) {
              if (S[j_10]) {
                assert {:msg "  Loop invariant (forall j: Int :: { (j in S) } { (edge_lookup(this.edges, j) in setOfRef) } (j in S) ==> (edge_lookup(this.edges, j) in setOfRef)) might not be preserved. Assertion (edge_lookup(this.edges, j) in setOfRef) might not hold. (graph-copy.vpr@149.17--149.83) [541]"}
                  setOfRef[(edge_lookup(Heap[this, edges], j_10): Ref)];
              }
              assume false;
            }
            assume (forall j_11_1: int ::
              { S[j_11_1] } { setOfRef[(edge_lookup(Heap[this, edges], j_11_1): Ref)] }
              S[j_11_1] ==> setOfRef[(edge_lookup(Heap[this, edges], j_11_1): Ref)]
            );
            if (*) {
              if (setOfRef[r_18] && (edges_domain(Heap[r_18, edges]): Set int)[j_12]) {
                assert {:msg "  Loop invariant (forall r: Ref, j: Int :: { (r in setOfRef), (j in edges_domain(r.edges)) } { (r in setOfRef), edge_lookup(r.edges, j) } { (r in setOfRef), (edge_lookup(r.edges, j) in setOfRef) } { edges_domain(r.edges), edge_lookup(r.edges, j) } { edges_domain(r.edges), (edge_lookup(r.edges, j) in setOfRef) } { (j in edges_domain(r.edges)) } { (edge_lookup(r.edges, j) in setOfRef) } (r in setOfRef) && (j in edges_domain(r.edges)) ==> (edge_lookup(r.edges, j) in setOfRef)) might not be preserved. Assertion (edge_lookup(r.edges, j) in setOfRef) might not hold. (graph-copy.vpr@150.17--150.125) [542]"}
                  setOfRef[(edge_lookup(Heap[r_18, edges], j_12): Ref)];
              }
              assume false;
            }
            assume (forall r_19_1: Ref, j_13_1: int ::
              { setOfRef[r_19_1], (edges_domain(Heap[r_19_1, edges]): Set int)[j_13_1] } { setOfRef[r_19_1], (edge_lookup(Heap[r_19_1, edges], j_13_1): Ref) } { setOfRef[r_19_1], setOfRef[(edge_lookup(Heap[r_19_1, edges], j_13_1): Ref)] } { (edges_domain(Heap[r_19_1, edges]): Set int), (edge_lookup(Heap[r_19_1, edges], j_13_1): Ref) } { (edges_domain(Heap[r_19_1, edges]): Set int), setOfRef[(edge_lookup(Heap[r_19_1, edges], j_13_1): Ref)] } { (edges_domain(Heap[r_19_1, edges]): Set int)[j_13_1] } { setOfRef[(edge_lookup(Heap[r_19_1, edges], j_13_1): Ref)] }
              setOfRef[r_19_1] && (edges_domain(Heap[r_19_1, edges]): Set int)[j_13_1] ==> setOfRef[(edge_lookup(Heap[r_19_1, edges], j_13_1): Ref)]
            );
            assert {:msg "  Loop invariant (node_map_image subset res_copy_nodes) might not be preserved. Assertion (node_map_image subset res_copy_nodes) might not hold. (graph-copy.vpr@151.32--151.53) [543]"}
              Set#Subset(node_map_image, res_copy_nodes);
            assert {:msg "  Loop invariant |(setOfRef intersection res_copy_nodes)| == 0 might not be preserved. Assertion |(setOfRef intersection res_copy_nodes)| == 0 might not hold. (graph-copy.vpr@152.17--152.60) [544]"}
              Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
            if (*) {
              if (Seq#Contains((map_domain(res_node_map): Seq Ref), r_20)) {
                assert {:msg "  Loop invariant (forall r: Ref :: { (r in map_domain(res_node_map)) } { (lookup(res_node_map, r) in res_copy_nodes) } (r in map_domain(res_node_map)) ==> (lookup(res_node_map, r) in res_copy_nodes)) might not be preserved. Assertion (lookup(res_node_map, r) in res_copy_nodes) might not hold. (graph-copy.vpr@153.17--153.108) [545]"}
                  res_copy_nodes[(lookup(res_node_map, r_20): Ref)];
              }
              assume false;
            }
            assume (forall r_21_1: Ref ::
              { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), r_21_1) } { Seq#Contains((map_domain(res_node_map): Seq Ref), r_21_1) } { res_copy_nodes[(lookup(res_node_map, r_21_1): Ref)] }
              Seq#Contains((map_domain(res_node_map): Seq Ref), r_21_1) ==> res_copy_nodes[(lookup(res_node_map, r_21_1): Ref)]
            );
            havoc QPMask;
            
            // -- check that the permission amount is positive
              
            
            // -- check if receiver r is injective
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.val, write)) might not be preserved. Quantified resource r.val might not be injective. (graph-copy.vpr@154.17--154.68) [546]"}
                (forall r_22: Ref, r_22_1: Ref ::
                { neverTriggered35(r_22), neverTriggered35(r_22_1) }
                (((r_22 != r_22_1 && res_copy_nodes[r_22]) && res_copy_nodes[r_22_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_22 != r_22_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.val, write)) might not be preserved. There might be insufficient permission to access r.val (graph-copy.vpr@154.17--154.68) [547]"}
                (forall r_22: Ref ::
                { Heap[r_22, val] } { QPMask[r_22, val] } { res_copy_nodes[r_22] }
                res_copy_nodes[r_22] ==> Mask[r_22, val] >= FullPerm
              );
            
            // -- assumptions for inverse of receiver r
              assume (forall r_22: Ref ::
                { Heap[r_22, val] } { QPMask[r_22, val] } { res_copy_nodes[r_22] }
                res_copy_nodes[r_22] && NoPerm < FullPerm ==> qpRange35(r_22) && invRecv35(r_22) == r_22
              );
              assume (forall o_3: Ref ::
                { invRecv35(o_3) }
                res_copy_nodes[invRecv35(o_3)] && (NoPerm < FullPerm && qpRange35(o_3)) ==> invRecv35(o_3) == o_3
              );
            
            // -- assume permission updates for field val
              assume (forall o_3: Ref ::
                { QPMask[o_3, val] }
                (res_copy_nodes[invRecv35(o_3)] && (NoPerm < FullPerm && qpRange35(o_3)) ==> invRecv35(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!(res_copy_nodes[invRecv35(o_3)] && (NoPerm < FullPerm && qpRange35(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            havoc QPMask;
            
            // -- check that the permission amount is positive
              
            
            // -- check if receiver r is injective
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.edges, write)) might not be preserved. Quantified resource r.edges might not be injective. (graph-copy.vpr@155.17--155.70) [548]"}
                (forall r_23: Ref, r_23_1: Ref ::
                { neverTriggered36(r_23), neverTriggered36(r_23_1) }
                (((r_23 != r_23_1 && res_copy_nodes[r_23]) && res_copy_nodes[r_23_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_23 != r_23_1
              );
            
            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall r: Ref :: { (r in res_copy_nodes) } (r in res_copy_nodes) ==> acc(r.edges, write)) might not be preserved. There might be insufficient permission to access r.edges (graph-copy.vpr@155.17--155.70) [549]"}
                (forall r_23: Ref ::
                { Heap[r_23, edges] } { QPMask[r_23, edges] } { res_copy_nodes[r_23] }
                res_copy_nodes[r_23] ==> Mask[r_23, edges] >= FullPerm
              );
            
            // -- assumptions for inverse of receiver r
              assume (forall r_23: Ref ::
                { Heap[r_23, edges] } { QPMask[r_23, edges] } { res_copy_nodes[r_23] }
                res_copy_nodes[r_23] && NoPerm < FullPerm ==> qpRange36(r_23) && invRecv36(r_23) == r_23
              );
              assume (forall o_3: Ref ::
                { invRecv36(o_3) }
                res_copy_nodes[invRecv36(o_3)] && (NoPerm < FullPerm && qpRange36(o_3)) ==> invRecv36(o_3) == o_3
              );
            
            // -- assume permission updates for field edges
              assume (forall o_3: Ref ::
                { QPMask[o_3, edges] }
                (res_copy_nodes[invRecv36(o_3)] && (NoPerm < FullPerm && qpRange36(o_3)) ==> invRecv36(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - FullPerm) && (!(res_copy_nodes[invRecv36(o_3)] && (NoPerm < FullPerm && qpRange36(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
              );
            
            // -- assume permission updates for independent locations
              assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
                { QPMask[o_3, f_5] }
                f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
              );
            Mask := QPMask;
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
            // Terminate execution
            assume false;
          }
        
        // -- Inhale loop invariant after loop, and assume guard
          assume !(Set#Card(S) > 0);
          assume state(Heap, Mask);
          assume res_copy_nodes[nodeCopy];
          assume setOfRef[this];
          havoc QPMask;
          assert {:msg "  While statement might fail. Quantified resource x.val might not be injective. (graph-copy.vpr@145.17--145.66) [550]"}
            (forall x_80: Ref, x_80_1: Ref ::
            
            (((x_80 != x_80_1 && setOfRef[x_80]) && setOfRef[x_80_1]) && NoPerm < rd) && NoPerm < rd ==> x_80 != x_80_1
          );
          
          // -- Define Inverse Function
            assume (forall x_80: Ref ::
              { Heap[x_80, val] } { QPMask[x_80, val] } { setOfRef[x_80] }
              setOfRef[x_80] && NoPerm < rd ==> qpRange37(x_80) && invRecv37(x_80) == x_80
            );
            assume (forall o_3: Ref ::
              { invRecv37(o_3) }
              (setOfRef[invRecv37(o_3)] && NoPerm < rd) && qpRange37(o_3) ==> invRecv37(o_3) == o_3
            );
          // Check that permission expression is non-negative for all fields
          assert {:msg "  While statement might fail. Fraction rd might be negative. (graph-copy.vpr@145.17--145.66) [551]"}
            (forall x_80: Ref ::
            { Heap[x_80, val] } { QPMask[x_80, val] } { setOfRef[x_80] }
            setOfRef[x_80] ==> rd >= NoPerm
          );
          
          // -- Assume set of fields is nonNull
            assume (forall x_80: Ref ::
              { Heap[x_80, val] } { QPMask[x_80, val] } { setOfRef[x_80] }
              setOfRef[x_80] && rd > NoPerm ==> x_80 != null
            );
          
          // -- Define permissions
            assume (forall o_3: Ref ::
              { QPMask[o_3, val] }
              ((setOfRef[invRecv37(o_3)] && NoPerm < rd) && qpRange37(o_3) ==> (NoPerm < rd ==> invRecv37(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + rd) && (!((setOfRef[invRecv37(o_3)] && NoPerm < rd) && qpRange37(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
            );
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
              f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          assume state(Heap, Mask);
          assume (forall x_81: Ref ::
            { setOfRef[x_81] }
            setOfRef[x_81] ==> Heap[x_81, val] == old(Heap)[x_81, val]
          );
          havoc QPMask;
          assert {:msg "  While statement might fail. Quantified resource x.edges might not be injective. (graph-copy.vpr@147.17--147.68) [552]"}
            (forall x_82: Ref, x_82_1: Ref ::
            
            (((x_82 != x_82_1 && setOfRef[x_82]) && setOfRef[x_82_1]) && NoPerm < rd) && NoPerm < rd ==> x_82 != x_82_1
          );
          
          // -- Define Inverse Function
            assume (forall x_82: Ref ::
              { Heap[x_82, edges] } { QPMask[x_82, edges] } { setOfRef[x_82] }
              setOfRef[x_82] && NoPerm < rd ==> qpRange38(x_82) && invRecv38(x_82) == x_82
            );
            assume (forall o_3: Ref ::
              { invRecv38(o_3) }
              (setOfRef[invRecv38(o_3)] && NoPerm < rd) && qpRange38(o_3) ==> invRecv38(o_3) == o_3
            );
          // Check that permission expression is non-negative for all fields
          assert {:msg "  While statement might fail. Fraction rd might be negative. (graph-copy.vpr@147.17--147.68) [553]"}
            (forall x_82: Ref ::
            { Heap[x_82, edges] } { QPMask[x_82, edges] } { setOfRef[x_82] }
            setOfRef[x_82] ==> rd >= NoPerm
          );
          
          // -- Assume set of fields is nonNull
            assume (forall x_82: Ref ::
              { Heap[x_82, edges] } { QPMask[x_82, edges] } { setOfRef[x_82] }
              setOfRef[x_82] && rd > NoPerm ==> x_82 != null
            );
          
          // -- Define permissions
            assume (forall o_3: Ref ::
              { QPMask[o_3, edges] }
              ((setOfRef[invRecv38(o_3)] && NoPerm < rd) && qpRange38(o_3) ==> (NoPerm < rd ==> invRecv38(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + rd) && (!((setOfRef[invRecv38(o_3)] && NoPerm < rd) && qpRange38(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
            );
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
              f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          assume state(Heap, Mask);
          assume (forall x_83: Ref ::
            { setOfRef[x_83] }
            setOfRef[x_83] ==> Heap[x_83, edges] == old(Heap)[x_83, edges]
          );
          assume (forall j_14: int ::
            { S[j_14] } { setOfRef[(edge_lookup(Heap[this, edges], j_14): Ref)] }
            S[j_14] ==> setOfRef[(edge_lookup(Heap[this, edges], j_14): Ref)]
          );
          assume (forall r_24: Ref, j_15: int ::
            { setOfRef[r_24], (edges_domain(Heap[r_24, edges]): Set int)[j_15] } { setOfRef[r_24], (edge_lookup(Heap[r_24, edges], j_15): Ref) } { setOfRef[r_24], setOfRef[(edge_lookup(Heap[r_24, edges], j_15): Ref)] } { (edges_domain(Heap[r_24, edges]): Set int), (edge_lookup(Heap[r_24, edges], j_15): Ref) } { (edges_domain(Heap[r_24, edges]): Set int), setOfRef[(edge_lookup(Heap[r_24, edges], j_15): Ref)] } { (edges_domain(Heap[r_24, edges]): Set int)[j_15] } { setOfRef[(edge_lookup(Heap[r_24, edges], j_15): Ref)] }
            setOfRef[r_24] && (edges_domain(Heap[r_24, edges]): Set int)[j_15] ==> setOfRef[(edge_lookup(Heap[r_24, edges], j_15): Ref)]
          );
          assume Set#Subset(node_map_image, res_copy_nodes);
          assume Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
          assume (forall r_25: Ref ::
            { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), r_25) } { Seq#Contains((map_domain(res_node_map): Seq Ref), r_25) } { res_copy_nodes[(lookup(res_node_map, r_25): Ref)] }
            Seq#Contains((map_domain(res_node_map): Seq Ref), r_25) ==> res_copy_nodes[(lookup(res_node_map, r_25): Ref)]
          );
          havoc QPMask;
          assert {:msg "  While statement might fail. Quantified resource r.val might not be injective. (graph-copy.vpr@154.17--154.68) [554]"}
            (forall r_26: Ref, r_26_1: Ref ::
            
            (((r_26 != r_26_1 && res_copy_nodes[r_26]) && res_copy_nodes[r_26_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_26 != r_26_1
          );
          
          // -- Define Inverse Function
            assume (forall r_26: Ref ::
              { Heap[r_26, val] } { QPMask[r_26, val] } { res_copy_nodes[r_26] }
              res_copy_nodes[r_26] && NoPerm < FullPerm ==> qpRange39(r_26) && invRecv39(r_26) == r_26
            );
            assume (forall o_3: Ref ::
              { invRecv39(o_3) }
              (res_copy_nodes[invRecv39(o_3)] && NoPerm < FullPerm) && qpRange39(o_3) ==> invRecv39(o_3) == o_3
            );
          
          // -- Assume set of fields is nonNull
            assume (forall r_26: Ref ::
              { Heap[r_26, val] } { QPMask[r_26, val] } { res_copy_nodes[r_26] }
              res_copy_nodes[r_26] ==> r_26 != null
            );
          
          // -- Define permissions
            assume (forall o_3: Ref ::
              { QPMask[o_3, val] }
              ((res_copy_nodes[invRecv39(o_3)] && NoPerm < FullPerm) && qpRange39(o_3) ==> (NoPerm < FullPerm ==> invRecv39(o_3) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!((res_copy_nodes[invRecv39(o_3)] && NoPerm < FullPerm) && qpRange39(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
            );
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
              f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          assume state(Heap, Mask);
          havoc QPMask;
          assert {:msg "  While statement might fail. Quantified resource r.edges might not be injective. (graph-copy.vpr@155.17--155.70) [555]"}
            (forall r_27: Ref, r_27_1: Ref ::
            
            (((r_27 != r_27_1 && res_copy_nodes[r_27]) && res_copy_nodes[r_27_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> r_27 != r_27_1
          );
          
          // -- Define Inverse Function
            assume (forall r_27: Ref ::
              { Heap[r_27, edges] } { QPMask[r_27, edges] } { res_copy_nodes[r_27] }
              res_copy_nodes[r_27] && NoPerm < FullPerm ==> qpRange40(r_27) && invRecv40(r_27) == r_27
            );
            assume (forall o_3: Ref ::
              { invRecv40(o_3) }
              (res_copy_nodes[invRecv40(o_3)] && NoPerm < FullPerm) && qpRange40(o_3) ==> invRecv40(o_3) == o_3
            );
          
          // -- Assume set of fields is nonNull
            assume (forall r_27: Ref ::
              { Heap[r_27, edges] } { QPMask[r_27, edges] } { res_copy_nodes[r_27] }
              res_copy_nodes[r_27] ==> r_27 != null
            );
          
          // -- Define permissions
            assume (forall o_3: Ref ::
              { QPMask[o_3, edges] }
              ((res_copy_nodes[invRecv40(o_3)] && NoPerm < FullPerm) && qpRange40(o_3) ==> (NoPerm < FullPerm ==> invRecv40(o_3) == o_3) && QPMask[o_3, edges] == Mask[o_3, edges] + FullPerm) && (!((res_copy_nodes[invRecv40(o_3)] && NoPerm < FullPerm) && qpRange40(o_3)) ==> QPMask[o_3, edges] == Mask[o_3, edges])
            );
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
              f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          assume state(Heap, Mask);
          assume state(Heap, Mask);
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion nodeCopy != null might not hold. (graph-copy.vpr@104.11--104.57) [556]"}
      nodeCopy != null;
    assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion (nodeCopy in res_copy_nodes) might not hold. (graph-copy.vpr@104.11--104.57) [557]"}
      res_copy_nodes[nodeCopy];
    assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion |(setOfRef intersection res_copy_nodes)| == 0 might not hold. (graph-copy.vpr@105.11--105.54) [558]"}
      Set#Card(Set#Intersection(setOfRef, res_copy_nodes)) == 0;
    havoc QPMask;
    
    // -- check that the permission amount is positive
      assert {:msg "  Postcondition of graph_copy_rec might not hold. Fraction rd might be negative. (graph-copy.vpr@106.11--106.60) [559]"}
        (forall x_28: Ref ::
        { Heap[x_28, val] } { QPMask[x_28, val] } { setOfRef[x_28] }
        setOfRef[x_28] && dummyFunction(Heap[x_28, val]) ==> rd >= NoPerm
      );
    
    // -- check if receiver x is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@106.11--106.60) [560]"}
        (forall x_28: Ref, x_28_1: Ref ::
        { neverTriggered9(x_28), neverTriggered9(x_28_1) }
        (((x_28 != x_28_1 && setOfRef[x_28]) && setOfRef[x_28_1]) && NoPerm < rd) && NoPerm < rd ==> x_28 != x_28_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of graph_copy_rec might not hold. There might be insufficient permission to access x.val (graph-copy.vpr@106.11--106.60) [561]"}
        (forall x_28: Ref ::
        { Heap[x_28, val] } { QPMask[x_28, val] } { setOfRef[x_28] }
        setOfRef[x_28] ==> Mask[x_28, val] >= rd
      );
    
    // -- assumptions for inverse of receiver x
      assume (forall x_28: Ref ::
        { Heap[x_28, val] } { QPMask[x_28, val] } { setOfRef[x_28] }
        setOfRef[x_28] && NoPerm < rd ==> qpRange9(x_28) && invRecv9(x_28) == x_28
      );
      assume (forall o_3: Ref ::
        { invRecv9(o_3) }
        setOfRef[invRecv9(o_3)] && (NoPerm < rd && qpRange9(o_3)) ==> invRecv9(o_3) == o_3
      );
    
    // -- assume permission updates for field val
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        (setOfRef[invRecv9(o_3)] && (NoPerm < rd && qpRange9(o_3)) ==> invRecv9(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - rd) && (!(setOfRef[invRecv9(o_3)] && (NoPerm < rd && qpRange9(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    if (*) {
      if (setOfRef[x_29]) {
        assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion x.val == old(x.val) might not hold. (graph-copy.vpr@107.11--107.65) [562]"}
          Heap[x_29, val] == old(Heap)[x_29, val];
      }
      assume false;
    }
    assume (forall x_30_1: Ref ::
      { setOfRef[x_30_1] }
      setOfRef[x_30_1] ==> Heap[x_30_1, val] == old(Heap)[x_30_1, val]
    );
    havoc QPMask;
    
    // -- check that the permission amount is positive
      assert {:msg "  Postcondition of graph_copy_rec might not hold. Fraction rd might be negative. (graph-copy.vpr@108.11--108.62) [563]"}
        (forall x_31: Ref ::
        { Heap[x_31, edges] } { QPMask[x_31, edges] } { setOfRef[x_31] }
        setOfRef[x_31] && dummyFunction(Heap[x_31, edges]) ==> rd >= NoPerm
      );
    
    // -- check if receiver x is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@108.11--108.62) [564]"}
        (forall x_31: Ref, x_31_1: Ref ::
        { neverTriggered10(x_31), neverTriggered10(x_31_1) }
        (((x_31 != x_31_1 && setOfRef[x_31]) && setOfRef[x_31_1]) && NoPerm < rd) && NoPerm < rd ==> x_31 != x_31_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of graph_copy_rec might not hold. There might be insufficient permission to access x.edges (graph-copy.vpr@108.11--108.62) [565]"}
        (forall x_31: Ref ::
        { Heap[x_31, edges] } { QPMask[x_31, edges] } { setOfRef[x_31] }
        setOfRef[x_31] ==> Mask[x_31, edges] >= rd
      );
    
    // -- assumptions for inverse of receiver x
      assume (forall x_31: Ref ::
        { Heap[x_31, edges] } { QPMask[x_31, edges] } { setOfRef[x_31] }
        setOfRef[x_31] && NoPerm < rd ==> qpRange10(x_31) && invRecv10(x_31) == x_31
      );
      assume (forall o_3: Ref ::
        { invRecv10(o_3) }
        setOfRef[invRecv10(o_3)] && (NoPerm < rd && qpRange10(o_3)) ==> invRecv10(o_3) == o_3
      );
    
    // -- assume permission updates for field edges
      assume (forall o_3: Ref ::
        { QPMask[o_3, edges] }
        (setOfRef[invRecv10(o_3)] && (NoPerm < rd && qpRange10(o_3)) ==> invRecv10(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - rd) && (!(setOfRef[invRecv10(o_3)] && (NoPerm < rd && qpRange10(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    if (*) {
      if (setOfRef[x_32]) {
        assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion x.edges == old(x.edges) might not hold. (graph-copy.vpr@109.11--109.69) [566]"}
          Heap[x_32, edges] == old(Heap)[x_32, edges];
      }
      assume false;
    }
    assume (forall x_33_1: Ref ::
      { setOfRef[x_33_1] }
      setOfRef[x_33_1] ==> Heap[x_33_1, edges] == old(Heap)[x_33_1, edges]
    );
    if (*) {
      if (setOfRef[x_34] && (edges_domain(Heap[x_34, edges]): Set int)[i_4]) {
        assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion (edge_lookup(x.edges, i) in setOfRef) might not hold. (graph-copy.vpr@110.11--110.119) [567]"}
          setOfRef[(edge_lookup(Heap[x_34, edges], i_4): Ref)];
      }
      assume false;
    }
    assume (forall x_35_1: Ref, i_5_1: int ::
      { setOfRef[x_35_1], (edges_domain(Heap[x_35_1, edges]): Set int)[i_5_1] } { setOfRef[x_35_1], (edge_lookup(Heap[x_35_1, edges], i_5_1): Ref) } { setOfRef[x_35_1], setOfRef[(edge_lookup(Heap[x_35_1, edges], i_5_1): Ref)] } { (edges_domain(Heap[x_35_1, edges]): Set int), (edge_lookup(Heap[x_35_1, edges], i_5_1): Ref) } { (edges_domain(Heap[x_35_1, edges]): Set int), setOfRef[(edge_lookup(Heap[x_35_1, edges], i_5_1): Ref)] } { (edges_domain(Heap[x_35_1, edges]): Set int)[i_5_1] } { setOfRef[(edge_lookup(Heap[x_35_1, edges], i_5_1): Ref)] }
      setOfRef[x_35_1] && (edges_domain(Heap[x_35_1, edges]): Set int)[i_5_1] ==> setOfRef[(edge_lookup(Heap[x_35_1, edges], i_5_1): Ref)]
    );
    assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion res_copy_nodes == (res_copy_nodes union old(node_map_image)) might not hold. (graph-copy.vpr@111.11--111.69) [568]"}
      Set#Equal(res_copy_nodes, Set#Union(res_copy_nodes, node_map_image));
    if (*) {
      if (Seq#Contains((map_domain(res_node_map): Seq Ref), x_36)) {
        assert {:msg "  Postcondition of graph_copy_rec might not hold. Assertion (lookup(res_node_map, x) in res_copy_nodes) might not hold. (graph-copy.vpr@112.11--112.102) [569]"}
          res_copy_nodes[(lookup(res_node_map, x_36): Ref)];
      }
      assume false;
    }
    assume (forall x_37_1: Ref ::
      { Seq#ContainsTrigger((map_domain(res_node_map): Seq Ref), x_37_1) } { Seq#Contains((map_domain(res_node_map): Seq Ref), x_37_1) } { res_copy_nodes[(lookup(res_node_map, x_37_1): Ref)] }
      Seq#Contains((map_domain(res_node_map): Seq Ref), x_37_1) ==> res_copy_nodes[(lookup(res_node_map, x_37_1): Ref)]
    );
    havoc QPMask;
    
    // -- check that the permission amount is positive
      
    
    // -- check if receiver x is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource x.val might not be injective. (graph-copy.vpr@113.11--113.62) [570]"}
        (forall x_38: Ref, x_38_1: Ref ::
        { neverTriggered11(x_38), neverTriggered11(x_38_1) }
        (((x_38 != x_38_1 && res_copy_nodes[x_38]) && res_copy_nodes[x_38_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_38 != x_38_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of graph_copy_rec might not hold. There might be insufficient permission to access x.val (graph-copy.vpr@113.11--113.62) [571]"}
        (forall x_38: Ref ::
        { Heap[x_38, val] } { QPMask[x_38, val] } { res_copy_nodes[x_38] }
        res_copy_nodes[x_38] ==> Mask[x_38, val] >= FullPerm
      );
    
    // -- assumptions for inverse of receiver x
      assume (forall x_38: Ref ::
        { Heap[x_38, val] } { QPMask[x_38, val] } { res_copy_nodes[x_38] }
        res_copy_nodes[x_38] && NoPerm < FullPerm ==> qpRange11(x_38) && invRecv11(x_38) == x_38
      );
      assume (forall o_3: Ref ::
        { invRecv11(o_3) }
        res_copy_nodes[invRecv11(o_3)] && (NoPerm < FullPerm && qpRange11(o_3)) ==> invRecv11(o_3) == o_3
      );
    
    // -- assume permission updates for field val
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        (res_copy_nodes[invRecv11(o_3)] && (NoPerm < FullPerm && qpRange11(o_3)) ==> invRecv11(o_3) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!(res_copy_nodes[invRecv11(o_3)] && (NoPerm < FullPerm && qpRange11(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    havoc QPMask;
    
    // -- check that the permission amount is positive
      
    
    // -- check if receiver x is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource x.edges might not be injective. (graph-copy.vpr@114.11--114.64) [572]"}
        (forall x_39: Ref, x_39_1: Ref ::
        { neverTriggered12(x_39), neverTriggered12(x_39_1) }
        (((x_39 != x_39_1 && res_copy_nodes[x_39]) && res_copy_nodes[x_39_1]) && NoPerm < FullPerm) && NoPerm < FullPerm ==> x_39 != x_39_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of graph_copy_rec might not hold. There might be insufficient permission to access x.edges (graph-copy.vpr@114.11--114.64) [573]"}
        (forall x_39: Ref ::
        { Heap[x_39, edges] } { QPMask[x_39, edges] } { res_copy_nodes[x_39] }
        res_copy_nodes[x_39] ==> Mask[x_39, edges] >= FullPerm
      );
    
    // -- assumptions for inverse of receiver x
      assume (forall x_39: Ref ::
        { Heap[x_39, edges] } { QPMask[x_39, edges] } { res_copy_nodes[x_39] }
        res_copy_nodes[x_39] && NoPerm < FullPerm ==> qpRange12(x_39) && invRecv12(x_39) == x_39
      );
      assume (forall o_3: Ref ::
        { invRecv12(o_3) }
        res_copy_nodes[invRecv12(o_3)] && (NoPerm < FullPerm && qpRange12(o_3)) ==> invRecv12(o_3) == o_3
      );
    
    // -- assume permission updates for field edges
      assume (forall o_3: Ref ::
        { QPMask[o_3, edges] }
        (res_copy_nodes[invRecv12(o_3)] && (NoPerm < FullPerm && qpRange12(o_3)) ==> invRecv12(o_3) == o_3 && QPMask[o_3, edges] == Mask[o_3, edges] - FullPerm) && (!(res_copy_nodes[invRecv12(o_3)] && (NoPerm < FullPerm && qpRange12(o_3))) ==> QPMask[o_3, edges] == Mask[o_3, edges])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != edges ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method pop
// ==================================================

procedure vpop(s1: (Set int)) returns (s2: (Set int), i_1: int)
  modifies Heap, Mask;
{
  var PostHeap: HeapType;
  var PostMask: MaskType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Checked inhaling of precondition
    assume 0 < Set#Card(s1);
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
    assume s1[i_1];
    assume state(PostHeap, PostMask);
    assume Set#Equal(s2, Set#Difference(s1, Set#Singleton(i_1)));
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale false -- graph-copy.vpr@177.10--177.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of pop might not hold. Assertion (i in s1) might not hold. (graph-copy.vpr@175.11--175.18) [574]"}
      s1[i_1];
    assert {:msg "  Postcondition of pop might not hold. Assertion s2 == (s1 setminus Set(i)) might not hold. (graph-copy.vpr@176.12--176.36) [575]"}
      Set#Equal(s2, Set#Difference(s1, Set#Singleton(i_1)));
}