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

function  neverTriggered1(k_8: int): bool;
function  neverTriggered2(k_11: int): bool;
function  neverTriggered3(k_8: int): bool;
function  neverTriggered4(k_11: int): bool;
function  neverTriggered5(k_8: int): bool;
function  neverTriggered6(k_11: int): bool;
function  neverTriggered7(k_8: int): bool;
function  neverTriggered8(k_11: int): bool;
function  neverTriggered9(i_1: int): bool;
function  neverTriggered10(i_3: int): bool;
function  neverTriggered11(i_6: int): bool;
function  neverTriggered12(i_1: int): bool;
function  neverTriggered13(i_3: int): bool;
function  neverTriggered14(i_4: int): bool;
function  neverTriggered15(i_5: int): bool;
function  neverTriggered16(i_6: int): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function  invRecv1(recv: Ref): int;
function  invRecv2(recv: Ref): int;
function  invRecv3(recv: Ref): int;
function  invRecv4(recv: Ref): int;
function  invRecv5(recv: Ref): int;
function  invRecv6(recv: Ref): int;
function  invRecv7(recv: Ref): int;
function  invRecv8(recv: Ref): int;
function  invRecv9(recv: Ref): int;
function  invRecv10(recv: Ref): int;
function  invRecv11(recv: Ref): int;
function  invRecv12(recv: Ref): int;
function  invRecv13(recv: Ref): int;
function  invRecv14(recv: Ref): int;
function  invRecv15(recv: Ref): int;
function  invRecv16(recv: Ref): int;
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

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 5: count_list
// - height 4: sum_square
// - height 3: sum_list
// - height 2: sum_array
// - height 1: count_square
// - height 0: count_array
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
// Translation of all fields
// ==================================================

const unique Ref__Integer_value: Field NormalField int;
axiom !IsPredicateField(Ref__Integer_value);
axiom !IsWandField(Ref__Integer_value);

// ==================================================
// Translation of function sum_list
// ==================================================

// Uninterpreted function definitions
function  sum_list(Heap: HeapType, i: int, hi: int, ar: (Seq int)): int;
function  sum_list'(Heap: HeapType, i: int, hi: int, ar: (Seq int)): int;
axiom (forall Heap: HeapType, i: int, hi: int, ar: (Seq int) ::
  { sum_list(Heap, i, hi, ar) }
  sum_list(Heap, i, hi, ar) == sum_list'(Heap, i, hi, ar) && dummyFunction(sum_list#triggerStateless(i, hi, ar))
);
axiom (forall Heap: HeapType, i: int, hi: int, ar: (Seq int) ::
  { sum_list'(Heap, i, hi, ar) }
  dummyFunction(sum_list#triggerStateless(i, hi, ar))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int, hi: int, ar: (Seq int) ::
  { state(Heap, Mask), sum_list(Heap, i, hi, ar) }
  state(Heap, Mask) && AssumeFunctionsAbove < 3 ==> (0 <= i && i <= hi) && hi <= Seq#Length(ar) ==> sum_list(Heap, i, hi, ar) == (if i < hi then Seq#Index(ar, i) + sum_list'(Heap, i + 1, hi, ar) else 0)
);

// Framing axioms
function  sum_list#frame(frame: FrameType, i: int, hi: int, ar: (Seq int)): int;
axiom (forall Heap: HeapType, Mask: MaskType, i: int, hi: int, ar: (Seq int) ::
  { state(Heap, Mask), sum_list'(Heap, i, hi, ar) }
  state(Heap, Mask) ==> sum_list'(Heap, i, hi, ar) == sum_list#frame(EmptyFrame, i, hi, ar)
);

// Trigger function (controlling recursive postconditions)
function  sum_list#trigger(frame: FrameType, i: int, hi: int, ar: (Seq int)): bool;

// State-independent trigger function
function  sum_list#triggerStateless(i: int, hi: int, ar: (Seq int)): int;

// Check contract well-formedness and postcondition
procedure sum_list#definedness(i: int, hi: int, ar: (Seq int)) returns (Result: int)
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 3;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume 0 <= i;
    assume i <= hi;
    assume state(Heap, Mask);
    assume hi <= Seq#Length(ar);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (i < hi ? ar[i] + sum_list(i + 1, hi, ar) : 0)
      if (i < hi) {
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@6.1--11.2) [569]"}
          i >= 0;
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@6.1--11.2) [570]"}
          i < Seq#Length(ar);
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function sum_list might not hold. Assertion 0 <= i + 1 might not hold. (testZeroArray.vpr@10.21--10.44) [571]"}
            0 <= i + 1;
          assert {:msg "  Precondition of function sum_list might not hold. Assertion i + 1 <= hi might not hold. (testZeroArray.vpr@10.21--10.44) [572]"}
            i + 1 <= hi;
          assert {:msg "  Precondition of function sum_list might not hold. Assertion hi <= |ar| might not hold. (testZeroArray.vpr@10.21--10.44) [573]"}
            hi <= Seq#Length(ar);
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume sum_list#trigger(EmptyFrame, i + 1, hi, ar);
        }
      }

  // -- Translate function body
    Result := (if i < hi then Seq#Index(ar, i) + sum_list(Heap, i + 1, hi, ar) else 0);
}

// ==================================================
// Translation of function sum_array
// ==================================================

// Uninterpreted function definitions
function  sum_array(Heap: HeapType, i: int, lo: int, hi: int, ar: (Seq Ref)): int;
function  sum_array'(Heap: HeapType, i: int, lo: int, hi: int, ar: (Seq Ref)): int;
axiom (forall Heap: HeapType, i: int, lo: int, hi: int, ar: (Seq Ref) ::
  { sum_array(Heap, i, lo, hi, ar) }
  sum_array(Heap, i, lo, hi, ar) == sum_array'(Heap, i, lo, hi, ar) && dummyFunction(sum_array#triggerStateless(i, lo, hi, ar))
);
axiom (forall Heap: HeapType, i: int, lo: int, hi: int, ar: (Seq Ref) ::
  { sum_array'(Heap, i, lo, hi, ar) }
  dummyFunction(sum_array#triggerStateless(i, lo, hi, ar))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int, lo: int, hi: int, ar: (Seq Ref) ::
  { state(Heap, Mask), sum_array(Heap, i, lo, hi, ar) }
  state(Heap, Mask) && AssumeFunctionsAbove < 2 ==> ((0 <= lo && (lo <= i && i <= hi)) && hi <= Seq#Length(ar)) && (forall j: int, k: int ::
    { Seq#Index(ar, j), Seq#Index(ar, k) }
    0 <= j && (j < hi && (0 <= k && (k < hi && j != k))) ==> Seq#Index(ar, j) != Seq#Index(ar, k)
  ) ==> sum_array(Heap, i, lo, hi, ar) == (if i < hi then Heap[Seq#Index(ar, i), Ref__Integer_value] + sum_array'(Heap, i + 1, lo, hi, ar) else 0)
);

// Framing axioms
function  sum_array#frame(frame: FrameType, i: int, lo: int, hi: int, ar: (Seq Ref)): int;
axiom (forall Heap: HeapType, Mask: MaskType, i: int, lo: int, hi: int, ar: (Seq Ref) ::
  { state(Heap, Mask), sum_array'(Heap, i, lo, hi, ar) }
  state(Heap, Mask) ==> sum_array'(Heap, i, lo, hi, ar) == sum_array#frame(FrameFragment(sum_array#condqp1(Heap, i, lo, hi, ar)), i, lo, hi, ar)
);
// ==================================================
// Function used for framing of quantified permission (forall k: Int :: { ar[k] } lo <= k && k < hi ==> acc(ar[k].Ref__Integer_value, wildcard)) in function sum_array
// ==================================================

function  sum_array#condqp1(Heap: HeapType, i_1_1: int, lo_1_1: int, hi_1_1: int, ar_1_1: (Seq Ref)): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, i: int, lo: int, hi: int, ar: (Seq Ref) ::
  { sum_array#condqp1(Heap2Heap, i, lo, hi, ar), sum_array#condqp1(Heap1Heap, i, lo, hi, ar), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall k_2: int ::

    (lo <= k_2 && k_2 < hi <==> lo <= k_2 && k_2 < hi) && (lo <= k_2 && k_2 < hi ==> Heap2Heap[Seq#Index(ar, k_2), Ref__Integer_value] == Heap1Heap[Seq#Index(ar, k_2), Ref__Integer_value])
  ) ==> sum_array#condqp1(Heap2Heap, i, lo, hi, ar) == sum_array#condqp1(Heap1Heap, i, lo, hi, ar)
);

// Trigger function (controlling recursive postconditions)
function  sum_array#trigger(frame: FrameType, i: int, lo: int, hi: int, ar: (Seq Ref)): bool;

// State-independent trigger function
function  sum_array#triggerStateless(i: int, lo: int, hi: int, ar: (Seq Ref)): int;

// Check contract well-formedness and postcondition
procedure sum_array#definedness(i: int, lo: int, hi: int, ar: (Seq Ref)) returns (Result: int)
  modifies Heap, Mask;
{
  var j_1: int;
  var k_1: int;
  var k_3: int;
  var QPMask: MaskType;
  var wildcard: real where wildcard > 0.000000000;
  var j_4: int;
  var k_9: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 2;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume 0 <= lo;
    assume lo <= i;
    assume i <= hi;
    assume state(Heap, Mask);
    assume hi <= Seq#Length(ar);
    assume state(Heap, Mask);

    // -- Check definedness of (forall j: Int, k: Int :: { ar[j], ar[k] } 0 <= j && (j < hi && (0 <= k && (k < hi && j != k))) ==> ar[j] != ar[k])
      if (*) {
        if (0 <= j_1 && (j_1 < hi && (0 <= k_1 && (k_1 < hi && j_1 != k_1)))) {
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might be negative. (testZeroArray.vpr@16.12--16.102) [574]"}
            j_1 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might exceed sequence length. (testZeroArray.vpr@16.12--16.102) [575]"}
            j_1 < Seq#Length(ar);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@16.12--16.102) [576]"}
            k_1 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@16.12--16.102) [577]"}
            k_1 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall j_3: int, k_6: int ::
      { Seq#Index(ar, j_3), Seq#Index(ar, k_6) }
      0 <= j_3 && (j_3 < hi && (0 <= k_6 && (k_6 < hi && j_3 != k_6))) ==> Seq#Index(ar, j_3) != Seq#Index(ar, k_6)
    );
    assume state(Heap, Mask);

    // -- Check definedness of (forall k: Int :: { ar[k] } lo <= k && k < hi ==> acc(ar[k].Ref__Integer_value, wildcard))
      if (*) {
        if (lo <= k_3 && k_3 < hi) {
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@17.13--17.95) [578]"}
            k_3 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@17.13--17.95) [579]"}
            k_3 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@17.13--17.95) [580]"}
      (forall k_8: int, k_8_1: int ::

      (((k_8 != k_8_1 && (lo <= k_8 && k_8 < hi)) && (lo <= k_8_1 && k_8_1 < hi)) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_8) != Seq#Index(ar, k_8_1)
    );

    // -- Define Inverse Function
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        lo <= k_8 && k_8 < hi ==> qpRange1(Seq#Index(ar, k_8)) && invRecv1(Seq#Index(ar, k_8)) == k_8
      );
      assume (forall o_3: Ref ::
        { invRecv1(o_3) }
        (lo <= invRecv1(o_3) && invRecv1(o_3) < hi) && qpRange1(o_3) ==> Seq#Index(ar, invRecv1(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        lo <= k_8 && k_8 < hi ==> Seq#Index(ar, k_8) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        ((lo <= invRecv1(o_3) && invRecv1(o_3) < hi) && qpRange1(o_3) ==> Seq#Index(ar, invRecv1(o_3)) == o_3 && Mask[o_3, Ref__Integer_value] < QPMask[o_3, Ref__Integer_value]) && (!((lo <= invRecv1(o_3) && invRecv1(o_3) < hi) && qpRange1(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (i < hi ? ar[i].Ref__Integer_value + sum_array(i + 1, lo, hi, ar) : 0)
      if (i < hi) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@13.1--20.2) [581]"}
          HasDirectPerm(Mask, Seq#Index(ar, i), Ref__Integer_value);
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@13.1--20.2) [582]"}
          i >= 0;
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@13.1--20.2) [583]"}
          i < Seq#Length(ar);
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function sum_array might not hold. Assertion 0 <= lo might not hold. (testZeroArray.vpr@19.40--19.68) [584]"}
            0 <= lo;
          assert {:msg "  Precondition of function sum_array might not hold. Assertion lo <= i + 1 might not hold. (testZeroArray.vpr@19.40--19.68) [585]"}
            lo <= i + 1;
          assert {:msg "  Precondition of function sum_array might not hold. Assertion i + 1 <= hi might not hold. (testZeroArray.vpr@19.40--19.68) [586]"}
            i + 1 <= hi;
          assert {:msg "  Precondition of function sum_array might not hold. Assertion hi <= |ar| might not hold. (testZeroArray.vpr@19.40--19.68) [587]"}
            hi <= Seq#Length(ar);
          if (*) {
            if (0 <= j_4 && (j_4 < hi && (0 <= k_9 && (k_9 < hi && j_4 != k_9)))) {
              assert {:msg "  Precondition of function sum_array might not hold. Assertion ar[j] != ar[k] might not hold. (testZeroArray.vpr@19.40--19.68) [588]"}
                Seq#Index(ar, j_4) != Seq#Index(ar, k_9);
            }
            assume false;
          }
          assume (forall j_5_1: int, k_10_1: int ::
            { Seq#Index(ar, j_5_1), Seq#Index(ar, k_10_1) }
            0 <= j_5_1 && (j_5_1 < hi && (0 <= k_10_1 && (k_10_1 < hi && j_5_1 != k_10_1))) ==> Seq#Index(ar, j_5_1) != Seq#Index(ar, k_10_1)
          );
          havoc QPMask;
          // wild card assumptions
          havoc wildcard;
          assert {:msg "  Precondition of function sum_array might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@19.40--19.68) [589]"}
            (forall k_11: int ::

            lo <= k_11 && k_11 < hi ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
          );
          assume (forall k_11: int ::

            lo <= k_11 && k_11 < hi ==> wildcard < Mask[Seq#Index(ar, k_11), Ref__Integer_value]
          );

          // -- check that the permission amount is positive
            assert {:msg "  Precondition of function sum_array might not hold. Fraction wildcard might be negative. (testZeroArray.vpr@19.40--19.68) [590]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (lo <= k_11 && k_11 < hi) && dummyFunction(Heap[Seq#Index(ar, k_11), Ref__Integer_value]) ==> wildcard >= NoPerm
            );

          // -- check if receiver ar[k] is injective
            assert {:msg "  Precondition of function sum_array might not hold. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@19.40--19.68) [591]"}
              (forall k_11: int, k_11_1: int ::
              { neverTriggered2(k_11), neverTriggered2(k_11_1) }
              (((k_11 != k_11_1 && (lo <= k_11 && k_11 < hi)) && (lo <= k_11_1 && k_11_1 < hi)) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_11) != Seq#Index(ar, k_11_1)
            );

          // -- check if sufficient permission is held
            assert {:msg "  Precondition of function sum_array might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@19.40--19.68) [592]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              lo <= k_11 && k_11 < hi ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
            );

          // -- assumptions for inverse of receiver ar[k]
            assume (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (lo <= k_11 && k_11 < hi) && NoPerm < wildcard ==> qpRange2(Seq#Index(ar, k_11)) && invRecv2(Seq#Index(ar, k_11)) == k_11
            );
            assume (forall o_3: Ref ::
              { invRecv2(o_3) }
              (lo <= invRecv2(o_3) && invRecv2(o_3) < hi) && (NoPerm < wildcard && qpRange2(o_3)) ==> Seq#Index(ar, invRecv2(o_3)) == o_3
            );

          // -- assume permission updates for field Ref__Integer_value
            assume (forall o_3: Ref ::
              { QPMask[o_3, Ref__Integer_value] }
              ((lo <= invRecv2(o_3) && invRecv2(o_3) < hi) && (NoPerm < wildcard && qpRange2(o_3)) ==> Seq#Index(ar, invRecv2(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - wildcard) && (!((lo <= invRecv2(o_3) && invRecv2(o_3) < hi) && (NoPerm < wildcard && qpRange2(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
            );

          // -- assume permission updates for independent locations
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { QPMask[o_3, f_5] }
              f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume sum_array#trigger(FrameFragment(sum_array#condqp1(Heap, i + 1, lo, hi, ar)), i + 1, lo, hi, ar);
        }
      }

  // -- Translate function body
    Result := (if i < hi then Heap[Seq#Index(ar, i), Ref__Integer_value] + sum_array(Heap, i + 1, lo, hi, ar) else 0);
}

// ==================================================
// Translation of function sum_square
// ==================================================

// Uninterpreted function definitions
function  sum_square(Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref)): int;
function  sum_square'(Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref)): int;
axiom (forall Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref) ::
  { sum_square(Heap, i, lo, hi, step, vmin, vmax, ar) }
  sum_square(Heap, i, lo, hi, step, vmin, vmax, ar) == sum_square'(Heap, i, lo, hi, step, vmin, vmax, ar) && dummyFunction(sum_square#triggerStateless(i, lo, hi, step, vmin, vmax, ar))
);
axiom (forall Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref) ::
  { sum_square'(Heap, i, lo, hi, step, vmin, vmax, ar) }
  dummyFunction(sum_square#triggerStateless(i, lo, hi, step, vmin, vmax, ar))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref) ::
  { state(Heap, Mask), sum_square(Heap, i, lo, hi, step, vmin, vmax, ar) }
  state(Heap, Mask) && AssumeFunctionsAbove < 4 ==> (((0 <= lo && (lo <= hi && (hi <= step && step > 0))) && (0 <= vmin && (vmin <= i && i <= vmax))) && vmax <= Seq#Length(ar)) && (forall j: int, k: int ::
    { Seq#Index(ar, j), Seq#Index(ar, k) }
    0 <= j && (j < vmax && (0 <= k && (k < vmax && j != k))) ==> Seq#Index(ar, j) != Seq#Index(ar, k)
  ) ==> sum_square(Heap, i, lo, hi, step, vmin, vmax, ar) == (if i < vmax then (if lo <= i mod step && i mod step < hi then Heap[Seq#Index(ar, i), Ref__Integer_value] else 0) + sum_square'(Heap, i + 1, lo, hi, step, vmin, vmax, ar) else 0)
);

// Framing axioms
function  sum_square#frame(frame: FrameType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref)): int;
axiom (forall Heap: HeapType, Mask: MaskType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref) ::
  { state(Heap, Mask), sum_square'(Heap, i, lo, hi, step, vmin, vmax, ar) }
  state(Heap, Mask) ==> sum_square'(Heap, i, lo, hi, step, vmin, vmax, ar) == sum_square#frame(FrameFragment(sum_square#condqp2(Heap, i, lo, hi, step, vmin, vmax, ar)), i, lo, hi, step, vmin, vmax, ar)
);
// ==================================================
// Function used for framing of quantified permission (forall k: Int :: { ar[k] } min <= k && (k < max && (lo <= k % step && k % step < hi)) ==> acc(ar[k].Ref__Integer_value, wildcard)) in function sum_square
// ==================================================

function  sum_square#condqp2(Heap: HeapType, i_1_1: int, lo_1_1: int, hi_1_1: int, step_1_1: int, vmin_1_1: int, vmax_1_1: int, ar_1_1: (Seq Ref)): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref) ::
  { sum_square#condqp2(Heap2Heap, i, lo, hi, step, vmin, vmax, ar), sum_square#condqp2(Heap1Heap, i, lo, hi, step, vmin, vmax, ar), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall k_2: int ::

    (vmin <= k_2 && (k_2 < vmax && (lo <= k_2 mod step && k_2 mod step < hi)) <==> vmin <= k_2 && (k_2 < vmax && (lo <= k_2 mod step && k_2 mod step < hi))) && (vmin <= k_2 && (k_2 < vmax && (lo <= k_2 mod step && k_2 mod step < hi)) ==> Heap2Heap[Seq#Index(ar, k_2), Ref__Integer_value] == Heap1Heap[Seq#Index(ar, k_2), Ref__Integer_value])
  ) ==> sum_square#condqp2(Heap2Heap, i, lo, hi, step, vmin, vmax, ar) == sum_square#condqp2(Heap1Heap, i, lo, hi, step, vmin, vmax, ar)
);

// Trigger function (controlling recursive postconditions)
function  sum_square#trigger(frame: FrameType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref)): bool;

// State-independent trigger function
function  sum_square#triggerStateless(i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref)): int;

// Check contract well-formedness and postcondition
procedure sum_square#definedness(i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref)) returns (Result: int)
  modifies Heap, Mask;
{
  var j_2: int;
  var k_4: int;
  var k_5: int;
  var QPMask: MaskType;
  var wildcard: real where wildcard > 0.000000000;
  var j_4: int;
  var k_9: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 4;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume 0 <= lo;
    assume lo <= hi;
    assume hi <= step;
    assume step > 0;
    assume state(Heap, Mask);
    assume 0 <= vmin;
    assume vmin <= i;
    assume i <= vmax;
    assume state(Heap, Mask);
    assume vmax <= Seq#Length(ar);
    assume state(Heap, Mask);

    // -- Check definedness of (forall j: Int, k: Int :: { ar[j], ar[k] } 0 <= j && (j < max && (0 <= k && (k < max && j != k))) ==> ar[j] != ar[k])
      if (*) {
        if (0 <= j_2 && (j_2 < vmax && (0 <= k_4 && (k_4 < vmax && j_2 != k_4)))) {
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might be negative. (testZeroArray.vpr@26.12--26.104) [593]"}
            j_2 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might exceed sequence length. (testZeroArray.vpr@26.12--26.104) [594]"}
            j_2 < Seq#Length(ar);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@26.12--26.104) [595]"}
            k_4 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@26.12--26.104) [596]"}
            k_4 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall j_3: int, k_6: int ::
      { Seq#Index(ar, j_3), Seq#Index(ar, k_6) }
      0 <= j_3 && (j_3 < vmax && (0 <= k_6 && (k_6 < vmax && j_3 != k_6))) ==> Seq#Index(ar, j_3) != Seq#Index(ar, k_6)
    );
    assume state(Heap, Mask);

    // -- Check definedness of (forall k: Int :: { ar[k] } min <= k && (k < max && (lo <= k % step && k % step < hi)) ==> acc(ar[k].Ref__Integer_value, wildcard))
      if (*) {
        if (vmin <= k_5) {
          if (k_5 < vmax) {
            assert {:msg "  Contract might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@27.13--27.136) [597]"}
              step != 0;
            if (lo <= k_5 mod step) {
              assert {:msg "  Contract might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@27.13--27.136) [598]"}
                step != 0;
            }
          }
        }
        if (vmin <= k_5 && (k_5 < vmax && (lo <= k_5 mod step && k_5 mod step < hi))) {
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@27.13--27.136) [599]"}
            k_5 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@27.13--27.136) [600]"}
            k_5 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@27.13--27.136) [601]"}
      (forall k_8: int, k_8_1: int ::

      (((k_8 != k_8_1 && (vmin <= k_8 && (k_8 < vmax && (lo <= k_8 mod step && k_8 mod step < hi)))) && (vmin <= k_8_1 && (k_8_1 < vmax && (lo <= k_8_1 mod step && k_8_1 mod step < hi)))) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_8) != Seq#Index(ar, k_8_1)
    );

    // -- Define Inverse Function
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        vmin <= k_8 && (k_8 < vmax && (lo <= k_8 mod step && k_8 mod step < hi)) ==> qpRange3(Seq#Index(ar, k_8)) && invRecv3(Seq#Index(ar, k_8)) == k_8
      );
      assume (forall o_3: Ref ::
        { invRecv3(o_3) }
        (vmin <= invRecv3(o_3) && (invRecv3(o_3) < vmax && (lo <= invRecv3(o_3) mod step && invRecv3(o_3) mod step < hi))) && qpRange3(o_3) ==> Seq#Index(ar, invRecv3(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        vmin <= k_8 && (k_8 < vmax && (lo <= k_8 mod step && k_8 mod step < hi)) ==> Seq#Index(ar, k_8) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        ((vmin <= invRecv3(o_3) && (invRecv3(o_3) < vmax && (lo <= invRecv3(o_3) mod step && invRecv3(o_3) mod step < hi))) && qpRange3(o_3) ==> Seq#Index(ar, invRecv3(o_3)) == o_3 && Mask[o_3, Ref__Integer_value] < QPMask[o_3, Ref__Integer_value]) && (!((vmin <= invRecv3(o_3) && (invRecv3(o_3) < vmax && (lo <= invRecv3(o_3) mod step && invRecv3(o_3) mod step < hi))) && qpRange3(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (i < max ? (lo <= i % step && i % step < hi ? ar[i].Ref__Integer_value : 0) + sum_square(i + 1, lo, hi, step, min, max, ar) : 0)
      if (i < vmax) {
        assert {:msg "  Function might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@22.1--30.2) [602]"}
          step != 0;
        if (lo <= i mod step) {
          assert {:msg "  Function might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@22.1--30.2) [603]"}
            step != 0;
        }
        if (lo <= i mod step && i mod step < hi) {
          assert {:msg "  Function might not be well-formed. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@22.1--30.2) [604]"}
            HasDirectPerm(Mask, Seq#Index(ar, i), Ref__Integer_value);
          assert {:msg "  Function might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@22.1--30.2) [605]"}
            i >= 0;
          assert {:msg "  Function might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@22.1--30.2) [606]"}
            i < Seq#Length(ar);
        }
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function sum_square might not hold. Assertion 0 <= lo might not hold. (testZeroArray.vpr@29.85--29.130) [607]"}
            0 <= lo;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion lo <= hi might not hold. (testZeroArray.vpr@29.85--29.130) [608]"}
            lo <= hi;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion hi <= step might not hold. (testZeroArray.vpr@29.85--29.130) [609]"}
            hi <= step;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion step > 0 might not hold. (testZeroArray.vpr@29.85--29.130) [610]"}
            step > 0;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion 0 <= min might not hold. (testZeroArray.vpr@29.85--29.130) [611]"}
            0 <= vmin;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion min <= i + 1 might not hold. (testZeroArray.vpr@29.85--29.130) [612]"}
            vmin <= i + 1;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion i + 1 <= max might not hold. (testZeroArray.vpr@29.85--29.130) [613]"}
            i + 1 <= vmax;
          assert {:msg "  Precondition of function sum_square might not hold. Assertion max <= |ar| might not hold. (testZeroArray.vpr@29.85--29.130) [614]"}
            vmax <= Seq#Length(ar);
          if (*) {
            if (0 <= j_4 && (j_4 < vmax && (0 <= k_9 && (k_9 < vmax && j_4 != k_9)))) {
              assert {:msg "  Precondition of function sum_square might not hold. Assertion ar[j] != ar[k] might not hold. (testZeroArray.vpr@29.85--29.130) [615]"}
                Seq#Index(ar, j_4) != Seq#Index(ar, k_9);
            }
            assume false;
          }
          assume (forall j_5_1: int, k_10_1: int ::
            { Seq#Index(ar, j_5_1), Seq#Index(ar, k_10_1) }
            0 <= j_5_1 && (j_5_1 < vmax && (0 <= k_10_1 && (k_10_1 < vmax && j_5_1 != k_10_1))) ==> Seq#Index(ar, j_5_1) != Seq#Index(ar, k_10_1)
          );
          havoc QPMask;
          // wild card assumptions
          havoc wildcard;
          assert {:msg "  Precondition of function sum_square might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@29.85--29.130) [616]"}
            (forall k_11: int ::

            vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)) ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
          );
          assume (forall k_11: int ::

            vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)) ==> wildcard < Mask[Seq#Index(ar, k_11), Ref__Integer_value]
          );

          // -- check that the permission amount is positive
            assert {:msg "  Precondition of function sum_square might not hold. Fraction wildcard might be negative. (testZeroArray.vpr@29.85--29.130) [617]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi))) && dummyFunction(Heap[Seq#Index(ar, k_11), Ref__Integer_value]) ==> wildcard >= NoPerm
            );

          // -- check if receiver ar[k] is injective
            assert {:msg "  Precondition of function sum_square might not hold. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@29.85--29.130) [618]"}
              (forall k_11: int, k_11_1: int ::
              { neverTriggered4(k_11), neverTriggered4(k_11_1) }
              (((k_11 != k_11_1 && (vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)))) && (vmin <= k_11_1 && (k_11_1 < vmax && (lo <= k_11_1 mod step && k_11_1 mod step < hi)))) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_11) != Seq#Index(ar, k_11_1)
            );

          // -- check if sufficient permission is held
            assert {:msg "  Precondition of function sum_square might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@29.85--29.130) [619]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)) ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
            );

          // -- assumptions for inverse of receiver ar[k]
            assume (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi))) && NoPerm < wildcard ==> qpRange4(Seq#Index(ar, k_11)) && invRecv4(Seq#Index(ar, k_11)) == k_11
            );
            assume (forall o_3: Ref ::
              { invRecv4(o_3) }
              (vmin <= invRecv4(o_3) && (invRecv4(o_3) < vmax && (lo <= invRecv4(o_3) mod step && invRecv4(o_3) mod step < hi))) && (NoPerm < wildcard && qpRange4(o_3)) ==> Seq#Index(ar, invRecv4(o_3)) == o_3
            );

          // -- assume permission updates for field Ref__Integer_value
            assume (forall o_3: Ref ::
              { QPMask[o_3, Ref__Integer_value] }
              ((vmin <= invRecv4(o_3) && (invRecv4(o_3) < vmax && (lo <= invRecv4(o_3) mod step && invRecv4(o_3) mod step < hi))) && (NoPerm < wildcard && qpRange4(o_3)) ==> Seq#Index(ar, invRecv4(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - wildcard) && (!((vmin <= invRecv4(o_3) && (invRecv4(o_3) < vmax && (lo <= invRecv4(o_3) mod step && invRecv4(o_3) mod step < hi))) && (NoPerm < wildcard && qpRange4(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
            );

          // -- assume permission updates for independent locations
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { QPMask[o_3, f_5] }
              f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume sum_square#trigger(FrameFragment(sum_square#condqp2(Heap, i + 1, lo, hi, step, vmin, vmax, ar)), i + 1, lo, hi, step, vmin, vmax, ar);
        }
      }

  // -- Translate function body
    Result := (if i < vmax then (if lo <= i mod step && i mod step < hi then Heap[Seq#Index(ar, i), Ref__Integer_value] else 0) + sum_square(Heap, i + 1, lo, hi, step, vmin, vmax, ar) else 0);
}

// ==================================================
// Translation of function count_square
// ==================================================

// Uninterpreted function definitions
function  count_square(Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int): int;
function  count_square'(Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int): int;
axiom (forall Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int ::
  { count_square(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) }
  count_square(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) == count_square'(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) && dummyFunction(count_square#triggerStateless(i, lo, hi, step, vmin, vmax, ar, v_2))
);
axiom (forall Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int ::
  { count_square'(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) }
  dummyFunction(count_square#triggerStateless(i, lo, hi, step, vmin, vmax, ar, v_2))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int ::
  { state(Heap, Mask), count_square(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) }
  state(Heap, Mask) && AssumeFunctionsAbove < 1 ==> (((0 <= lo && (lo <= hi && (hi <= step && step > 0))) && (0 <= vmin && (vmin <= i && i <= vmax))) && vmax <= Seq#Length(ar)) && (forall j: int, k: int ::
    { Seq#Index(ar, j), Seq#Index(ar, k) }
    0 <= j && (j < vmax && (0 <= k && (k < vmax && j != k))) ==> Seq#Index(ar, j) != Seq#Index(ar, k)
  ) ==> count_square(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) == (if i < vmax then (if lo <= i mod step && (i mod step < hi && Heap[Seq#Index(ar, i), Ref__Integer_value] == v_2) then 1 else 0) + count_square'(Heap, i + 1, lo, hi, step, vmin, vmax, ar, v_2) else 0)
);

// Framing axioms
function  count_square#frame(frame: FrameType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int): int;
axiom (forall Heap: HeapType, Mask: MaskType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int ::
  { state(Heap, Mask), count_square'(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) }
  state(Heap, Mask) ==> count_square'(Heap, i, lo, hi, step, vmin, vmax, ar, v_2) == count_square#frame(FrameFragment(count_square#condqp3(Heap, i, lo, hi, step, vmin, vmax, ar, v_2)), i, lo, hi, step, vmin, vmax, ar, v_2)
);
// ==================================================
// Function used for framing of quantified permission (forall k: Int :: { ar[k] } min <= k && (k < max && (lo <= k % step && k % step < hi)) ==> acc(ar[k].Ref__Integer_value, wildcard)) in function count_square
// ==================================================

function  count_square#condqp3(Heap: HeapType, i_1_1: int, lo_1_1: int, hi_1_1: int, step_1_1: int, vmin_1_1: int, vmax_1_1: int, ar_1_1: (Seq Ref), v_1_1: int): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int ::
  { count_square#condqp3(Heap2Heap, i, lo, hi, step, vmin, vmax, ar, v_2), count_square#condqp3(Heap1Heap, i, lo, hi, step, vmin, vmax, ar, v_2), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall k_2: int ::

    (vmin <= k_2 && (k_2 < vmax && (lo <= k_2 mod step && k_2 mod step < hi)) <==> vmin <= k_2 && (k_2 < vmax && (lo <= k_2 mod step && k_2 mod step < hi))) && (vmin <= k_2 && (k_2 < vmax && (lo <= k_2 mod step && k_2 mod step < hi)) ==> Heap2Heap[Seq#Index(ar, k_2), Ref__Integer_value] == Heap1Heap[Seq#Index(ar, k_2), Ref__Integer_value])
  ) ==> count_square#condqp3(Heap2Heap, i, lo, hi, step, vmin, vmax, ar, v_2) == count_square#condqp3(Heap1Heap, i, lo, hi, step, vmin, vmax, ar, v_2)
);

// Trigger function (controlling recursive postconditions)
function  count_square#trigger(frame: FrameType, i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int): bool;

// State-independent trigger function
function  count_square#triggerStateless(i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int): int;

// Check contract well-formedness and postcondition
procedure count_square#definedness(i: int, lo: int, hi: int, step: int, vmin: int, vmax: int, ar: (Seq Ref), v_2: int) returns (Result: int)
  modifies Heap, Mask;
{
  var j_5: int;
  var k_7: int;
  var k_10: int;
  var QPMask: MaskType;
  var wildcard: real where wildcard > 0.000000000;
  var j_4: int;
  var k_9: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 1;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume 0 <= lo;
    assume lo <= hi;
    assume hi <= step;
    assume step > 0;
    assume state(Heap, Mask);
    assume 0 <= vmin;
    assume vmin <= i;
    assume i <= vmax;
    assume state(Heap, Mask);
    assume vmax <= Seq#Length(ar);
    assume state(Heap, Mask);

    // -- Check definedness of (forall j: Int, k: Int :: { ar[j], ar[k] } 0 <= j && (j < max && (0 <= k && (k < max && j != k))) ==> ar[j] != ar[k])
      if (*) {
        if (0 <= j_5 && (j_5 < vmax && (0 <= k_7 && (k_7 < vmax && j_5 != k_7)))) {
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might be negative. (testZeroArray.vpr@36.12--36.104) [620]"}
            j_5 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might exceed sequence length. (testZeroArray.vpr@36.12--36.104) [621]"}
            j_5 < Seq#Length(ar);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@36.12--36.104) [622]"}
            k_7 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@36.12--36.104) [623]"}
            k_7 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall j_3: int, k_6: int ::
      { Seq#Index(ar, j_3), Seq#Index(ar, k_6) }
      0 <= j_3 && (j_3 < vmax && (0 <= k_6 && (k_6 < vmax && j_3 != k_6))) ==> Seq#Index(ar, j_3) != Seq#Index(ar, k_6)
    );
    assume state(Heap, Mask);

    // -- Check definedness of (forall k: Int :: { ar[k] } min <= k && (k < max && (lo <= k % step && k % step < hi)) ==> acc(ar[k].Ref__Integer_value, wildcard))
      if (*) {
        if (vmin <= k_10) {
          if (k_10 < vmax) {
            assert {:msg "  Contract might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@37.13--37.136) [624]"}
              step != 0;
            if (lo <= k_10 mod step) {
              assert {:msg "  Contract might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@37.13--37.136) [625]"}
                step != 0;
            }
          }
        }
        if (vmin <= k_10 && (k_10 < vmax && (lo <= k_10 mod step && k_10 mod step < hi))) {
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@37.13--37.136) [626]"}
            k_10 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@37.13--37.136) [627]"}
            k_10 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@37.13--37.136) [628]"}
      (forall k_8: int, k_8_1: int ::

      (((k_8 != k_8_1 && (vmin <= k_8 && (k_8 < vmax && (lo <= k_8 mod step && k_8 mod step < hi)))) && (vmin <= k_8_1 && (k_8_1 < vmax && (lo <= k_8_1 mod step && k_8_1 mod step < hi)))) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_8) != Seq#Index(ar, k_8_1)
    );

    // -- Define Inverse Function
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        vmin <= k_8 && (k_8 < vmax && (lo <= k_8 mod step && k_8 mod step < hi)) ==> qpRange5(Seq#Index(ar, k_8)) && invRecv5(Seq#Index(ar, k_8)) == k_8
      );
      assume (forall o_3: Ref ::
        { invRecv5(o_3) }
        (vmin <= invRecv5(o_3) && (invRecv5(o_3) < vmax && (lo <= invRecv5(o_3) mod step && invRecv5(o_3) mod step < hi))) && qpRange5(o_3) ==> Seq#Index(ar, invRecv5(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        vmin <= k_8 && (k_8 < vmax && (lo <= k_8 mod step && k_8 mod step < hi)) ==> Seq#Index(ar, k_8) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        ((vmin <= invRecv5(o_3) && (invRecv5(o_3) < vmax && (lo <= invRecv5(o_3) mod step && invRecv5(o_3) mod step < hi))) && qpRange5(o_3) ==> Seq#Index(ar, invRecv5(o_3)) == o_3 && Mask[o_3, Ref__Integer_value] < QPMask[o_3, Ref__Integer_value]) && (!((vmin <= invRecv5(o_3) && (invRecv5(o_3) < vmax && (lo <= invRecv5(o_3) mod step && invRecv5(o_3) mod step < hi))) && qpRange5(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (i < max ? (lo <= i % step && (i % step < hi && ar[i].Ref__Integer_value == v) ? 1 : 0) + count_square(i + 1, lo, hi, step, min, max, ar, v) : 0)
      if (i < vmax) {
        assert {:msg "  Function might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@32.1--40.2) [629]"}
          step != 0;
        if (lo <= i mod step) {
          assert {:msg "  Function might not be well-formed. Divisor step might be zero. (testZeroArray.vpr@32.1--40.2) [630]"}
            step != 0;
          if (i mod step < hi) {
            assert {:msg "  Function might not be well-formed. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@32.1--40.2) [631]"}
              HasDirectPerm(Mask, Seq#Index(ar, i), Ref__Integer_value);
            assert {:msg "  Function might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@32.1--40.2) [632]"}
              i >= 0;
            assert {:msg "  Function might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@32.1--40.2) [633]"}
              i < Seq#Length(ar);
          }
        }
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function count_square might not hold. Assertion 0 <= lo might not hold. (testZeroArray.vpr@39.97--39.147) [634]"}
            0 <= lo;
          assert {:msg "  Precondition of function count_square might not hold. Assertion lo <= hi might not hold. (testZeroArray.vpr@39.97--39.147) [635]"}
            lo <= hi;
          assert {:msg "  Precondition of function count_square might not hold. Assertion hi <= step might not hold. (testZeroArray.vpr@39.97--39.147) [636]"}
            hi <= step;
          assert {:msg "  Precondition of function count_square might not hold. Assertion step > 0 might not hold. (testZeroArray.vpr@39.97--39.147) [637]"}
            step > 0;
          assert {:msg "  Precondition of function count_square might not hold. Assertion 0 <= min might not hold. (testZeroArray.vpr@39.97--39.147) [638]"}
            0 <= vmin;
          assert {:msg "  Precondition of function count_square might not hold. Assertion min <= i + 1 might not hold. (testZeroArray.vpr@39.97--39.147) [639]"}
            vmin <= i + 1;
          assert {:msg "  Precondition of function count_square might not hold. Assertion i + 1 <= max might not hold. (testZeroArray.vpr@39.97--39.147) [640]"}
            i + 1 <= vmax;
          assert {:msg "  Precondition of function count_square might not hold. Assertion max <= |ar| might not hold. (testZeroArray.vpr@39.97--39.147) [641]"}
            vmax <= Seq#Length(ar);
          if (*) {
            if (0 <= j_4 && (j_4 < vmax && (0 <= k_9 && (k_9 < vmax && j_4 != k_9)))) {
              assert {:msg "  Precondition of function count_square might not hold. Assertion ar[j] != ar[k] might not hold. (testZeroArray.vpr@39.97--39.147) [642]"}
                Seq#Index(ar, j_4) != Seq#Index(ar, k_9);
            }
            assume false;
          }
          assume (forall j_5_1: int, k_10_1: int ::
            { Seq#Index(ar, j_5_1), Seq#Index(ar, k_10_1) }
            0 <= j_5_1 && (j_5_1 < vmax && (0 <= k_10_1 && (k_10_1 < vmax && j_5_1 != k_10_1))) ==> Seq#Index(ar, j_5_1) != Seq#Index(ar, k_10_1)
          );
          havoc QPMask;
          // wild card assumptions
          havoc wildcard;
          assert {:msg "  Precondition of function count_square might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@39.97--39.147) [643]"}
            (forall k_11: int ::

            vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)) ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
          );
          assume (forall k_11: int ::

            vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)) ==> wildcard < Mask[Seq#Index(ar, k_11), Ref__Integer_value]
          );

          // -- check that the permission amount is positive
            assert {:msg "  Precondition of function count_square might not hold. Fraction wildcard might be negative. (testZeroArray.vpr@39.97--39.147) [644]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi))) && dummyFunction(Heap[Seq#Index(ar, k_11), Ref__Integer_value]) ==> wildcard >= NoPerm
            );

          // -- check if receiver ar[k] is injective
            assert {:msg "  Precondition of function count_square might not hold. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@39.97--39.147) [645]"}
              (forall k_11: int, k_11_1: int ::
              { neverTriggered6(k_11), neverTriggered6(k_11_1) }
              (((k_11 != k_11_1 && (vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)))) && (vmin <= k_11_1 && (k_11_1 < vmax && (lo <= k_11_1 mod step && k_11_1 mod step < hi)))) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_11) != Seq#Index(ar, k_11_1)
            );

          // -- check if sufficient permission is held
            assert {:msg "  Precondition of function count_square might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@39.97--39.147) [646]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi)) ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
            );

          // -- assumptions for inverse of receiver ar[k]
            assume (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (vmin <= k_11 && (k_11 < vmax && (lo <= k_11 mod step && k_11 mod step < hi))) && NoPerm < wildcard ==> qpRange6(Seq#Index(ar, k_11)) && invRecv6(Seq#Index(ar, k_11)) == k_11
            );
            assume (forall o_3: Ref ::
              { invRecv6(o_3) }
              (vmin <= invRecv6(o_3) && (invRecv6(o_3) < vmax && (lo <= invRecv6(o_3) mod step && invRecv6(o_3) mod step < hi))) && (NoPerm < wildcard && qpRange6(o_3)) ==> Seq#Index(ar, invRecv6(o_3)) == o_3
            );

          // -- assume permission updates for field Ref__Integer_value
            assume (forall o_3: Ref ::
              { QPMask[o_3, Ref__Integer_value] }
              ((vmin <= invRecv6(o_3) && (invRecv6(o_3) < vmax && (lo <= invRecv6(o_3) mod step && invRecv6(o_3) mod step < hi))) && (NoPerm < wildcard && qpRange6(o_3)) ==> Seq#Index(ar, invRecv6(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - wildcard) && (!((vmin <= invRecv6(o_3) && (invRecv6(o_3) < vmax && (lo <= invRecv6(o_3) mod step && invRecv6(o_3) mod step < hi))) && (NoPerm < wildcard && qpRange6(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
            );

          // -- assume permission updates for independent locations
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { QPMask[o_3, f_5] }
              f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume count_square#trigger(FrameFragment(count_square#condqp3(Heap, i + 1, lo, hi, step, vmin, vmax, ar, v_2)), i + 1, lo, hi, step, vmin, vmax, ar, v_2);
        }
      }

  // -- Translate function body
    Result := (if i < vmax then (if lo <= i mod step && (i mod step < hi && Heap[Seq#Index(ar, i), Ref__Integer_value] == v_2) then 1 else 0) + count_square(Heap, i + 1, lo, hi, step, vmin, vmax, ar, v_2) else 0);
}

// ==================================================
// Translation of function count_list
// ==================================================

// Uninterpreted function definitions
function  count_list(Heap: HeapType, i: int, hi: int, ar: (Seq int), v_2: int): int;
function  count_list'(Heap: HeapType, i: int, hi: int, ar: (Seq int), v_2: int): int;
axiom (forall Heap: HeapType, i: int, hi: int, ar: (Seq int), v_2: int ::
  { count_list(Heap, i, hi, ar, v_2) }
  count_list(Heap, i, hi, ar, v_2) == count_list'(Heap, i, hi, ar, v_2) && dummyFunction(count_list#triggerStateless(i, hi, ar, v_2))
);
axiom (forall Heap: HeapType, i: int, hi: int, ar: (Seq int), v_2: int ::
  { count_list'(Heap, i, hi, ar, v_2) }
  dummyFunction(count_list#triggerStateless(i, hi, ar, v_2))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int, hi: int, ar: (Seq int), v_2: int ::
  { state(Heap, Mask), count_list(Heap, i, hi, ar, v_2) }
  state(Heap, Mask) && AssumeFunctionsAbove < 5 ==> (0 <= i && i <= hi) && hi <= Seq#Length(ar) ==> count_list(Heap, i, hi, ar, v_2) == (if i < hi then (if Seq#Index(ar, i) == v_2 then 1 else 0) + count_list'(Heap, i + 1, hi, ar, v_2) else 0)
);

// Framing axioms
function  count_list#frame(frame: FrameType, i: int, hi: int, ar: (Seq int), v_2: int): int;
axiom (forall Heap: HeapType, Mask: MaskType, i: int, hi: int, ar: (Seq int), v_2: int ::
  { state(Heap, Mask), count_list'(Heap, i, hi, ar, v_2) }
  state(Heap, Mask) ==> count_list'(Heap, i, hi, ar, v_2) == count_list#frame(EmptyFrame, i, hi, ar, v_2)
);

// Trigger function (controlling recursive postconditions)
function  count_list#trigger(frame: FrameType, i: int, hi: int, ar: (Seq int), v_2: int): bool;

// State-independent trigger function
function  count_list#triggerStateless(i: int, hi: int, ar: (Seq int), v_2: int): int;

// Check contract well-formedness and postcondition
procedure count_list#definedness(i: int, hi: int, ar: (Seq int), v_2: int) returns (Result: int)
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 5;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume 0 <= i;
    assume i <= hi;
    assume state(Heap, Mask);
    assume hi <= Seq#Length(ar);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (i < hi ? (ar[i] == v ? 1 : 0) + count_list(i + 1, hi, ar, v) : 0)
      if (i < hi) {
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@42.1--47.2) [647]"}
          i >= 0;
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@42.1--47.2) [648]"}
          i < Seq#Length(ar);
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function count_list might not hold. Assertion 0 <= i + 1 might not hold. (testZeroArray.vpr@46.36--46.64) [649]"}
            0 <= i + 1;
          assert {:msg "  Precondition of function count_list might not hold. Assertion i + 1 <= hi might not hold. (testZeroArray.vpr@46.36--46.64) [650]"}
            i + 1 <= hi;
          assert {:msg "  Precondition of function count_list might not hold. Assertion hi <= |ar| might not hold. (testZeroArray.vpr@46.36--46.64) [651]"}
            hi <= Seq#Length(ar);
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume count_list#trigger(EmptyFrame, i + 1, hi, ar, v_2);
        }
      }

  // -- Translate function body
    Result := (if i < hi then (if Seq#Index(ar, i) == v_2 then 1 else 0) + count_list(Heap, i + 1, hi, ar, v_2) else 0);
}

// ==================================================
// Translation of function count_array
// ==================================================

// Uninterpreted function definitions
function  count_array(Heap: HeapType, i: int, hi: int, ar: (Seq Ref), v_2: int): int;
function  count_array'(Heap: HeapType, i: int, hi: int, ar: (Seq Ref), v_2: int): int;
axiom (forall Heap: HeapType, i: int, hi: int, ar: (Seq Ref), v_2: int ::
  { count_array(Heap, i, hi, ar, v_2) }
  count_array(Heap, i, hi, ar, v_2) == count_array'(Heap, i, hi, ar, v_2) && dummyFunction(count_array#triggerStateless(i, hi, ar, v_2))
);
axiom (forall Heap: HeapType, i: int, hi: int, ar: (Seq Ref), v_2: int ::
  { count_array'(Heap, i, hi, ar, v_2) }
  dummyFunction(count_array#triggerStateless(i, hi, ar, v_2))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int, hi: int, ar: (Seq Ref), v_2: int ::
  { state(Heap, Mask), count_array(Heap, i, hi, ar, v_2) }
  state(Heap, Mask) && AssumeFunctionsAbove < 0 ==> ((0 <= i && i <= hi) && hi <= Seq#Length(ar)) && (forall j: int, k: int ::
    { Seq#Index(ar, j), Seq#Index(ar, k) }
    0 <= j && (j < hi && (0 <= k && (k < hi && j != k))) ==> Seq#Index(ar, j) != Seq#Index(ar, k)
  ) ==> count_array(Heap, i, hi, ar, v_2) == (if i < hi then (if Heap[Seq#Index(ar, i), Ref__Integer_value] == v_2 then 1 else 0) + count_array'(Heap, i + 1, hi, ar, v_2) else 0)
);

// Framing axioms
function  count_array#frame(frame: FrameType, i: int, hi: int, ar: (Seq Ref), v_2: int): int;
axiom (forall Heap: HeapType, Mask: MaskType, i: int, hi: int, ar: (Seq Ref), v_2: int ::
  { state(Heap, Mask), count_array'(Heap, i, hi, ar, v_2) }
  state(Heap, Mask) ==> count_array'(Heap, i, hi, ar, v_2) == count_array#frame(FrameFragment(count_array#condqp4(Heap, i, hi, ar, v_2)), i, hi, ar, v_2)
);
// ==================================================
// Function used for framing of quantified permission (forall k: Int :: { ar[k] } 0 <= k && k < hi ==> acc(ar[k].Ref__Integer_value, wildcard)) in function count_array
// ==================================================

function  count_array#condqp4(Heap: HeapType, i_1_1: int, hi_1_1: int, ar_1_1: (Seq Ref), v_1_1: int): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, i: int, hi: int, ar: (Seq Ref), v_2: int ::
  { count_array#condqp4(Heap2Heap, i, hi, ar, v_2), count_array#condqp4(Heap1Heap, i, hi, ar, v_2), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall k_2: int ::

    (0 <= k_2 && k_2 < hi <==> 0 <= k_2 && k_2 < hi) && (0 <= k_2 && k_2 < hi ==> Heap2Heap[Seq#Index(ar, k_2), Ref__Integer_value] == Heap1Heap[Seq#Index(ar, k_2), Ref__Integer_value])
  ) ==> count_array#condqp4(Heap2Heap, i, hi, ar, v_2) == count_array#condqp4(Heap1Heap, i, hi, ar, v_2)
);

// Trigger function (controlling recursive postconditions)
function  count_array#trigger(frame: FrameType, i: int, hi: int, ar: (Seq Ref), v_2: int): bool;

// State-independent trigger function
function  count_array#triggerStateless(i: int, hi: int, ar: (Seq Ref), v_2: int): int;

// Check contract well-formedness and postcondition
procedure count_array#definedness(i: int, hi: int, ar: (Seq Ref), v_2: int) returns (Result: int)
  modifies Heap, Mask;
{
  var j_6: int;
  var k_12: int;
  var k_13: int;
  var QPMask: MaskType;
  var wildcard: real where wildcard > 0.000000000;
  var j_4: int;
  var k_9: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 0;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    assume 0 <= i;
    assume i <= hi;
    assume state(Heap, Mask);
    assume hi <= Seq#Length(ar);
    assume state(Heap, Mask);

    // -- Check definedness of (forall j: Int, k: Int :: { ar[j], ar[k] } 0 <= j && (j < hi && (0 <= k && (k < hi && j != k))) ==> ar[j] != ar[k])
      if (*) {
        if (0 <= j_6 && (j_6 < hi && (0 <= k_12 && (k_12 < hi && j_6 != k_12)))) {
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might be negative. (testZeroArray.vpr@52.12--52.102) [652]"}
            j_6 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might exceed sequence length. (testZeroArray.vpr@52.12--52.102) [653]"}
            j_6 < Seq#Length(ar);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@52.12--52.102) [654]"}
            k_12 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@52.12--52.102) [655]"}
            k_12 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall j_3: int, k_6: int ::
      { Seq#Index(ar, j_3), Seq#Index(ar, k_6) }
      0 <= j_3 && (j_3 < hi && (0 <= k_6 && (k_6 < hi && j_3 != k_6))) ==> Seq#Index(ar, j_3) != Seq#Index(ar, k_6)
    );
    assume state(Heap, Mask);

    // -- Check definedness of (forall k: Int :: { ar[k] } 0 <= k && k < hi ==> acc(ar[k].Ref__Integer_value, wildcard))
      if (*) {
        if (0 <= k_13 && k_13 < hi) {
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@53.13--53.94) [656]"}
            k_13 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@53.13--53.94) [657]"}
            k_13 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@53.13--53.94) [658]"}
      (forall k_8: int, k_8_1: int ::

      (((k_8 != k_8_1 && (0 <= k_8 && k_8 < hi)) && (0 <= k_8_1 && k_8_1 < hi)) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_8) != Seq#Index(ar, k_8_1)
    );

    // -- Define Inverse Function
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        0 <= k_8 && k_8 < hi ==> qpRange7(Seq#Index(ar, k_8)) && invRecv7(Seq#Index(ar, k_8)) == k_8
      );
      assume (forall o_3: Ref ::
        { invRecv7(o_3) }
        (0 <= invRecv7(o_3) && invRecv7(o_3) < hi) && qpRange7(o_3) ==> Seq#Index(ar, invRecv7(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall k_8: int ::
        { Seq#Index(ar, k_8) } { Seq#Index(ar, k_8) }
        0 <= k_8 && k_8 < hi ==> Seq#Index(ar, k_8) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        ((0 <= invRecv7(o_3) && invRecv7(o_3) < hi) && qpRange7(o_3) ==> Seq#Index(ar, invRecv7(o_3)) == o_3 && Mask[o_3, Ref__Integer_value] < QPMask[o_3, Ref__Integer_value]) && (!((0 <= invRecv7(o_3) && invRecv7(o_3) < hi) && qpRange7(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (i < hi ? (ar[i].Ref__Integer_value == v ? 1 : 0) + count_array(i + 1, hi, ar, v) : 0)
      if (i < hi) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@49.1--56.2) [659]"}
          HasDirectPerm(Mask, Seq#Index(ar, i), Ref__Integer_value);
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@49.1--56.2) [660]"}
          i >= 0;
        assert {:msg "  Function might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@49.1--56.2) [661]"}
          i < Seq#Length(ar);
        if (*) {
          // Exhale precondition of function application
          assert {:msg "  Precondition of function count_array might not hold. Assertion 0 <= i + 1 might not hold. (testZeroArray.vpr@55.55--55.84) [662]"}
            0 <= i + 1;
          assert {:msg "  Precondition of function count_array might not hold. Assertion i + 1 <= hi might not hold. (testZeroArray.vpr@55.55--55.84) [663]"}
            i + 1 <= hi;
          assert {:msg "  Precondition of function count_array might not hold. Assertion hi <= |ar| might not hold. (testZeroArray.vpr@55.55--55.84) [664]"}
            hi <= Seq#Length(ar);
          if (*) {
            if (0 <= j_4 && (j_4 < hi && (0 <= k_9 && (k_9 < hi && j_4 != k_9)))) {
              assert {:msg "  Precondition of function count_array might not hold. Assertion ar[j] != ar[k] might not hold. (testZeroArray.vpr@55.55--55.84) [665]"}
                Seq#Index(ar, j_4) != Seq#Index(ar, k_9);
            }
            assume false;
          }
          assume (forall j_5_1: int, k_10_1: int ::
            { Seq#Index(ar, j_5_1), Seq#Index(ar, k_10_1) }
            0 <= j_5_1 && (j_5_1 < hi && (0 <= k_10_1 && (k_10_1 < hi && j_5_1 != k_10_1))) ==> Seq#Index(ar, j_5_1) != Seq#Index(ar, k_10_1)
          );
          havoc QPMask;
          // wild card assumptions
          havoc wildcard;
          assert {:msg "  Precondition of function count_array might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@55.55--55.84) [666]"}
            (forall k_11: int ::

            0 <= k_11 && k_11 < hi ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
          );
          assume (forall k_11: int ::

            0 <= k_11 && k_11 < hi ==> wildcard < Mask[Seq#Index(ar, k_11), Ref__Integer_value]
          );

          // -- check that the permission amount is positive
            assert {:msg "  Precondition of function count_array might not hold. Fraction wildcard might be negative. (testZeroArray.vpr@55.55--55.84) [667]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (0 <= k_11 && k_11 < hi) && dummyFunction(Heap[Seq#Index(ar, k_11), Ref__Integer_value]) ==> wildcard >= NoPerm
            );

          // -- check if receiver ar[k] is injective
            assert {:msg "  Precondition of function count_array might not hold. Quantified resource ar[k].Ref__Integer_value might not be injective. (testZeroArray.vpr@55.55--55.84) [668]"}
              (forall k_11: int, k_11_1: int ::
              { neverTriggered8(k_11), neverTriggered8(k_11_1) }
              (((k_11 != k_11_1 && (0 <= k_11 && k_11 < hi)) && (0 <= k_11_1 && k_11_1 < hi)) && NoPerm < wildcard) && NoPerm < wildcard ==> Seq#Index(ar, k_11) != Seq#Index(ar, k_11_1)
            );

          // -- check if sufficient permission is held
            assert {:msg "  Precondition of function count_array might not hold. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@55.55--55.84) [669]"}
              (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              0 <= k_11 && k_11 < hi ==> Mask[Seq#Index(ar, k_11), Ref__Integer_value] > NoPerm
            );

          // -- assumptions for inverse of receiver ar[k]
            assume (forall k_11: int ::
              { Seq#Index(ar, k_11) } { Seq#Index(ar, k_11) }
              (0 <= k_11 && k_11 < hi) && NoPerm < wildcard ==> qpRange8(Seq#Index(ar, k_11)) && invRecv8(Seq#Index(ar, k_11)) == k_11
            );
            assume (forall o_3: Ref ::
              { invRecv8(o_3) }
              (0 <= invRecv8(o_3) && invRecv8(o_3) < hi) && (NoPerm < wildcard && qpRange8(o_3)) ==> Seq#Index(ar, invRecv8(o_3)) == o_3
            );

          // -- assume permission updates for field Ref__Integer_value
            assume (forall o_3: Ref ::
              { QPMask[o_3, Ref__Integer_value] }
              ((0 <= invRecv8(o_3) && invRecv8(o_3) < hi) && (NoPerm < wildcard && qpRange8(o_3)) ==> Seq#Index(ar, invRecv8(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - wildcard) && (!((0 <= invRecv8(o_3) && invRecv8(o_3) < hi) && (NoPerm < wildcard && qpRange8(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
            );

          // -- assume permission updates for independent locations
            assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
              { QPMask[o_3, f_5] }
              f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
            );
          Mask := QPMask;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume count_array#trigger(FrameFragment(count_array#condqp4(Heap, i + 1, hi, ar, v_2)), i + 1, hi, ar, v_2);
        }
      }

  // -- Translate function body
    Result := (if i < hi then (if Heap[Seq#Index(ar, i), Ref__Integer_value] == v_2 then 1 else 0) + count_array(Heap, i + 1, hi, ar, v_2) else 0);
}

// ==================================================
// Translation of method Ref__loop_main_23
// ==================================================

procedure Ref__loop_main_23(diz: Ref, current_thread_id: int, len: int, ar: (Seq Ref)) returns ()
  modifies Heap, Mask;
{
  var j_7: int;
  var k_14: int;
  var i_2: int;
  var QPMask: MaskType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var i_7: int;
  var i_8: int;
  var i_7_1: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Assumptions about method arguments
    assume Heap[diz, $allocated];

  // -- Checked inhaling of precondition
    assume diz != null;
    assume state(Heap, Mask);
    assume current_thread_id >= 0;
    assume state(Heap, Mask);
    if (0 < len) {
      assume Seq#Length(ar) == len;
    }
    assume state(Heap, Mask);

    // -- Check definedness of (forall j: Int, k: Int :: { ar[j], ar[k] } 0 <= j && (j < len && (0 <= k && (k < len && j != k))) ==> ar[j] != ar[k])
      if (*) {
        if (0 <= j_7 && (j_7 < len && (0 <= k_14 && (k_14 < len && j_7 != k_14)))) {
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might be negative. (testZeroArray.vpr@62.12--62.104) [670]"}
            j_7 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might exceed sequence length. (testZeroArray.vpr@62.12--62.104) [671]"}
            j_7 < Seq#Length(ar);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@62.12--62.104) [672]"}
            k_14 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@62.12--62.104) [673]"}
            k_14 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall j_1_1: int, k_1_1: int ::
      { Seq#Index(ar, j_1_1), Seq#Index(ar, k_1_1) }
      0 <= j_1_1 && (j_1_1 < len && (0 <= k_1_1 && (k_1_1 < len && j_1_1 != k_1_1))) ==> Seq#Index(ar, j_1_1) != Seq#Index(ar, k_1_1)
    );
    assume state(Heap, Mask);

    // -- Check definedness of (forall i: Int :: { ar[i] } 0 <= i && i < len ==> acc(ar[i].Ref__Integer_value, write))
      if (*) {
        if (0 <= i_2 && i_2 < len) {
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@63.13--63.92) [674]"}
            i_2 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@63.13--63.92) [675]"}
            i_2 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@63.13--63.92) [676]"}
      (forall i_1: int, i_1_2: int ::

      (((i_1 != i_1_2 && (0 <= i_1 && i_1 < len)) && (0 <= i_1_2 && i_1_2 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_1) != Seq#Index(ar, i_1_2)
    );

    // -- Define Inverse Function
      assume (forall i_1: int ::
        { Seq#Index(ar, i_1) } { Seq#Index(ar, i_1) }
        (0 <= i_1 && i_1 < len) && NoPerm < FullPerm ==> qpRange9(Seq#Index(ar, i_1)) && invRecv9(Seq#Index(ar, i_1)) == i_1
      );
      assume (forall o_3: Ref ::
        { invRecv9(o_3) }
        ((0 <= invRecv9(o_3) && invRecv9(o_3) < len) && NoPerm < FullPerm) && qpRange9(o_3) ==> Seq#Index(ar, invRecv9(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall i_1: int ::
        { Seq#Index(ar, i_1) } { Seq#Index(ar, i_1) }
        0 <= i_1 && i_1 < len ==> Seq#Index(ar, i_1) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        (((0 <= invRecv9(o_3) && invRecv9(o_3) < len) && NoPerm < FullPerm) && qpRange9(o_3) ==> (NoPerm < FullPerm ==> Seq#Index(ar, invRecv9(o_3)) == o_3) && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] + FullPerm) && (!(((0 <= invRecv9(o_3) && invRecv9(o_3) < len) && NoPerm < FullPerm) && qpRange9(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
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
    if (0 < len) {
      assume Seq#Length(ar) == len;
    }
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall i: Int :: { ar[i] } 0 <= i && i < len ==> acc(ar[i].Ref__Integer_value, write))
      if (*) {
        if (0 <= i_7 && i_7 < len) {
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@65.12--65.91) [677]"}
            i_7 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@65.12--65.91) [678]"}
            i_7 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@65.12--65.91) [679]"}
      (forall i_3: int, i_3_1: int ::

      (((i_3 != i_3_1 && (0 <= i_3 && i_3 < len)) && (0 <= i_3_1 && i_3_1 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_3) != Seq#Index(ar, i_3_1)
    );

    // -- Define Inverse Function
      assume (forall i_3: int ::
        { Seq#Index(ar, i_3) } { Seq#Index(ar, i_3) }
        (0 <= i_3 && i_3 < len) && NoPerm < FullPerm ==> qpRange10(Seq#Index(ar, i_3)) && invRecv10(Seq#Index(ar, i_3)) == i_3
      );
      assume (forall o_3: Ref ::
        { invRecv10(o_3) }
        ((0 <= invRecv10(o_3) && invRecv10(o_3) < len) && NoPerm < FullPerm) && qpRange10(o_3) ==> Seq#Index(ar, invRecv10(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall i_3: int ::
        { Seq#Index(ar, i_3) } { Seq#Index(ar, i_3) }
        0 <= i_3 && i_3 < len ==> Seq#Index(ar, i_3) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        (((0 <= invRecv10(o_3) && invRecv10(o_3) < len) && NoPerm < FullPerm) && qpRange10(o_3) ==> (NoPerm < FullPerm ==> Seq#Index(ar, invRecv10(o_3)) == o_3) && QPMask[o_3, Ref__Integer_value] == PostMask[o_3, Ref__Integer_value] + FullPerm) && (!(((0 <= invRecv10(o_3) && invRecv10(o_3) < len) && NoPerm < FullPerm) && qpRange10(o_3)) ==> QPMask[o_3, Ref__Integer_value] == PostMask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall i: Int :: { ar[i] } 0 <= i && i < len ==> ar[i].Ref__Integer_value == 0)
      if (*) {
        if (0 <= i_8 && i_8 < len) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@66.12--66.86) [680]"}
            HasDirectPerm(PostMask, Seq#Index(ar, i_8), Ref__Integer_value);
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@66.12--66.86) [681]"}
            i_8 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@66.12--66.86) [682]"}
            i_8 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall i_5: int ::
      { Seq#Index(ar, i_5) }
      0 <= i_5 && i_5 < len ==> PostHeap[Seq#Index(ar, i_5), Ref__Integer_value] == 0
    );
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Translating statement: inhale false -- testZeroArray.vpr@68.3--68.15
    assume false;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    if (0 < len) {
      assert {:msg "  Postcondition of Ref__loop_main_23 might not hold. Assertion |ar| == len might not hold. (testZeroArray.vpr@64.11--64.38) [683]"}
        Seq#Length(ar) == len;
    }
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver ar[i] is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@65.12--65.91) [684]"}
        (forall i_6: int, i_6_1: int ::
        { neverTriggered11(i_6), neverTriggered11(i_6_1) }
        (((i_6 != i_6_1 && (0 <= i_6 && i_6 < len)) && (0 <= i_6_1 && i_6_1 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_6) != Seq#Index(ar, i_6_1)
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of Ref__loop_main_23 might not hold. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@65.12--65.91) [685]"}
        (forall i_6: int ::
        { Seq#Index(ar, i_6) } { Seq#Index(ar, i_6) }
        0 <= i_6 && i_6 < len ==> Mask[Seq#Index(ar, i_6), Ref__Integer_value] >= FullPerm
      );

    // -- assumptions for inverse of receiver ar[i]
      assume (forall i_6: int ::
        { Seq#Index(ar, i_6) } { Seq#Index(ar, i_6) }
        (0 <= i_6 && i_6 < len) && NoPerm < FullPerm ==> qpRange11(Seq#Index(ar, i_6)) && invRecv11(Seq#Index(ar, i_6)) == i_6
      );
      assume (forall o_3: Ref ::
        { invRecv11(o_3) }
        (0 <= invRecv11(o_3) && invRecv11(o_3) < len) && (NoPerm < FullPerm && qpRange11(o_3)) ==> Seq#Index(ar, invRecv11(o_3)) == o_3
      );

    // -- assume permission updates for field Ref__Integer_value
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        ((0 <= invRecv11(o_3) && invRecv11(o_3) < len) && (NoPerm < FullPerm && qpRange11(o_3)) ==> Seq#Index(ar, invRecv11(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - FullPerm) && (!((0 <= invRecv11(o_3) && invRecv11(o_3) < len) && (NoPerm < FullPerm && qpRange11(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    if (*) {
      if (0 <= i_7_1 && i_7_1 < len) {
        assert {:msg "  Postcondition of Ref__loop_main_23 might not hold. Assertion ar[i].Ref__Integer_value == 0 might not hold. (testZeroArray.vpr@66.12--66.86) [686]"}
          Heap[Seq#Index(ar, i_7_1), Ref__Integer_value] == 0;
      }
      assume false;
    }
    assume (forall i_8_1: int ::
      { Seq#Index(ar, i_8_1) }
      0 <= i_8_1 && i_8_1 < len ==> Heap[Seq#Index(ar, i_8_1), Ref__Integer_value] == 0
    );
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method Ref__loop_body_23
// ==================================================

procedure Ref__loop_body_23(diz: Ref, current_thread_id: int, len: int, ar: (Seq Ref), i: int) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var __flatten_2: Ref;
  var __flatten_3: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Assumptions about method arguments
    assume Heap[diz, $allocated];

  // -- Checked inhaling of precondition
    assume diz != null;
    assume state(Heap, Mask);
    assume current_thread_id >= 0;
    assume state(Heap, Mask);
    assume 0 <= i;
    assume i < len;
    assume state(Heap, Mask);
    assume Seq#Length(ar) == len;
    assume state(Heap, Mask);

    // -- Check definedness of acc(ar[i].Ref__Integer_value, write)
      assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@76.12--76.48) [687]"}
        i >= 0;
      assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@76.12--76.48) [688]"}
        i < Seq#Length(ar);
    perm := FullPerm;
    assume Seq#Index(ar, i) != null;
    Mask[Seq#Index(ar, i), Ref__Integer_value] := Mask[Seq#Index(ar, i), Ref__Integer_value] + perm;
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
    assume 0 <= i;
    assume i < len;
    assume state(PostHeap, PostMask);
    assume Seq#Length(ar) == len;
    assume state(PostHeap, PostMask);

    // -- Check definedness of acc(ar[i].Ref__Integer_value, write)
      assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@79.11--79.47) [689]"}
        i >= 0;
      assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@79.11--79.47) [690]"}
        i < Seq#Length(ar);
    perm := FullPerm;
    assume Seq#Index(ar, i) != null;
    PostMask[Seq#Index(ar, i), Ref__Integer_value] := PostMask[Seq#Index(ar, i), Ref__Integer_value] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);

    // -- Check definedness of ar[i].Ref__Integer_value == 0
      assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@80.11--80.40) [691]"}
        HasDirectPerm(PostMask, Seq#Index(ar, i), Ref__Integer_value);
      assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@80.11--80.40) [692]"}
        i >= 0;
      assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@80.11--80.40) [693]"}
        i < Seq#Length(ar);
    assume PostHeap[Seq#Index(ar, i), Ref__Integer_value] == 0;
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Assumptions about local variables
    assume Heap[__flatten_2, $allocated];

  // -- Translating statement: __flatten_2 := ar[i] -- testZeroArray.vpr@84.3--84.23

    // -- Check definedness of ar[i]
      assert {:msg "  Assignment might fail. Index ar[i] into ar might be negative. (testZeroArray.vpr@84.3--84.23) [694]"}
        i >= 0;
      assert {:msg "  Assignment might fail. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@84.3--84.23) [695]"}
        i < Seq#Length(ar);
    __flatten_2 := Seq#Index(ar, i);
    assume state(Heap, Mask);

  // -- Translating statement: __flatten_3 := 0 -- testZeroArray.vpr@85.3--85.19
    __flatten_3 := 0;
    assume state(Heap, Mask);

  // -- Translating statement: __flatten_2.Ref__Integer_value := __flatten_3 -- testZeroArray.vpr@86.3--86.48
    assert {:msg "  Assignment might fail. There might be insufficient permission to access __flatten_2.Ref__Integer_value (testZeroArray.vpr@86.3--86.48) [696]"}
      FullPerm == Mask[__flatten_2, Ref__Integer_value];
    Heap[__flatten_2, Ref__Integer_value] := __flatten_3;
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    assert {:msg "  Postcondition of Ref__loop_body_23 might not hold. Assertion 0 <= i might not hold. (testZeroArray.vpr@77.11--77.32) [697]"}
      0 <= i;
    assert {:msg "  Postcondition of Ref__loop_body_23 might not hold. Assertion i < len might not hold. (testZeroArray.vpr@77.11--77.32) [698]"}
      i < len;
    assert {:msg "  Postcondition of Ref__loop_body_23 might not hold. Assertion |ar| == len might not hold. (testZeroArray.vpr@78.11--78.22) [699]"}
      Seq#Length(ar) == len;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of Ref__loop_body_23 might not hold. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@79.11--79.47) [700]"}
        perm <= Mask[Seq#Index(ar, i), Ref__Integer_value];
    }
    Mask[Seq#Index(ar, i), Ref__Integer_value] := Mask[Seq#Index(ar, i), Ref__Integer_value] - perm;
    assert {:msg "  Postcondition of Ref__loop_body_23 might not hold. Assertion ar[i].Ref__Integer_value == 0 might not hold. (testZeroArray.vpr@80.11--80.40) [701]"}
      Heap[Seq#Index(ar, i), Ref__Integer_value] == 0;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method Ref__zero_array
// ==================================================

procedure Ref__zero_array(diz: Ref, current_thread_id: int, ar: (Seq Ref), len: int) returns ()
  modifies Heap, Mask;
{
  var j_8: int;
  var k_15: int;
  var i_9: int;
  var QPMask: MaskType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var i_10: int;
  var k_16: int;
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var j_2_1: int;
  var k_6: int;
  var ExhaleHeap: HeapType;
  var k_4_1: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Assumptions about method arguments
    assume Heap[diz, $allocated];

  // -- Checked inhaling of precondition
    assume diz != null;
    assume state(Heap, Mask);
    assume current_thread_id >= 0;
    assume state(Heap, Mask);
    assume Seq#Length(ar) == len;
    assume state(Heap, Mask);

    // -- Check definedness of (forall j: Int, k: Int :: { ar[j], ar[k] } 0 <= j && (j < len && (0 <= k && (k < len && j != k))) ==> ar[j] != ar[k])
      if (*) {
        if (0 <= j_8 && (j_8 < len && (0 <= k_15 && (k_15 < len && j_8 != k_15)))) {
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might be negative. (testZeroArray.vpr@93.12--93.104) [702]"}
            j_8 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[j] into ar might exceed sequence length. (testZeroArray.vpr@93.12--93.104) [703]"}
            j_8 < Seq#Length(ar);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@93.12--93.104) [704]"}
            k_15 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@93.12--93.104) [705]"}
            k_15 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall j_1_1: int, k_1_1: int ::
      { Seq#Index(ar, j_1_1), Seq#Index(ar, k_1_1) }
      0 <= j_1_1 && (j_1_1 < len && (0 <= k_1_1 && (k_1_1 < len && j_1_1 != k_1_1))) ==> Seq#Index(ar, j_1_1) != Seq#Index(ar, k_1_1)
    );
    assume state(Heap, Mask);

    // -- Check definedness of (forall i: Int :: { ar[i] } 0 <= i && i < len ==> acc(ar[i].Ref__Integer_value, write))
      if (*) {
        if (0 <= i_9 && i_9 < len) {
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@94.13--94.92) [706]"}
            i_9 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@94.13--94.92) [707]"}
            i_9 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@94.13--94.92) [708]"}
      (forall i_1: int, i_1_2: int ::

      (((i_1 != i_1_2 && (0 <= i_1 && i_1 < len)) && (0 <= i_1_2 && i_1_2 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_1) != Seq#Index(ar, i_1_2)
    );

    // -- Define Inverse Function
      assume (forall i_1: int ::
        { Seq#Index(ar, i_1) } { Seq#Index(ar, i_1) }
        (0 <= i_1 && i_1 < len) && NoPerm < FullPerm ==> qpRange12(Seq#Index(ar, i_1)) && invRecv12(Seq#Index(ar, i_1)) == i_1
      );
      assume (forall o_3: Ref ::
        { invRecv12(o_3) }
        ((0 <= invRecv12(o_3) && invRecv12(o_3) < len) && NoPerm < FullPerm) && qpRange12(o_3) ==> Seq#Index(ar, invRecv12(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall i_1: int ::
        { Seq#Index(ar, i_1) } { Seq#Index(ar, i_1) }
        0 <= i_1 && i_1 < len ==> Seq#Index(ar, i_1) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        (((0 <= invRecv12(o_3) && invRecv12(o_3) < len) && NoPerm < FullPerm) && qpRange12(o_3) ==> (NoPerm < FullPerm ==> Seq#Index(ar, invRecv12(o_3)) == o_3) && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] + FullPerm) && (!(((0 <= invRecv12(o_3) && invRecv12(o_3) < len) && NoPerm < FullPerm) && qpRange12(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
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
    assume Seq#Length(ar) == len;
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall i: Int :: { ar[i] } 0 <= i && i < len ==> acc(ar[i].Ref__Integer_value, write))
      if (*) {
        if (0 <= i_10 && i_10 < len) {
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might be negative. (testZeroArray.vpr@96.12--96.91) [709]"}
            i_10 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[i] into ar might exceed sequence length. (testZeroArray.vpr@96.12--96.91) [710]"}
            i_10 < Seq#Length(ar);
        }
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@96.12--96.91) [711]"}
      (forall i_3: int, i_3_1: int ::

      (((i_3 != i_3_1 && (0 <= i_3 && i_3 < len)) && (0 <= i_3_1 && i_3_1 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_3) != Seq#Index(ar, i_3_1)
    );

    // -- Define Inverse Function
      assume (forall i_3: int ::
        { Seq#Index(ar, i_3) } { Seq#Index(ar, i_3) }
        (0 <= i_3 && i_3 < len) && NoPerm < FullPerm ==> qpRange13(Seq#Index(ar, i_3)) && invRecv13(Seq#Index(ar, i_3)) == i_3
      );
      assume (forall o_3: Ref ::
        { invRecv13(o_3) }
        ((0 <= invRecv13(o_3) && invRecv13(o_3) < len) && NoPerm < FullPerm) && qpRange13(o_3) ==> Seq#Index(ar, invRecv13(o_3)) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall i_3: int ::
        { Seq#Index(ar, i_3) } { Seq#Index(ar, i_3) }
        0 <= i_3 && i_3 < len ==> Seq#Index(ar, i_3) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        (((0 <= invRecv13(o_3) && invRecv13(o_3) < len) && NoPerm < FullPerm) && qpRange13(o_3) ==> (NoPerm < FullPerm ==> Seq#Index(ar, invRecv13(o_3)) == o_3) && QPMask[o_3, Ref__Integer_value] == PostMask[o_3, Ref__Integer_value] + FullPerm) && (!(((0 <= invRecv13(o_3) && invRecv13(o_3) < len) && NoPerm < FullPerm) && qpRange13(o_3)) ==> QPMask[o_3, Ref__Integer_value] == PostMask[o_3, Ref__Integer_value])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall k: Int :: { ar[k] } 0 <= k && k < len ==> ar[k].Ref__Integer_value == 0)
      if (*) {
        if (0 <= k_16 && k_16 < len) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ar[k].Ref__Integer_value (testZeroArray.vpr@97.12--97.86) [712]"}
            HasDirectPerm(PostMask, Seq#Index(ar, k_16), Ref__Integer_value);
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might be negative. (testZeroArray.vpr@97.12--97.86) [713]"}
            k_16 >= 0;
          assert {:msg "  Contract might not be well-formed. Index ar[k] into ar might exceed sequence length. (testZeroArray.vpr@97.12--97.86) [714]"}
            k_16 < Seq#Length(ar);
        }
        assume false;
      }
    assume (forall k_3_1: int ::
      { Seq#Index(ar, k_3_1) }
      0 <= k_3_1 && k_3_1 < len ==> PostHeap[Seq#Index(ar, k_3_1), Ref__Integer_value] == 0
    );
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Translating statement: assert |ar| == len -- testZeroArray.vpr@99.3--99.21
    assert {:msg "  Assert might fail. Assertion |ar| == len might not hold. (testZeroArray.vpr@99.10--99.21) [715]"}
      Seq#Length(ar) == len;
    assume state(Heap, Mask);

  // -- Translating statement: Ref__loop_main_23(diz, current_thread_id, len, ar) -- testZeroArray.vpr@100.3--100.53
    PreCallHeap := Heap;
    PreCallMask := Mask;

    // -- Exhaling precondition
      assert {:msg "  The precondition of method Ref__loop_main_23 might not hold. Assertion diz != null might not hold. (testZeroArray.vpr@100.3--100.53) [716]"}
        diz != null;
      assert {:msg "  The precondition of method Ref__loop_main_23 might not hold. Assertion current_thread_id >= 0 might not hold. (testZeroArray.vpr@100.3--100.53) [717]"}
        current_thread_id >= 0;
      if (0 < len) {
        assert {:msg "  The precondition of method Ref__loop_main_23 might not hold. Assertion |ar| == len might not hold. (testZeroArray.vpr@100.3--100.53) [718]"}
          Seq#Length(ar) == len;
      }
      if (*) {
        if (0 <= j_2_1 && (j_2_1 < len && (0 <= k_6 && (k_6 < len && j_2_1 != k_6)))) {
          assert {:msg "  The precondition of method Ref__loop_main_23 might not hold. Assertion ar[j] != ar[k] might not hold. (testZeroArray.vpr@100.3--100.53) [719]"}
            Seq#Index(ar, j_2_1) != Seq#Index(ar, k_6);
        }
        assume false;
      }
      assume (forall j_3_1: int, k_7_1: int ::
        { Seq#Index(ar, j_3_1), Seq#Index(ar, k_7_1) }
        0 <= j_3_1 && (j_3_1 < len && (0 <= k_7_1 && (k_7_1 < len && j_3_1 != k_7_1))) ==> Seq#Index(ar, j_3_1) != Seq#Index(ar, k_7_1)
      );
      havoc QPMask;

      // -- check that the permission amount is positive


      // -- check if receiver ar[i] is injective
        assert {:msg "  The precondition of method Ref__loop_main_23 might not hold. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@100.3--100.53) [720]"}
          (forall i_5: int, i_5_1: int ::
          { neverTriggered15(i_5), neverTriggered15(i_5_1) }
          (((i_5 != i_5_1 && (0 <= i_5 && i_5 < len)) && (0 <= i_5_1 && i_5_1 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_5) != Seq#Index(ar, i_5_1)
        );

      // -- check if sufficient permission is held
        assert {:msg "  The precondition of method Ref__loop_main_23 might not hold. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@100.3--100.53) [721]"}
          (forall i_5: int ::
          { Seq#Index(ar, i_5) } { Seq#Index(ar, i_5) }
          0 <= i_5 && i_5 < len ==> Mask[Seq#Index(ar, i_5), Ref__Integer_value] >= FullPerm
        );

      // -- assumptions for inverse of receiver ar[i]
        assume (forall i_5: int ::
          { Seq#Index(ar, i_5) } { Seq#Index(ar, i_5) }
          (0 <= i_5 && i_5 < len) && NoPerm < FullPerm ==> qpRange15(Seq#Index(ar, i_5)) && invRecv15(Seq#Index(ar, i_5)) == i_5
        );
        assume (forall o_3: Ref ::
          { invRecv15(o_3) }
          (0 <= invRecv15(o_3) && invRecv15(o_3) < len) && (NoPerm < FullPerm && qpRange15(o_3)) ==> Seq#Index(ar, invRecv15(o_3)) == o_3
        );

      // -- assume permission updates for field Ref__Integer_value
        assume (forall o_3: Ref ::
          { QPMask[o_3, Ref__Integer_value] }
          ((0 <= invRecv15(o_3) && invRecv15(o_3) < len) && (NoPerm < FullPerm && qpRange15(o_3)) ==> Seq#Index(ar, invRecv15(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - FullPerm) && (!((0 <= invRecv15(o_3) && invRecv15(o_3) < len) && (NoPerm < FullPerm && qpRange15(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
        );

      // -- assume permission updates for independent locations
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { QPMask[o_3, f_5] }
          f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      // Finish exhale
      havoc ExhaleHeap;
      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
      Heap := ExhaleHeap;

    // -- Inhaling postcondition
      if (0 < len) {
        assume Seq#Length(ar) == len;
      }
      havoc QPMask;
      assert {:msg "  Method call might fail. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@100.3--100.53) [722]"}
        (forall i_6: int, i_6_1: int ::

        (((i_6 != i_6_1 && (0 <= i_6 && i_6 < len)) && (0 <= i_6_1 && i_6_1 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_6) != Seq#Index(ar, i_6_1)
      );

      // -- Define Inverse Function
        assume (forall i_6: int ::
          { Seq#Index(ar, i_6) } { Seq#Index(ar, i_6) }
          (0 <= i_6 && i_6 < len) && NoPerm < FullPerm ==> qpRange16(Seq#Index(ar, i_6)) && invRecv16(Seq#Index(ar, i_6)) == i_6
        );
        assume (forall o_3: Ref ::
          { invRecv16(o_3) }
          ((0 <= invRecv16(o_3) && invRecv16(o_3) < len) && NoPerm < FullPerm) && qpRange16(o_3) ==> Seq#Index(ar, invRecv16(o_3)) == o_3
        );

      // -- Assume set of fields is nonNull
        assume (forall i_6: int ::
          { Seq#Index(ar, i_6) } { Seq#Index(ar, i_6) }
          0 <= i_6 && i_6 < len ==> Seq#Index(ar, i_6) != null
        );

      // -- Define permissions
        assume (forall o_3: Ref ::
          { QPMask[o_3, Ref__Integer_value] }
          (((0 <= invRecv16(o_3) && invRecv16(o_3) < len) && NoPerm < FullPerm) && qpRange16(o_3) ==> (NoPerm < FullPerm ==> Seq#Index(ar, invRecv16(o_3)) == o_3) && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] + FullPerm) && (!(((0 <= invRecv16(o_3) && invRecv16(o_3) < len) && NoPerm < FullPerm) && qpRange16(o_3)) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
        );
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
          f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      assume (forall i_7_1: int ::
        { Seq#Index(ar, i_7_1) }
        0 <= i_7_1 && i_7_1 < len ==> Heap[Seq#Index(ar, i_7_1), Ref__Integer_value] == 0
      );
      assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    assert {:msg "  Postcondition of Ref__zero_array might not hold. Assertion |ar| == len might not hold. (testZeroArray.vpr@95.11--95.22) [723]"}
      Seq#Length(ar) == len;
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver ar[i] is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource ar[i].Ref__Integer_value might not be injective. (testZeroArray.vpr@96.12--96.91) [724]"}
        (forall i_4: int, i_4_1: int ::
        { neverTriggered14(i_4), neverTriggered14(i_4_1) }
        (((i_4 != i_4_1 && (0 <= i_4 && i_4 < len)) && (0 <= i_4_1 && i_4_1 < len)) && NoPerm < FullPerm) && NoPerm < FullPerm ==> Seq#Index(ar, i_4) != Seq#Index(ar, i_4_1)
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of Ref__zero_array might not hold. There might be insufficient permission to access ar[i].Ref__Integer_value (testZeroArray.vpr@96.12--96.91) [725]"}
        (forall i_4: int ::
        { Seq#Index(ar, i_4) } { Seq#Index(ar, i_4) }
        0 <= i_4 && i_4 < len ==> Mask[Seq#Index(ar, i_4), Ref__Integer_value] >= FullPerm
      );

    // -- assumptions for inverse of receiver ar[i]
      assume (forall i_4: int ::
        { Seq#Index(ar, i_4) } { Seq#Index(ar, i_4) }
        (0 <= i_4 && i_4 < len) && NoPerm < FullPerm ==> qpRange14(Seq#Index(ar, i_4)) && invRecv14(Seq#Index(ar, i_4)) == i_4
      );
      assume (forall o_3: Ref ::
        { invRecv14(o_3) }
        (0 <= invRecv14(o_3) && invRecv14(o_3) < len) && (NoPerm < FullPerm && qpRange14(o_3)) ==> Seq#Index(ar, invRecv14(o_3)) == o_3
      );

    // -- assume permission updates for field Ref__Integer_value
      assume (forall o_3: Ref ::
        { QPMask[o_3, Ref__Integer_value] }
        ((0 <= invRecv14(o_3) && invRecv14(o_3) < len) && (NoPerm < FullPerm && qpRange14(o_3)) ==> Seq#Index(ar, invRecv14(o_3)) == o_3 && QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value] - FullPerm) && (!((0 <= invRecv14(o_3) && invRecv14(o_3) < len) && (NoPerm < FullPerm && qpRange14(o_3))) ==> QPMask[o_3, Ref__Integer_value] == Mask[o_3, Ref__Integer_value])
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != Ref__Integer_value ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    if (*) {
      if (0 <= k_4_1 && k_4_1 < len) {
        assert {:msg "  Postcondition of Ref__zero_array might not hold. Assertion ar[k].Ref__Integer_value == 0 might not hold. (testZeroArray.vpr@97.12--97.86) [726]"}
          Heap[Seq#Index(ar, k_4_1), Ref__Integer_value] == 0;
      }
      assume false;
    }
    assume (forall k_5_1: int ::
      { Seq#Index(ar, k_5_1) }
      0 <= k_5_1 && k_5_1 < len ==> Heap[Seq#Index(ar, k_5_1), Ref__Integer_value] == 0
    );
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}
