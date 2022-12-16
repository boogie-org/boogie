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
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 4: contentNodes
// - height 3: lengthNodes
// - height 2: content
// - height 1: length
// - height 0: peek
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

const unique data: Field NormalField int;
axiom !IsPredicateField(data);
axiom !IsWandField(data);
const unique next: Field NormalField Ref;
axiom !IsPredicateField(next);
axiom !IsWandField(next);
const unique head: Field NormalField Ref;
axiom !IsPredicateField(head);
axiom !IsWandField(head);
const unique held: Field NormalField int;
axiom !IsPredicateField(held);
axiom !IsWandField(held);
const unique changed: Field NormalField bool;
axiom !IsPredicateField(changed);
axiom !IsWandField(changed);

// ==================================================
// Translation of function contentNodes
// ==================================================

// Uninterpreted function definitions
function  contentNodes(Heap: HeapType, this: Ref, end: Ref): Seq int;
function  contentNodes'(Heap: HeapType, this: Ref, end: Ref): Seq int;
axiom (forall Heap: HeapType, this: Ref, end: Ref ::
  { contentNodes(Heap, this, end) }
  contentNodes(Heap, this, end) == contentNodes'(Heap, this, end) && dummyFunction(contentNodes#triggerStateless(this, end))
);
axiom (forall Heap: HeapType, this: Ref, end: Ref ::
  { contentNodes'(Heap, this, end) }
  dummyFunction(contentNodes#triggerStateless(this, end))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), contentNodes(Heap, this, end) } { state(Heap, Mask), contentNodes#triggerStateless(this, end), lseg#trigger(Heap, lseg(this, end)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 4 ==> contentNodes(Heap, this, end) == (if this == end then (Seq#Empty(): Seq int) else Seq#Append(Seq#Singleton(Heap[this, data]), contentNodes'(Heap, Heap[this, next], end)))
);

// Framing axioms
function  contentNodes#frame(frame: FrameType, this: Ref, end: Ref): Seq int;
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), contentNodes'(Heap, this, end) } { state(Heap, Mask), contentNodes#triggerStateless(this, end), lseg#trigger(Heap, lseg(this, end)) }
  state(Heap, Mask) ==> contentNodes'(Heap, this, end) == contentNodes#frame(Heap[null, lseg(this, end)], this, end)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), contentNodes'(Heap, this, end) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 4 || contentNodes#trigger(Heap[null, lseg(this, end)], this, end)) ==> this == end ==> Seq#Equal(contentNodes'(Heap, this, end), (Seq#Empty(): Seq int))
);
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), contentNodes'(Heap, this, end) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 4 || contentNodes#trigger(Heap[null, lseg(this, end)], this, end)) ==> this != end ==> 0 < Seq#Length(contentNodes'(Heap, this, end)) && Seq#Index(contentNodes'(Heap, this, end), 0) == Heap[this, data]
);
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), contentNodes'(Heap, this, end) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 4 || contentNodes#trigger(Heap[null, lseg(this, end)], this, end)) ==> (forall i: int, j: int ::
    { Seq#Index(contentNodes'(Heap, this, end), i), Seq#Index(contentNodes'(Heap, this, end), j) }
    0 <= i && (i < j && j < Seq#Length(contentNodes'(Heap, this, end))) ==> Seq#Index(contentNodes'(Heap, this, end), i) <= Seq#Index(contentNodes'(Heap, this, end), j)
  )
);

// Trigger function (controlling recursive postconditions)
function  contentNodes#trigger(frame: FrameType, this: Ref, end: Ref): bool;

// State-independent trigger function
function  contentNodes#triggerStateless(this: Ref, end: Ref): Seq int;

// Check contract well-formedness and postcondition
procedure contentNodes#definedness(this: Ref, end: Ref) returns (Result: (Seq int))
  modifies Heap, Mask;
{
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var Unfolding1Heap: HeapType;
  var Unfolding1Mask: MaskType;
  var newPMask: PMaskType;
  var ExhaleHeap: HeapType;
  var i_1: int;
  var j_1: int;
  var i_2: int;
  var j_2: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[this, $allocated];
    assume Heap[end, $allocated];
    assume AssumeFunctionsAbove == 4;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, lseg(this, end)] := Mask[null, lseg(this, end)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of (this == end ? Seq[Int]() : (unfolding acc(lseg(this, end), write) in Seq(this.data) ++ contentNodes(this.next, end)))
      if (this == end) {
      } else {
        UnfoldingHeap := Heap;
        UnfoldingMask := Mask;
        assume lseg#trigger(UnfoldingHeap, lseg(this, end));
        assume UnfoldingHeap[null, lseg(this, end)] == FrameFragment((if this != end then CombineFrames(FrameFragment(UnfoldingHeap[this, data]), CombineFrames(FrameFragment(UnfoldingHeap[this, next]), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)])) else EmptyFrame));
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Function might not be well-formed. There might be insufficient permission to access lseg(this, end) (linked-list-predicates.vpr@18.1--29.2) [1001]"}
            perm <= UnfoldingMask[null, lseg(this, end)];
        }
        UnfoldingMask[null, lseg(this, end)] := UnfoldingMask[null, lseg(this, end)] - perm;
        if (this != end) {
          perm := FullPerm;
          assume this != null;
          UnfoldingMask[this, data] := UnfoldingMask[this, data] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          assume this != null;
          UnfoldingMask[this, next] := UnfoldingMask[this, next] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(this, end), UnfoldingHeap[null, lseg(this, end)], lseg(UnfoldingHeap[this, next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)]);
          assume state(UnfoldingHeap, UnfoldingMask);
          
          // -- Execute unfolding (for extra information)
            Unfolding1Heap := UnfoldingHeap;
            Unfolding1Mask := UnfoldingMask;
            assume lseg#trigger(Unfolding1Heap, lseg(Unfolding1Heap[this, next], end));
            assume Unfolding1Heap[null, lseg(Unfolding1Heap[this, next], end)] == FrameFragment((if Unfolding1Heap[this, next] != end then CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, next], data]), CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, next], next]), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)])) else EmptyFrame));
            perm := FullPerm;
            Unfolding1Mask[null, lseg(Unfolding1Heap[this, next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[this, next], end)] - perm;
            if (Unfolding1Heap[this, next] != end) {
              perm := FullPerm;
              assume Unfolding1Heap[this, next] != null;
              Unfolding1Mask[Unfolding1Heap[this, next], data] := Unfolding1Mask[Unfolding1Heap[this, next], data] + perm;
              assume state(Unfolding1Heap, Unfolding1Mask);
              perm := FullPerm;
              assume Unfolding1Heap[this, next] != null;
              Unfolding1Mask[Unfolding1Heap[this, next], next] := Unfolding1Mask[Unfolding1Heap[this, next], next] + perm;
              assume state(Unfolding1Heap, Unfolding1Mask);
              perm := FullPerm;
              Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(Unfolding1Heap[this, next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[this, next], end)], lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)]);
              assume state(Unfolding1Heap, Unfolding1Mask);
              assume Unfolding1Heap[Unfolding1Heap[this, next], next] != end ==> Unfolding1Heap[Unfolding1Heap[this, next], data] <= Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], data];
              
              // -- Free assumptions (inhale module)
                if (Unfolding1Heap[Unfolding1Heap[this, next], next] != end) {
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][Unfolding1Heap[Unfolding1Heap[this, next], next], data] := true;
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][Unfolding1Heap[Unfolding1Heap[this, next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_3: Ref, f_7: (Field A B) ::
                    { newPMask[o_3, f_7] }
                    Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][o_3, f_7] || Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)][o_3, f_7] ==> newPMask[o_3, f_7]
                  );
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := newPMask;
                }
                assume state(Unfolding1Heap, Unfolding1Mask);
            }
            assume state(Unfolding1Heap, Unfolding1Mask);
          assume UnfoldingHeap[this, next] != end ==> UnfoldingHeap[this, data] <= UnfoldingHeap[UnfoldingHeap[this, next], data];
          
          // -- Free assumptions (inhale module)
            if (UnfoldingHeap[this, next] != end) {
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][UnfoldingHeap[this, next], data] := true;
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][UnfoldingHeap[this, next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_4: Ref, f_8: (Field A B) ::
                { newPMask[o_4, f_8] }
                UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][o_4, f_8] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][o_4, f_8] ==> newPMask[o_4, f_8]
              );
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)] := newPMask;
            }
            assume state(UnfoldingHeap, UnfoldingMask);
        }
        assume state(UnfoldingHeap, UnfoldingMask);
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.data (linked-list-predicates.vpr@18.1--29.2) [1002]"}
          HasDirectPerm(UnfoldingMask, this, data);
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.next (linked-list-predicates.vpr@18.1--29.2) [1003]"}
          HasDirectPerm(UnfoldingMask, this, next);
        if (*) {
          // Exhale precondition of function application
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this.next, end) (linked-list-predicates.vpr@27.39--27.67) [1004]"}
              perm <= UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)];
          }
          UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(UnfoldingHeap, ExhaleHeap, UnfoldingMask);
          UnfoldingHeap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume contentNodes#trigger(UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)], UnfoldingHeap[this, next], end);
        }
        
        // -- Free assumptions (exp module)
          if (this != end) {
            Heap[null, lseg#sm(this, end)][this, data] := true;
            Heap[null, lseg#sm(this, end)][this, next] := true;
            havoc newPMask;
            assume (forall <A, B> o_5: Ref, f_9: (Field A B) ::
              { newPMask[o_5, f_9] }
              Heap[null, lseg#sm(this, end)][o_5, f_9] || Heap[null, lseg#sm(Heap[this, next], end)][o_5, f_9] ==> newPMask[o_5, f_9]
            );
            Heap[null, lseg#sm(this, end)] := newPMask;
          }
          assume state(Heap, Mask);
      }
  
  // -- Translate function body
    Result := (if this == end then (Seq#Empty(): Seq int) else Seq#Append(Seq#Singleton(Heap[this, data]), contentNodes(Heap, Heap[this, next], end)));
  
  // -- Exhaling postcondition (with checking)
    if (this == end) {
      assert {:msg "  Postcondition of contentNodes might not hold. Assertion result == Seq[Int]() might not hold. (linked-list-predicates.vpr@20.12--20.48) [1005]"}
        Seq#Equal(Result, (Seq#Empty(): Seq int));
    }
    if (this != end) {
      assert {:msg "  Postcondition of contentNodes might not hold. Assertion 0 < |result| might not hold. (linked-list-predicates.vpr@21.12--22.87) [1006]"}
        0 < Seq#Length(Result);
      
      // -- Check definedness of result[0] == (unfolding acc(lseg(this, end), write) in this.data)
        assert {:msg "  Contract might not be well-formed. Index result[0] into result might exceed sequence length. (linked-list-predicates.vpr@21.12--22.87) [1007]"}
          0 < Seq#Length(Result);
        UnfoldingHeap := Heap;
        UnfoldingMask := Mask;
        assume lseg#trigger(UnfoldingHeap, lseg(this, end));
        assume UnfoldingHeap[null, lseg(this, end)] == FrameFragment((if this != end then CombineFrames(FrameFragment(UnfoldingHeap[this, data]), CombineFrames(FrameFragment(UnfoldingHeap[this, next]), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)])) else EmptyFrame));
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access lseg(this, end) (linked-list-predicates.vpr@21.12--22.87) [1008]"}
            perm <= UnfoldingMask[null, lseg(this, end)];
        }
        UnfoldingMask[null, lseg(this, end)] := UnfoldingMask[null, lseg(this, end)] - perm;
        if (this != end) {
          perm := FullPerm;
          assume this != null;
          UnfoldingMask[this, data] := UnfoldingMask[this, data] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          assume this != null;
          UnfoldingMask[this, next] := UnfoldingMask[this, next] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(this, end), UnfoldingHeap[null, lseg(this, end)], lseg(UnfoldingHeap[this, next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)]);
          assume state(UnfoldingHeap, UnfoldingMask);
          
          // -- Execute unfolding (for extra information)
            Unfolding1Heap := UnfoldingHeap;
            Unfolding1Mask := UnfoldingMask;
            assume lseg#trigger(Unfolding1Heap, lseg(Unfolding1Heap[this, next], end));
            assume Unfolding1Heap[null, lseg(Unfolding1Heap[this, next], end)] == FrameFragment((if Unfolding1Heap[this, next] != end then CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, next], data]), CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, next], next]), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)])) else EmptyFrame));
            perm := FullPerm;
            Unfolding1Mask[null, lseg(Unfolding1Heap[this, next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[this, next], end)] - perm;
            if (Unfolding1Heap[this, next] != end) {
              perm := FullPerm;
              assume Unfolding1Heap[this, next] != null;
              Unfolding1Mask[Unfolding1Heap[this, next], data] := Unfolding1Mask[Unfolding1Heap[this, next], data] + perm;
              assume state(Unfolding1Heap, Unfolding1Mask);
              perm := FullPerm;
              assume Unfolding1Heap[this, next] != null;
              Unfolding1Mask[Unfolding1Heap[this, next], next] := Unfolding1Mask[Unfolding1Heap[this, next], next] + perm;
              assume state(Unfolding1Heap, Unfolding1Mask);
              perm := FullPerm;
              Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(Unfolding1Heap[this, next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[this, next], end)], lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)]);
              assume state(Unfolding1Heap, Unfolding1Mask);
              assume Unfolding1Heap[Unfolding1Heap[this, next], next] != end ==> Unfolding1Heap[Unfolding1Heap[this, next], data] <= Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], data];
              
              // -- Free assumptions (inhale module)
                if (Unfolding1Heap[Unfolding1Heap[this, next], next] != end) {
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][Unfolding1Heap[Unfolding1Heap[this, next], next], data] := true;
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][Unfolding1Heap[Unfolding1Heap[this, next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_6: Ref, f_10: (Field A B) ::
                    { newPMask[o_6, f_10] }
                    Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][o_6, f_10] || Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)][o_6, f_10] ==> newPMask[o_6, f_10]
                  );
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := newPMask;
                }
                assume state(Unfolding1Heap, Unfolding1Mask);
            }
            assume state(Unfolding1Heap, Unfolding1Mask);
          assume UnfoldingHeap[this, next] != end ==> UnfoldingHeap[this, data] <= UnfoldingHeap[UnfoldingHeap[this, next], data];
          
          // -- Free assumptions (inhale module)
            if (UnfoldingHeap[this, next] != end) {
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][UnfoldingHeap[this, next], data] := true;
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][UnfoldingHeap[this, next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_7: Ref, f_11: (Field A B) ::
                { newPMask[o_7, f_11] }
                UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][o_7, f_11] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][o_7, f_11] ==> newPMask[o_7, f_11]
              );
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)] := newPMask;
            }
            assume state(UnfoldingHeap, UnfoldingMask);
        }
        assume state(UnfoldingHeap, UnfoldingMask);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.data (linked-list-predicates.vpr@21.12--22.87) [1009]"}
          HasDirectPerm(UnfoldingMask, this, data);
        
        // -- Free assumptions (exp module)
          if (this != end) {
            Heap[null, lseg#sm(this, end)][this, data] := true;
            Heap[null, lseg#sm(this, end)][this, next] := true;
            havoc newPMask;
            assume (forall <A, B> o_8: Ref, f_12: (Field A B) ::
              { newPMask[o_8, f_12] }
              Heap[null, lseg#sm(this, end)][o_8, f_12] || Heap[null, lseg#sm(Heap[this, next], end)][o_8, f_12] ==> newPMask[o_8, f_12]
            );
            Heap[null, lseg#sm(this, end)] := newPMask;
          }
          assume state(Heap, Mask);
        
        // -- Free assumptions (exp module)
          if (this != end) {
            Heap[null, lseg#sm(this, end)][this, data] := true;
            Heap[null, lseg#sm(this, end)][this, next] := true;
            havoc newPMask;
            assume (forall <A, B> o_9: Ref, f_13: (Field A B) ::
              { newPMask[o_9, f_13] }
              Heap[null, lseg#sm(this, end)][o_9, f_13] || Heap[null, lseg#sm(Heap[this, next], end)][o_9, f_13] ==> newPMask[o_9, f_13]
            );
            Heap[null, lseg#sm(this, end)] := newPMask;
          }
          assume state(Heap, Mask);
      assert {:msg "  Postcondition of contentNodes might not hold. Assertion result[0] == (unfolding acc(lseg(this, end), write) in this.data) might not hold. (linked-list-predicates.vpr@21.12--22.87) [1010]"}
        Seq#Index(Result, 0) == Heap[this, data];
      
      // -- Free assumptions (exhale module)
        if (this != end) {
          Heap[null, lseg#sm(this, end)][this, data] := true;
          Heap[null, lseg#sm(this, end)][this, next] := true;
          havoc newPMask;
          assume (forall <A, B> o_10: Ref, f_14: (Field A B) ::
            { newPMask[o_10, f_14] }
            Heap[null, lseg#sm(this, end)][o_10, f_14] || Heap[null, lseg#sm(Heap[this, next], end)][o_10, f_14] ==> newPMask[o_10, f_14]
          );
          Heap[null, lseg#sm(this, end)] := newPMask;
        }
        assume state(Heap, Mask);
    }
    
    // -- Check definedness of (forall i: Int, j: Int :: { result[i], result[j] } 0 <= i && (i < j && j < |result|) ==> result[i] <= result[j])
      if (*) {
        if (0 <= i_1 && (i_1 < j_1 && j_1 < Seq#Length(Result))) {
          assert {:msg "  Contract might not be well-formed. Index result[i] into result might be negative. (linked-list-predicates.vpr@23.12--23.95) [1011]"}
            i_1 >= 0;
          assert {:msg "  Contract might not be well-formed. Index result[i] into result might exceed sequence length. (linked-list-predicates.vpr@23.12--23.95) [1012]"}
            i_1 < Seq#Length(Result);
          assert {:msg "  Contract might not be well-formed. Index result[j] into result might be negative. (linked-list-predicates.vpr@23.12--23.95) [1013]"}
            j_1 >= 0;
          assert {:msg "  Contract might not be well-formed. Index result[j] into result might exceed sequence length. (linked-list-predicates.vpr@23.12--23.95) [1014]"}
            j_1 < Seq#Length(Result);
        }
        assume false;
      }
    if (*) {
      if (0 <= i_2 && (i_2 < j_2 && j_2 < Seq#Length(Result))) {
        assert {:msg "  Postcondition of contentNodes might not hold. Assertion result[i] <= result[j] might not hold. (linked-list-predicates.vpr@23.12--23.95) [1015]"}
          Seq#Index(Result, i_2) <= Seq#Index(Result, j_2);
      }
      assume false;
    }
    assume (forall i_3_1: int, j_3_1: int ::
      { Seq#Index(Result, i_3_1), Seq#Index(Result, j_3_1) }
      0 <= i_3_1 && (i_3_1 < j_3_1 && j_3_1 < Seq#Length(Result)) ==> Seq#Index(Result, i_3_1) <= Seq#Index(Result, j_3_1)
    );
}

// ==================================================
// Translation of function lengthNodes
// ==================================================

// Uninterpreted function definitions
function  lengthNodes(Heap: HeapType, this: Ref, end: Ref): int;
function  lengthNodes'(Heap: HeapType, this: Ref, end: Ref): int;
axiom (forall Heap: HeapType, this: Ref, end: Ref ::
  { lengthNodes(Heap, this, end) }
  lengthNodes(Heap, this, end) == lengthNodes'(Heap, this, end) && dummyFunction(lengthNodes#triggerStateless(this, end))
);
axiom (forall Heap: HeapType, this: Ref, end: Ref ::
  { lengthNodes'(Heap, this, end) }
  dummyFunction(lengthNodes#triggerStateless(this, end))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), lengthNodes(Heap, this, end) } { state(Heap, Mask), lengthNodes#triggerStateless(this, end), lseg#trigger(Heap, lseg(this, end)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 3 ==> lengthNodes(Heap, this, end) == (if this == end then 0 else 1 + lengthNodes'(Heap, Heap[this, next], end))
);

// Framing axioms
function  lengthNodes#frame(frame: FrameType, this: Ref, end: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), lengthNodes'(Heap, this, end) } { state(Heap, Mask), lengthNodes#triggerStateless(this, end), lseg#trigger(Heap, lseg(this, end)) }
  state(Heap, Mask) ==> lengthNodes'(Heap, this, end) == lengthNodes#frame(Heap[null, lseg(this, end)], this, end)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref, end: Ref ::
  { state(Heap, Mask), lengthNodes'(Heap, this, end) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 3 || lengthNodes#trigger(Heap[null, lseg(this, end)], this, end)) ==> lengthNodes'(Heap, this, end) == Seq#Length(contentNodes(Heap, this, end))
);

// Trigger function (controlling recursive postconditions)
function  lengthNodes#trigger(frame: FrameType, this: Ref, end: Ref): bool;

// State-independent trigger function
function  lengthNodes#triggerStateless(this: Ref, end: Ref): int;

// Check contract well-formedness and postcondition
procedure lengthNodes#definedness(this: Ref, end: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var Unfolding1Heap: HeapType;
  var Unfolding1Mask: MaskType;
  var newPMask: PMaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[this, $allocated];
    assume Heap[end, $allocated];
    assume AssumeFunctionsAbove == 3;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, lseg(this, end)] := Mask[null, lseg(this, end)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of (unfolding acc(lseg(this, end), write) in (this == end ? 0 : 1 + lengthNodes(this.next, end)))
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume lseg#trigger(UnfoldingHeap, lseg(this, end));
      assume UnfoldingHeap[null, lseg(this, end)] == FrameFragment((if this != end then CombineFrames(FrameFragment(UnfoldingHeap[this, data]), CombineFrames(FrameFragment(UnfoldingHeap[this, next]), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)])) else EmptyFrame));
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access lseg(this, end) (linked-list-predicates.vpr@32.1--39.2) [1016]"}
          perm <= UnfoldingMask[null, lseg(this, end)];
      }
      UnfoldingMask[null, lseg(this, end)] := UnfoldingMask[null, lseg(this, end)] - perm;
      if (this != end) {
        perm := FullPerm;
        assume this != null;
        UnfoldingMask[this, data] := UnfoldingMask[this, data] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
        perm := FullPerm;
        assume this != null;
        UnfoldingMask[this, next] := UnfoldingMask[this, next] + perm;
        assume state(UnfoldingHeap, UnfoldingMask);
        perm := FullPerm;
        UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] + perm;
        
        // -- Extra unfolding of predicate
          assume InsidePredicate(lseg(this, end), UnfoldingHeap[null, lseg(this, end)], lseg(UnfoldingHeap[this, next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)]);
        assume state(UnfoldingHeap, UnfoldingMask);
        
        // -- Execute unfolding (for extra information)
          Unfolding1Heap := UnfoldingHeap;
          Unfolding1Mask := UnfoldingMask;
          assume lseg#trigger(Unfolding1Heap, lseg(Unfolding1Heap[this, next], end));
          assume Unfolding1Heap[null, lseg(Unfolding1Heap[this, next], end)] == FrameFragment((if Unfolding1Heap[this, next] != end then CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, next], data]), CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, next], next]), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)])) else EmptyFrame));
          perm := FullPerm;
          Unfolding1Mask[null, lseg(Unfolding1Heap[this, next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[this, next], end)] - perm;
          if (Unfolding1Heap[this, next] != end) {
            perm := FullPerm;
            assume Unfolding1Heap[this, next] != null;
            Unfolding1Mask[Unfolding1Heap[this, next], data] := Unfolding1Mask[Unfolding1Heap[this, next], data] + perm;
            assume state(Unfolding1Heap, Unfolding1Mask);
            perm := FullPerm;
            assume Unfolding1Heap[this, next] != null;
            Unfolding1Mask[Unfolding1Heap[this, next], next] := Unfolding1Mask[Unfolding1Heap[this, next], next] + perm;
            assume state(Unfolding1Heap, Unfolding1Mask);
            perm := FullPerm;
            Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] + perm;
            
            // -- Extra unfolding of predicate
              assume InsidePredicate(lseg(Unfolding1Heap[this, next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[this, next], end)], lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)]);
            assume state(Unfolding1Heap, Unfolding1Mask);
            assume Unfolding1Heap[Unfolding1Heap[this, next], next] != end ==> Unfolding1Heap[Unfolding1Heap[this, next], data] <= Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], data];
            
            // -- Free assumptions (inhale module)
              if (Unfolding1Heap[Unfolding1Heap[this, next], next] != end) {
                Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][Unfolding1Heap[Unfolding1Heap[this, next], next], data] := true;
                Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][Unfolding1Heap[Unfolding1Heap[this, next], next], next] := true;
                havoc newPMask;
                assume (forall <A, B> o_11: Ref, f_15: (Field A B) ::
                  { newPMask[o_11, f_15] }
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)][o_11, f_15] || Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)][o_11, f_15] ==> newPMask[o_11, f_15]
                );
                Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := newPMask;
              }
              assume state(Unfolding1Heap, Unfolding1Mask);
          }
          assume state(Unfolding1Heap, Unfolding1Mask);
        assume UnfoldingHeap[this, next] != end ==> UnfoldingHeap[this, data] <= UnfoldingHeap[UnfoldingHeap[this, next], data];
        
        // -- Free assumptions (inhale module)
          if (UnfoldingHeap[this, next] != end) {
            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][UnfoldingHeap[this, next], data] := true;
            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][UnfoldingHeap[this, next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_12: Ref, f_16: (Field A B) ::
              { newPMask[o_12, f_16] }
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)][o_12, f_16] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][o_12, f_16] ==> newPMask[o_12, f_16]
            );
            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, next], end)] := newPMask;
          }
          assume state(UnfoldingHeap, UnfoldingMask);
      }
      assume state(UnfoldingHeap, UnfoldingMask);
      if (this == end) {
      } else {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.next (linked-list-predicates.vpr@32.1--39.2) [1017]"}
          HasDirectPerm(UnfoldingMask, this, next);
        if (*) {
          // Exhale precondition of function application
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function lengthNodes might not hold. There might be insufficient permission to access lseg(this.next, end) (linked-list-predicates.vpr@38.21--38.48) [1018]"}
              perm <= UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)];
          }
          UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(UnfoldingHeap, ExhaleHeap, UnfoldingMask);
          UnfoldingHeap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume lengthNodes#trigger(UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)], UnfoldingHeap[this, next], end);
        }
      }
      
      // -- Free assumptions (exp module)
        if (this != end) {
          Heap[null, lseg#sm(this, end)][this, data] := true;
          Heap[null, lseg#sm(this, end)][this, next] := true;
          havoc newPMask;
          assume (forall <A, B> o_13: Ref, f_17: (Field A B) ::
            { newPMask[o_13, f_17] }
            Heap[null, lseg#sm(this, end)][o_13, f_17] || Heap[null, lseg#sm(Heap[this, next], end)][o_13, f_17] ==> newPMask[o_13, f_17]
          );
          Heap[null, lseg#sm(this, end)] := newPMask;
        }
        assume state(Heap, Mask);
  
  // -- Translate function body
    Result := (if this == end then 0 else 1 + lengthNodes(Heap, Heap[this, next], end));
  
  // -- Exhaling postcondition (with checking)
    
    // -- Check definedness of result == |contentNodes(this, end)|
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this, end) (linked-list-predicates.vpr@34.23--34.46) [1019]"}
            perm <= Mask[null, lseg(this, end)];
        }
        Mask[null, lseg(this, end)] := Mask[null, lseg(this, end)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assert {:msg "  Postcondition of lengthNodes might not hold. Assertion result == |contentNodes(this, end)| might not hold. (linked-list-predicates.vpr@34.12--34.47) [1020]"}
      Result == Seq#Length(contentNodes(Heap, this, end));
}

// ==================================================
// Translation of function content
// ==================================================

// Uninterpreted function definitions
function  content(Heap: HeapType, this: Ref): Seq int;
function  content'(Heap: HeapType, this: Ref): Seq int;
axiom (forall Heap: HeapType, this: Ref ::
  { content(Heap, this) }
  content(Heap, this) == content'(Heap, this) && dummyFunction(content#triggerStateless(this))
);
axiom (forall Heap: HeapType, this: Ref ::
  { content'(Heap, this) }
  dummyFunction(content#triggerStateless(this))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), content(Heap, this) } { state(Heap, Mask), content#triggerStateless(this), List#trigger(Heap, List(this)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 2 ==> content(Heap, this) == contentNodes(Heap, Heap[this, head], null)
);

// Framing axioms
function  content#frame(frame: FrameType, this: Ref): Seq int;
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), content'(Heap, this) } { state(Heap, Mask), content#triggerStateless(this), List#trigger(Heap, List(this)) }
  state(Heap, Mask) ==> content'(Heap, this) == content#frame(Heap[null, List(this)], this)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), content'(Heap, this) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 2 || content#trigger(Heap[null, List(this)], this)) ==> (forall i: int, j: int ::
    { Seq#Index(content'(Heap, this), i), Seq#Index(content'(Heap, this), j) }
    0 <= i && (i < j && j < Seq#Length(content'(Heap, this))) ==> Seq#Index(content'(Heap, this), i) <= Seq#Index(content'(Heap, this), j)
  )
);

// Trigger function (controlling recursive postconditions)
function  content#trigger(frame: FrameType, this: Ref): bool;

// State-independent trigger function
function  content#triggerStateless(this: Ref): Seq int;

// Check contract well-formedness and postcondition
procedure content#definedness(this: Ref) returns (Result: (Seq int))
  modifies Heap, Mask;
{
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var ExhaleHeap: HeapType;
  var newPMask: PMaskType;
  var i_3: int;
  var j_3: int;
  var i_2: int;
  var j_2: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[this, $allocated];
    assume AssumeFunctionsAbove == 2;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of (unfolding acc(List(this), write) in contentNodes(this.head, null))
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume List#trigger(UnfoldingHeap, List(this));
      assume UnfoldingHeap[null, List(this)] == CombineFrames(FrameFragment(UnfoldingHeap[this, head]), UnfoldingHeap[null, lseg(UnfoldingHeap[this, head], null)]);
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@53.1--58.2) [1021]"}
          perm <= UnfoldingMask[null, List(this)];
      }
      UnfoldingMask[null, List(this)] := UnfoldingMask[null, List(this)] - perm;
      perm := FullPerm;
      assume this != null;
      UnfoldingMask[this, head] := UnfoldingMask[this, head] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      perm := FullPerm;
      UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] + perm;
      
      // -- Extra unfolding of predicate
        assume InsidePredicate(List(this), UnfoldingHeap[null, List(this)], lseg(UnfoldingHeap[this, head], null), UnfoldingHeap[null, lseg(UnfoldingHeap[this, head], null)]);
      assume state(UnfoldingHeap, UnfoldingMask);
      assume state(UnfoldingHeap, UnfoldingMask);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@53.1--58.2) [1022]"}
        HasDirectPerm(UnfoldingMask, this, head);
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@57.32--57.61) [1023]"}
            perm <= UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)];
        }
        UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(UnfoldingHeap, ExhaleHeap, UnfoldingMask);
        UnfoldingHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      
      // -- Free assumptions (exp module)
        Heap[null, List#sm(this)][this, head] := true;
        havoc newPMask;
        assume (forall <A, B> o_14: Ref, f_18: (Field A B) ::
          { newPMask[o_14, f_18] }
          Heap[null, List#sm(this)][o_14, f_18] || Heap[null, lseg#sm(Heap[this, head], null)][o_14, f_18] ==> newPMask[o_14, f_18]
        );
        Heap[null, List#sm(this)] := newPMask;
        assume state(Heap, Mask);
  
  // -- Translate function body
    Result := contentNodes(Heap, Heap[this, head], null);
  
  // -- Exhaling postcondition (with checking)
    
    // -- Check definedness of (forall i: Int, j: Int :: { result[i], result[j] } 0 <= i && (i < j && j < |result|) ==> result[i] <= result[j])
      if (*) {
        if (0 <= i_3 && (i_3 < j_3 && j_3 < Seq#Length(Result))) {
          assert {:msg "  Contract might not be well-formed. Index result[i] into result might be negative. (linked-list-predicates.vpr@55.12--55.95) [1024]"}
            i_3 >= 0;
          assert {:msg "  Contract might not be well-formed. Index result[i] into result might exceed sequence length. (linked-list-predicates.vpr@55.12--55.95) [1025]"}
            i_3 < Seq#Length(Result);
          assert {:msg "  Contract might not be well-formed. Index result[j] into result might be negative. (linked-list-predicates.vpr@55.12--55.95) [1026]"}
            j_3 >= 0;
          assert {:msg "  Contract might not be well-formed. Index result[j] into result might exceed sequence length. (linked-list-predicates.vpr@55.12--55.95) [1027]"}
            j_3 < Seq#Length(Result);
        }
        assume false;
      }
    if (*) {
      if (0 <= i_2 && (i_2 < j_2 && j_2 < Seq#Length(Result))) {
        assert {:msg "  Postcondition of content might not hold. Assertion result[i] <= result[j] might not hold. (linked-list-predicates.vpr@55.12--55.95) [1028]"}
          Seq#Index(Result, i_2) <= Seq#Index(Result, j_2);
      }
      assume false;
    }
    assume (forall i_3_1: int, j_3_1: int ::
      { Seq#Index(Result, i_3_1), Seq#Index(Result, j_3_1) }
      0 <= i_3_1 && (i_3_1 < j_3_1 && j_3_1 < Seq#Length(Result)) ==> Seq#Index(Result, i_3_1) <= Seq#Index(Result, j_3_1)
    );
}

// ==================================================
// Translation of function length
// ==================================================

// Uninterpreted function definitions
function  length(Heap: HeapType, this: Ref): int;
function  length'(Heap: HeapType, this: Ref): int;
axiom (forall Heap: HeapType, this: Ref ::
  { length(Heap, this) }
  length(Heap, this) == length'(Heap, this) && dummyFunction(length#triggerStateless(this))
);
axiom (forall Heap: HeapType, this: Ref ::
  { length'(Heap, this) }
  dummyFunction(length#triggerStateless(this))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), length(Heap, this) } { state(Heap, Mask), length#triggerStateless(this), List#trigger(Heap, List(this)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 1 ==> length(Heap, this) == lengthNodes(Heap, Heap[this, head], null)
);

// Framing axioms
function  length#frame(frame: FrameType, this: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), length'(Heap, this) } { state(Heap, Mask), length#triggerStateless(this), List#trigger(Heap, List(this)) }
  state(Heap, Mask) ==> length'(Heap, this) == length#frame(Heap[null, List(this)], this)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), length'(Heap, this) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 1 || length#trigger(Heap[null, List(this)], this)) ==> length'(Heap, this) == Seq#Length(content(Heap, this))
);

// Trigger function (controlling recursive postconditions)
function  length#trigger(frame: FrameType, this: Ref): bool;

// State-independent trigger function
function  length#triggerStateless(this: Ref): int;

// Check contract well-formedness and postcondition
procedure length#definedness(this: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var ExhaleHeap: HeapType;
  var newPMask: PMaskType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[this, $allocated];
    assume AssumeFunctionsAbove == 1;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of (unfolding acc(List(this), write) in lengthNodes(this.head, null))
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume List#trigger(UnfoldingHeap, List(this));
      assume UnfoldingHeap[null, List(this)] == CombineFrames(FrameFragment(UnfoldingHeap[this, head]), UnfoldingHeap[null, lseg(UnfoldingHeap[this, head], null)]);
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@60.1--65.2) [1029]"}
          perm <= UnfoldingMask[null, List(this)];
      }
      UnfoldingMask[null, List(this)] := UnfoldingMask[null, List(this)] - perm;
      perm := FullPerm;
      assume this != null;
      UnfoldingMask[this, head] := UnfoldingMask[this, head] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      perm := FullPerm;
      UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] + perm;
      
      // -- Extra unfolding of predicate
        assume InsidePredicate(List(this), UnfoldingHeap[null, List(this)], lseg(UnfoldingHeap[this, head], null), UnfoldingHeap[null, lseg(UnfoldingHeap[this, head], null)]);
      assume state(UnfoldingHeap, UnfoldingMask);
      assume state(UnfoldingHeap, UnfoldingMask);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@60.1--65.2) [1030]"}
        HasDirectPerm(UnfoldingMask, this, head);
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function lengthNodes might not hold. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@64.32--64.60) [1031]"}
            perm <= UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)];
        }
        UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(UnfoldingHeap, ExhaleHeap, UnfoldingMask);
        UnfoldingHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      
      // -- Free assumptions (exp module)
        Heap[null, List#sm(this)][this, head] := true;
        havoc newPMask;
        assume (forall <A, B> o_15: Ref, f_19: (Field A B) ::
          { newPMask[o_15, f_19] }
          Heap[null, List#sm(this)][o_15, f_19] || Heap[null, lseg#sm(Heap[this, head], null)][o_15, f_19] ==> newPMask[o_15, f_19]
        );
        Heap[null, List#sm(this)] := newPMask;
        assume state(Heap, Mask);
  
  // -- Translate function body
    Result := lengthNodes(Heap, Heap[this, head], null);
  
  // -- Exhaling postcondition (with checking)
    
    // -- Check definedness of result == |content(this)|
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@62.22--62.35) [1032]"}
            perm <= Mask[null, List(this)];
        }
        Mask[null, List(this)] := Mask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assert {:msg "  Postcondition of length might not hold. Assertion result == |content(this)| might not hold. (linked-list-predicates.vpr@62.11--62.36) [1033]"}
      Result == Seq#Length(content(Heap, this));
}

// ==================================================
// Translation of function peek
// ==================================================

// Uninterpreted function definitions
function  peek(Heap: HeapType, this: Ref): int;
function  peek'(Heap: HeapType, this: Ref): int;
axiom (forall Heap: HeapType, this: Ref ::
  { peek(Heap, this) }
  peek(Heap, this) == peek'(Heap, this) && dummyFunction(peek#triggerStateless(this))
);
axiom (forall Heap: HeapType, this: Ref ::
  { peek'(Heap, this) }
  dummyFunction(peek#triggerStateless(this))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), peek(Heap, this) } { state(Heap, Mask), peek#triggerStateless(this), List#trigger(Heap, List(this)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 0 ==> 0 < length(Heap, this) ==> peek(Heap, this) == Heap[Heap[this, head], data]
);

// Framing axioms
function  peek#frame(frame: FrameType, this: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), peek'(Heap, this) }
  state(Heap, Mask) ==> peek'(Heap, this) == peek#frame(Heap[null, List(this)], this)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, this: Ref ::
  { state(Heap, Mask), peek'(Heap, this) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 0 || peek#trigger(Heap[null, List(this)], this)) ==> 0 < length(Heap, this) ==> peek'(Heap, this) == Seq#Index(content(Heap, this), 0)
);

// Trigger function (controlling recursive postconditions)
function  peek#trigger(frame: FrameType, this: Ref): bool;

// State-independent trigger function
function  peek#triggerStateless(this: Ref): int;

// Check contract well-formedness and postcondition
procedure peek#definedness(this: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var Unfolding1Heap: HeapType;
  var Unfolding1Mask: MaskType;
  var Unfolding2Heap: HeapType;
  var Unfolding2Mask: MaskType;
  var newPMask: PMaskType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[this, $allocated];
    assume AssumeFunctionsAbove == 0;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of 0 < length(this)
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@69.16--69.28) [1034]"}
            perm <= Mask[null, List(this)];
        }
        Mask[null, List(this)] := Mask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assume 0 < length(Heap, this);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of (unfolding acc(List(this), write) in (unfolding acc(lseg(this.head, null), write) in this.head.data))
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume List#trigger(UnfoldingHeap, List(this));
      assume UnfoldingHeap[null, List(this)] == CombineFrames(FrameFragment(UnfoldingHeap[this, head]), UnfoldingHeap[null, lseg(UnfoldingHeap[this, head], null)]);
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@67.1--73.2) [1035]"}
          perm <= UnfoldingMask[null, List(this)];
      }
      UnfoldingMask[null, List(this)] := UnfoldingMask[null, List(this)] - perm;
      perm := FullPerm;
      assume this != null;
      UnfoldingMask[this, head] := UnfoldingMask[this, head] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      perm := FullPerm;
      UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, head], null)] + perm;
      
      // -- Extra unfolding of predicate
        assume InsidePredicate(List(this), UnfoldingHeap[null, List(this)], lseg(UnfoldingHeap[this, head], null), UnfoldingHeap[null, lseg(UnfoldingHeap[this, head], null)]);
      assume state(UnfoldingHeap, UnfoldingMask);
      assume state(UnfoldingHeap, UnfoldingMask);
      Unfolding1Heap := UnfoldingHeap;
      Unfolding1Mask := UnfoldingMask;
      assume lseg#trigger(Unfolding1Heap, lseg(Unfolding1Heap[this, head], null));
      assume Unfolding1Heap[null, lseg(Unfolding1Heap[this, head], null)] == FrameFragment((if Unfolding1Heap[this, head] != null then CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, head], data]), CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[this, head], next]), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, head], next], null)])) else EmptyFrame));
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@67.1--73.2) [1036]"}
          perm <= Unfolding1Mask[null, lseg(Unfolding1Heap[this, head], null)];
      }
      Unfolding1Mask[null, lseg(Unfolding1Heap[this, head], null)] := Unfolding1Mask[null, lseg(Unfolding1Heap[this, head], null)] - perm;
      if (Unfolding1Heap[this, head] != null) {
        perm := FullPerm;
        assume Unfolding1Heap[this, head] != null;
        Unfolding1Mask[Unfolding1Heap[this, head], data] := Unfolding1Mask[Unfolding1Heap[this, head], data] + perm;
        assume state(Unfolding1Heap, Unfolding1Mask);
        perm := FullPerm;
        assume Unfolding1Heap[this, head] != null;
        Unfolding1Mask[Unfolding1Heap[this, head], next] := Unfolding1Mask[Unfolding1Heap[this, head], next] + perm;
        assume state(Unfolding1Heap, Unfolding1Mask);
        perm := FullPerm;
        Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, head], next], null)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, head], next], null)] + perm;
        
        // -- Extra unfolding of predicate
          assume InsidePredicate(lseg(Unfolding1Heap[this, head], null), Unfolding1Heap[null, lseg(Unfolding1Heap[this, head], null)], lseg(Unfolding1Heap[Unfolding1Heap[this, head], next], null), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, head], next], null)]);
        assume state(Unfolding1Heap, Unfolding1Mask);
        
        // -- Execute unfolding (for extra information)
          Unfolding2Heap := Unfolding1Heap;
          Unfolding2Mask := Unfolding1Mask;
          assume lseg#trigger(Unfolding2Heap, lseg(Unfolding2Heap[Unfolding2Heap[this, head], next], null));
          assume Unfolding2Heap[null, lseg(Unfolding2Heap[Unfolding2Heap[this, head], next], null)] == FrameFragment((if Unfolding2Heap[Unfolding2Heap[this, head], next] != null then CombineFrames(FrameFragment(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], data]), CombineFrames(FrameFragment(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next]), Unfolding2Heap[null, lseg(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)])) else EmptyFrame));
          perm := FullPerm;
          Unfolding2Mask[null, lseg(Unfolding2Heap[Unfolding2Heap[this, head], next], null)] := Unfolding2Mask[null, lseg(Unfolding2Heap[Unfolding2Heap[this, head], next], null)] - perm;
          if (Unfolding2Heap[Unfolding2Heap[this, head], next] != null) {
            perm := FullPerm;
            assume Unfolding2Heap[Unfolding2Heap[this, head], next] != null;
            Unfolding2Mask[Unfolding2Heap[Unfolding2Heap[this, head], next], data] := Unfolding2Mask[Unfolding2Heap[Unfolding2Heap[this, head], next], data] + perm;
            assume state(Unfolding2Heap, Unfolding2Mask);
            perm := FullPerm;
            assume Unfolding2Heap[Unfolding2Heap[this, head], next] != null;
            Unfolding2Mask[Unfolding2Heap[Unfolding2Heap[this, head], next], next] := Unfolding2Mask[Unfolding2Heap[Unfolding2Heap[this, head], next], next] + perm;
            assume state(Unfolding2Heap, Unfolding2Mask);
            perm := FullPerm;
            Unfolding2Mask[null, lseg(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)] := Unfolding2Mask[null, lseg(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)] + perm;
            
            // -- Extra unfolding of predicate
              assume InsidePredicate(lseg(Unfolding2Heap[Unfolding2Heap[this, head], next], null), Unfolding2Heap[null, lseg(Unfolding2Heap[Unfolding2Heap[this, head], next], null)], lseg(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null), Unfolding2Heap[null, lseg(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)]);
            assume state(Unfolding2Heap, Unfolding2Mask);
            assume Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next] != null ==> Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], data] <= Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], data];
            
            // -- Free assumptions (inhale module)
              if (Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next] != null) {
                Unfolding2Heap[null, lseg#sm(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)][Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], data] := true;
                Unfolding2Heap[null, lseg#sm(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)][Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], next] := true;
                havoc newPMask;
                assume (forall <A, B> o_16: Ref, f_20: (Field A B) ::
                  { newPMask[o_16, f_20] }
                  Unfolding2Heap[null, lseg#sm(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)][o_16, f_20] || Unfolding2Heap[null, lseg#sm(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], next], null)][o_16, f_20] ==> newPMask[o_16, f_20]
                );
                Unfolding2Heap[null, lseg#sm(Unfolding2Heap[Unfolding2Heap[Unfolding2Heap[this, head], next], next], null)] := newPMask;
              }
              assume state(Unfolding2Heap, Unfolding2Mask);
          }
          assume state(Unfolding2Heap, Unfolding2Mask);
        assume Unfolding1Heap[Unfolding1Heap[this, head], next] != null ==> Unfolding1Heap[Unfolding1Heap[this, head], data] <= Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, head], next], data];
        
        // -- Free assumptions (inhale module)
          if (Unfolding1Heap[Unfolding1Heap[this, head], next] != null) {
            Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, head], next], null)][Unfolding1Heap[Unfolding1Heap[this, head], next], data] := true;
            Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, head], next], null)][Unfolding1Heap[Unfolding1Heap[this, head], next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_17: Ref, f_21: (Field A B) ::
              { newPMask[o_17, f_21] }
              Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, head], next], null)][o_17, f_21] || Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, head], next], next], null)][o_17, f_21] ==> newPMask[o_17, f_21]
            );
            Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[this, head], next], null)] := newPMask;
          }
          assume state(Unfolding1Heap, Unfolding1Mask);
      }
      assume state(Unfolding1Heap, Unfolding1Mask);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@67.1--73.2) [1037]"}
        HasDirectPerm(Unfolding1Mask, this, head);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.head.data (linked-list-predicates.vpr@67.1--73.2) [1038]"}
        HasDirectPerm(Unfolding1Mask, Unfolding1Heap[this, head], data);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@67.1--73.2) [1039]"}
        HasDirectPerm(Unfolding1Mask, this, head);
      
      // -- Free assumptions (exp module)
        if (UnfoldingHeap[this, head] != null) {
          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, head], null)][UnfoldingHeap[this, head], data] := true;
          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, head], null)][UnfoldingHeap[this, head], next] := true;
          havoc newPMask;
          assume (forall <A, B> o_18: Ref, f_22: (Field A B) ::
            { newPMask[o_18, f_22] }
            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, head], null)][o_18, f_22] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, head], next], null)][o_18, f_22] ==> newPMask[o_18, f_22]
          );
          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[this, head], null)] := newPMask;
        }
        assume state(UnfoldingHeap, UnfoldingMask);
      
      // -- Free assumptions (exp module)
        Heap[null, List#sm(this)][this, head] := true;
        havoc newPMask;
        assume (forall <A, B> o_19: Ref, f_23: (Field A B) ::
          { newPMask[o_19, f_23] }
          Heap[null, List#sm(this)][o_19, f_23] || Heap[null, lseg#sm(Heap[this, head], null)][o_19, f_23] ==> newPMask[o_19, f_23]
        );
        Heap[null, List#sm(this)] := newPMask;
        assume state(Heap, Mask);
        if (Heap[this, head] != null) {
          Heap[null, lseg#sm(Heap[this, head], null)][Heap[this, head], data] := true;
          Heap[null, lseg#sm(Heap[this, head], null)][Heap[this, head], next] := true;
          havoc newPMask;
          assume (forall <A, B> o_20: Ref, f_24: (Field A B) ::
            { newPMask[o_20, f_24] }
            Heap[null, lseg#sm(Heap[this, head], null)][o_20, f_24] || Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_20, f_24] ==> newPMask[o_20, f_24]
          );
          Heap[null, lseg#sm(Heap[this, head], null)] := newPMask;
        }
        assume state(Heap, Mask);
  
  // -- Translate function body
    Result := Heap[Heap[this, head], data];
  
  // -- Exhaling postcondition (with checking)
    
    // -- Check definedness of result == content(this)[0]
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@70.21--70.34) [1040]"}
            perm <= Mask[null, List(this)];
        }
        Mask[null, List(this)] := Mask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assert {:msg "  Contract might not be well-formed. Index content(this)[0] into content(this) might exceed sequence length. (linked-list-predicates.vpr@70.11--70.37) [1041]"}
        0 < Seq#Length(content(Heap, this));
    assert {:msg "  Postcondition of peek might not hold. Assertion result == content(this)[0] might not hold. (linked-list-predicates.vpr@70.11--70.37) [1042]"}
      Result == Seq#Index(content(Heap, this), 0);
}

// ==================================================
// Translation of predicate lseg
// ==================================================

type PredicateType_lseg;
function  lseg(this: Ref, end: Ref): Field PredicateType_lseg FrameType;
function  lseg#sm(this: Ref, end: Ref): Field PredicateType_lseg PMaskType;
axiom (forall this: Ref, end: Ref ::
  { PredicateMaskField(lseg(this, end)) }
  PredicateMaskField(lseg(this, end)) == lseg#sm(this, end)
);
axiom (forall this: Ref, end: Ref ::
  { lseg(this, end) }
  IsPredicateField(lseg(this, end))
);
axiom (forall this: Ref, end: Ref ::
  { lseg(this, end) }
  getPredicateId(lseg(this, end)) == 0
);
function  lseg#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  lseg#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall this: Ref, end: Ref, this2: Ref, end2: Ref ::
  { lseg(this, end), lseg(this2, end2) }
  lseg(this, end) == lseg(this2, end2) ==> this == this2 && end == end2
);
axiom (forall this: Ref, end: Ref, this2: Ref, end2: Ref ::
  { lseg#sm(this, end), lseg#sm(this2, end2) }
  lseg#sm(this, end) == lseg#sm(this2, end2) ==> this == this2 && end == end2
);

axiom (forall Heap: HeapType, this: Ref, end: Ref ::
  { lseg#trigger(Heap, lseg(this, end)) }
  lseg#everUsed(lseg(this, end))
);

procedure lseg#definedness(this: Ref, end: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var Unfolding1Heap: HeapType;
  var Unfolding1Mask: MaskType;
  var newPMask: PMaskType;
  
  // -- Check definedness of predicate body of lseg
    
    // -- Initializing the state
      Mask := ZeroMask;
      assume state(Heap, Mask);
      assume AssumeFunctionsAbove == -1;
      assume Heap[this, $allocated];
      assume Heap[end, $allocated];
    if (this != end) {
      perm := FullPerm;
      assume this != null;
      Mask[this, data] := Mask[this, data] + perm;
      assume state(Heap, Mask);
      perm := FullPerm;
      assume this != null;
      Mask[this, next] := Mask[this, next] + perm;
      assume state(Heap, Mask);
      
      // -- Check definedness of acc(lseg(this.next, end), write)
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.next (linked-list-predicates.vpr@11.1--16.2) [1043]"}
          HasDirectPerm(Mask, this, next);
      perm := FullPerm;
      Mask[null, lseg(Heap[this, next], end)] := Mask[null, lseg(Heap[this, next], end)] + perm;
      assume state(Heap, Mask);
      
      // -- Check definedness of (unfolding acc(lseg(this.next, end), write) in this.next != end ==> this.data <= this.next.data)
        UnfoldingHeap := Heap;
        UnfoldingMask := Mask;
        assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[this, next], end));
        assume UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)] == FrameFragment((if UnfoldingHeap[this, next] != end then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)])) else EmptyFrame));
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access lseg(this.next, end) (linked-list-predicates.vpr@11.1--16.2) [1044]"}
            perm <= UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)];
        }
        UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] - perm;
        if (UnfoldingHeap[this, next] != end) {
          perm := FullPerm;
          assume UnfoldingHeap[this, next] != null;
          UnfoldingMask[UnfoldingHeap[this, next], data] := UnfoldingMask[UnfoldingHeap[this, next], data] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          assume UnfoldingHeap[this, next] != null;
          UnfoldingMask[UnfoldingHeap[this, next], next] := UnfoldingMask[UnfoldingHeap[this, next], next] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(UnfoldingHeap[this, next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)], lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)]);
          assume state(UnfoldingHeap, UnfoldingMask);
          
          // -- Execute unfolding (for extra information)
            Unfolding1Heap := UnfoldingHeap;
            Unfolding1Mask := UnfoldingMask;
            assume lseg#trigger(Unfolding1Heap, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end));
            assume Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] == FrameFragment((if Unfolding1Heap[Unfolding1Heap[this, next], next] != end then CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], data]), CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next]), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)])) else EmptyFrame));
            perm := FullPerm;
            Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)] - perm;
            if (Unfolding1Heap[Unfolding1Heap[this, next], next] != end) {
              perm := FullPerm;
              assume Unfolding1Heap[Unfolding1Heap[this, next], next] != null;
              Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[this, next], next], data] := Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[this, next], next], data] + perm;
              assume state(Unfolding1Heap, Unfolding1Mask);
              perm := FullPerm;
              assume Unfolding1Heap[Unfolding1Heap[this, next], next] != null;
              Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[this, next], next], next] := Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[this, next], next], next] + perm;
              assume state(Unfolding1Heap, Unfolding1Mask);
              perm := FullPerm;
              Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[this, next], next], end)], lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)]);
              assume state(Unfolding1Heap, Unfolding1Mask);
              assume Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next] != end ==> Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], data] <= Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], data];
              
              // -- Free assumptions (inhale module)
                if (Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next] != end) {
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)][Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], data] := true;
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)][Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_21: Ref, f_25: (Field A B) ::
                    { newPMask[o_21, f_25] }
                    Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)][o_21, f_25] || Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], next], end)][o_21, f_25] ==> newPMask[o_21, f_25]
                  );
                  Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[this, next], next], next], end)] := newPMask;
                }
                assume state(Unfolding1Heap, Unfolding1Mask);
            }
            assume state(Unfolding1Heap, Unfolding1Mask);
          assume UnfoldingHeap[UnfoldingHeap[this, next], next] != end ==> UnfoldingHeap[UnfoldingHeap[this, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], data];
          
          // -- Free assumptions (inhale module)
            if (UnfoldingHeap[UnfoldingHeap[this, next], next] != end) {
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][UnfoldingHeap[UnfoldingHeap[this, next], next], data] := true;
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][UnfoldingHeap[UnfoldingHeap[this, next], next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_22: Ref, f_26: (Field A B) ::
                { newPMask[o_22, f_26] }
                UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][o_22, f_26] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], next], end)][o_22, f_26] ==> newPMask[o_22, f_26]
              );
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] := newPMask;
            }
            assume state(UnfoldingHeap, UnfoldingMask);
        }
        assume state(UnfoldingHeap, UnfoldingMask);
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.next (linked-list-predicates.vpr@11.1--16.2) [1045]"}
          HasDirectPerm(UnfoldingMask, this, next);
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.next (linked-list-predicates.vpr@11.1--16.2) [1046]"}
          HasDirectPerm(UnfoldingMask, this, next);
        if (UnfoldingHeap[this, next] != end) {
          assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.data (linked-list-predicates.vpr@11.1--16.2) [1047]"}
            HasDirectPerm(UnfoldingMask, this, data);
          assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.next.data (linked-list-predicates.vpr@11.1--16.2) [1048]"}
            HasDirectPerm(UnfoldingMask, UnfoldingHeap[this, next], data);
          assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.next (linked-list-predicates.vpr@11.1--16.2) [1049]"}
            HasDirectPerm(UnfoldingMask, this, next);
        }
        
        // -- Free assumptions (exp module)
          if (Heap[this, next] != end) {
            Heap[null, lseg#sm(Heap[this, next], end)][Heap[this, next], data] := true;
            Heap[null, lseg#sm(Heap[this, next], end)][Heap[this, next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_23: Ref, f_27: (Field A B) ::
              { newPMask[o_23, f_27] }
              Heap[null, lseg#sm(Heap[this, next], end)][o_23, f_27] || Heap[null, lseg#sm(Heap[Heap[this, next], next], end)][o_23, f_27] ==> newPMask[o_23, f_27]
            );
            Heap[null, lseg#sm(Heap[this, next], end)] := newPMask;
          }
          assume state(Heap, Mask);
      
      // -- Execute unfolding (for extra information)
        UnfoldingHeap := Heap;
        UnfoldingMask := Mask;
        assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[this, next], end));
        assume UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)] == FrameFragment((if UnfoldingHeap[this, next] != end then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)])) else EmptyFrame));
        perm := FullPerm;
        UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], end)] - perm;
        if (UnfoldingHeap[this, next] != end) {
          perm := FullPerm;
          assume UnfoldingHeap[this, next] != null;
          UnfoldingMask[UnfoldingHeap[this, next], data] := UnfoldingMask[UnfoldingHeap[this, next], data] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          assume UnfoldingHeap[this, next] != null;
          UnfoldingMask[UnfoldingHeap[this, next], next] := UnfoldingMask[UnfoldingHeap[this, next], next] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(UnfoldingHeap[this, next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)], lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)]);
          assume state(UnfoldingHeap, UnfoldingMask);
          assume UnfoldingHeap[UnfoldingHeap[this, next], next] != end ==> UnfoldingHeap[UnfoldingHeap[this, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], data];
          
          // -- Free assumptions (inhale module)
            if (UnfoldingHeap[UnfoldingHeap[this, next], next] != end) {
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][UnfoldingHeap[UnfoldingHeap[this, next], next], data] := true;
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][UnfoldingHeap[UnfoldingHeap[this, next], next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_24: Ref, f_28: (Field A B) ::
                { newPMask[o_24, f_28] }
                UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][o_24, f_28] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], next], end)][o_24, f_28] ==> newPMask[o_24, f_28]
              );
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] := newPMask;
            }
            assume state(UnfoldingHeap, UnfoldingMask);
        }
        assume state(UnfoldingHeap, UnfoldingMask);
      assume Heap[this, next] != end ==> Heap[this, data] <= Heap[Heap[this, next], data];
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of predicate List
// ==================================================

type PredicateType_List;
function  List(this: Ref): Field PredicateType_List FrameType;
function  List#sm(this: Ref): Field PredicateType_List PMaskType;
axiom (forall this: Ref ::
  { PredicateMaskField(List(this)) }
  PredicateMaskField(List(this)) == List#sm(this)
);
axiom (forall this: Ref ::
  { List(this) }
  IsPredicateField(List(this))
);
axiom (forall this: Ref ::
  { List(this) }
  getPredicateId(List(this)) == 1
);
function  List#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  List#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall this: Ref, this2: Ref ::
  { List(this), List(this2) }
  List(this) == List(this2) ==> this == this2
);
axiom (forall this: Ref, this2: Ref ::
  { List#sm(this), List#sm(this2) }
  List#sm(this) == List#sm(this2) ==> this == this2
);

axiom (forall Heap: HeapType, this: Ref ::
  { List#trigger(Heap, List(this)) }
  List#everUsed(List(this))
);

procedure List#definedness(this: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  
  // -- Check definedness of predicate body of List
    
    // -- Initializing the state
      Mask := ZeroMask;
      assume state(Heap, Mask);
      assume AssumeFunctionsAbove == -1;
      assume Heap[this, $allocated];
    perm := FullPerm;
    assume this != null;
    Mask[this, head] := Mask[this, head] + perm;
    assume state(Heap, Mask);
    
    // -- Check definedness of acc(lseg(this.head, null), write)
      assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@48.1--51.2) [1050]"}
        HasDirectPerm(Mask, this, head);
    perm := FullPerm;
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method create
// ==================================================

procedure create() returns (this: Ref)
  modifies Heap, Mask;
{
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var freshObj: Ref;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var newPMask: PMaskType;
  var freshVersion: FrameType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
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
    PostMask[null, List(this)] := PostMask[null, List(this)] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of content(this) == Seq[Int]()
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@77.11--77.24) [1051]"}
            perm <= PostMask[null, List(this)];
        }
        PostMask[null, List(this)] := PostMask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
        PostHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assume Seq#Equal(content(PostHeap, this), (Seq#Empty(): Seq int));
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: this := new(data, next, head, held, changed) -- linked-list-predicates.vpr@79.3--79.17
    havoc freshObj;
    assume freshObj != null && !Heap[freshObj, $allocated];
    Heap[freshObj, $allocated] := true;
    this := freshObj;
    Mask[this, data] := Mask[this, data] + FullPerm;
    Mask[this, next] := Mask[this, next] + FullPerm;
    Mask[this, head] := Mask[this, head] + FullPerm;
    Mask[this, held] := Mask[this, held] + FullPerm;
    Mask[this, changed] := Mask[this, changed] + FullPerm;
    assume state(Heap, Mask);
  
  // -- Translating statement: this.head := null -- linked-list-predicates.vpr@80.3--80.20
    assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@80.3--80.20) [1052]"}
      FullPerm == Mask[this, head];
    Heap[this, head] := null;
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(lseg(this.head, null), write) -- linked-list-predicates.vpr@81.3--81.34
    
    // -- Check definedness of acc(lseg(this.head, null), write)
      assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@81.3--81.34) [1053]"}
        HasDirectPerm(Mask, this, head);
    if (Heap[this, head] != null) {
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access this.head.data (linked-list-predicates.vpr@81.3--81.34) [1055]"}
          perm <= Mask[Heap[this, head], data];
      }
      Mask[Heap[this, head], data] := Mask[Heap[this, head], data] - perm;
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access this.head.next (linked-list-predicates.vpr@81.3--81.34) [1057]"}
          perm <= Mask[Heap[this, head], next];
      }
      Mask[Heap[this, head], next] := Mask[Heap[this, head], next] - perm;
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access lseg(this.head.next, null) (linked-list-predicates.vpr@81.3--81.34) [1059]"}
          perm <= Mask[null, lseg(Heap[Heap[this, head], next], null)];
      }
      Mask[null, lseg(Heap[Heap[this, head], next], null)] := Mask[null, lseg(Heap[Heap[this, head], next], null)] - perm;
      
      // -- Record predicate instance information
        assume InsidePredicate(lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)], lseg(Heap[Heap[this, head], next], null), Heap[null, lseg(Heap[Heap[this, head], next], null)]);
      
      // -- Execute unfolding (for extra information)
        UnfoldingHeap := Heap;
        UnfoldingMask := Mask;
        assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null));
        assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[this, head], next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)])) else EmptyFrame));
        if (UnfoldingHeap[UnfoldingHeap[this, head], next] != null) {
          perm := FullPerm;
          assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
          UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
          UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)]);
          assume state(UnfoldingHeap, UnfoldingMask);
          assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data];
          
          // -- Free assumptions (inhale module)
            if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null) {
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data] := true;
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_25: Ref, f_29: (Field A B) ::
                { newPMask[o_25, f_29] }
                UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][o_25, f_29] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next], null)][o_25, f_29] ==> newPMask[o_25, f_29]
              );
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := newPMask;
            }
            assume state(UnfoldingHeap, UnfoldingMask);
        }
        assume state(UnfoldingHeap, UnfoldingMask);
      if (UnfoldingHeap[UnfoldingHeap[this, head], next] != null) {
        assert {:msg "  Folding lseg(this.head, null) might fail. Assertion this.head.data <= this.head.next.data might not hold. (linked-list-predicates.vpr@81.3--81.34) [1060]"}
          UnfoldingHeap[UnfoldingHeap[this, head], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data];
      }
    }
    
    // -- Free assumptions (exhale module)
      if (Heap[Heap[this, head], next] != null) {
        Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], data] := true;
        Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], next] := true;
        havoc newPMask;
        assume (forall <A, B> o_26: Ref, f_30: (Field A B) ::
          { newPMask[o_26, f_30] }
          Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_26, f_30] || Heap[null, lseg#sm(Heap[Heap[Heap[this, head], next], next], null)][o_26, f_30] ==> newPMask[o_26, f_30]
        );
        Heap[null, lseg#sm(Heap[Heap[this, head], next], null)] := newPMask;
      }
      assume state(Heap, Mask);
    perm := FullPerm;
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume lseg#trigger(Heap, lseg(Heap[this, head], null));
    assume Heap[null, lseg(Heap[this, head], null)] == FrameFragment((if Heap[this, head] != null then CombineFrames(FrameFragment(Heap[Heap[this, head], data]), CombineFrames(FrameFragment(Heap[Heap[this, head], next]), Heap[null, lseg(Heap[Heap[this, head], next], null)])) else EmptyFrame));
    if (!HasDirectPerm(Mask, null, lseg(Heap[this, head], null))) {
      Heap[null, lseg#sm(Heap[this, head], null)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, lseg(Heap[this, head], null)] := freshVersion;
    }
    if (Heap[this, head] != null) {
      Heap[null, lseg#sm(Heap[this, head], null)][Heap[this, head], data] := true;
      Heap[null, lseg#sm(Heap[this, head], null)][Heap[this, head], next] := true;
      havoc newPMask;
      assume (forall <A, B> o_27: Ref, f_31: (Field A B) ::
        { newPMask[o_27, f_31] }
        Heap[null, lseg#sm(Heap[this, head], null)][o_27, f_31] || Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_27, f_31] ==> newPMask[o_27, f_31]
      );
      Heap[null, lseg#sm(Heap[this, head], null)] := newPMask;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(List(this), write) -- linked-list-predicates.vpr@82.3--82.23
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(this) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@82.3--82.23) [1063]"}
        perm <= Mask[this, head];
    }
    Mask[this, head] := Mask[this, head] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(this) might fail. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@82.3--82.23) [1065]"}
        perm <= Mask[null, lseg(Heap[this, head], null)];
    }
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] - perm;
    
    // -- Record predicate instance information
      assume InsidePredicate(List(this), Heap[null, List(this)], lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)]);
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume List#trigger(Heap, List(this));
    assume Heap[null, List(this)] == CombineFrames(FrameFragment(Heap[this, head]), Heap[null, lseg(Heap[this, head], null)]);
    if (!HasDirectPerm(Mask, null, List(this))) {
      Heap[null, List#sm(this)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, List(this)] := freshVersion;
    }
    Heap[null, List#sm(this)][this, head] := true;
    havoc newPMask;
    assume (forall <A, B> o_28: Ref, f_32: (Field A B) ::
      { newPMask[o_28, f_32] }
      Heap[null, List#sm(this)][o_28, f_32] || Heap[null, lseg#sm(Heap[this, head], null)][o_28, f_32] ==> newPMask[o_28, f_32]
    );
    Heap[null, List#sm(this)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of create might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@76.11--76.26) [1067]"}
        perm <= Mask[null, List(this)];
    }
    Mask[null, List(this)] := Mask[null, List(this)] - perm;
    assert {:msg "  Postcondition of create might not hold. Assertion content(this) == Seq[Int]() might not hold. (linked-list-predicates.vpr@77.11--77.38) [1068]"}
      Seq#Equal(content(Heap, this), (Seq#Empty(): Seq int));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method concat
// ==================================================

procedure vconcat(this: Ref, ptr: Ref, end: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var newVersion: FrameType;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var newPMask: PMaskType;
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var arg_this: Ref;
  var freshVersion: FrameType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[this, $allocated];
    assume Heap[ptr, $allocated];
    assume Heap[end, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, lseg(this, ptr)] := Mask[null, lseg(this, ptr)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    perm := FullPerm;
    Mask[null, lseg(ptr, end)] := Mask[null, lseg(ptr, end)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    if (end != null) {
      perm := 1 / 2;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@88.12--88.46) [1069]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> end != null;
      Mask[end, next] := Mask[end, next] + perm;
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    
    // -- Check definedness of 0 < |contentNodes(this, ptr)| && 0 < |contentNodes(ptr, end)|
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this, ptr) (linked-list-predicates.vpr@89.17--89.40) [1070]"}
            perm <= Mask[null, lseg(this, ptr)];
        }
        Mask[null, lseg(this, ptr)] := Mask[null, lseg(this, ptr)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      if (0 < Seq#Length(contentNodes(Heap, this, ptr))) {
        if (*) {
          // Exhale precondition of function application
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(ptr, end) (linked-list-predicates.vpr@89.50--89.72) [1071]"}
              perm <= Mask[null, lseg(ptr, end)];
          }
          Mask[null, lseg(ptr, end)] := Mask[null, lseg(ptr, end)] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        }
      }
    if (0 < Seq#Length(contentNodes(Heap, this, ptr)) && 0 < Seq#Length(contentNodes(Heap, ptr, end))) {
      assume state(Heap, Mask);
      
      // -- Check definedness of contentNodes(this, ptr)[|contentNodes(this, ptr)| - 1] <= contentNodes(ptr, end)[0]
        if (*) {
          // Exhale precondition of function application
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this, ptr) (linked-list-predicates.vpr@90.14--90.37) [1072]"}
              perm <= Mask[null, lseg(this, ptr)];
          }
          Mask[null, lseg(this, ptr)] := Mask[null, lseg(this, ptr)] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        }
        if (*) {
          // Exhale precondition of function application
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this, ptr) (linked-list-predicates.vpr@90.39--90.62) [1073]"}
              perm <= Mask[null, lseg(this, ptr)];
          }
          Mask[null, lseg(this, ptr)] := Mask[null, lseg(this, ptr)] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        }
        assert {:msg "  Contract might not be well-formed. Index contentNodes(this, ptr)[|contentNodes(this, ptr)| - 1] into contentNodes(this, ptr) might be negative. (linked-list-predicates.vpr@89.12--90.95) [1074]"}
          Seq#Length(contentNodes(Heap, this, ptr)) - 1 >= 0;
        assert {:msg "  Contract might not be well-formed. Index contentNodes(this, ptr)[|contentNodes(this, ptr)| - 1] into contentNodes(this, ptr) might exceed sequence length. (linked-list-predicates.vpr@89.12--90.95) [1075]"}
          Seq#Length(contentNodes(Heap, this, ptr)) - 1 < Seq#Length(contentNodes(Heap, this, ptr));
        if (*) {
          // Exhale precondition of function application
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(ptr, end) (linked-list-predicates.vpr@90.70--90.92) [1076]"}
              perm <= Mask[null, lseg(ptr, end)];
          }
          Mask[null, lseg(ptr, end)] := Mask[null, lseg(ptr, end)] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
          // Stop execution
          assume false;
        }
        assert {:msg "  Contract might not be well-formed. Index contentNodes(ptr, end)[0] into contentNodes(ptr, end) might exceed sequence length. (linked-list-predicates.vpr@89.12--90.95) [1077]"}
          0 < Seq#Length(contentNodes(Heap, ptr, end));
      assume Seq#Index(contentNodes(Heap, this, ptr), Seq#Length(contentNodes(Heap, this, ptr)) - 1) <= Seq#Index(contentNodes(Heap, ptr, end), 0);
    }
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
    PostMask[null, lseg(this, end)] := PostMask[null, lseg(this, end)] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of contentNodes(this, end) == old(contentNodes(this, ptr) ++ contentNodes(ptr, end))
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this, end) (linked-list-predicates.vpr@92.11--92.34) [1078]"}
            perm <= PostMask[null, lseg(this, end)];
        }
        PostMask[null, lseg(this, end)] := PostMask[null, lseg(this, end)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
        PostHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this, ptr) (linked-list-predicates.vpr@92.42--92.65) [1079]"}
            perm <= old(Mask)[null, lseg(this, ptr)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(ptr, end) (linked-list-predicates.vpr@92.69--92.91) [1080]"}
            perm <= old(Mask)[null, lseg(ptr, end)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
    assume Seq#Equal(contentNodes(PostHeap, this, end), Seq#Append(contentNodes(old(Heap), this, ptr), contentNodes(old(Heap), ptr, end)));
    assume state(PostHeap, PostMask);
    if (end != null) {
      perm := 1 / 2;
      assert {:msg "  Contract might not be well-formed. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@93.11--93.45) [1081]"}
        perm >= NoPerm;
      assume perm > NoPerm ==> end != null;
      PostMask[end, next] := PostMask[end, next] + perm;
      assume state(PostHeap, PostMask);
    }
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: if (this != ptr) -- linked-list-predicates.vpr@95.3--100.4
    if (this != ptr) {
      
      // -- Translating statement: unfold acc(lseg(this, ptr), write) -- linked-list-predicates.vpr@97.5--97.32
        assume lseg#trigger(Heap, lseg(this, ptr));
        assume Heap[null, lseg(this, ptr)] == FrameFragment((if this != ptr then CombineFrames(FrameFragment(Heap[this, data]), CombineFrames(FrameFragment(Heap[this, next]), Heap[null, lseg(Heap[this, next], ptr)])) else EmptyFrame));
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Unfolding lseg(this, ptr) might fail. There might be insufficient permission to access lseg(this, ptr) (linked-list-predicates.vpr@97.5--97.32) [1083]"}
            perm <= Mask[null, lseg(this, ptr)];
        }
        Mask[null, lseg(this, ptr)] := Mask[null, lseg(this, ptr)] - perm;
        
        // -- Update version of predicate
          if (!HasDirectPerm(Mask, null, lseg(this, ptr))) {
            havoc newVersion;
            Heap[null, lseg(this, ptr)] := newVersion;
          }
        if (this != ptr) {
          perm := FullPerm;
          assume this != null;
          Mask[this, data] := Mask[this, data] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          assume this != null;
          Mask[this, next] := Mask[this, next] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          Mask[null, lseg(Heap[this, next], ptr)] := Mask[null, lseg(Heap[this, next], ptr)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(this, ptr), Heap[null, lseg(this, ptr)], lseg(Heap[this, next], ptr), Heap[null, lseg(Heap[this, next], ptr)]);
          assume state(Heap, Mask);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[this, next], ptr));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], ptr)] == FrameFragment((if UnfoldingHeap[this, next] != ptr then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)])) else EmptyFrame));
            perm := FullPerm;
            UnfoldingMask[null, lseg(UnfoldingHeap[this, next], ptr)] := UnfoldingMask[null, lseg(UnfoldingHeap[this, next], ptr)] - perm;
            if (UnfoldingHeap[this, next] != ptr) {
              perm := FullPerm;
              assume UnfoldingHeap[this, next] != null;
              UnfoldingMask[UnfoldingHeap[this, next], data] := UnfoldingMask[UnfoldingHeap[this, next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[this, next] != null;
              UnfoldingMask[UnfoldingHeap[this, next], next] := UnfoldingMask[UnfoldingHeap[this, next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[this, next], ptr), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], ptr)], lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[this, next], next] != ptr ==> UnfoldingHeap[UnfoldingHeap[this, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[this, next], next] != ptr) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)][UnfoldingHeap[UnfoldingHeap[this, next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)][UnfoldingHeap[UnfoldingHeap[this, next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_29: Ref, f_33: (Field A B) ::
                    { newPMask[o_29, f_33] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)][o_29, f_33] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], next], ptr)][o_29, f_33] ==> newPMask[o_29, f_33]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], ptr)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          assume Heap[this, next] != ptr ==> Heap[this, data] <= Heap[Heap[this, next], data];
          
          // -- Free assumptions (inhale module)
            if (Heap[this, next] != ptr) {
              Heap[null, lseg#sm(Heap[this, next], ptr)][Heap[this, next], data] := true;
              Heap[null, lseg#sm(Heap[this, next], ptr)][Heap[this, next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_30: Ref, f_34: (Field A B) ::
                { newPMask[o_30, f_34] }
                Heap[null, lseg#sm(Heap[this, next], ptr)][o_30, f_34] || Heap[null, lseg#sm(Heap[Heap[this, next], next], ptr)][o_30, f_34] ==> newPMask[o_30, f_34]
              );
              Heap[null, lseg#sm(Heap[this, next], ptr)] := newPMask;
            }
            assume state(Heap, Mask);
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: concat(this.next, ptr, end) -- linked-list-predicates.vpr@98.5--98.32
        PreCallHeap := Heap;
        PreCallMask := Mask;
        
        // -- Check definedness of this.next
          assert {:msg "  Method call might fail. There might be insufficient permission to access this.next (linked-list-predicates.vpr@98.5--98.32) [1087]"}
            HasDirectPerm(Mask, this, next);
        arg_this := Heap[this, next];
        
        // -- Exhaling precondition
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access lseg(this.next, ptr) (linked-list-predicates.vpr@98.5--98.32) [1088]"}
              perm <= Mask[null, lseg(arg_this, ptr)];
          }
          Mask[null, lseg(arg_this, ptr)] := Mask[null, lseg(arg_this, ptr)] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access lseg(ptr, end) (linked-list-predicates.vpr@98.5--98.32) [1089]"}
              perm <= Mask[null, lseg(ptr, end)];
          }
          Mask[null, lseg(ptr, end)] := Mask[null, lseg(ptr, end)] - perm;
          if (end != null) {
            assert {:msg "  The precondition of method concat might not hold. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@98.5--98.32) [1090]"}
              1 / 2 >= NoPerm;
            perm := 1 / 2;
            if (perm != NoPerm) {
              assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access end.next (linked-list-predicates.vpr@98.5--98.32) [1091]"}
                perm <= Mask[end, next];
            }
            Mask[end, next] := Mask[end, next] - perm;
          }
          if (0 < Seq#Length(contentNodes(Heap, arg_this, ptr)) && 0 < Seq#Length(contentNodes(Heap, ptr, end))) {
            assert {:msg "  The precondition of method concat might not hold. Assertion contentNodes(this.next, ptr)[|contentNodes(this.next, ptr)| - 1] <= contentNodes(ptr, end)[0] might not hold. (linked-list-predicates.vpr@98.5--98.32) [1092]"}
              Seq#Index(contentNodes(Heap, arg_this, ptr), Seq#Length(contentNodes(Heap, arg_this, ptr)) - 1) <= Seq#Index(contentNodes(Heap, ptr, end), 0);
          }
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
        
        // -- Inhaling postcondition
          perm := FullPerm;
          Mask[null, lseg(arg_this, end)] := Mask[null, lseg(arg_this, end)] + perm;
          assume state(Heap, Mask);
          assume state(Heap, Mask);
          assume Seq#Equal(contentNodes(Heap, arg_this, end), Seq#Append(contentNodes(old(PreCallHeap), arg_this, ptr), contentNodes(old(PreCallHeap), ptr, end)));
          if (end != null) {
            perm := 1 / 2;
            assert {:msg "  Method call might fail. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@98.5--98.32) [1093]"}
              perm >= NoPerm;
            assume perm > NoPerm ==> end != null;
            Mask[end, next] := Mask[end, next] + perm;
            assume state(Heap, Mask);
          }
          assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: fold acc(lseg(this, end), write) -- linked-list-predicates.vpr@99.5--99.30
        if (this != end) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this, end) might fail. There might be insufficient permission to access this.data (linked-list-predicates.vpr@99.5--99.30) [1095]"}
              perm <= Mask[this, data];
          }
          Mask[this, data] := Mask[this, data] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this, end) might fail. There might be insufficient permission to access this.next (linked-list-predicates.vpr@99.5--99.30) [1097]"}
              perm <= Mask[this, next];
          }
          Mask[this, next] := Mask[this, next] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this, end) might fail. There might be insufficient permission to access lseg(this.next, end) (linked-list-predicates.vpr@99.5--99.30) [1099]"}
              perm <= Mask[null, lseg(Heap[this, next], end)];
          }
          Mask[null, lseg(Heap[this, next], end)] := Mask[null, lseg(Heap[this, next], end)] - perm;
          
          // -- Record predicate instance information
            assume InsidePredicate(lseg(this, end), Heap[null, lseg(this, end)], lseg(Heap[this, next], end), Heap[null, lseg(Heap[this, next], end)]);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[this, next], end));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)] == FrameFragment((if UnfoldingHeap[this, next] != end then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[this, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)])) else EmptyFrame));
            if (UnfoldingHeap[this, next] != end) {
              perm := FullPerm;
              assume UnfoldingHeap[this, next] != null;
              UnfoldingMask[UnfoldingHeap[this, next], data] := UnfoldingMask[UnfoldingHeap[this, next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[this, next] != null;
              UnfoldingMask[UnfoldingHeap[this, next], next] := UnfoldingMask[UnfoldingHeap[this, next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[this, next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[this, next], end)], lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, next], next], end)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[this, next], next] != end ==> UnfoldingHeap[UnfoldingHeap[this, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[this, next], next] != end) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][UnfoldingHeap[UnfoldingHeap[this, next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][UnfoldingHeap[UnfoldingHeap[this, next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_31: Ref, f_35: (Field A B) ::
                    { newPMask[o_31, f_35] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)][o_31, f_35] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, next], next], next], end)][o_31, f_35] ==> newPMask[o_31, f_35]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[this, next], next], end)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          if (UnfoldingHeap[this, next] != end) {
            assert {:msg "  Folding lseg(this, end) might fail. Assertion this.data <= this.next.data might not hold. (linked-list-predicates.vpr@99.5--99.30) [1100]"}
              UnfoldingHeap[this, data] <= UnfoldingHeap[UnfoldingHeap[this, next], data];
          }
        }
        
        // -- Free assumptions (exhale module)
          if (Heap[this, next] != end) {
            Heap[null, lseg#sm(Heap[this, next], end)][Heap[this, next], data] := true;
            Heap[null, lseg#sm(Heap[this, next], end)][Heap[this, next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_32: Ref, f_36: (Field A B) ::
              { newPMask[o_32, f_36] }
              Heap[null, lseg#sm(Heap[this, next], end)][o_32, f_36] || Heap[null, lseg#sm(Heap[Heap[this, next], next], end)][o_32, f_36] ==> newPMask[o_32, f_36]
            );
            Heap[null, lseg#sm(Heap[this, next], end)] := newPMask;
          }
          assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, lseg(this, end)] := Mask[null, lseg(this, end)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume lseg#trigger(Heap, lseg(this, end));
        assume Heap[null, lseg(this, end)] == FrameFragment((if this != end then CombineFrames(FrameFragment(Heap[this, data]), CombineFrames(FrameFragment(Heap[this, next]), Heap[null, lseg(Heap[this, next], end)])) else EmptyFrame));
        if (!HasDirectPerm(Mask, null, lseg(this, end))) {
          Heap[null, lseg#sm(this, end)] := ZeroPMask;
          havoc freshVersion;
          Heap[null, lseg(this, end)] := freshVersion;
        }
        if (this != end) {
          Heap[null, lseg#sm(this, end)][this, data] := true;
          Heap[null, lseg#sm(this, end)][this, next] := true;
          havoc newPMask;
          assume (forall <A, B> o_33: Ref, f_37: (Field A B) ::
            { newPMask[o_33, f_37] }
            Heap[null, lseg#sm(this, end)][o_33, f_37] || Heap[null, lseg#sm(Heap[this, next], end)][o_33, f_37] ==> newPMask[o_33, f_37]
          );
          Heap[null, lseg#sm(this, end)] := newPMask;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of concat might not hold. There might be insufficient permission to access lseg(this, end) (linked-list-predicates.vpr@91.12--91.32) [1102]"}
        perm <= Mask[null, lseg(this, end)];
    }
    Mask[null, lseg(this, end)] := Mask[null, lseg(this, end)] - perm;
    assert {:msg "  Postcondition of concat might not hold. Assertion contentNodes(this, end) == old(contentNodes(this, ptr) ++ contentNodes(ptr, end)) might not hold. (linked-list-predicates.vpr@92.11--92.92) [1103]"}
      Seq#Equal(contentNodes(Heap, this, end), Seq#Append(contentNodes(old(Heap), this, ptr), contentNodes(old(Heap), ptr, end)));
    if (end != null) {
      assert {:msg "  Postcondition of concat might not hold. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@93.11--93.45) [1104]"}
        1 / 2 >= NoPerm;
      perm := 1 / 2;
      if (perm != NoPerm) {
        assert {:msg "  Postcondition of concat might not hold. There might be insufficient permission to access end.next (linked-list-predicates.vpr@93.11--93.45) [1105]"}
          perm <= Mask[end, next];
      }
      Mask[end, next] := Mask[end, next] - perm;
    }
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method insert
// ==================================================

procedure insert(this: Ref, elem: int) returns (index: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var ExhaleHeap: HeapType;
  var tmp: Ref;
  var newVersion: FrameType;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var newPMask: PMaskType;
  var freshObj: Ref;
  var freshVersion: FrameType;
  var ptr: Ref;
  var i: int;
  var i_2: int;
  var i_4: int;
  var i_6: int;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var Unfolding1Heap: HeapType;
  var Unfolding1Mask: MaskType;
  var ptrn: Ref;
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var arg_this: Ref;
  var i_10: int;
  var i_12: int;
  var arg_this_1: Ref;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[this, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
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
    perm := FullPerm;
    PostMask[null, List(this)] := PostMask[null, List(this)] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    assume 0 <= index;
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of index <= |old(content(this))|
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@106.39--106.52) [1106]"}
            perm <= old(Mask)[null, List(this)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
    assume index <= Seq#Length(content(old(Heap), this));
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of content(this) == old(content(this))[0..index] ++ Seq(elem) ++ old(content(this))[index..]
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@107.11--107.24) [1107]"}
            perm <= PostMask[null, List(this)];
        }
        PostMask[null, List(this)] := PostMask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
        PostHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@107.32--107.45) [1108]"}
            perm <= old(Mask)[null, List(this)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@107.77--107.90) [1109]"}
            perm <= old(Mask)[null, List(this)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
    assume Seq#Equal(content(PostHeap, this), Seq#Append(Seq#Append(Seq#Drop(Seq#Take(content(old(Heap), this), index), 0), Seq#Singleton(elem)), Seq#Drop(content(old(Heap), this), index)));
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Assumptions about local variables
    assume Heap[tmp, $allocated];
  
  // -- Translating statement: index := 0 -- linked-list-predicates.vpr@110.3--110.13
    index := 0;
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(List(this), write) -- linked-list-predicates.vpr@112.3--112.25
    assume List#trigger(Heap, List(this));
    assume Heap[null, List(this)] == CombineFrames(FrameFragment(Heap[this, head]), Heap[null, lseg(Heap[this, head], null)]);
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding List(this) might fail. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@112.3--112.25) [1111]"}
        perm <= Mask[null, List(this)];
    }
    Mask[null, List(this)] := Mask[null, List(this)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, List(this))) {
        havoc newVersion;
        Heap[null, List(this)] := newVersion;
      }
    perm := FullPerm;
    assume this != null;
    Mask[this, head] := Mask[this, head] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] + perm;
    
    // -- Extra unfolding of predicate
      assume InsidePredicate(List(this), Heap[null, List(this)], lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)]);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: if (this.head != null) -- linked-list-predicates.vpr@114.3--116.4
    
    // -- Check definedness of this.head != null
      assert {:msg "  Conditional statement might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@114.6--114.23) [1114]"}
        HasDirectPerm(Mask, this, head);
    if (Heap[this, head] != null) {
      
      // -- Translating statement: unfold acc(lseg(this.head, null), write) -- linked-list-predicates.vpr@115.5--115.38
        
        // -- Check definedness of acc(lseg(this.head, null), write)
          assert {:msg "  Unfolding lseg(this.head, null) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@115.5--115.38) [1115]"}
            HasDirectPerm(Mask, this, head);
        assume lseg#trigger(Heap, lseg(Heap[this, head], null));
        assume Heap[null, lseg(Heap[this, head], null)] == FrameFragment((if Heap[this, head] != null then CombineFrames(FrameFragment(Heap[Heap[this, head], data]), CombineFrames(FrameFragment(Heap[Heap[this, head], next]), Heap[null, lseg(Heap[Heap[this, head], next], null)])) else EmptyFrame));
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Unfolding lseg(this.head, null) might fail. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@115.5--115.38) [1117]"}
            perm <= Mask[null, lseg(Heap[this, head], null)];
        }
        Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] - perm;
        
        // -- Update version of predicate
          if (!HasDirectPerm(Mask, null, lseg(Heap[this, head], null))) {
            havoc newVersion;
            Heap[null, lseg(Heap[this, head], null)] := newVersion;
          }
        if (Heap[this, head] != null) {
          perm := FullPerm;
          assume Heap[this, head] != null;
          Mask[Heap[this, head], data] := Mask[Heap[this, head], data] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          assume Heap[this, head] != null;
          Mask[Heap[this, head], next] := Mask[Heap[this, head], next] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          Mask[null, lseg(Heap[Heap[this, head], next], null)] := Mask[null, lseg(Heap[Heap[this, head], next], null)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)], lseg(Heap[Heap[this, head], next], null), Heap[null, lseg(Heap[Heap[this, head], next], null)]);
          assume state(Heap, Mask);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[this, head], next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)])) else EmptyFrame));
            perm := FullPerm;
            UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] - perm;
            if (UnfoldingHeap[UnfoldingHeap[this, head], next] != null) {
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_34: Ref, f_38: (Field A B) ::
                    { newPMask[o_34, f_38] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][o_34, f_38] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next], null)][o_34, f_38] ==> newPMask[o_34, f_38]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          assume Heap[Heap[this, head], next] != null ==> Heap[Heap[this, head], data] <= Heap[Heap[Heap[this, head], next], data];
          
          // -- Free assumptions (inhale module)
            if (Heap[Heap[this, head], next] != null) {
              Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], data] := true;
              Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_35: Ref, f_39: (Field A B) ::
                { newPMask[o_35, f_39] }
                Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_35, f_39] || Heap[null, lseg#sm(Heap[Heap[Heap[this, head], next], next], null)][o_35, f_39] ==> newPMask[o_35, f_39]
              );
              Heap[null, lseg#sm(Heap[Heap[this, head], next], null)] := newPMask;
            }
            assume state(Heap, Mask);
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: if (this.head == null || elem <= this.head.data) -- linked-list-predicates.vpr@118.3--161.4
    
    // -- Check definedness of this.head == null || elem <= this.head.data
      assert {:msg "  Conditional statement might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@118.6--118.49) [1121]"}
        HasDirectPerm(Mask, this, head);
      if (!(Heap[this, head] == null)) {
        assert {:msg "  Conditional statement might fail. There might be insufficient permission to access this.head.data (linked-list-predicates.vpr@118.6--118.49) [1122]"}
          HasDirectPerm(Mask, Heap[this, head], data);
        assert {:msg "  Conditional statement might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@118.6--118.49) [1123]"}
          HasDirectPerm(Mask, this, head);
      }
    if (Heap[this, head] == null || elem <= Heap[Heap[this, head], data]) {
      
      // -- Translating statement: tmp := new(data, next, head, held, changed) -- linked-list-predicates.vpr@119.5--119.18
        havoc freshObj;
        assume freshObj != null && !Heap[freshObj, $allocated];
        Heap[freshObj, $allocated] := true;
        tmp := freshObj;
        Mask[tmp, data] := Mask[tmp, data] + FullPerm;
        Mask[tmp, next] := Mask[tmp, next] + FullPerm;
        Mask[tmp, head] := Mask[tmp, head] + FullPerm;
        Mask[tmp, held] := Mask[tmp, held] + FullPerm;
        Mask[tmp, changed] := Mask[tmp, changed] + FullPerm;
        assume state(Heap, Mask);
      
      // -- Translating statement: tmp.data := elem -- linked-list-predicates.vpr@120.5--120.21
        assert {:msg "  Assignment might fail. There might be insufficient permission to access tmp.data (linked-list-predicates.vpr@120.5--120.21) [1124]"}
          FullPerm == Mask[tmp, data];
        Heap[tmp, data] := elem;
        assume state(Heap, Mask);
      
      // -- Translating statement: tmp.next := this.head -- linked-list-predicates.vpr@121.5--121.26
        
        // -- Check definedness of this.head
          assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@121.5--121.26) [1125]"}
            HasDirectPerm(Mask, this, head);
        assert {:msg "  Assignment might fail. There might be insufficient permission to access tmp.next (linked-list-predicates.vpr@121.5--121.26) [1126]"}
          FullPerm == Mask[tmp, next];
        Heap[tmp, next] := Heap[this, head];
        assume state(Heap, Mask);
      
      // -- Translating statement: fold acc(lseg(this.head, null), write) -- linked-list-predicates.vpr@122.5--122.36
        
        // -- Check definedness of acc(lseg(this.head, null), write)
          assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@122.5--122.36) [1127]"}
            HasDirectPerm(Mask, this, head);
        if (Heap[this, head] != null) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access this.head.data (linked-list-predicates.vpr@122.5--122.36) [1129]"}
              perm <= Mask[Heap[this, head], data];
          }
          Mask[Heap[this, head], data] := Mask[Heap[this, head], data] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access this.head.next (linked-list-predicates.vpr@122.5--122.36) [1131]"}
              perm <= Mask[Heap[this, head], next];
          }
          Mask[Heap[this, head], next] := Mask[Heap[this, head], next] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this.head, null) might fail. There might be insufficient permission to access lseg(this.head.next, null) (linked-list-predicates.vpr@122.5--122.36) [1133]"}
              perm <= Mask[null, lseg(Heap[Heap[this, head], next], null)];
          }
          Mask[null, lseg(Heap[Heap[this, head], next], null)] := Mask[null, lseg(Heap[Heap[this, head], next], null)] - perm;
          
          // -- Record predicate instance information
            assume InsidePredicate(lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)], lseg(Heap[Heap[this, head], next], null), Heap[null, lseg(Heap[Heap[this, head], next], null)]);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[this, head], next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)])) else EmptyFrame));
            if (UnfoldingHeap[UnfoldingHeap[this, head], next] != null) {
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_36: Ref, f_40: (Field A B) ::
                    { newPMask[o_36, f_40] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][o_36, f_40] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next], null)][o_36, f_40] ==> newPMask[o_36, f_40]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          if (UnfoldingHeap[UnfoldingHeap[this, head], next] != null) {
            assert {:msg "  Folding lseg(this.head, null) might fail. Assertion this.head.data <= this.head.next.data might not hold. (linked-list-predicates.vpr@122.5--122.36) [1134]"}
              UnfoldingHeap[UnfoldingHeap[this, head], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data];
          }
        }
        
        // -- Free assumptions (exhale module)
          if (Heap[Heap[this, head], next] != null) {
            Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], data] := true;
            Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_37: Ref, f_41: (Field A B) ::
              { newPMask[o_37, f_41] }
              Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_37, f_41] || Heap[null, lseg#sm(Heap[Heap[Heap[this, head], next], next], null)][o_37, f_41] ==> newPMask[o_37, f_41]
            );
            Heap[null, lseg#sm(Heap[Heap[this, head], next], null)] := newPMask;
          }
          assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume lseg#trigger(Heap, lseg(Heap[this, head], null));
        assume Heap[null, lseg(Heap[this, head], null)] == FrameFragment((if Heap[this, head] != null then CombineFrames(FrameFragment(Heap[Heap[this, head], data]), CombineFrames(FrameFragment(Heap[Heap[this, head], next]), Heap[null, lseg(Heap[Heap[this, head], next], null)])) else EmptyFrame));
        if (!HasDirectPerm(Mask, null, lseg(Heap[this, head], null))) {
          Heap[null, lseg#sm(Heap[this, head], null)] := ZeroPMask;
          havoc freshVersion;
          Heap[null, lseg(Heap[this, head], null)] := freshVersion;
        }
        if (Heap[this, head] != null) {
          Heap[null, lseg#sm(Heap[this, head], null)][Heap[this, head], data] := true;
          Heap[null, lseg#sm(Heap[this, head], null)][Heap[this, head], next] := true;
          havoc newPMask;
          assume (forall <A, B> o_38: Ref, f_42: (Field A B) ::
            { newPMask[o_38, f_42] }
            Heap[null, lseg#sm(Heap[this, head], null)][o_38, f_42] || Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_38, f_42] ==> newPMask[o_38, f_42]
          );
          Heap[null, lseg#sm(Heap[this, head], null)] := newPMask;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: fold acc(lseg(tmp, null), write) -- linked-list-predicates.vpr@123.5--123.30
        if (tmp != null) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(tmp, null) might fail. There might be insufficient permission to access tmp.data (linked-list-predicates.vpr@123.5--123.30) [1137]"}
              perm <= Mask[tmp, data];
          }
          Mask[tmp, data] := Mask[tmp, data] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(tmp, null) might fail. There might be insufficient permission to access tmp.next (linked-list-predicates.vpr@123.5--123.30) [1139]"}
              perm <= Mask[tmp, next];
          }
          Mask[tmp, next] := Mask[tmp, next] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(tmp, null) might fail. There might be insufficient permission to access lseg(tmp.next, null) (linked-list-predicates.vpr@123.5--123.30) [1141]"}
              perm <= Mask[null, lseg(Heap[tmp, next], null)];
          }
          Mask[null, lseg(Heap[tmp, next], null)] := Mask[null, lseg(Heap[tmp, next], null)] - perm;
          
          // -- Record predicate instance information
            assume InsidePredicate(lseg(tmp, null), Heap[null, lseg(tmp, null)], lseg(Heap[tmp, next], null), Heap[null, lseg(Heap[tmp, next], null)]);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[tmp, next], null));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[tmp, next], null)] == FrameFragment((if UnfoldingHeap[tmp, next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[tmp, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[tmp, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)])) else EmptyFrame));
            if (UnfoldingHeap[tmp, next] != null) {
              perm := FullPerm;
              assume UnfoldingHeap[tmp, next] != null;
              UnfoldingMask[UnfoldingHeap[tmp, next], data] := UnfoldingMask[UnfoldingHeap[tmp, next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[tmp, next] != null;
              UnfoldingMask[UnfoldingHeap[tmp, next], next] := UnfoldingMask[UnfoldingHeap[tmp, next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[tmp, next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[tmp, next], null)], lseg(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[tmp, next], next] != null ==> UnfoldingHeap[UnfoldingHeap[tmp, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[tmp, next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[tmp, next], next] != null) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)][UnfoldingHeap[UnfoldingHeap[tmp, next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)][UnfoldingHeap[UnfoldingHeap[tmp, next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_39: Ref, f_43: (Field A B) ::
                    { newPMask[o_39, f_43] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)][o_39, f_43] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[tmp, next], next], next], null)][o_39, f_43] ==> newPMask[o_39, f_43]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[tmp, next], next], null)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          if (UnfoldingHeap[tmp, next] != null) {
            assert {:msg "  Folding lseg(tmp, null) might fail. Assertion tmp.data <= tmp.next.data might not hold. (linked-list-predicates.vpr@123.5--123.30) [1142]"}
              UnfoldingHeap[tmp, data] <= UnfoldingHeap[UnfoldingHeap[tmp, next], data];
          }
        }
        
        // -- Free assumptions (exhale module)
          if (Heap[tmp, next] != null) {
            Heap[null, lseg#sm(Heap[tmp, next], null)][Heap[tmp, next], data] := true;
            Heap[null, lseg#sm(Heap[tmp, next], null)][Heap[tmp, next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_40: Ref, f_44: (Field A B) ::
              { newPMask[o_40, f_44] }
              Heap[null, lseg#sm(Heap[tmp, next], null)][o_40, f_44] || Heap[null, lseg#sm(Heap[Heap[tmp, next], next], null)][o_40, f_44] ==> newPMask[o_40, f_44]
            );
            Heap[null, lseg#sm(Heap[tmp, next], null)] := newPMask;
          }
          assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, lseg(tmp, null)] := Mask[null, lseg(tmp, null)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume lseg#trigger(Heap, lseg(tmp, null));
        assume Heap[null, lseg(tmp, null)] == FrameFragment((if tmp != null then CombineFrames(FrameFragment(Heap[tmp, data]), CombineFrames(FrameFragment(Heap[tmp, next]), Heap[null, lseg(Heap[tmp, next], null)])) else EmptyFrame));
        if (!HasDirectPerm(Mask, null, lseg(tmp, null))) {
          Heap[null, lseg#sm(tmp, null)] := ZeroPMask;
          havoc freshVersion;
          Heap[null, lseg(tmp, null)] := freshVersion;
        }
        if (tmp != null) {
          Heap[null, lseg#sm(tmp, null)][tmp, data] := true;
          Heap[null, lseg#sm(tmp, null)][tmp, next] := true;
          havoc newPMask;
          assume (forall <A, B> o_41: Ref, f_45: (Field A B) ::
            { newPMask[o_41, f_45] }
            Heap[null, lseg#sm(tmp, null)][o_41, f_45] || Heap[null, lseg#sm(Heap[tmp, next], null)][o_41, f_45] ==> newPMask[o_41, f_45]
          );
          Heap[null, lseg#sm(tmp, null)] := newPMask;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: this.head := tmp -- linked-list-predicates.vpr@124.5--124.21
        assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@124.5--124.21) [1144]"}
          FullPerm == Mask[this, head];
        Heap[this, head] := tmp;
        assume state(Heap, Mask);
    } else {
      
      // -- Assumptions about local variables
        assume Heap[ptr, $allocated];
      
      // -- Translating statement: ptr := this.head -- linked-list-predicates.vpr@126.5--126.30
        
        // -- Check definedness of this.head
          assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@126.5--126.30) [1145]"}
            HasDirectPerm(Mask, this, head);
        ptr := Heap[this, head];
        assume state(Heap, Mask);
      
      // -- Translating statement: fold acc(lseg(this.head, ptr), write) -- linked-list-predicates.vpr@127.5--127.35
        
        // -- Check definedness of acc(lseg(this.head, ptr), write)
          assert {:msg "  Folding lseg(this.head, ptr) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@127.5--127.35) [1146]"}
            HasDirectPerm(Mask, this, head);
        if (Heap[this, head] != ptr) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this.head, ptr) might fail. There might be insufficient permission to access this.head.data (linked-list-predicates.vpr@127.5--127.35) [1148]"}
              perm <= Mask[Heap[this, head], data];
          }
          Mask[Heap[this, head], data] := Mask[Heap[this, head], data] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this.head, ptr) might fail. There might be insufficient permission to access this.head.next (linked-list-predicates.vpr@127.5--127.35) [1150]"}
              perm <= Mask[Heap[this, head], next];
          }
          Mask[Heap[this, head], next] := Mask[Heap[this, head], next] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(this.head, ptr) might fail. There might be insufficient permission to access lseg(this.head.next, ptr) (linked-list-predicates.vpr@127.5--127.35) [1152]"}
              perm <= Mask[null, lseg(Heap[Heap[this, head], next], ptr)];
          }
          Mask[null, lseg(Heap[Heap[this, head], next], ptr)] := Mask[null, lseg(Heap[Heap[this, head], next], ptr)] - perm;
          
          // -- Record predicate instance information
            assume InsidePredicate(lseg(Heap[this, head], ptr), Heap[null, lseg(Heap[this, head], ptr)], lseg(Heap[Heap[this, head], next], ptr), Heap[null, lseg(Heap[Heap[this, head], next], ptr)]);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], ptr));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], ptr)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[this, head], next] != ptr then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)])) else EmptyFrame));
            if (UnfoldingHeap[UnfoldingHeap[this, head], next] != ptr) {
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], ptr), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], ptr)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != ptr ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != ptr) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_42: Ref, f_46: (Field A B) ::
                    { newPMask[o_42, f_46] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)][o_42, f_46] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next], ptr)][o_42, f_46] ==> newPMask[o_42, f_46]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], ptr)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          if (UnfoldingHeap[UnfoldingHeap[this, head], next] != ptr) {
            assert {:msg "  Folding lseg(this.head, ptr) might fail. Assertion this.head.data <= this.head.next.data might not hold. (linked-list-predicates.vpr@127.5--127.35) [1153]"}
              UnfoldingHeap[UnfoldingHeap[this, head], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data];
          }
        }
        
        // -- Free assumptions (exhale module)
          if (Heap[Heap[this, head], next] != ptr) {
            Heap[null, lseg#sm(Heap[Heap[this, head], next], ptr)][Heap[Heap[this, head], next], data] := true;
            Heap[null, lseg#sm(Heap[Heap[this, head], next], ptr)][Heap[Heap[this, head], next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_43: Ref, f_47: (Field A B) ::
              { newPMask[o_43, f_47] }
              Heap[null, lseg#sm(Heap[Heap[this, head], next], ptr)][o_43, f_47] || Heap[null, lseg#sm(Heap[Heap[Heap[this, head], next], next], ptr)][o_43, f_47] ==> newPMask[o_43, f_47]
            );
            Heap[null, lseg#sm(Heap[Heap[this, head], next], ptr)] := newPMask;
          }
          assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume lseg#trigger(Heap, lseg(Heap[this, head], ptr));
        assume Heap[null, lseg(Heap[this, head], ptr)] == FrameFragment((if Heap[this, head] != ptr then CombineFrames(FrameFragment(Heap[Heap[this, head], data]), CombineFrames(FrameFragment(Heap[Heap[this, head], next]), Heap[null, lseg(Heap[Heap[this, head], next], ptr)])) else EmptyFrame));
        if (!HasDirectPerm(Mask, null, lseg(Heap[this, head], ptr))) {
          Heap[null, lseg#sm(Heap[this, head], ptr)] := ZeroPMask;
          havoc freshVersion;
          Heap[null, lseg(Heap[this, head], ptr)] := freshVersion;
        }
        if (Heap[this, head] != ptr) {
          Heap[null, lseg#sm(Heap[this, head], ptr)][Heap[this, head], data] := true;
          Heap[null, lseg#sm(Heap[this, head], ptr)][Heap[this, head], next] := true;
          havoc newPMask;
          assume (forall <A, B> o_44: Ref, f_48: (Field A B) ::
            { newPMask[o_44, f_48] }
            Heap[null, lseg#sm(Heap[this, head], ptr)][o_44, f_48] || Heap[null, lseg#sm(Heap[Heap[this, head], next], ptr)][o_44, f_48] ==> newPMask[o_44, f_48]
          );
          Heap[null, lseg#sm(Heap[this, head], ptr)] := newPMask;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: index := index + 1 -- linked-list-predicates.vpr@128.5--128.23
        index := index + 1;
        assume state(Heap, Mask);
      
      // -- Translating statement: while (ptr.next != null && (unfolding acc(lseg(ptr.next, null), write) in ptr.next.data < elem)) -- linked-list-predicates.vpr@130.5--150.6
        
        // -- Before loop head
          
          // -- Exhale loop invariant before loop
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(this.head, write) might not hold on entry. There might be insufficient permission to access this.head (linked-list-predicates.vpr@131.17--131.31) [1155]"}
                perm <= Mask[this, head];
            }
            Mask[this, head] := Mask[this, head] - perm;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(ptr.next, write) && (acc(ptr.data, write) && ptr.data <= elem) might not hold on entry. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@132.17--132.67) [1156]"}
                perm <= Mask[ptr, next];
            }
            Mask[ptr, next] := Mask[ptr, next] - perm;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(ptr.next, write) && (acc(ptr.data, write) && ptr.data <= elem) might not hold on entry. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@132.17--132.67) [1157]"}
                perm <= Mask[ptr, data];
            }
            Mask[ptr, data] := Mask[ptr, data] - perm;
            assert {:msg "  Loop invariant acc(ptr.next, write) && (acc(ptr.data, write) && ptr.data <= elem) might not hold on entry. Assertion ptr.data <= elem might not hold. (linked-list-predicates.vpr@132.17--132.67) [1158]"}
              Heap[ptr, data] <= elem;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(lseg(ptr.next, null), write) might not hold on entry. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@133.17--133.42) [1159]"}
                perm <= Mask[null, lseg(Heap[ptr, next], null)];
            }
            Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(lseg(this.head, ptr), write) might not hold on entry. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@134.17--134.42) [1160]"}
                perm <= Mask[null, lseg(Heap[this, head], ptr)];
            }
            Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] - perm;
            if (*) {
              if (0 <= i && i < Seq#Length(contentNodes(Heap, Heap[this, head], ptr))) {
                assert {:msg "  Loop invariant (forall i: Int :: { contentNodes(this.head, ptr)[i] } 0 <= i && i < |contentNodes(this.head, ptr)| ==> contentNodes(this.head, ptr)[i] <= ptr.data) might not hold on entry. Assertion contentNodes(this.head, ptr)[i] <= ptr.data might not hold. (linked-list-predicates.vpr@135.17--136.62) [1161]"}
                  Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i) <= Heap[ptr, data];
              }
              assume false;
            }
            assume (forall i_1_1: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[this, head], ptr)], Heap[this, head], ptr), i_1_1) }
              0 <= i_1_1 && i_1_1 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr)) ==> Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i_1_1) <= Heap[ptr, data]
            );
            if (*) {
              if (0 <= i_2 && i_2 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null))) {
                assert {:msg "  Loop invariant (forall i: Int :: { contentNodes(ptr.next, null)[i] } 0 <= i && i < |contentNodes(ptr.next, null)| ==> ptr.data <= contentNodes(ptr.next, null)[i]) might not hold on entry. Assertion ptr.data <= contentNodes(ptr.next, null)[i] might not hold. (linked-list-predicates.vpr@137.17--138.62) [1162]"}
                  Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_2);
              }
              assume false;
            }
            assume (forall i_3_1: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[ptr, next], null)], Heap[ptr, next], null), i_3_1) }
              0 <= i_3_1 && i_3_1 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null)) ==> Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_3_1)
            );
            assert {:msg "  Loop invariant index - 1 == |contentNodes(this.head, ptr)| might not hold on entry. Assertion index - 1 == |contentNodes(this.head, ptr)| might not hold. (linked-list-predicates.vpr@139.17--139.58) [1163]"}
              index - 1 == Seq#Length(contentNodes(Heap, Heap[this, head], ptr));
            assert {:msg "  Loop invariant old(content(this)) == contentNodes(this.head, ptr) ++ Seq(ptr.data) ++ contentNodes(ptr.next, null) might not hold on entry. Assertion old(content(this)) == contentNodes(this.head, ptr) ++ Seq(ptr.data) ++ contentNodes(ptr.next, null) might not hold. (linked-list-predicates.vpr@141.9--141.108) [1164]"}
              Seq#Equal(content(old(Heap), this), Seq#Append(Seq#Append(contentNodes(Heap, Heap[this, head], ptr), Seq#Singleton(Heap[ptr, data])), contentNodes(Heap, Heap[ptr, next], null)));
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
        
        // -- Havoc loop written variables (except locals)
          havoc ptr, index;
          assume Heap[ptr, $allocated];
        
        // -- Check definedness of invariant
          if (*) {
            perm := FullPerm;
            assume this != null;
            Mask[this, head] := Mask[this, head] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            perm := FullPerm;
            assume ptr != null;
            Mask[ptr, next] := Mask[ptr, next] + perm;
            assume state(Heap, Mask);
            perm := FullPerm;
            assume ptr != null;
            Mask[ptr, data] := Mask[ptr, data] + perm;
            assume state(Heap, Mask);
            
            // -- Check definedness of ptr.data <= elem
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@132.17--132.67) [1165]"}
                HasDirectPerm(Mask, ptr, data);
            assume Heap[ptr, data] <= elem;
            assume state(Heap, Mask);
            
            // -- Check definedness of acc(lseg(ptr.next, null), write)
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@133.17--133.42) [1166]"}
                HasDirectPerm(Mask, ptr, next);
            perm := FullPerm;
            Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of acc(lseg(this.head, ptr), write)
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@134.17--134.42) [1167]"}
                HasDirectPerm(Mask, this, head);
            perm := FullPerm;
            Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall i: Int :: { contentNodes(this.head, ptr)[i] } 0 <= i && i < |contentNodes(this.head, ptr)| ==> contentNodes(this.head, ptr)[i] <= ptr.data)
              if (*) {
                if (0 <= i_4) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@135.17--136.62) [1168]"}
                    HasDirectPerm(Mask, this, head);
                  if (*) {
                    // Exhale precondition of function application
                    perm := FullPerm;
                    if (perm != NoPerm) {
                      assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@135.49--135.77) [1169]"}
                        perm <= Mask[null, lseg(Heap[this, head], ptr)];
                    }
                    Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] - perm;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    // Stop execution
                    assume false;
                  }
                }
                if (0 <= i_4 && i_4 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr))) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@135.17--136.62) [1170]"}
                    HasDirectPerm(Mask, this, head);
                  if (*) {
                    // Exhale precondition of function application
                    perm := FullPerm;
                    if (perm != NoPerm) {
                      assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@136.19--136.47) [1171]"}
                        perm <= Mask[null, lseg(Heap[this, head], ptr)];
                    }
                    Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] - perm;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    // Stop execution
                    assume false;
                  }
                  assert {:msg "  Contract might not be well-formed. Index contentNodes(this.head, ptr)[i] into contentNodes(this.head, ptr) might be negative. (linked-list-predicates.vpr@135.17--136.62) [1172]"}
                    i_4 >= 0;
                  assert {:msg "  Contract might not be well-formed. Index contentNodes(this.head, ptr)[i] into contentNodes(this.head, ptr) might exceed sequence length. (linked-list-predicates.vpr@135.17--136.62) [1173]"}
                    i_4 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr));
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@135.17--136.62) [1174]"}
                    HasDirectPerm(Mask, ptr, data);
                }
                assume false;
              }
            assume (forall i_5: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[this, head], ptr)], Heap[this, head], ptr), i_5) }
              0 <= i_5 && i_5 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr)) ==> Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i_5) <= Heap[ptr, data]
            );
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of (forall i: Int :: { contentNodes(ptr.next, null)[i] } 0 <= i && i < |contentNodes(ptr.next, null)| ==> ptr.data <= contentNodes(ptr.next, null)[i])
              if (*) {
                if (0 <= i_6) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@137.17--138.62) [1175]"}
                    HasDirectPerm(Mask, ptr, next);
                  if (*) {
                    // Exhale precondition of function application
                    perm := FullPerm;
                    if (perm != NoPerm) {
                      assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@137.49--137.77) [1176]"}
                        perm <= Mask[null, lseg(Heap[ptr, next], null)];
                    }
                    Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    // Stop execution
                    assume false;
                  }
                }
                if (0 <= i_6 && i_6 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null))) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@137.17--138.62) [1177]"}
                    HasDirectPerm(Mask, ptr, data);
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@137.17--138.62) [1178]"}
                    HasDirectPerm(Mask, ptr, next);
                  if (*) {
                    // Exhale precondition of function application
                    perm := FullPerm;
                    if (perm != NoPerm) {
                      assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@138.31--138.59) [1179]"}
                        perm <= Mask[null, lseg(Heap[ptr, next], null)];
                    }
                    Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
                    // Finish exhale
                    havoc ExhaleHeap;
                    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                    Heap := ExhaleHeap;
                    // Stop execution
                    assume false;
                  }
                  assert {:msg "  Contract might not be well-formed. Index contentNodes(ptr.next, null)[i] into contentNodes(ptr.next, null) might be negative. (linked-list-predicates.vpr@137.17--138.62) [1180]"}
                    i_6 >= 0;
                  assert {:msg "  Contract might not be well-formed. Index contentNodes(ptr.next, null)[i] into contentNodes(ptr.next, null) might exceed sequence length. (linked-list-predicates.vpr@137.17--138.62) [1181]"}
                    i_6 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null));
                }
                assume false;
              }
            assume (forall i_7: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[ptr, next], null)], Heap[ptr, next], null), i_7) }
              0 <= i_7 && i_7 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null)) ==> Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_7)
            );
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of index - 1 == |contentNodes(this.head, ptr)|
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@139.17--139.58) [1182]"}
                HasDirectPerm(Mask, this, head);
              if (*) {
                // Exhale precondition of function application
                perm := FullPerm;
                if (perm != NoPerm) {
                  assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@139.29--139.57) [1183]"}
                    perm <= Mask[null, lseg(Heap[this, head], ptr)];
                }
                Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] - perm;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
            assume index - 1 == Seq#Length(contentNodes(Heap, Heap[this, head], ptr));
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            
            // -- Check definedness of old(content(this)) == contentNodes(this.head, ptr) ++ Seq(ptr.data) ++ contentNodes(ptr.next, null)
              if (*) {
                // Exhale precondition of function application
                perm := FullPerm;
                if (perm != NoPerm) {
                  assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@141.13--141.26) [1184]"}
                    perm <= old(Mask)[null, List(this)];
                }
                // Finish exhale
                // Stop execution
                assume false;
              }
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.head (linked-list-predicates.vpr@141.9--141.108) [1185]"}
                HasDirectPerm(Mask, this, head);
              if (*) {
                // Exhale precondition of function application
                perm := FullPerm;
                if (perm != NoPerm) {
                  assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@141.31--141.59) [1186]"}
                    perm <= Mask[null, lseg(Heap[this, head], ptr)];
                }
                Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] - perm;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@141.9--141.108) [1187]"}
                HasDirectPerm(Mask, ptr, data);
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@141.9--141.108) [1188]"}
                HasDirectPerm(Mask, ptr, next);
              if (*) {
                // Exhale precondition of function application
                perm := FullPerm;
                if (perm != NoPerm) {
                  assert {:msg "  Precondition of function contentNodes might not hold. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@141.80--141.108) [1189]"}
                    perm <= Mask[null, lseg(Heap[ptr, next], null)];
                }
                Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
                // Finish exhale
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                Heap := ExhaleHeap;
                // Stop execution
                assume false;
              }
            assume Seq#Equal(content(old(Heap), this), Seq#Append(Seq#Append(contentNodes(Heap, Heap[this, head], ptr), Seq#Singleton(Heap[ptr, data])), contentNodes(Heap, Heap[ptr, next], null)));
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
            perm := FullPerm;
            assume this != null;
            Mask[this, head] := Mask[this, head] + perm;
            assume state(Heap, Mask);
            perm := FullPerm;
            assume ptr != null;
            Mask[ptr, next] := Mask[ptr, next] + perm;
            assume state(Heap, Mask);
            perm := FullPerm;
            assume ptr != null;
            Mask[ptr, data] := Mask[ptr, data] + perm;
            assume state(Heap, Mask);
            assume Heap[ptr, data] <= elem;
            perm := FullPerm;
            Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] + perm;
            assume state(Heap, Mask);
            perm := FullPerm;
            Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] + perm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume (forall i_8: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[this, head], ptr)], Heap[this, head], ptr), i_8) }
              0 <= i_8 && i_8 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr)) ==> Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i_8) <= Heap[ptr, data]
            );
            assume state(Heap, Mask);
            assume (forall i_9: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[ptr, next], null)], Heap[ptr, next], null), i_9) }
              0 <= i_9 && i_9 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null)) ==> Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_9)
            );
            assume state(Heap, Mask);
            assume index - 1 == Seq#Length(contentNodes(Heap, Heap[this, head], ptr));
            assume state(Heap, Mask);
            assume Seq#Equal(content(old(Heap), this), Seq#Append(Seq#Append(contentNodes(Heap, Heap[this, head], ptr), Seq#Singleton(Heap[ptr, data])), contentNodes(Heap, Heap[ptr, next], null)));
            assume state(Heap, Mask);
            // Check and assume guard
            
            // -- Check definedness of ptr.next != null && (unfolding acc(lseg(ptr.next, null), write) in ptr.next.data < elem)
              assert {:msg "  While statement might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@130.11--130.90) [1190]"}
                HasDirectPerm(Mask, ptr, next);
              if (Heap[ptr, next] != null) {
                UnfoldingHeap := Heap;
                UnfoldingMask := Mask;
                assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[ptr, next], null));
                assume UnfoldingHeap[null, lseg(UnfoldingHeap[ptr, next], null)] == FrameFragment((if UnfoldingHeap[ptr, next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptr, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptr, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)])) else EmptyFrame));
                perm := FullPerm;
                if (perm != NoPerm) {
                  assert {:msg "  While statement might fail. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@130.11--130.90) [1191]"}
                    perm <= UnfoldingMask[null, lseg(UnfoldingHeap[ptr, next], null)];
                }
                UnfoldingMask[null, lseg(UnfoldingHeap[ptr, next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[ptr, next], null)] - perm;
                if (UnfoldingHeap[ptr, next] != null) {
                  perm := FullPerm;
                  assume UnfoldingHeap[ptr, next] != null;
                  UnfoldingMask[UnfoldingHeap[ptr, next], data] := UnfoldingMask[UnfoldingHeap[ptr, next], data] + perm;
                  assume state(UnfoldingHeap, UnfoldingMask);
                  perm := FullPerm;
                  assume UnfoldingHeap[ptr, next] != null;
                  UnfoldingMask[UnfoldingHeap[ptr, next], next] := UnfoldingMask[UnfoldingHeap[ptr, next], next] + perm;
                  assume state(UnfoldingHeap, UnfoldingMask);
                  perm := FullPerm;
                  UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] + perm;
                  
                  // -- Extra unfolding of predicate
                    assume InsidePredicate(lseg(UnfoldingHeap[ptr, next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[ptr, next], null)], lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)]);
                  assume state(UnfoldingHeap, UnfoldingMask);
                  
                  // -- Execute unfolding (for extra information)
                    Unfolding1Heap := UnfoldingHeap;
                    Unfolding1Mask := UnfoldingMask;
                    assume lseg#trigger(Unfolding1Heap, lseg(Unfolding1Heap[Unfolding1Heap[ptr, next], next], null));
                    assume Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[ptr, next], next], null)] == FrameFragment((if Unfolding1Heap[Unfolding1Heap[ptr, next], next] != null then CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], data]), CombineFrames(FrameFragment(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next]), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)])) else EmptyFrame));
                    perm := FullPerm;
                    Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[ptr, next], next], null)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[ptr, next], next], null)] - perm;
                    if (Unfolding1Heap[Unfolding1Heap[ptr, next], next] != null) {
                      perm := FullPerm;
                      assume Unfolding1Heap[Unfolding1Heap[ptr, next], next] != null;
                      Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[ptr, next], next], data] := Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[ptr, next], next], data] + perm;
                      assume state(Unfolding1Heap, Unfolding1Mask);
                      perm := FullPerm;
                      assume Unfolding1Heap[Unfolding1Heap[ptr, next], next] != null;
                      Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next] := Unfolding1Mask[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next] + perm;
                      assume state(Unfolding1Heap, Unfolding1Mask);
                      perm := FullPerm;
                      Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)] := Unfolding1Mask[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)] + perm;
                      
                      // -- Extra unfolding of predicate
                        assume InsidePredicate(lseg(Unfolding1Heap[Unfolding1Heap[ptr, next], next], null), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[ptr, next], next], null)], lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null), Unfolding1Heap[null, lseg(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)]);
                      assume state(Unfolding1Heap, Unfolding1Mask);
                      assume Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next] != null ==> Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], data] <= Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], data];
                      
                      // -- Free assumptions (inhale module)
                        if (Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next] != null) {
                          Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)][Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], data] := true;
                          Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)][Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], next] := true;
                          havoc newPMask;
                          assume (forall <A, B> o_45: Ref, f_49: (Field A B) ::
                            { newPMask[o_45, f_49] }
                            Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)][o_45, f_49] || Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], next], null)][o_45, f_49] ==> newPMask[o_45, f_49]
                          );
                          Unfolding1Heap[null, lseg#sm(Unfolding1Heap[Unfolding1Heap[Unfolding1Heap[ptr, next], next], next], null)] := newPMask;
                        }
                        assume state(Unfolding1Heap, Unfolding1Mask);
                    }
                    assume state(Unfolding1Heap, Unfolding1Mask);
                  assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null ==> UnfoldingHeap[UnfoldingHeap[ptr, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data];
                  
                  // -- Free assumptions (inhale module)
                    if (UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null) {
                      UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)][UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] := true;
                      UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)][UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] := true;
                      havoc newPMask;
                      assume (forall <A, B> o_46: Ref, f_50: (Field A B) ::
                        { newPMask[o_46, f_50] }
                        UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)][o_46, f_50] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][o_46, f_50] ==> newPMask[o_46, f_50]
                      );
                      UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] := newPMask;
                    }
                    assume state(UnfoldingHeap, UnfoldingMask);
                }
                assume state(UnfoldingHeap, UnfoldingMask);
                assert {:msg "  While statement might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@130.11--130.90) [1192]"}
                  HasDirectPerm(UnfoldingMask, ptr, next);
                assert {:msg "  While statement might fail. There might be insufficient permission to access ptr.next.data (linked-list-predicates.vpr@130.11--130.90) [1193]"}
                  HasDirectPerm(UnfoldingMask, UnfoldingHeap[ptr, next], data);
                assert {:msg "  While statement might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@130.11--130.90) [1194]"}
                  HasDirectPerm(UnfoldingMask, ptr, next);
                
                // -- Free assumptions (exp module)
                  if (Heap[ptr, next] != null) {
                    Heap[null, lseg#sm(Heap[ptr, next], null)][Heap[ptr, next], data] := true;
                    Heap[null, lseg#sm(Heap[ptr, next], null)][Heap[ptr, next], next] := true;
                    havoc newPMask;
                    assume (forall <A, B> o_47: Ref, f_51: (Field A B) ::
                      { newPMask[o_47, f_51] }
                      Heap[null, lseg#sm(Heap[ptr, next], null)][o_47, f_51] || Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][o_47, f_51] ==> newPMask[o_47, f_51]
                    );
                    Heap[null, lseg#sm(Heap[ptr, next], null)] := newPMask;
                  }
                  assume state(Heap, Mask);
              }
            assume Heap[ptr, next] != null && Heap[Heap[ptr, next], data] < elem;
            assume state(Heap, Mask);
            
            // -- Translate loop body
              
              // -- Assumptions about local variables
                assume Heap[ptrn, $allocated];
              
              // -- Translating statement: unfold acc(lseg(ptr.next, null), write) -- linked-list-predicates.vpr@143.7--143.39
                
                // -- Check definedness of acc(lseg(ptr.next, null), write)
                  assert {:msg "  Unfolding lseg(ptr.next, null) might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@143.7--143.39) [1195]"}
                    HasDirectPerm(Mask, ptr, next);
                assume lseg#trigger(Heap, lseg(Heap[ptr, next], null));
                assume Heap[null, lseg(Heap[ptr, next], null)] == FrameFragment((if Heap[ptr, next] != null then CombineFrames(FrameFragment(Heap[Heap[ptr, next], data]), CombineFrames(FrameFragment(Heap[Heap[ptr, next], next]), Heap[null, lseg(Heap[Heap[ptr, next], next], null)])) else EmptyFrame));
                perm := FullPerm;
                if (perm != NoPerm) {
                  assert {:msg "  Unfolding lseg(ptr.next, null) might fail. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@143.7--143.39) [1196]"}
                    perm <= Mask[null, lseg(Heap[ptr, next], null)];
                }
                Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
                
                // -- Update version of predicate
                  if (!HasDirectPerm(Mask, null, lseg(Heap[ptr, next], null))) {
                    havoc newVersion;
                    Heap[null, lseg(Heap[ptr, next], null)] := newVersion;
                  }
                if (Heap[ptr, next] != null) {
                  perm := FullPerm;
                  assume Heap[ptr, next] != null;
                  Mask[Heap[ptr, next], data] := Mask[Heap[ptr, next], data] + perm;
                  assume state(Heap, Mask);
                  perm := FullPerm;
                  assume Heap[ptr, next] != null;
                  Mask[Heap[ptr, next], next] := Mask[Heap[ptr, next], next] + perm;
                  assume state(Heap, Mask);
                  perm := FullPerm;
                  Mask[null, lseg(Heap[Heap[ptr, next], next], null)] := Mask[null, lseg(Heap[Heap[ptr, next], next], null)] + perm;
                  
                  // -- Extra unfolding of predicate
                    assume InsidePredicate(lseg(Heap[ptr, next], null), Heap[null, lseg(Heap[ptr, next], null)], lseg(Heap[Heap[ptr, next], next], null), Heap[null, lseg(Heap[Heap[ptr, next], next], null)]);
                  assume state(Heap, Mask);
                  
                  // -- Execute unfolding (for extra information)
                    UnfoldingHeap := Heap;
                    UnfoldingMask := Mask;
                    assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null));
                    assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)])) else EmptyFrame));
                    perm := FullPerm;
                    UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] - perm;
                    if (UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null) {
                      perm := FullPerm;
                      assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null;
                      UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] + perm;
                      assume state(UnfoldingHeap, UnfoldingMask);
                      perm := FullPerm;
                      assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null;
                      UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] + perm;
                      assume state(UnfoldingHeap, UnfoldingMask);
                      perm := FullPerm;
                      UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)] + perm;
                      
                      // -- Extra unfolding of predicate
                        assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)]);
                      assume state(UnfoldingHeap, UnfoldingMask);
                      assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] != null ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], data];
                      
                      // -- Free assumptions (inhale module)
                        if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] != null) {
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], data] := true;
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], next] := true;
                          havoc newPMask;
                          assume (forall <A, B> o_48: Ref, f_52: (Field A B) ::
                            { newPMask[o_48, f_52] }
                            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][o_48, f_52] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], next], null)][o_48, f_52] ==> newPMask[o_48, f_52]
                          );
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)] := newPMask;
                        }
                        assume state(UnfoldingHeap, UnfoldingMask);
                    }
                    assume state(UnfoldingHeap, UnfoldingMask);
                  assume Heap[Heap[ptr, next], next] != null ==> Heap[Heap[ptr, next], data] <= Heap[Heap[Heap[ptr, next], next], data];
                  
                  // -- Free assumptions (inhale module)
                    if (Heap[Heap[ptr, next], next] != null) {
                      Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][Heap[Heap[ptr, next], next], data] := true;
                      Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][Heap[Heap[ptr, next], next], next] := true;
                      havoc newPMask;
                      assume (forall <A, B> o_49: Ref, f_53: (Field A B) ::
                        { newPMask[o_49, f_53] }
                        Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][o_49, f_53] || Heap[null, lseg#sm(Heap[Heap[Heap[ptr, next], next], next], null)][o_49, f_53] ==> newPMask[o_49, f_53]
                      );
                      Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)] := newPMask;
                    }
                    assume state(Heap, Mask);
                }
                assume state(Heap, Mask);
                assume state(Heap, Mask);
              
              // -- Translating statement: index := index + 1 -- linked-list-predicates.vpr@144.7--144.25
                index := index + 1;
                assume state(Heap, Mask);
              
              // -- Translating statement: ptrn := ptr.next -- linked-list-predicates.vpr@145.7--145.32
                
                // -- Check definedness of ptr.next
                  assert {:msg "  Assignment might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@145.7--145.32) [1197]"}
                    HasDirectPerm(Mask, ptr, next);
                ptrn := Heap[ptr, next];
                assume state(Heap, Mask);
              
              // -- Translating statement: fold acc(lseg(ptrn, ptrn), write) -- linked-list-predicates.vpr@146.7--146.33
                if (ptrn != ptrn) {
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  Folding lseg(ptrn, ptrn) might fail. There might be insufficient permission to access ptrn.data (linked-list-predicates.vpr@146.7--146.33) [1198]"}
                      perm <= Mask[ptrn, data];
                  }
                  Mask[ptrn, data] := Mask[ptrn, data] - perm;
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  Folding lseg(ptrn, ptrn) might fail. There might be insufficient permission to access ptrn.next (linked-list-predicates.vpr@146.7--146.33) [1199]"}
                      perm <= Mask[ptrn, next];
                  }
                  Mask[ptrn, next] := Mask[ptrn, next] - perm;
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  Folding lseg(ptrn, ptrn) might fail. There might be insufficient permission to access lseg(ptrn.next, ptrn) (linked-list-predicates.vpr@146.7--146.33) [1200]"}
                      perm <= Mask[null, lseg(Heap[ptrn, next], ptrn)];
                  }
                  Mask[null, lseg(Heap[ptrn, next], ptrn)] := Mask[null, lseg(Heap[ptrn, next], ptrn)] - perm;
                  
                  // -- Record predicate instance information
                    assume InsidePredicate(lseg(ptrn, ptrn), Heap[null, lseg(ptrn, ptrn)], lseg(Heap[ptrn, next], ptrn), Heap[null, lseg(Heap[ptrn, next], ptrn)]);
                  
                  // -- Execute unfolding (for extra information)
                    UnfoldingHeap := Heap;
                    UnfoldingMask := Mask;
                    assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[ptrn, next], ptrn));
                    assume UnfoldingHeap[null, lseg(UnfoldingHeap[ptrn, next], ptrn)] == FrameFragment((if UnfoldingHeap[ptrn, next] != ptrn then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptrn, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptrn, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)])) else EmptyFrame));
                    if (UnfoldingHeap[ptrn, next] != ptrn) {
                      perm := FullPerm;
                      assume UnfoldingHeap[ptrn, next] != null;
                      UnfoldingMask[UnfoldingHeap[ptrn, next], data] := UnfoldingMask[UnfoldingHeap[ptrn, next], data] + perm;
                      assume state(UnfoldingHeap, UnfoldingMask);
                      perm := FullPerm;
                      assume UnfoldingHeap[ptrn, next] != null;
                      UnfoldingMask[UnfoldingHeap[ptrn, next], next] := UnfoldingMask[UnfoldingHeap[ptrn, next], next] + perm;
                      assume state(UnfoldingHeap, UnfoldingMask);
                      perm := FullPerm;
                      UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)] + perm;
                      
                      // -- Extra unfolding of predicate
                        assume InsidePredicate(lseg(UnfoldingHeap[ptrn, next], ptrn), UnfoldingHeap[null, lseg(UnfoldingHeap[ptrn, next], ptrn)], lseg(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)]);
                      assume state(UnfoldingHeap, UnfoldingMask);
                      assume UnfoldingHeap[UnfoldingHeap[ptrn, next], next] != ptrn ==> UnfoldingHeap[UnfoldingHeap[ptrn, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptrn, next], next], data];
                      
                      // -- Free assumptions (inhale module)
                        if (UnfoldingHeap[UnfoldingHeap[ptrn, next], next] != ptrn) {
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)][UnfoldingHeap[UnfoldingHeap[ptrn, next], next], data] := true;
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)][UnfoldingHeap[UnfoldingHeap[ptrn, next], next], next] := true;
                          havoc newPMask;
                          assume (forall <A, B> o_50: Ref, f_54: (Field A B) ::
                            { newPMask[o_50, f_54] }
                            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)][o_50, f_54] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptrn, next], next], next], ptrn)][o_50, f_54] ==> newPMask[o_50, f_54]
                          );
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptrn, next], next], ptrn)] := newPMask;
                        }
                        assume state(UnfoldingHeap, UnfoldingMask);
                    }
                    assume state(UnfoldingHeap, UnfoldingMask);
                  if (UnfoldingHeap[ptrn, next] != ptrn) {
                    assert {:msg "  Folding lseg(ptrn, ptrn) might fail. Assertion ptrn.data <= ptrn.next.data might not hold. (linked-list-predicates.vpr@146.7--146.33) [1201]"}
                      UnfoldingHeap[ptrn, data] <= UnfoldingHeap[UnfoldingHeap[ptrn, next], data];
                  }
                }
                
                // -- Free assumptions (exhale module)
                  if (Heap[ptrn, next] != ptrn) {
                    Heap[null, lseg#sm(Heap[ptrn, next], ptrn)][Heap[ptrn, next], data] := true;
                    Heap[null, lseg#sm(Heap[ptrn, next], ptrn)][Heap[ptrn, next], next] := true;
                    havoc newPMask;
                    assume (forall <A, B> o_51: Ref, f_55: (Field A B) ::
                      { newPMask[o_51, f_55] }
                      Heap[null, lseg#sm(Heap[ptrn, next], ptrn)][o_51, f_55] || Heap[null, lseg#sm(Heap[Heap[ptrn, next], next], ptrn)][o_51, f_55] ==> newPMask[o_51, f_55]
                    );
                    Heap[null, lseg#sm(Heap[ptrn, next], ptrn)] := newPMask;
                  }
                  assume state(Heap, Mask);
                perm := FullPerm;
                Mask[null, lseg(ptrn, ptrn)] := Mask[null, lseg(ptrn, ptrn)] + perm;
                assume state(Heap, Mask);
                assume state(Heap, Mask);
                assume lseg#trigger(Heap, lseg(ptrn, ptrn));
                assume Heap[null, lseg(ptrn, ptrn)] == FrameFragment((if ptrn != ptrn then CombineFrames(FrameFragment(Heap[ptrn, data]), CombineFrames(FrameFragment(Heap[ptrn, next]), Heap[null, lseg(Heap[ptrn, next], ptrn)])) else EmptyFrame));
                if (!HasDirectPerm(Mask, null, lseg(ptrn, ptrn))) {
                  Heap[null, lseg#sm(ptrn, ptrn)] := ZeroPMask;
                  havoc freshVersion;
                  Heap[null, lseg(ptrn, ptrn)] := freshVersion;
                }
                if (ptrn != ptrn) {
                  Heap[null, lseg#sm(ptrn, ptrn)][ptrn, data] := true;
                  Heap[null, lseg#sm(ptrn, ptrn)][ptrn, next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_52: Ref, f_56: (Field A B) ::
                    { newPMask[o_52, f_56] }
                    Heap[null, lseg#sm(ptrn, ptrn)][o_52, f_56] || Heap[null, lseg#sm(Heap[ptrn, next], ptrn)][o_52, f_56] ==> newPMask[o_52, f_56]
                  );
                  Heap[null, lseg#sm(ptrn, ptrn)] := newPMask;
                }
                assume state(Heap, Mask);
                assume state(Heap, Mask);
              
              // -- Translating statement: fold acc(lseg(ptr, ptrn), write) -- linked-list-predicates.vpr@147.7--147.32
                if (ptr != ptrn) {
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  Folding lseg(ptr, ptrn) might fail. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@147.7--147.32) [1202]"}
                      perm <= Mask[ptr, data];
                  }
                  Mask[ptr, data] := Mask[ptr, data] - perm;
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  Folding lseg(ptr, ptrn) might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@147.7--147.32) [1203]"}
                      perm <= Mask[ptr, next];
                  }
                  Mask[ptr, next] := Mask[ptr, next] - perm;
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  Folding lseg(ptr, ptrn) might fail. There might be insufficient permission to access lseg(ptr.next, ptrn) (linked-list-predicates.vpr@147.7--147.32) [1204]"}
                      perm <= Mask[null, lseg(Heap[ptr, next], ptrn)];
                  }
                  Mask[null, lseg(Heap[ptr, next], ptrn)] := Mask[null, lseg(Heap[ptr, next], ptrn)] - perm;
                  
                  // -- Record predicate instance information
                    assume InsidePredicate(lseg(ptr, ptrn), Heap[null, lseg(ptr, ptrn)], lseg(Heap[ptr, next], ptrn), Heap[null, lseg(Heap[ptr, next], ptrn)]);
                  
                  // -- Execute unfolding (for extra information)
                    UnfoldingHeap := Heap;
                    UnfoldingMask := Mask;
                    assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[ptr, next], ptrn));
                    assume UnfoldingHeap[null, lseg(UnfoldingHeap[ptr, next], ptrn)] == FrameFragment((if UnfoldingHeap[ptr, next] != ptrn then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptr, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptr, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)])) else EmptyFrame));
                    if (UnfoldingHeap[ptr, next] != ptrn) {
                      perm := FullPerm;
                      assume UnfoldingHeap[ptr, next] != null;
                      UnfoldingMask[UnfoldingHeap[ptr, next], data] := UnfoldingMask[UnfoldingHeap[ptr, next], data] + perm;
                      assume state(UnfoldingHeap, UnfoldingMask);
                      perm := FullPerm;
                      assume UnfoldingHeap[ptr, next] != null;
                      UnfoldingMask[UnfoldingHeap[ptr, next], next] := UnfoldingMask[UnfoldingHeap[ptr, next], next] + perm;
                      assume state(UnfoldingHeap, UnfoldingMask);
                      perm := FullPerm;
                      UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)] + perm;
                      
                      // -- Extra unfolding of predicate
                        assume InsidePredicate(lseg(UnfoldingHeap[ptr, next], ptrn), UnfoldingHeap[null, lseg(UnfoldingHeap[ptr, next], ptrn)], lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)]);
                      assume state(UnfoldingHeap, UnfoldingMask);
                      assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != ptrn ==> UnfoldingHeap[UnfoldingHeap[ptr, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data];
                      
                      // -- Free assumptions (inhale module)
                        if (UnfoldingHeap[UnfoldingHeap[ptr, next], next] != ptrn) {
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)][UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] := true;
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)][UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] := true;
                          havoc newPMask;
                          assume (forall <A, B> o_53: Ref, f_57: (Field A B) ::
                            { newPMask[o_53, f_57] }
                            UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)][o_53, f_57] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], ptrn)][o_53, f_57] ==> newPMask[o_53, f_57]
                          );
                          UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], ptrn)] := newPMask;
                        }
                        assume state(UnfoldingHeap, UnfoldingMask);
                    }
                    assume state(UnfoldingHeap, UnfoldingMask);
                  if (UnfoldingHeap[ptr, next] != ptrn) {
                    assert {:msg "  Folding lseg(ptr, ptrn) might fail. Assertion ptr.data <= ptr.next.data might not hold. (linked-list-predicates.vpr@147.7--147.32) [1205]"}
                      UnfoldingHeap[ptr, data] <= UnfoldingHeap[UnfoldingHeap[ptr, next], data];
                  }
                }
                
                // -- Free assumptions (exhale module)
                  if (Heap[ptr, next] != ptrn) {
                    Heap[null, lseg#sm(Heap[ptr, next], ptrn)][Heap[ptr, next], data] := true;
                    Heap[null, lseg#sm(Heap[ptr, next], ptrn)][Heap[ptr, next], next] := true;
                    havoc newPMask;
                    assume (forall <A, B> o_54: Ref, f_58: (Field A B) ::
                      { newPMask[o_54, f_58] }
                      Heap[null, lseg#sm(Heap[ptr, next], ptrn)][o_54, f_58] || Heap[null, lseg#sm(Heap[Heap[ptr, next], next], ptrn)][o_54, f_58] ==> newPMask[o_54, f_58]
                    );
                    Heap[null, lseg#sm(Heap[ptr, next], ptrn)] := newPMask;
                  }
                  assume state(Heap, Mask);
                perm := FullPerm;
                Mask[null, lseg(ptr, ptrn)] := Mask[null, lseg(ptr, ptrn)] + perm;
                assume state(Heap, Mask);
                assume state(Heap, Mask);
                assume lseg#trigger(Heap, lseg(ptr, ptrn));
                assume Heap[null, lseg(ptr, ptrn)] == FrameFragment((if ptr != ptrn then CombineFrames(FrameFragment(Heap[ptr, data]), CombineFrames(FrameFragment(Heap[ptr, next]), Heap[null, lseg(Heap[ptr, next], ptrn)])) else EmptyFrame));
                if (!HasDirectPerm(Mask, null, lseg(ptr, ptrn))) {
                  Heap[null, lseg#sm(ptr, ptrn)] := ZeroPMask;
                  havoc freshVersion;
                  Heap[null, lseg(ptr, ptrn)] := freshVersion;
                }
                if (ptr != ptrn) {
                  Heap[null, lseg#sm(ptr, ptrn)][ptr, data] := true;
                  Heap[null, lseg#sm(ptr, ptrn)][ptr, next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_55: Ref, f_59: (Field A B) ::
                    { newPMask[o_55, f_59] }
                    Heap[null, lseg#sm(ptr, ptrn)][o_55, f_59] || Heap[null, lseg#sm(Heap[ptr, next], ptrn)][o_55, f_59] ==> newPMask[o_55, f_59]
                  );
                  Heap[null, lseg#sm(ptr, ptrn)] := newPMask;
                }
                assume state(Heap, Mask);
                assume state(Heap, Mask);
              
              // -- Translating statement: concat(this.head, ptr, ptrn) -- linked-list-predicates.vpr@148.7--148.35
                PreCallHeap := Heap;
                PreCallMask := Mask;
                
                // -- Check definedness of this.head
                  assert {:msg "  Method call might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@148.7--148.35) [1206]"}
                    HasDirectPerm(Mask, this, head);
                arg_this := Heap[this, head];
                
                // -- Exhaling precondition
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@148.7--148.35) [1207]"}
                      perm <= Mask[null, lseg(arg_this, ptr)];
                  }
                  Mask[null, lseg(arg_this, ptr)] := Mask[null, lseg(arg_this, ptr)] - perm;
                  perm := FullPerm;
                  if (perm != NoPerm) {
                    assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access lseg(ptr, ptrn) (linked-list-predicates.vpr@148.7--148.35) [1208]"}
                      perm <= Mask[null, lseg(ptr, ptrn)];
                  }
                  Mask[null, lseg(ptr, ptrn)] := Mask[null, lseg(ptr, ptrn)] - perm;
                  if (ptrn != null) {
                    assert {:msg "  The precondition of method concat might not hold. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@148.7--148.35) [1209]"}
                      1 / 2 >= NoPerm;
                    perm := 1 / 2;
                    if (perm != NoPerm) {
                      assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access ptrn.next (linked-list-predicates.vpr@148.7--148.35) [1210]"}
                        perm <= Mask[ptrn, next];
                    }
                    Mask[ptrn, next] := Mask[ptrn, next] - perm;
                  }
                  if (0 < Seq#Length(contentNodes(Heap, arg_this, ptr)) && 0 < Seq#Length(contentNodes(Heap, ptr, ptrn))) {
                    assert {:msg "  The precondition of method concat might not hold. Assertion contentNodes(this.head, ptr)[|contentNodes(this.head, ptr)| - 1] <= contentNodes(ptr, ptrn)[0] might not hold. (linked-list-predicates.vpr@148.7--148.35) [1211]"}
                      Seq#Index(contentNodes(Heap, arg_this, ptr), Seq#Length(contentNodes(Heap, arg_this, ptr)) - 1) <= Seq#Index(contentNodes(Heap, ptr, ptrn), 0);
                  }
                  // Finish exhale
                  havoc ExhaleHeap;
                  assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
                  Heap := ExhaleHeap;
                
                // -- Inhaling postcondition
                  perm := FullPerm;
                  Mask[null, lseg(arg_this, ptrn)] := Mask[null, lseg(arg_this, ptrn)] + perm;
                  assume state(Heap, Mask);
                  assume state(Heap, Mask);
                  assume Seq#Equal(contentNodes(Heap, arg_this, ptrn), Seq#Append(contentNodes(old(PreCallHeap), arg_this, ptr), contentNodes(old(PreCallHeap), ptr, ptrn)));
                  if (ptrn != null) {
                    perm := 1 / 2;
                    assert {:msg "  Method call might fail. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@148.7--148.35) [1212]"}
                      perm >= NoPerm;
                    assume perm > NoPerm ==> ptrn != null;
                    Mask[ptrn, next] := Mask[ptrn, next] + perm;
                    assume state(Heap, Mask);
                  }
                  assume state(Heap, Mask);
                assume state(Heap, Mask);
              
              // -- Translating statement: ptr := ptrn -- linked-list-predicates.vpr@149.7--149.18
                ptr := ptrn;
                assume state(Heap, Mask);
            // Exhale invariant
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(this.head, write) might not be preserved. There might be insufficient permission to access this.head (linked-list-predicates.vpr@131.17--131.31) [1213]"}
                perm <= Mask[this, head];
            }
            Mask[this, head] := Mask[this, head] - perm;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(ptr.next, write) && (acc(ptr.data, write) && ptr.data <= elem) might not be preserved. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@132.17--132.67) [1214]"}
                perm <= Mask[ptr, next];
            }
            Mask[ptr, next] := Mask[ptr, next] - perm;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(ptr.next, write) && (acc(ptr.data, write) && ptr.data <= elem) might not be preserved. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@132.17--132.67) [1215]"}
                perm <= Mask[ptr, data];
            }
            Mask[ptr, data] := Mask[ptr, data] - perm;
            assert {:msg "  Loop invariant acc(ptr.next, write) && (acc(ptr.data, write) && ptr.data <= elem) might not be preserved. Assertion ptr.data <= elem might not hold. (linked-list-predicates.vpr@132.17--132.67) [1216]"}
              Heap[ptr, data] <= elem;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(lseg(ptr.next, null), write) might not be preserved. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@133.17--133.42) [1217]"}
                perm <= Mask[null, lseg(Heap[ptr, next], null)];
            }
            Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Loop invariant acc(lseg(this.head, ptr), write) might not be preserved. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@134.17--134.42) [1218]"}
                perm <= Mask[null, lseg(Heap[this, head], ptr)];
            }
            Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] - perm;
            if (*) {
              if (0 <= i_10 && i_10 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr))) {
                assert {:msg "  Loop invariant (forall i: Int :: { contentNodes(this.head, ptr)[i] } 0 <= i && i < |contentNodes(this.head, ptr)| ==> contentNodes(this.head, ptr)[i] <= ptr.data) might not be preserved. Assertion contentNodes(this.head, ptr)[i] <= ptr.data might not hold. (linked-list-predicates.vpr@135.17--136.62) [1219]"}
                  Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i_10) <= Heap[ptr, data];
              }
              assume false;
            }
            assume (forall i_11_1: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[this, head], ptr)], Heap[this, head], ptr), i_11_1) }
              0 <= i_11_1 && i_11_1 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr)) ==> Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i_11_1) <= Heap[ptr, data]
            );
            if (*) {
              if (0 <= i_12 && i_12 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null))) {
                assert {:msg "  Loop invariant (forall i: Int :: { contentNodes(ptr.next, null)[i] } 0 <= i && i < |contentNodes(ptr.next, null)| ==> ptr.data <= contentNodes(ptr.next, null)[i]) might not be preserved. Assertion ptr.data <= contentNodes(ptr.next, null)[i] might not hold. (linked-list-predicates.vpr@137.17--138.62) [1220]"}
                  Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_12);
              }
              assume false;
            }
            assume (forall i_13_1: int ::
              { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[ptr, next], null)], Heap[ptr, next], null), i_13_1) }
              0 <= i_13_1 && i_13_1 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null)) ==> Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_13_1)
            );
            assert {:msg "  Loop invariant index - 1 == |contentNodes(this.head, ptr)| might not be preserved. Assertion index - 1 == |contentNodes(this.head, ptr)| might not hold. (linked-list-predicates.vpr@139.17--139.58) [1221]"}
              index - 1 == Seq#Length(contentNodes(Heap, Heap[this, head], ptr));
            assert {:msg "  Loop invariant old(content(this)) == contentNodes(this.head, ptr) ++ Seq(ptr.data) ++ contentNodes(ptr.next, null) might not be preserved. Assertion old(content(this)) == contentNodes(this.head, ptr) ++ Seq(ptr.data) ++ contentNodes(ptr.next, null) might not hold. (linked-list-predicates.vpr@141.9--141.108) [1222]"}
              Seq#Equal(content(old(Heap), this), Seq#Append(Seq#Append(contentNodes(Heap, Heap[this, head], ptr), Seq#Singleton(Heap[ptr, data])), contentNodes(Heap, Heap[ptr, next], null)));
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
            // Terminate execution
            assume false;
          }
        
        // -- Inhale loop invariant after loop, and assume guard
          assume !(Heap[ptr, next] != null && Heap[Heap[ptr, next], data] < elem);
          assume state(Heap, Mask);
          perm := FullPerm;
          assume this != null;
          Mask[this, head] := Mask[this, head] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          assume ptr != null;
          Mask[ptr, next] := Mask[ptr, next] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          assume ptr != null;
          Mask[ptr, data] := Mask[ptr, data] + perm;
          assume state(Heap, Mask);
          assume Heap[ptr, data] <= elem;
          perm := FullPerm;
          Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] + perm;
          assume state(Heap, Mask);
          perm := FullPerm;
          Mask[null, lseg(Heap[this, head], ptr)] := Mask[null, lseg(Heap[this, head], ptr)] + perm;
          assume state(Heap, Mask);
          assume state(Heap, Mask);
          assume (forall i_14: int ::
            { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[this, head], ptr)], Heap[this, head], ptr), i_14) }
            0 <= i_14 && i_14 < Seq#Length(contentNodes(Heap, Heap[this, head], ptr)) ==> Seq#Index(contentNodes(Heap, Heap[this, head], ptr), i_14) <= Heap[ptr, data]
          );
          assume state(Heap, Mask);
          assume (forall i_15: int ::
            { Seq#Index(contentNodes#frame(Heap[null, lseg(Heap[ptr, next], null)], Heap[ptr, next], null), i_15) }
            0 <= i_15 && i_15 < Seq#Length(contentNodes(Heap, Heap[ptr, next], null)) ==> Heap[ptr, data] <= Seq#Index(contentNodes(Heap, Heap[ptr, next], null), i_15)
          );
          assume state(Heap, Mask);
          assume index - 1 == Seq#Length(contentNodes(Heap, Heap[this, head], ptr));
          assume state(Heap, Mask);
          assume Seq#Equal(content(old(Heap), this), Seq#Append(Seq#Append(contentNodes(Heap, Heap[this, head], ptr), Seq#Singleton(Heap[ptr, data])), contentNodes(Heap, Heap[ptr, next], null)));
          assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: tmp := new(data, next, head, held, changed) -- linked-list-predicates.vpr@152.5--152.18
        havoc freshObj;
        assume freshObj != null && !Heap[freshObj, $allocated];
        Heap[freshObj, $allocated] := true;
        tmp := freshObj;
        Mask[tmp, data] := Mask[tmp, data] + FullPerm;
        Mask[tmp, next] := Mask[tmp, next] + FullPerm;
        Mask[tmp, head] := Mask[tmp, head] + FullPerm;
        Mask[tmp, held] := Mask[tmp, held] + FullPerm;
        Mask[tmp, changed] := Mask[tmp, changed] + FullPerm;
        assume state(Heap, Mask);
      
      // -- Translating statement: tmp.data := elem -- linked-list-predicates.vpr@153.5--153.21
        assert {:msg "  Assignment might fail. There might be insufficient permission to access tmp.data (linked-list-predicates.vpr@153.5--153.21) [1223]"}
          FullPerm == Mask[tmp, data];
        Heap[tmp, data] := elem;
        assume state(Heap, Mask);
      
      // -- Translating statement: tmp.next := ptr.next -- linked-list-predicates.vpr@154.5--154.25
        
        // -- Check definedness of ptr.next
          assert {:msg "  Assignment might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@154.5--154.25) [1224]"}
            HasDirectPerm(Mask, ptr, next);
        assert {:msg "  Assignment might fail. There might be insufficient permission to access tmp.next (linked-list-predicates.vpr@154.5--154.25) [1225]"}
          FullPerm == Mask[tmp, next];
        Heap[tmp, next] := Heap[ptr, next];
        assume state(Heap, Mask);
      
      // -- Translating statement: ptr.next := tmp -- linked-list-predicates.vpr@155.5--155.20
        assert {:msg "  Assignment might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@155.5--155.20) [1226]"}
          FullPerm == Mask[ptr, next];
        Heap[ptr, next] := tmp;
        assume state(Heap, Mask);
      
      // -- Translating statement: fold acc(lseg(ptr.next, null), write) -- linked-list-predicates.vpr@156.5--156.35
        
        // -- Check definedness of acc(lseg(ptr.next, null), write)
          assert {:msg "  Folding lseg(ptr.next, null) might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@156.5--156.35) [1227]"}
            HasDirectPerm(Mask, ptr, next);
        if (Heap[ptr, next] != null) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(ptr.next, null) might fail. There might be insufficient permission to access ptr.next.data (linked-list-predicates.vpr@156.5--156.35) [1229]"}
              perm <= Mask[Heap[ptr, next], data];
          }
          Mask[Heap[ptr, next], data] := Mask[Heap[ptr, next], data] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(ptr.next, null) might fail. There might be insufficient permission to access ptr.next.next (linked-list-predicates.vpr@156.5--156.35) [1231]"}
              perm <= Mask[Heap[ptr, next], next];
          }
          Mask[Heap[ptr, next], next] := Mask[Heap[ptr, next], next] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(ptr.next, null) might fail. There might be insufficient permission to access lseg(ptr.next.next, null) (linked-list-predicates.vpr@156.5--156.35) [1233]"}
              perm <= Mask[null, lseg(Heap[Heap[ptr, next], next], null)];
          }
          Mask[null, lseg(Heap[Heap[ptr, next], next], null)] := Mask[null, lseg(Heap[Heap[ptr, next], next], null)] - perm;
          
          // -- Record predicate instance information
            assume InsidePredicate(lseg(Heap[ptr, next], null), Heap[null, lseg(Heap[ptr, next], null)], lseg(Heap[Heap[ptr, next], next], null), Heap[null, lseg(Heap[Heap[ptr, next], next], null)]);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)])) else EmptyFrame));
            if (UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null) {
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null;
              UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] != null ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] != null) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_56: Ref, f_60: (Field A B) ::
                    { newPMask[o_56, f_60] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][o_56, f_60] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], next], null)][o_56, f_60] ==> newPMask[o_56, f_60]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          if (UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null) {
            assert {:msg "  Folding lseg(ptr.next, null) might fail. Assertion ptr.next.data <= ptr.next.next.data might not hold. (linked-list-predicates.vpr@156.5--156.35) [1234]"}
              UnfoldingHeap[UnfoldingHeap[ptr, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data];
          }
        }
        
        // -- Free assumptions (exhale module)
          if (Heap[Heap[ptr, next], next] != null) {
            Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][Heap[Heap[ptr, next], next], data] := true;
            Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][Heap[Heap[ptr, next], next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_57: Ref, f_61: (Field A B) ::
              { newPMask[o_57, f_61] }
              Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][o_57, f_61] || Heap[null, lseg#sm(Heap[Heap[Heap[ptr, next], next], next], null)][o_57, f_61] ==> newPMask[o_57, f_61]
            );
            Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)] := newPMask;
          }
          assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume lseg#trigger(Heap, lseg(Heap[ptr, next], null));
        assume Heap[null, lseg(Heap[ptr, next], null)] == FrameFragment((if Heap[ptr, next] != null then CombineFrames(FrameFragment(Heap[Heap[ptr, next], data]), CombineFrames(FrameFragment(Heap[Heap[ptr, next], next]), Heap[null, lseg(Heap[Heap[ptr, next], next], null)])) else EmptyFrame));
        if (!HasDirectPerm(Mask, null, lseg(Heap[ptr, next], null))) {
          Heap[null, lseg#sm(Heap[ptr, next], null)] := ZeroPMask;
          havoc freshVersion;
          Heap[null, lseg(Heap[ptr, next], null)] := freshVersion;
        }
        if (Heap[ptr, next] != null) {
          Heap[null, lseg#sm(Heap[ptr, next], null)][Heap[ptr, next], data] := true;
          Heap[null, lseg#sm(Heap[ptr, next], null)][Heap[ptr, next], next] := true;
          havoc newPMask;
          assume (forall <A, B> o_58: Ref, f_62: (Field A B) ::
            { newPMask[o_58, f_62] }
            Heap[null, lseg#sm(Heap[ptr, next], null)][o_58, f_62] || Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][o_58, f_62] ==> newPMask[o_58, f_62]
          );
          Heap[null, lseg#sm(Heap[ptr, next], null)] := newPMask;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: fold acc(lseg(ptr, null), write) -- linked-list-predicates.vpr@159.5--159.30
        if (ptr != null) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(ptr, null) might fail. There might be insufficient permission to access ptr.data (linked-list-predicates.vpr@159.5--159.30) [1237]"}
              perm <= Mask[ptr, data];
          }
          Mask[ptr, data] := Mask[ptr, data] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(ptr, null) might fail. There might be insufficient permission to access ptr.next (linked-list-predicates.vpr@159.5--159.30) [1239]"}
              perm <= Mask[ptr, next];
          }
          Mask[ptr, next] := Mask[ptr, next] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Folding lseg(ptr, null) might fail. There might be insufficient permission to access lseg(ptr.next, null) (linked-list-predicates.vpr@159.5--159.30) [1241]"}
              perm <= Mask[null, lseg(Heap[ptr, next], null)];
          }
          Mask[null, lseg(Heap[ptr, next], null)] := Mask[null, lseg(Heap[ptr, next], null)] - perm;
          
          // -- Record predicate instance information
            assume InsidePredicate(lseg(ptr, null), Heap[null, lseg(ptr, null)], lseg(Heap[ptr, next], null), Heap[null, lseg(Heap[ptr, next], null)]);
          
          // -- Execute unfolding (for extra information)
            UnfoldingHeap := Heap;
            UnfoldingMask := Mask;
            assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[ptr, next], null));
            assume UnfoldingHeap[null, lseg(UnfoldingHeap[ptr, next], null)] == FrameFragment((if UnfoldingHeap[ptr, next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptr, next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[ptr, next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)])) else EmptyFrame));
            if (UnfoldingHeap[ptr, next] != null) {
              perm := FullPerm;
              assume UnfoldingHeap[ptr, next] != null;
              UnfoldingMask[UnfoldingHeap[ptr, next], data] := UnfoldingMask[UnfoldingHeap[ptr, next], data] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              assume UnfoldingHeap[ptr, next] != null;
              UnfoldingMask[UnfoldingHeap[ptr, next], next] := UnfoldingMask[UnfoldingHeap[ptr, next], next] + perm;
              assume state(UnfoldingHeap, UnfoldingMask);
              perm := FullPerm;
              UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] + perm;
              
              // -- Extra unfolding of predicate
                assume InsidePredicate(lseg(UnfoldingHeap[ptr, next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[ptr, next], null)], lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)]);
              assume state(UnfoldingHeap, UnfoldingMask);
              assume UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null ==> UnfoldingHeap[UnfoldingHeap[ptr, next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], data];
              
              // -- Free assumptions (inhale module)
                if (UnfoldingHeap[UnfoldingHeap[ptr, next], next] != null) {
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)][UnfoldingHeap[UnfoldingHeap[ptr, next], next], data] := true;
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)][UnfoldingHeap[UnfoldingHeap[ptr, next], next], next] := true;
                  havoc newPMask;
                  assume (forall <A, B> o_59: Ref, f_63: (Field A B) ::
                    { newPMask[o_59, f_63] }
                    UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)][o_59, f_63] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[ptr, next], next], next], null)][o_59, f_63] ==> newPMask[o_59, f_63]
                  );
                  UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[ptr, next], next], null)] := newPMask;
                }
                assume state(UnfoldingHeap, UnfoldingMask);
            }
            assume state(UnfoldingHeap, UnfoldingMask);
          if (UnfoldingHeap[ptr, next] != null) {
            assert {:msg "  Folding lseg(ptr, null) might fail. Assertion ptr.data <= ptr.next.data might not hold. (linked-list-predicates.vpr@159.5--159.30) [1242]"}
              UnfoldingHeap[ptr, data] <= UnfoldingHeap[UnfoldingHeap[ptr, next], data];
          }
        }
        
        // -- Free assumptions (exhale module)
          if (Heap[ptr, next] != null) {
            Heap[null, lseg#sm(Heap[ptr, next], null)][Heap[ptr, next], data] := true;
            Heap[null, lseg#sm(Heap[ptr, next], null)][Heap[ptr, next], next] := true;
            havoc newPMask;
            assume (forall <A, B> o_60: Ref, f_64: (Field A B) ::
              { newPMask[o_60, f_64] }
              Heap[null, lseg#sm(Heap[ptr, next], null)][o_60, f_64] || Heap[null, lseg#sm(Heap[Heap[ptr, next], next], null)][o_60, f_64] ==> newPMask[o_60, f_64]
            );
            Heap[null, lseg#sm(Heap[ptr, next], null)] := newPMask;
          }
          assume state(Heap, Mask);
        perm := FullPerm;
        Mask[null, lseg(ptr, null)] := Mask[null, lseg(ptr, null)] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume lseg#trigger(Heap, lseg(ptr, null));
        assume Heap[null, lseg(ptr, null)] == FrameFragment((if ptr != null then CombineFrames(FrameFragment(Heap[ptr, data]), CombineFrames(FrameFragment(Heap[ptr, next]), Heap[null, lseg(Heap[ptr, next], null)])) else EmptyFrame));
        if (!HasDirectPerm(Mask, null, lseg(ptr, null))) {
          Heap[null, lseg#sm(ptr, null)] := ZeroPMask;
          havoc freshVersion;
          Heap[null, lseg(ptr, null)] := freshVersion;
        }
        if (ptr != null) {
          Heap[null, lseg#sm(ptr, null)][ptr, data] := true;
          Heap[null, lseg#sm(ptr, null)][ptr, next] := true;
          havoc newPMask;
          assume (forall <A, B> o_61: Ref, f_65: (Field A B) ::
            { newPMask[o_61, f_65] }
            Heap[null, lseg#sm(ptr, null)][o_61, f_65] || Heap[null, lseg#sm(Heap[ptr, next], null)][o_61, f_65] ==> newPMask[o_61, f_65]
          );
          Heap[null, lseg#sm(ptr, null)] := newPMask;
        }
        assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: concat(this.head, ptr, null) -- linked-list-predicates.vpr@160.5--160.33
        PreCallHeap := Heap;
        PreCallMask := Mask;
        
        // -- Check definedness of this.head
          assert {:msg "  Method call might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@160.5--160.33) [1244]"}
            HasDirectPerm(Mask, this, head);
        arg_this_1 := Heap[this, head];
        
        // -- Exhaling precondition
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access lseg(this.head, ptr) (linked-list-predicates.vpr@160.5--160.33) [1245]"}
              perm <= Mask[null, lseg(arg_this_1, ptr)];
          }
          Mask[null, lseg(arg_this_1, ptr)] := Mask[null, lseg(arg_this_1, ptr)] - perm;
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access lseg(ptr, null) (linked-list-predicates.vpr@160.5--160.33) [1246]"}
              perm <= Mask[null, lseg(ptr, null)];
          }
          Mask[null, lseg(ptr, null)] := Mask[null, lseg(ptr, null)] - perm;
          if (null != null) {
            assert {:msg "  The precondition of method concat might not hold. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@160.5--160.33) [1247]"}
              1 / 2 >= NoPerm;
            perm := 1 / 2;
            if (perm != NoPerm) {
              assert {:msg "  The precondition of method concat might not hold. There might be insufficient permission to access null.next (linked-list-predicates.vpr@160.5--160.33) [1248]"}
                perm <= Mask[null, next];
            }
            Mask[null, next] := Mask[null, next] - perm;
          }
          if (0 < Seq#Length(contentNodes(Heap, arg_this_1, ptr)) && 0 < Seq#Length(contentNodes(Heap, ptr, null))) {
            assert {:msg "  The precondition of method concat might not hold. Assertion contentNodes(this.head, ptr)[|contentNodes(this.head, ptr)| - 1] <= contentNodes(ptr, null)[0] might not hold. (linked-list-predicates.vpr@160.5--160.33) [1249]"}
              Seq#Index(contentNodes(Heap, arg_this_1, ptr), Seq#Length(contentNodes(Heap, arg_this_1, ptr)) - 1) <= Seq#Index(contentNodes(Heap, ptr, null), 0);
          }
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
        
        // -- Inhaling postcondition
          perm := FullPerm;
          Mask[null, lseg(arg_this_1, null)] := Mask[null, lseg(arg_this_1, null)] + perm;
          assume state(Heap, Mask);
          assume state(Heap, Mask);
          assume Seq#Equal(contentNodes(Heap, arg_this_1, null), Seq#Append(contentNodes(old(PreCallHeap), arg_this_1, ptr), contentNodes(old(PreCallHeap), ptr, null)));
          if (null != null) {
            perm := 1 / 2;
            assert {:msg "  Method call might fail. Fraction 1 / 2 might be negative. (linked-list-predicates.vpr@160.5--160.33) [1250]"}
              perm >= NoPerm;
            assume perm > NoPerm ==> null != null;
            Mask[null, next] := Mask[null, next] + perm;
            assume state(Heap, Mask);
          }
          assume state(Heap, Mask);
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(List(this), write) -- linked-list-predicates.vpr@163.3--163.23
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(this) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@163.3--163.23) [1252]"}
        perm <= Mask[this, head];
    }
    Mask[this, head] := Mask[this, head] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(this) might fail. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@163.3--163.23) [1254]"}
        perm <= Mask[null, lseg(Heap[this, head], null)];
    }
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] - perm;
    
    // -- Record predicate instance information
      assume InsidePredicate(List(this), Heap[null, List(this)], lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)]);
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume List#trigger(Heap, List(this));
    assume Heap[null, List(this)] == CombineFrames(FrameFragment(Heap[this, head]), Heap[null, lseg(Heap[this, head], null)]);
    if (!HasDirectPerm(Mask, null, List(this))) {
      Heap[null, List#sm(this)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, List(this)] := freshVersion;
    }
    Heap[null, List#sm(this)][this, head] := true;
    havoc newPMask;
    assume (forall <A, B> o_62: Ref, f_66: (Field A B) ::
      { newPMask[o_62, f_66] }
      Heap[null, List#sm(this)][o_62, f_66] || Heap[null, lseg#sm(Heap[this, head], null)][o_62, f_66] ==> newPMask[o_62, f_66]
    );
    Heap[null, List#sm(this)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of insert might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@105.11--105.26) [1256]"}
        perm <= Mask[null, List(this)];
    }
    Mask[null, List(this)] := Mask[null, List(this)] - perm;
    assert {:msg "  Postcondition of insert might not hold. Assertion 0 <= index might not hold. (linked-list-predicates.vpr@106.11--106.54) [1257]"}
      0 <= index;
    assert {:msg "  Postcondition of insert might not hold. Assertion index <= |old(content(this))| might not hold. (linked-list-predicates.vpr@106.11--106.54) [1258]"}
      index <= Seq#Length(content(old(Heap), this));
    assert {:msg "  Postcondition of insert might not hold. Assertion content(this) == old(content(this))[0..index] ++ Seq(elem) ++ old(content(this))[index..] might not hold. (linked-list-predicates.vpr@107.11--107.100) [1259]"}
      Seq#Equal(content(Heap, this), Seq#Append(Seq#Append(Seq#Drop(Seq#Take(content(old(Heap), this), index), 0), Seq#Singleton(elem)), Seq#Drop(content(old(Heap), this), index)));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method dequeue
// ==================================================

procedure dequeue(this: Ref) returns (res: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var newVersion: FrameType;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var newPMask: PMaskType;
  var freshVersion: FrameType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[this, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    
    // -- Check definedness of 0 < length(this)
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@168.16--168.28) [1260]"}
            perm <= Mask[null, List(this)];
        }
        Mask[null, List(this)] := Mask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assume 0 < length(Heap, this);
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
    PostMask[null, List(this)] := PostMask[null, List(this)] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of res == old(content(this)[0])
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@170.22--170.35) [1261]"}
            perm <= old(Mask)[null, List(this)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
      assert {:msg "  Contract might not be well-formed. Index content(this)[0] into content(this) might exceed sequence length. (linked-list-predicates.vpr@170.11--170.39) [1262]"}
        0 < Seq#Length(content(old(Heap), this));
    assume res == Seq#Index(content(old(Heap), this), 0);
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of content(this) == old(content(this)[1..])
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@171.11--171.24) [1263]"}
            perm <= PostMask[null, List(this)];
        }
        PostMask[null, List(this)] := PostMask[null, List(this)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(PostHeap, ExhaleHeap, PostMask);
        PostHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@171.32--171.45) [1264]"}
            perm <= old(Mask)[null, List(this)];
        }
        // Finish exhale
        // Stop execution
        assume false;
      }
    assume Seq#Equal(content(PostHeap, this), Seq#Drop(content(old(Heap), this), 1));
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: unfold acc(List(this), write) -- linked-list-predicates.vpr@173.3--173.25
    assume List#trigger(Heap, List(this));
    assume Heap[null, List(this)] == CombineFrames(FrameFragment(Heap[this, head]), Heap[null, lseg(Heap[this, head], null)]);
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding List(this) might fail. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@173.3--173.25) [1266]"}
        perm <= Mask[null, List(this)];
    }
    Mask[null, List(this)] := Mask[null, List(this)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, List(this))) {
        havoc newVersion;
        Heap[null, List(this)] := newVersion;
      }
    perm := FullPerm;
    assume this != null;
    Mask[this, head] := Mask[this, head] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] + perm;
    
    // -- Extra unfolding of predicate
      assume InsidePredicate(List(this), Heap[null, List(this)], lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)]);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(lseg(this.head, null), write) -- linked-list-predicates.vpr@174.3--174.36
    
    // -- Check definedness of acc(lseg(this.head, null), write)
      assert {:msg "  Unfolding lseg(this.head, null) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@174.3--174.36) [1269]"}
        HasDirectPerm(Mask, this, head);
    assume lseg#trigger(Heap, lseg(Heap[this, head], null));
    assume Heap[null, lseg(Heap[this, head], null)] == FrameFragment((if Heap[this, head] != null then CombineFrames(FrameFragment(Heap[Heap[this, head], data]), CombineFrames(FrameFragment(Heap[Heap[this, head], next]), Heap[null, lseg(Heap[Heap[this, head], next], null)])) else EmptyFrame));
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding lseg(this.head, null) might fail. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@174.3--174.36) [1271]"}
        perm <= Mask[null, lseg(Heap[this, head], null)];
    }
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, lseg(Heap[this, head], null))) {
        havoc newVersion;
        Heap[null, lseg(Heap[this, head], null)] := newVersion;
      }
    if (Heap[this, head] != null) {
      perm := FullPerm;
      assume Heap[this, head] != null;
      Mask[Heap[this, head], data] := Mask[Heap[this, head], data] + perm;
      assume state(Heap, Mask);
      perm := FullPerm;
      assume Heap[this, head] != null;
      Mask[Heap[this, head], next] := Mask[Heap[this, head], next] + perm;
      assume state(Heap, Mask);
      perm := FullPerm;
      Mask[null, lseg(Heap[Heap[this, head], next], null)] := Mask[null, lseg(Heap[Heap[this, head], next], null)] + perm;
      
      // -- Extra unfolding of predicate
        assume InsidePredicate(lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)], lseg(Heap[Heap[this, head], next], null), Heap[null, lseg(Heap[Heap[this, head], next], null)]);
      assume state(Heap, Mask);
      
      // -- Execute unfolding (for extra information)
        UnfoldingHeap := Heap;
        UnfoldingMask := Mask;
        assume lseg#trigger(UnfoldingHeap, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null));
        assume UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] == FrameFragment((if UnfoldingHeap[UnfoldingHeap[this, head], next] != null then CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data]), CombineFrames(FrameFragment(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next]), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)])) else EmptyFrame));
        perm := FullPerm;
        UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)] - perm;
        if (UnfoldingHeap[UnfoldingHeap[this, head], next] != null) {
          perm := FullPerm;
          assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
          UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], data] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          assume UnfoldingHeap[UnfoldingHeap[this, head], next] != null;
          UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] := UnfoldingMask[UnfoldingHeap[UnfoldingHeap[this, head], next], next] + perm;
          assume state(UnfoldingHeap, UnfoldingMask);
          perm := FullPerm;
          UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := UnfoldingMask[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] + perm;
          
          // -- Extra unfolding of predicate
            assume InsidePredicate(lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[this, head], next], null)], lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null), UnfoldingHeap[null, lseg(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)]);
          assume state(UnfoldingHeap, UnfoldingMask);
          assume UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null ==> UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], data] <= UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data];
          
          // -- Free assumptions (inhale module)
            if (UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next] != null) {
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], data] := true;
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next] := true;
              havoc newPMask;
              assume (forall <A, B> o_63: Ref, f_67: (Field A B) ::
                { newPMask[o_63, f_67] }
                UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)][o_63, f_67] || UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], next], null)][o_63, f_67] ==> newPMask[o_63, f_67]
              );
              UnfoldingHeap[null, lseg#sm(UnfoldingHeap[UnfoldingHeap[UnfoldingHeap[this, head], next], next], null)] := newPMask;
            }
            assume state(UnfoldingHeap, UnfoldingMask);
        }
        assume state(UnfoldingHeap, UnfoldingMask);
      assume Heap[Heap[this, head], next] != null ==> Heap[Heap[this, head], data] <= Heap[Heap[Heap[this, head], next], data];
      
      // -- Free assumptions (inhale module)
        if (Heap[Heap[this, head], next] != null) {
          Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], data] := true;
          Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][Heap[Heap[this, head], next], next] := true;
          havoc newPMask;
          assume (forall <A, B> o_64: Ref, f_68: (Field A B) ::
            { newPMask[o_64, f_68] }
            Heap[null, lseg#sm(Heap[Heap[this, head], next], null)][o_64, f_68] || Heap[null, lseg#sm(Heap[Heap[Heap[this, head], next], next], null)][o_64, f_68] ==> newPMask[o_64, f_68]
          );
          Heap[null, lseg#sm(Heap[Heap[this, head], next], null)] := newPMask;
        }
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: res := this.head.data -- linked-list-predicates.vpr@175.3--175.24
    
    // -- Check definedness of this.head.data
      assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head.data (linked-list-predicates.vpr@175.3--175.24) [1275]"}
        HasDirectPerm(Mask, Heap[this, head], data);
      assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@175.3--175.24) [1276]"}
        HasDirectPerm(Mask, this, head);
    res := Heap[Heap[this, head], data];
    assume state(Heap, Mask);
  
  // -- Translating statement: this.head := this.head.next -- linked-list-predicates.vpr@176.3--176.30
    
    // -- Check definedness of this.head.next
      assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head.next (linked-list-predicates.vpr@176.3--176.30) [1277]"}
        HasDirectPerm(Mask, Heap[this, head], next);
      assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@176.3--176.30) [1278]"}
        HasDirectPerm(Mask, this, head);
    assert {:msg "  Assignment might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@176.3--176.30) [1279]"}
      FullPerm == Mask[this, head];
    Heap[this, head] := Heap[Heap[this, head], next];
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(List(this), write) -- linked-list-predicates.vpr@177.3--177.23
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(this) might fail. There might be insufficient permission to access this.head (linked-list-predicates.vpr@177.3--177.23) [1281]"}
        perm <= Mask[this, head];
    }
    Mask[this, head] := Mask[this, head] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(this) might fail. There might be insufficient permission to access lseg(this.head, null) (linked-list-predicates.vpr@177.3--177.23) [1283]"}
        perm <= Mask[null, lseg(Heap[this, head], null)];
    }
    Mask[null, lseg(Heap[this, head], null)] := Mask[null, lseg(Heap[this, head], null)] - perm;
    
    // -- Record predicate instance information
      assume InsidePredicate(List(this), Heap[null, List(this)], lseg(Heap[this, head], null), Heap[null, lseg(Heap[this, head], null)]);
    perm := FullPerm;
    Mask[null, List(this)] := Mask[null, List(this)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume List#trigger(Heap, List(this));
    assume Heap[null, List(this)] == CombineFrames(FrameFragment(Heap[this, head]), Heap[null, lseg(Heap[this, head], null)]);
    if (!HasDirectPerm(Mask, null, List(this))) {
      Heap[null, List#sm(this)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, List(this)] := freshVersion;
    }
    Heap[null, List#sm(this)][this, head] := true;
    havoc newPMask;
    assume (forall <A, B> o_65: Ref, f_69: (Field A B) ::
      { newPMask[o_65, f_69] }
      Heap[null, List#sm(this)][o_65, f_69] || Heap[null, lseg#sm(Heap[this, head], null)][o_65, f_69] ==> newPMask[o_65, f_69]
    );
    Heap[null, List#sm(this)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of dequeue might not hold. There might be insufficient permission to access List(this) (linked-list-predicates.vpr@169.11--169.26) [1285]"}
        perm <= Mask[null, List(this)];
    }
    Mask[null, List(this)] := Mask[null, List(this)] - perm;
    assert {:msg "  Postcondition of dequeue might not hold. Assertion res == old(content(this)[0]) might not hold. (linked-list-predicates.vpr@170.11--170.39) [1286]"}
      res == Seq#Index(content(old(Heap), this), 0);
    assert {:msg "  Postcondition of dequeue might not hold. Assertion content(this) == old(content(this)[1..]) might not hold. (linked-list-predicates.vpr@171.11--171.51) [1287]"}
      Seq#Equal(content(Heap, this), Seq#Drop(content(old(Heap), this), 1));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method test
// ==================================================

procedure test(lock: Ref) returns ()
  modifies Heap, Mask;
{
  var acq_lblGuard: bool;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var r_1: Ref;
  var perm: Perm;
  var LabelacqMask: MaskType;
  var LabelacqHeap: HeapType;
  var ExhaleHeap: HeapType;
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var r1: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
    acq_lblGuard := false;
  
  // -- Assumptions about method arguments
    assume Heap[lock, $allocated];
  
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
        assume false;
      }
    
    // -- Normally inhale the exhale part.
      
      // -- Check definedness of (forperm r: Ref [r.held] :: false)
        if (*) {
          if (HasDirectPerm(PostMask, r_1, held)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access r.held (linked-list-predicates.vpr@195.11--195.51) [1288]"}
              HasDirectPerm(PostMask, r_1, held);
          }
          assume false;
        }
      assume (forall r_1_1: Ref ::
        { PostMask[r_1_1, held] }
        HasDirectPerm(PostMask, r_1_1, held) ==> false
      );
      assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: inhale acc(List(lock), write) &&
  //   (acc(lock.held, write) && acc(lock.changed, write)) -- linked-list-predicates.vpr@198.3--198.64
    perm := FullPerm;
    Mask[null, List(lock)] := Mask[null, List(lock)] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    assume lock != null;
    Mask[lock, held] := Mask[lock, held] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    assume lock != null;
    Mask[lock, changed] := Mask[lock, changed] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: label acq -- linked-list-predicates.vpr@199.1--199.10
    acq:
    LabelacqMask := Mask;
    LabelacqHeap := Heap;
    acq_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Translating statement: if (2 <= length(lock)) -- linked-list-predicates.vpr@201.3--208.4
    
    // -- Check definedness of 2 <= length(lock)
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access List(lock) (linked-list-predicates.vpr@201.11--201.23) [1292]"}
            perm <= Mask[null, List(lock)];
        }
        Mask[null, List(lock)] := Mask[null, List(lock)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    if (2 <= length(Heap, lock)) {
      
      // -- Translating statement: r1 := dequeue(lock) -- linked-list-predicates.vpr@203.5--203.24
        PreCallHeap := Heap;
        PreCallMask := Mask;
        havoc r1;
        
        // -- Exhaling precondition
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  The precondition of method dequeue might not hold. There might be insufficient permission to access List(lock) (linked-list-predicates.vpr@203.5--203.24) [1293]"}
              perm <= Mask[null, List(lock)];
          }
          Mask[null, List(lock)] := Mask[null, List(lock)] - perm;
          assert {:msg "  The precondition of method dequeue might not hold. Assertion 0 < length(lock) might not hold. (linked-list-predicates.vpr@203.5--203.24) [1294]"}
            0 < length(Heap, lock);
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
          Heap := ExhaleHeap;
        
        // -- Inhaling postcondition
          perm := FullPerm;
          Mask[null, List(lock)] := Mask[null, List(lock)] + perm;
          assume state(Heap, Mask);
          assume state(Heap, Mask);
          assume r1 == Seq#Index(content(old(PreCallHeap), lock), 0);
          assume state(Heap, Mask);
          assume Seq#Equal(content(Heap, lock), Seq#Drop(content(old(PreCallHeap), lock), 1));
          assume state(Heap, Mask);
        assume state(Heap, Mask);
      
      // -- Translating statement: assert r1 <= peek(lock) -- linked-list-predicates.vpr@205.5--205.28
        
        // -- Check definedness of r1 <= peek(lock)
          if (*) {
            // Exhale precondition of function application
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Precondition of function peek might not hold. There might be insufficient permission to access List(lock) (linked-list-predicates.vpr@205.18--205.28) [1295]"}
                perm <= Mask[null, List(lock)];
            }
            Mask[null, List(lock)] := Mask[null, List(lock)] - perm;
            assert {:msg "  Precondition of function peek might not hold. Assertion 0 < length(lock) might not hold. (linked-list-predicates.vpr@205.18--205.28) [1296]"}
              0 < length(Heap, lock);
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
            // Stop execution
            assume false;
          }
        assert {:msg "  Assert might fail. Assertion r1 <= peek(lock) might not hold. (linked-list-predicates.vpr@205.12--205.28) [1297]"}
          r1 <= peek(Heap, lock);
        assume state(Heap, Mask);
      
      // -- Translating statement: lock.changed := true -- linked-list-predicates.vpr@207.5--207.25
        assert {:msg "  Assignment might fail. There might be insufficient permission to access lock.changed (linked-list-predicates.vpr@207.5--207.25) [1298]"}
          FullPerm == Mask[lock, changed];
        Heap[lock, changed] := true;
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(List(lock), write) &&
  //   (acc(lock.held, write) &&
  //   (acc(lock.changed, write) &&
  //   (old[acq](content(lock)) == content(lock) || lock.changed))) -- linked-list-predicates.vpr@211.3--212.71
    
    // -- Check definedness of acc(List(lock), write) && (acc(lock.held, write) && (acc(lock.changed, write) && (old[acq](content(lock)) == content(lock) || lock.changed)))
      assert {:msg "  Exhale might fail. Did not reach labelled state acq required to evaluate old[acq](content(lock)). (linked-list-predicates.vpr@211.13--212.71) [1299]"}
        acq_lblGuard;
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(lock) (linked-list-predicates.vpr@212.23--212.36) [1300]"}
            perm <= LabelacqMask[null, List(lock)];
        }
        LabelacqMask[null, List(lock)] := LabelacqMask[null, List(lock)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(LabelacqHeap, ExhaleHeap, LabelacqMask);
        LabelacqHeap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function content might not hold. There might be insufficient permission to access List(lock) (linked-list-predicates.vpr@212.41--212.54) [1301]"}
            perm <= Mask[null, List(lock)];
        }
        Mask[null, List(lock)] := Mask[null, List(lock)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      if (!Seq#Equal(content(LabelacqHeap, lock), content(Heap, lock))) {
        assert {:msg "  Exhale might fail. There might be insufficient permission to access lock.changed (linked-list-predicates.vpr@211.13--212.71) [1302]"}
          HasDirectPerm(Mask, lock, changed);
      }
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Exhale might fail. There might be insufficient permission to access List(lock) (linked-list-predicates.vpr@211.13--212.71) [1304]"}
        perm <= Mask[null, List(lock)];
    }
    Mask[null, List(lock)] := Mask[null, List(lock)] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Exhale might fail. There might be insufficient permission to access lock.held (linked-list-predicates.vpr@211.13--212.71) [1306]"}
        perm <= Mask[lock, held];
    }
    Mask[lock, held] := Mask[lock, held] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Exhale might fail. There might be insufficient permission to access lock.changed (linked-list-predicates.vpr@211.13--212.71) [1308]"}
        perm <= Mask[lock, changed];
    }
    Mask[lock, changed] := Mask[lock, changed] - perm;
    assert {:msg "  Exhale might fail. Assertion old[acq](content(lock)) == content(lock) || lock.changed might not hold. (linked-list-predicates.vpr@211.13--212.71) [1309]"}
      Seq#Equal(content(LabelacqHeap, lock), content(Heap, lock)) || Heap[lock, changed];
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of test might not hold. Assertion (forperm r: Ref [r.held] :: false) might not hold. (linked-list-predicates.vpr@195.11--195.51) [1310]"}
      (forall r_2: Ref ::
      { Mask[r_2, held] }
      HasDirectPerm(Mask, r_2, held) ==> false
    );
}