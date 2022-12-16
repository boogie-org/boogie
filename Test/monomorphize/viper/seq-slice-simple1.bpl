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
// Translation of method example1_pkg_F
// ==================================================

procedure example1_pkg_F(xs_pkg_V0: (Seq int)) returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var xs_pkg_V0_CN0: (Seq int);
  var ys_pkg_V1: (Seq int);
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Checked inhaling of precondition
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: xs_pkg_V0_CN0 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@8.3--8.30
    xs_pkg_V0_CN0 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: xs_pkg_V0_CN0 := xs_pkg_V0 -- seq-slice-simple1.gobra.vpr@12.3--12.29
    xs_pkg_V0_CN0 := xs_pkg_V0;
    assume state(Heap, Mask);
  
  // -- Translating statement: ys_pkg_V1 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@17.3--17.26
    ys_pkg_V1 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: ys_pkg_V1 := xs_pkg_V0_CN0[1..][..14 - 1] -- seq-slice-simple1.gobra.vpr@21.3--21.44
    ys_pkg_V1 := Seq#Take(Seq#Drop(xs_pkg_V0_CN0, 1), 13);
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@22.3--22.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example2_pkg_F
// ==================================================

procedure example2_pkg_F() returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert true && [0..10)[5..] == [5..10) -- seq-slice-simple1.gobra.vpr@36.3--36.41
    assert {:msg "  Assert might fail. Assertion [0..10)[5..] == [5..10) might not hold. (seq-slice-simple1.gobra.vpr@36.10--36.41) [44]"}
      Seq#Equal(Seq#Drop(Seq#Range(0, 10), 5), Seq#Range(5, 10));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && [0..10)[..5] == [0..5) -- seq-slice-simple1.gobra.vpr@40.3--40.40
    assert {:msg "  Assert might fail. Assertion [0..10)[..5] == [0..5) might not hold. (seq-slice-simple1.gobra.vpr@40.10--40.40) [46]"}
      Seq#Equal(Seq#Take(Seq#Range(0, 10), 5), Seq#Range(0, 5));
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@41.3--41.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example3_pkg_F
// ==================================================

procedure example3_pkg_F() returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert true && [0..10)[1..][2..][3..] == [6..10) -- seq-slice-simple1.gobra.vpr@55.3--55.51
    assert {:msg "  Assert might fail. Assertion [0..10)[1..][2..][3..] == [6..10) might not hold. (seq-slice-simple1.gobra.vpr@55.10--55.51) [48]"}
      Seq#Equal(Seq#Drop(Seq#Drop(Seq#Drop(Seq#Range(0, 10), 1), 2), 3), Seq#Range(6, 10));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && [0..10)[..5][..3] == [0..3) -- seq-slice-simple1.gobra.vpr@59.3--59.45
    assert {:msg "  Assert might fail. Assertion [0..10)[..5][..3] == [0..3) might not hold. (seq-slice-simple1.gobra.vpr@59.10--59.45) [50]"}
      Seq#Equal(Seq#Take(Seq#Take(Seq#Range(0, 10), 5), 3), Seq#Range(0, 3));
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@60.3--60.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example4_pkg_F
// ==================================================

procedure example4_pkg_F(xs_pkg_V2: (Seq int)) returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var xs_pkg_V2_CN1: (Seq int);
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Checked inhaling of precondition
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: xs_pkg_V2_CN1 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@70.3--70.30
    xs_pkg_V2_CN1 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: xs_pkg_V2_CN1 := xs_pkg_V2 -- seq-slice-simple1.gobra.vpr@74.3--74.29
    xs_pkg_V2_CN1 := xs_pkg_V2;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && xs_pkg_V2_CN1[0..] == xs_pkg_V2_CN1 -- seq-slice-simple1.gobra.vpr@81.3--81.53
    assert {:msg "  Assert might fail. Assertion xs_pkg_V2_CN1[0..] == xs_pkg_V2_CN1 might not hold. (seq-slice-simple1.gobra.vpr@81.10--81.53) [52]"}
      Seq#Equal(Seq#Drop(xs_pkg_V2_CN1, 0), xs_pkg_V2_CN1);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && xs_pkg_V2_CN1[..|xs_pkg_V2_CN1|] == xs_pkg_V2_CN1 -- seq-slice-simple1.gobra.vpr@85.3--85.67
    assert {:msg "  Assert might fail. Assertion xs_pkg_V2_CN1[..|xs_pkg_V2_CN1|] == xs_pkg_V2_CN1 might not hold. (seq-slice-simple1.gobra.vpr@85.10--85.67) [54]"}
      Seq#Equal(Seq#Take(xs_pkg_V2_CN1, Seq#Length(xs_pkg_V2_CN1)), xs_pkg_V2_CN1);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && xs_pkg_V2_CN1 == xs_pkg_V2_CN1 -- seq-slice-simple1.gobra.vpr@89.3--89.48
    assert {:msg "  Assert might fail. Assertion xs_pkg_V2_CN1 == xs_pkg_V2_CN1 might not hold. (seq-slice-simple1.gobra.vpr@89.10--89.48) [56]"}
      Seq#Equal(xs_pkg_V2_CN1, xs_pkg_V2_CN1);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && xs_pkg_V2_CN1[0..][..|xs_pkg_V2_CN1| - 0] == xs_pkg_V2_CN1 -- seq-slice-simple1.gobra.vpr@93.3--93.76
    assert {:msg "  Assert might fail. Assertion xs_pkg_V2_CN1[0..][..|xs_pkg_V2_CN1| - 0] == xs_pkg_V2_CN1 might not hold. (seq-slice-simple1.gobra.vpr@93.10--93.76) [58]"}
      Seq#Equal(Seq#Take(Seq#Drop(xs_pkg_V2_CN1, 0), Seq#Length(xs_pkg_V2_CN1) - 0), xs_pkg_V2_CN1);
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@94.3--94.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example5_pkg_F
// ==================================================

procedure example5_pkg_F() returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert true && Seq(1, 2, 4, 8)[2..] == Seq(4, 8) -- seq-slice-simple1.gobra.vpr@108.3--108.51
    assert {:msg "  Assert might fail. Assertion Seq(1, 2, 4, 8)[2..] == Seq(4, 8) might not hold. (seq-slice-simple1.gobra.vpr@108.10--108.51) [60]"}
      Seq#Equal(Seq#Drop(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(1), Seq#Singleton(2)), Seq#Singleton(4)), Seq#Singleton(8)), 2), Seq#Append(Seq#Singleton(4), Seq#Singleton(8)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && Seq(1, 2, 4, 8)[..2] == Seq(1, 2) -- seq-slice-simple1.gobra.vpr@112.3--112.51
    assert {:msg "  Assert might fail. Assertion Seq(1, 2, 4, 8)[..2] == Seq(1, 2) might not hold. (seq-slice-simple1.gobra.vpr@112.10--112.51) [62]"}
      Seq#Equal(Seq#Take(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(1), Seq#Singleton(2)), Seq#Singleton(4)), Seq#Singleton(8)), 2), Seq#Append(Seq#Singleton(1), Seq#Singleton(2)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && Seq(1, 2, 4, 8)[1..][..3 - 1] == Seq(2, 4) -- seq-slice-simple1.gobra.vpr@116.3--116.60
    assert {:msg "  Assert might fail. Assertion Seq(1, 2, 4, 8)[1..][..3 - 1] == Seq(2, 4) might not hold. (seq-slice-simple1.gobra.vpr@116.10--116.60) [64]"}
      Seq#Equal(Seq#Take(Seq#Drop(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(1), Seq#Singleton(2)), Seq#Singleton(4)), Seq#Singleton(8)), 1), 2), Seq#Append(Seq#Singleton(2), Seq#Singleton(4)));
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@117.3--117.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example6_pkg_F
// ==================================================

procedure example6_pkg_F() returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert true && [0..9)[0 - 10..] == [0..9) -- seq-slice-simple1.gobra.vpr@131.3--131.44
    assert {:msg "  Assert might fail. Assertion [0..9)[0 - 10..] == [0..9) might not hold. (seq-slice-simple1.gobra.vpr@131.10--131.44) [66]"}
      Seq#Equal(Seq#Drop(Seq#Range(0, 9), -10), Seq#Range(0, 9));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && [0..9)[..1000] == [0..9) -- seq-slice-simple1.gobra.vpr@135.3--135.42
    assert {:msg "  Assert might fail. Assertion [0..9)[..1000] == [0..9) might not hold. (seq-slice-simple1.gobra.vpr@135.10--135.42) [68]"}
      Seq#Equal(Seq#Take(Seq#Range(0, 9), 1000), Seq#Range(0, 9));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && [0..9)[0 - 100..][..100 - (0 - 100)] == [0..9) -- seq-slice-simple1.gobra.vpr@139.3--139.64
    assert {:msg "  Assert might fail. Assertion [0..9)[0 - 100..][..100 - (0 - 100)] == [0..9) might not hold. (seq-slice-simple1.gobra.vpr@139.10--139.64) [70]"}
      Seq#Equal(Seq#Take(Seq#Drop(Seq#Range(0, 9), -100), 200), Seq#Range(0, 9));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && [0..9)[100..][..0 - 100 - 100] == Seq[Int]() -- seq-slice-simple1.gobra.vpr@143.3--143.62
    assert {:msg "  Assert might fail. Assertion [0..9)[100..][..0 - 100 - 100] == Seq[Int]() might not hold. (seq-slice-simple1.gobra.vpr@143.10--143.62) [72]"}
      Seq#Equal(Seq#Take(Seq#Drop(Seq#Range(0, 9), 100), -200), (Seq#Empty(): Seq int));
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@144.3--144.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example7_pkg_F
// ==================================================

procedure example7_pkg_F() returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert true && |[0..9)[5..]| == 4 -- seq-slice-simple1.gobra.vpr@158.3--158.36
    assert {:msg "  Assert might fail. Assertion |[0..9)[5..]| == 4 might not hold. (seq-slice-simple1.gobra.vpr@158.10--158.36) [74]"}
      Seq#Length(Seq#Drop(Seq#Range(0, 9), 5)) == 4;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && |[0..9)[..5]| == 5 -- seq-slice-simple1.gobra.vpr@162.3--162.36
    assert {:msg "  Assert might fail. Assertion |[0..9)[..5]| == 5 might not hold. (seq-slice-simple1.gobra.vpr@162.10--162.36) [76]"}
      Seq#Length(Seq#Take(Seq#Range(0, 9), 5)) == 5;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert true && |[0..9)[2..][..8 - 2]| == 6 -- seq-slice-simple1.gobra.vpr@166.3--166.45
    assert {:msg "  Assert might fail. Assertion |[0..9)[2..][..8 - 2]| == 6 might not hold. (seq-slice-simple1.gobra.vpr@166.10--166.45) [78]"}
      Seq#Length(Seq#Take(Seq#Drop(Seq#Range(0, 9), 2), 6)) == 6;
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@167.3--167.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example8_pkg_F
// ==================================================

procedure example8_pkg_F(xs_pkg_V3: (Seq int), x_pkg_V3: int) returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var xs_pkg_V3_CN2: (Seq int);
  var x_pkg_V3_CN3: int;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Checked inhaling of precondition
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume Seq#Contains(Seq#Drop(xs_pkg_V3, 4), x_pkg_V3);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: xs_pkg_V3_CN2 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@180.3--180.30
    xs_pkg_V3_CN2 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: x_pkg_V3_CN3 := 0 -- seq-slice-simple1.gobra.vpr@181.3--181.20
    x_pkg_V3_CN3 := 0;
    assume state(Heap, Mask);
  
  // -- Translating statement: xs_pkg_V3_CN2 := xs_pkg_V3 -- seq-slice-simple1.gobra.vpr@185.3--185.29
    xs_pkg_V3_CN2 := xs_pkg_V3;
    assume state(Heap, Mask);
  
  // -- Translating statement: x_pkg_V3_CN3 := x_pkg_V3 -- seq-slice-simple1.gobra.vpr@189.3--189.27
    x_pkg_V3_CN3 := x_pkg_V3;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert (x_pkg_V3_CN3 in xs_pkg_V3_CN2) -- seq-slice-simple1.gobra.vpr@196.3--196.41
    assert {:msg "  Assert might fail. Assertion (x_pkg_V3_CN3 in xs_pkg_V3_CN2) might not hold. (seq-slice-simple1.gobra.vpr@196.11--196.40) [79]"}
      Seq#Contains(xs_pkg_V3_CN2, x_pkg_V3_CN3);
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@197.3--197.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example9_pkg_F
// ==================================================

procedure example9_pkg_F(xs_pkg_V4: (Seq int), x_pkg_V4: int) returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var xs_pkg_V4_CN4: (Seq int);
  var x_pkg_V4_CN5: int;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Checked inhaling of precondition
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume Seq#Contains(Seq#Take(xs_pkg_V4, 7), x_pkg_V4);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: xs_pkg_V4_CN4 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@210.3--210.30
    xs_pkg_V4_CN4 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: x_pkg_V4_CN5 := 0 -- seq-slice-simple1.gobra.vpr@211.3--211.20
    x_pkg_V4_CN5 := 0;
    assume state(Heap, Mask);
  
  // -- Translating statement: xs_pkg_V4_CN4 := xs_pkg_V4 -- seq-slice-simple1.gobra.vpr@215.3--215.29
    xs_pkg_V4_CN4 := xs_pkg_V4;
    assume state(Heap, Mask);
  
  // -- Translating statement: x_pkg_V4_CN5 := x_pkg_V4 -- seq-slice-simple1.gobra.vpr@219.3--219.27
    x_pkg_V4_CN5 := x_pkg_V4;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert (x_pkg_V4_CN5 in xs_pkg_V4_CN4) -- seq-slice-simple1.gobra.vpr@226.3--226.41
    assert {:msg "  Assert might fail. Assertion (x_pkg_V4_CN5 in xs_pkg_V4_CN4) might not hold. (seq-slice-simple1.gobra.vpr@226.11--226.40) [80]"}
      Seq#Contains(xs_pkg_V4_CN4, x_pkg_V4_CN5);
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@227.3--227.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example10_pkg_F
// ==================================================

procedure example10_pkg_F(xs_pkg_V5: (Seq int), x_pkg_V5: int) returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var xs_pkg_V5_CN6: (Seq int);
  var x_pkg_V5_CN7: int;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Checked inhaling of precondition
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume !Seq#Contains(Seq#Drop(xs_pkg_V5, 5), x_pkg_V5);
    assume state(Heap, Mask);
    assume !Seq#Contains(Seq#Take(xs_pkg_V5, 5), x_pkg_V5);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: xs_pkg_V5_CN6 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@241.3--241.30
    xs_pkg_V5_CN6 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: x_pkg_V5_CN7 := 0 -- seq-slice-simple1.gobra.vpr@242.3--242.20
    x_pkg_V5_CN7 := 0;
    assume state(Heap, Mask);
  
  // -- Translating statement: xs_pkg_V5_CN6 := xs_pkg_V5 -- seq-slice-simple1.gobra.vpr@246.3--246.29
    xs_pkg_V5_CN6 := xs_pkg_V5;
    assume state(Heap, Mask);
  
  // -- Translating statement: x_pkg_V5_CN7 := x_pkg_V5 -- seq-slice-simple1.gobra.vpr@250.3--250.27
    x_pkg_V5_CN7 := x_pkg_V5;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert !((x_pkg_V5_CN7 in xs_pkg_V5_CN6)) -- seq-slice-simple1.gobra.vpr@257.3--257.44
    assert {:msg "  Assert might fail. Assertion !((x_pkg_V5_CN7 in xs_pkg_V5_CN6)) might not hold. (seq-slice-simple1.gobra.vpr@257.10--257.44) [81]"}
      !Seq#Contains(xs_pkg_V5_CN6, x_pkg_V5_CN7);
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@258.3--258.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method example11_pkg_F
// ==================================================

procedure example11_pkg_F(xs_pkg_V6: (Seq int), n_pkg_V6: int) returns ()
  modifies Heap, Mask;
{
  var returnLabel_lblGuard: bool;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var xs_pkg_V6_CN8: (Seq int);
  var n_pkg_V6_CN9: int;
  var LabelreturnLabelMask: MaskType;
  var LabelreturnLabelHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    returnLabel_lblGuard := false;
  
  // -- Checked inhaling of precondition
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
    assume Seq#Equal(xs_pkg_V6, Seq#Append(Seq#Take(xs_pkg_V6, n_pkg_V6), Seq#Drop(xs_pkg_V6, n_pkg_V6)));
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: xs_pkg_V6_CN8 := Seq[Int]() -- seq-slice-simple1.gobra.vpr@271.3--271.30
    xs_pkg_V6_CN8 := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: n_pkg_V6_CN9 := 0 -- seq-slice-simple1.gobra.vpr@272.3--272.20
    n_pkg_V6_CN9 := 0;
    assume state(Heap, Mask);
  
  // -- Translating statement: xs_pkg_V6_CN8 := xs_pkg_V6 -- seq-slice-simple1.gobra.vpr@276.3--276.29
    xs_pkg_V6_CN8 := xs_pkg_V6;
    assume state(Heap, Mask);
  
  // -- Translating statement: n_pkg_V6_CN9 := n_pkg_V6 -- seq-slice-simple1.gobra.vpr@280.3--280.27
    n_pkg_V6_CN9 := n_pkg_V6;
    assume state(Heap, Mask);
  
  // -- Translating statement: label returnLabel -- seq-slice-simple1.gobra.vpr@285.3--285.20
    returnLabel:
    LabelreturnLabelMask := Mask;
    LabelreturnLabelHeap := Heap;
    returnLabel_lblGuard := true;
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    assert {:msg "  Postcondition of example11_pkg_F might not hold. Assertion xs_pkg_V6 == xs_pkg_V6[..n_pkg_V6] ++ xs_pkg_V6[n_pkg_V6..] might not hold. (seq-slice-simple1.gobra.vpr@264.11--264.78) [82]"}
      Seq#Equal(xs_pkg_V6, Seq#Append(Seq#Take(xs_pkg_V6, n_pkg_V6), Seq#Drop(xs_pkg_V6, n_pkg_V6)));
}