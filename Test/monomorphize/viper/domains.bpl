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
// Translation of domain List
// ==================================================

// The type for domain List
type ListDomainType T;

// Translation of domain function nil
function  nil<T>(): ListDomainType T;

// Translation of domain function cons
function  cons<T>(x: T, xs: (ListDomainType T)): ListDomainType T;

// Translation of domain function length
function  length<T>(xs: (ListDomainType T)): int;

// Translation of domain axiom nil_length
axiom (forall <T>  ::

  (length((nil(): ListDomainType T)): int) == 0
);

// Translation of domain axiom cons_length
axiom (forall <T> x_1: T ::

  (forall xs_1: (ListDomainType T) ::
    { (length((cons(x_1, xs_1): ListDomainType T)): int) } { (length(xs_1): int) }
    (length((cons(x_1, xs_1): ListDomainType T)): int) == (length(xs_1): int) + 1
  )
);

// Translation of domain axiom nil_cons
axiom (forall <T> z: T ::

  (forall zs: (ListDomainType T) ::
    { (cons(z, zs): ListDomainType T) }
    (cons(z, zs): ListDomainType T) != (nil(): ListDomainType T)
  )
);

// ==================================================
// Translation of domain Pair
// ==================================================

// The type for domain Pair
type PairDomainType A B;

// Translation of domain function Pair_pair
function  Pair_pair<A, B>(a_2: A, b_2: B): PairDomainType A B;

// Translation of domain function Pair_first
function  Pair_first<A, B>(p_1: (PairDomainType A B)): A;

// Translation of domain function Pair_second
function  Pair_second<A, B>(p_1: (PairDomainType A B)): B;

// Translation of domain axiom Pair_access_first
axiom (forall <A, B> a_3: A, b_3: B ::
  { (Pair_first((Pair_pair(a_3, b_3): PairDomainType A B)): A) }
  (Pair_first((Pair_pair(a_3, b_3): PairDomainType A B)): A) == a_3
);

// Translation of domain axiom Pair_access_second
axiom (forall <A, B> a_3: A, b_3: B ::
  { (Pair_second((Pair_pair(a_3, b_3): PairDomainType A B)): B) }
  (Pair_second((Pair_pair(a_3, b_3): PairDomainType A B)): B) == b_3
);

// ==================================================
// Translation of domain Triple
// ==================================================

// The type for domain Triple
type TripleDomainType A B C;

// Translation of domain function Triple_triple
function  Triple_triple<A, B, C>(a_2: A, b_2: B, c: C): TripleDomainType A B C;

// Translation of domain function Triple_first
function  Triple_first<A, B, C>(t_1: (TripleDomainType A B C)): A;

// Translation of domain function Triple_second
function  Triple_second<A, B, C>(t_1: (TripleDomainType A B C)): B;

// Translation of domain function Triple_third
function  Triple_third<A, B, C>(t_1: (TripleDomainType A B C)): C;

// Translation of domain function Triple_isPrefix
function  Triple_isPrefix<A, B, C>(p_1: (PairDomainType A B), t_1: (TripleDomainType A B C)): bool;

// Translation of domain axiom Triple_access_first
axiom (forall <A, B, C> a_3: A, b_3: B, c_1: C ::
  { (Triple_first((Triple_triple(a_3, b_3, c_1): TripleDomainType A B C)): A) }
  (Triple_first((Triple_triple(a_3, b_3, c_1): TripleDomainType A B C)): A) == a_3
);

// Translation of domain axiom Triple_access_second
axiom (forall <A, B, C> a_3: A, b_3: B, c_1: C ::
  { (Triple_second((Triple_triple(a_3, b_3, c_1): TripleDomainType A B C)): B) }
  (Triple_second((Triple_triple(a_3, b_3, c_1): TripleDomainType A B C)): B) == b_3
);

// Translation of domain axiom Triple_access_third
axiom (forall <A, B, C> a_3: A, b_3: B, c_1: C ::
  { (Triple_third((Triple_triple(a_3, b_3, c_1): TripleDomainType A B C)): C) }
  (Triple_third((Triple_triple(a_3, b_3, c_1): TripleDomainType A B C)): C) == c_1
);

// Translation of domain axiom Triple_is_prefix
axiom (forall <A, B, C> p_2: (PairDomainType A B), t_2: (TripleDomainType A B C) ::
  { (Triple_isPrefix(p_2, t_2): bool) } { (Pair_first(p_2): A), (Triple_first(t_2): A) } { (Pair_first(p_2): A), (Triple_second(t_2): B) } { (Triple_first(t_2): A), (Pair_second(p_2): B) } { (Pair_second(p_2): B), (Triple_second(t_2): B) }
  (Triple_isPrefix(p_2, t_2): bool) == ((Pair_first(p_2): A) == (Triple_first(t_2): A) && (Pair_second(p_2): B) == (Triple_second(t_2): B))
);

// ==================================================
// Translation of domain L
// ==================================================

// The type for domain L
type LDomainType;

// Translation of domain function f1
function  f1(x: int): int;

// Translation of domain function f2
function  f2(x: int): int;

// ==================================================
// Translation of domain Foo
// ==================================================

// The type for domain Foo
type FooDomainType A;

// Translation of domain function foo
function  foo<A>(a_2: A): int;

// Translation of domain function fooid
function  fooid<A>(a_2: A): A;

// Translation of domain axiom foo_ax1
axiom (forall <A> a_3: A ::
  { (foo(a_3): int) }
  (foo(a_3): int) > 0
);

// Translation of domain axiom foo_ax2
axiom (forall <A> a_3: A ::
  { (fooid(a_3): A) }
  (fooid(a_3): A) == a_3
);

// ==================================================
// Translation of domain Bar
// ==================================================

// The type for domain Bar
type BarDomainType A B;

// Translation of domain function barfoo1
function  barfoo1<A>(a_2: A): bool;

// Translation of domain function barfoo2
function  barfoo2<A>(a_2: A): int;

// Translation of domain axiom bar_ax1
axiom (forall <A> a_3: A ::
  { (barfoo1(a_3): bool) }
  (barfoo1(a_3): bool)
);

// Translation of domain axiom bar_ax2
axiom (forall <B> b_3: B ::

  (barfoo1(null): bool)
);

// Translation of domain axiom bar_ax3
axiom (forall <A> a_3: A ::
  { (barfoo2(a_3): int) } { (hide(a_3): int) }
  (barfoo2(a_3): int) != (hide(a_3): int)
);

// ==================================================
// Translation of domain Hidden
// ==================================================

// The type for domain Hidden
type HiddenDomainType A;

// Translation of domain function hide
function  hide<A>(a_2: A): int;

// Translation of domain axiom hidden_ax1
axiom (forall <A> a_3: A ::
  { (hide(a_3): int) }
  (hide(a_3): int) == 0
);

// ==================================================
// Translation of domain D10A
// ==================================================

// The type for domain D10A
type D10ADomainType A;

// Translation of domain function hide2
function  hide2<A>(a_2: A): int;

// ==================================================
// Translation of domain D10B
// ==================================================

// The type for domain D10B
type D10BDomainType;

// Translation of domain axiom d10b_ax1
axiom (forall x_1: int ::
  { (hide2(x_1): int) }
  (hide2(x_1): int) > 0
);

// ==================================================
// Translation of domain D10C
// ==================================================

// The type for domain D10C
type D10CDomainType A;

// Translation of domain axiom d10c_ax1
axiom (forall r_1: Ref ::
  { (hide2(r_1): int) }
  (hide2(r_1): int) < 0
);

// ==================================================
// Translation of domain Cell
// ==================================================

// The type for domain Cell
type CellDomainType A;

// Translation of domain function Cell_cell
function  Cell_cell<A>(a_2: A): CellDomainType A;

// Translation of domain function Cell_get
function  Cell_get<A>(c: (CellDomainType A)): A;

// Translation of domain axiom cell_ax1
axiom (forall <A> a_3: A ::
  { (Cell_get((Cell_cell(a_3): CellDomainType A)): A) }
  (Cell_get((Cell_cell(a_3): CellDomainType A)): A) == a_3
);

// ==================================================
// Translation of method test
// ==================================================

procedure test(x_1: int, xs_1: (ListDomainType int)) returns ()
  modifies Heap, Mask;
{
  var n: (ListDomainType int);

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: n := (nil(): List[Int]) -- domains.vpr@20.5--20.30
    n := (nil(): ListDomainType int);
    assume state(Heap, Mask);

  // -- Translating statement: assert (length(n): Int) == 0 -- domains.vpr@21.5--21.26
    assert {:msg "  Assert might fail. Assertion (length(n): Int) == 0 might not hold. (domains.vpr@21.12--21.26) [19]"}
      (length(n): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert n != (cons(x, xs): List[Int]) -- domains.vpr@22.5--22.28
    assert {:msg "  Assert might fail. Assertion n != (cons(x, xs): List[Int]) might not hold. (domains.vpr@22.12--22.28) [20]"}
      n != (cons(x_1, xs_1): ListDomainType int);
    assume state(Heap, Mask);

  // -- Translating statement: assert (length((cons(1, n): List[Int])): Int) == 1 -- domains.vpr@23.5--23.35
    assert {:msg "  Assert might fail. Assertion (length((cons(1, n): List[Int])): Int) == 1 might not hold. (domains.vpr@23.12--23.35) [21]"}
      (length((cons(1, n): ListDomainType int)): int) == 1;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test2
// ==================================================

procedure test2(a_3: int, b_3: bool) returns ()
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: assert (Pair_first((Pair_pair(a, b): Pair[Int, Bool])): Int) == a -- domains.vpr@68.3--68.42
    assert {:msg "  Assert might fail. Assertion (Pair_first((Pair_pair(a, b): Pair[Int, Bool])): Int) == a might not hold. (domains.vpr@68.10--68.42) [22]"}
      (Pair_first((Pair_pair(a_3, b_3): PairDomainType int bool)): int) == a_3;
    assume state(Heap, Mask);

  // -- Translating statement: assert (Pair_second((Pair_pair(a, b): Pair[Int, Bool])): Bool) == b -- domains.vpr@69.3--69.43
    assert {:msg "  Assert might fail. Assertion (Pair_second((Pair_pair(a, b): Pair[Int, Bool])): Bool) == b might not hold. (domains.vpr@69.10--69.43) [23]"}
      (Pair_second((Pair_pair(a_3, b_3): PairDomainType int bool)): bool) == b_3;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test3
// ==================================================

procedure test3(a_3: int, b_3: bool, c_1: Ref) returns ()
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Assumptions about method arguments
    assume Heap[c_1, $allocated];

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: assert (Triple_first((Triple_triple(a, b, c): Triple[Int, Bool, Ref])): Int) ==
  //   a -- domains.vpr@73.3--73.51
    assert {:msg "  Assert might fail. Assertion (Triple_first((Triple_triple(a, b, c): Triple[Int, Bool, Ref])): Int) == a might not hold. (domains.vpr@73.10--73.51) [24]"}
      (Triple_first((Triple_triple(a_3, b_3, c_1): TripleDomainType int bool Ref)): int) == a_3;
    assume state(Heap, Mask);

  // -- Translating statement: assert (Triple_second((Triple_triple(a, b, c): Triple[Int, Bool, Ref])): Bool) ==
  //   b -- domains.vpr@74.3--74.52
    assert {:msg "  Assert might fail. Assertion (Triple_second((Triple_triple(a, b, c): Triple[Int, Bool, Ref])): Bool) == b might not hold. (domains.vpr@74.10--74.52) [25]"}
      (Triple_second((Triple_triple(a_3, b_3, c_1): TripleDomainType int bool Ref)): bool) == b_3;
    assume state(Heap, Mask);

  // -- Translating statement: assert (Triple_third((Triple_triple(a, b, c): Triple[Int, Bool, Ref])): Ref) ==
  //   c -- domains.vpr@75.3--75.51
    assert {:msg "  Assert might fail. Assertion (Triple_third((Triple_triple(a, b, c): Triple[Int, Bool, Ref])): Ref) == c might not hold. (domains.vpr@75.10--75.51) [26]"}
      (Triple_third((Triple_triple(a_3, b_3, c_1): TripleDomainType int bool Ref)): Ref) == c_1;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test4
// ==================================================

procedure test4(a_3: int, b_3: bool, c_1: Ref) returns ()
  modifies Heap, Mask;
{
  var p_2: (PairDomainType int bool);
  var t_2: (TripleDomainType int bool Ref);

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Assumptions about method arguments
    assume Heap[c_1, $allocated];

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: p := (Pair_pair(a, b): Pair[Int, Bool]) -- domains.vpr@79.3--79.44
    p_2 := (Pair_pair(a_3, b_3): PairDomainType int bool);
    assume state(Heap, Mask);

  // -- Translating statement: t := (Triple_triple(a, b, c): Triple[Int, Bool, Ref]) -- domains.vpr@80.3--80.58
    t_2 := (Triple_triple(a_3, b_3, c_1): TripleDomainType int bool Ref);
    assume state(Heap, Mask);

  // -- Translating statement: assert (Triple_isPrefix(p, t): Bool) -- domains.vpr@81.3--81.31
    assert {:msg "  Assert might fail. Assertion (Triple_isPrefix(p, t): Bool) might not hold. (domains.vpr@81.10--81.31) [27]"}
      (Triple_isPrefix(p_2, t_2): bool);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method t5
// ==================================================

procedure t5() returns ()
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: inhale (forall i: Int :: { f1(i), f2(i) } f1(i) > 0) -- domains.vpr@91.10--91.50

    // -- Check definedness of (forall i: Int :: { f1(i), f2(i) } f1(i) > 0)
      if (*) {
        assume false;
      }
    assume (forall i_1: int ::
      { (f1(i_1): int), (f2(i_1): int) }
      (f1(i_1): int) > 0
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method t6
// ==================================================

procedure t6() returns ()
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: assert (foo(1): Int) > 0 -- domains.vpr@107.3--107.20
    assert {:msg "  Assert might fail. Assertion (foo(1): Int) > 0 might not hold. (domains.vpr@107.10--107.20) [28]"}
      (foo(1): int) > 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert (foo(null): Int) > 0 -- domains.vpr@108.3--108.23
    assert {:msg "  Assert might fail. Assertion (foo(null): Int) > 0 might not hold. (domains.vpr@108.10--108.23) [29]"}
      (foo(null): int) > 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert (foo(none): Int) > 0 -- domains.vpr@109.3--109.23
    assert {:msg "  Assert might fail. Assertion (foo(none): Int) > 0 might not hold. (domains.vpr@109.10--109.23) [30]"}
      (foo(NoPerm): int) > 0;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test7
// ==================================================

procedure test7() returns ()
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: assert (barfoo2(101): Int) != 0 -- domains.vpr@128.3--128.27
    assert {:msg "  Assert might fail. Assertion (barfoo2(101): Int) != 0 might not hold. (domains.vpr@128.10--128.27) [31]"}
      (barfoo2(101): int) != 0;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test8
// ==================================================

procedure test8() returns ()
  modifies Heap, Mask;
{

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: assert (hide2(101): Int) > 0 -- domains.vpr@144.3--144.24
    assert {:msg "  Assert might fail. Assertion (hide2(101): Int) > 0 might not hold. (domains.vpr@144.10--144.24) [32]"}
      (hide2(101): int) > 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert (hide2(null): Int) < 0 -- domains.vpr@145.3--145.25
    assert {:msg "  Assert might fail. Assertion (hide2(null): Int) < 0 might not hold. (domains.vpr@145.10--145.25) [33]"}
      (hide2(null): int) < 0;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test9
// ==================================================

procedure test9() returns ()
  modifies Heap, Mask;
{
  var c1: (CellDomainType int);
  var c2: (CellDomainType Ref);

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: c1 := (Cell_cell(0): Cell[Int]) -- domains.vpr@156.2--156.35
    c1 := (Cell_cell(0): CellDomainType int);
    assume state(Heap, Mask);

  // -- Translating statement: assert c1 == (Cell_cell(0): Cell[Int]) -- domains.vpr@158.3--158.28
    assert {:msg "  Assert might fail. Assertion c1 == (Cell_cell(0): Cell[Int]) might not hold. (domains.vpr@158.10--158.28) [34]"}
      c1 == (Cell_cell(0): CellDomainType int);
    assume state(Heap, Mask);

  // -- Translating statement: assert (Cell_get(c1): Int) == 0 -- domains.vpr@159.2--159.26
    assert {:msg "  Assert might fail. Assertion (Cell_get(c1): Int) == 0 might not hold. (domains.vpr@159.9--159.26) [35]"}
      (Cell_get(c1): int) == 0;
    assume state(Heap, Mask);

  // -- Translating statement: assert (Cell_get(c1): Int) == (Cell_get((Cell_cell(0): Cell[Int])): Int) -- domains.vpr@160.2--160.47
    assert {:msg "  Assert might fail. Assertion (Cell_get(c1): Int) == (Cell_get((Cell_cell(0): Cell[Int])): Int) might not hold. (domains.vpr@160.9--160.47) [36]"}
      (Cell_get(c1): int) == (Cell_get((Cell_cell(0): CellDomainType int)): int);
    assume state(Heap, Mask);

  // -- Translating statement: c2 := (Cell_cell(null): Cell[Ref]) -- domains.vpr@162.2--162.38
    c2 := (Cell_cell(null): CellDomainType Ref);
    assume state(Heap, Mask);

  // -- Translating statement: assert (Cell_get(c2): Ref) == null -- domains.vpr@164.2--164.29
    assert {:msg "  Assert might fail. Assertion (Cell_get(c2): Ref) == null might not hold. (domains.vpr@164.9--164.29) [37]"}
      (Cell_get(c2): Ref) == null;
    assume state(Heap, Mask);
}
