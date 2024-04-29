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

function  neverTriggered1(k$0_1: int): bool;
function  neverTriggered2(k$1_1: int): bool;
function  neverTriggered3(k$1_2: int): bool;
function  neverTriggered4(k$2: int): bool;
function  neverTriggered5(k$2_2: int): bool;
function  neverTriggered6(k$2_3: int): bool;
function  neverTriggered7(k$2_4: int): bool;
function  neverTriggered8(k$2_5: int): bool;
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
// Translation of domain IArray
// ==================================================

// The type for domain IArray
type IArrayDomainType;

// Translation of domain function loc
function  loc(a_2: IArrayDomainType, i: int): Ref;

// Translation of domain function len
function  len(a_2: IArrayDomainType): int;

// Translation of domain function first
function  first(r_1: Ref): IArrayDomainType;

// Translation of domain function second
function  second(r_1: Ref): int;

// Translation of domain axiom all_diff
axiom (forall a_3: IArrayDomainType, i_1: int ::
  { (loc(a_3, i_1): Ref) }
  (first((loc(a_3, i_1): Ref)): IArrayDomainType) == a_3 && (second((loc(a_3, i_1): Ref)): int) == i_1
);

// Translation of domain axiom length_nonneg
axiom (forall a_3: IArrayDomainType ::
  { (len(a_3): int) }
  (len(a_3): int) >= 0
);

// ==================================================
// Translation of all fields
// ==================================================

const unique val: Field NormalField int;
axiom !IsPredicateField(val);
axiom !IsWandField(val);

// ==================================================
// Translation of method lcp
// ==================================================

procedure lcp(a_3: IArrayDomainType, x: int, y: int) returns (n: int)
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var k: int;
  var k_4: int;
  var ExhaleHeap: HeapType;
  var k_2: int;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var k_9: int;
  var k_2_1: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Checked inhaling of precondition

    // -- Check definedness of (forall k$0: Int :: { loc(a, k$0) } 0 <= k$0 && k$0 < len(a) ==> acc(loc(a, k$0).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, k$0).val might not be injective. (longest-common-prefix.vpr@16.12--16.21) [105]"}
      (forall k$0_1: int, k$0_1_1: int ::

      (((k$0_1 != k$0_1_1 && (0 <= k$0_1 && k$0_1 < (len(a_3): int))) && (0 <= k$0_1_1 && k$0_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$0_1): Ref) != (loc(a_3, k$0_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall k$0_1: int ::
        { (loc(a_3, k$0_1): Ref) } { (loc(a_3, k$0_1): Ref) }
        (0 <= k$0_1 && k$0_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange1((loc(a_3, k$0_1): Ref)) && invRecv1((loc(a_3, k$0_1): Ref)) == k$0_1
      );
      assume (forall o_3: Ref ::
        { invRecv1(o_3) }
        ((0 <= invRecv1(o_3) && invRecv1(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange1(o_3) ==> (loc(a_3, invRecv1(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall k$0_1: int ::
        { (loc(a_3, k$0_1): Ref) } { (loc(a_3, k$0_1): Ref) }
        0 <= k$0_1 && k$0_1 < (len(a_3): int) ==> (loc(a_3, k$0_1): Ref) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        (((0 <= invRecv1(o_3) && invRecv1(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange1(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv1(o_3)): Ref) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!(((0 <= invRecv1(o_3) && invRecv1(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange1(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume 0 <= x;
    assume 0 <= y;
    assume x < (len(a_3): int);
    assume y < (len(a_3): int);
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

    // -- Check definedness of (forall k$1: Int :: { loc(a, k$1) } 0 <= k$1 && k$1 < len(a) ==> acc(loc(a, k$1).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, k$1).val might not be injective. (longest-common-prefix.vpr@18.12--18.21) [106]"}
      (forall k$1_1: int, k$1_1_1: int ::

      (((k$1_1 != k$1_1_1 && (0 <= k$1_1 && k$1_1 < (len(a_3): int))) && (0 <= k$1_1_1 && k$1_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$1_1): Ref) != (loc(a_3, k$1_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall k$1_1: int ::
        { (loc(a_3, k$1_1): Ref) } { (loc(a_3, k$1_1): Ref) }
        (0 <= k$1_1 && k$1_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange2((loc(a_3, k$1_1): Ref)) && invRecv2((loc(a_3, k$1_1): Ref)) == k$1_1
      );
      assume (forall o_3: Ref ::
        { invRecv2(o_3) }
        ((0 <= invRecv2(o_3) && invRecv2(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange2(o_3) ==> (loc(a_3, invRecv2(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall k$1_1: int ::
        { (loc(a_3, k$1_1): Ref) } { (loc(a_3, k$1_1): Ref) }
        0 <= k$1_1 && k$1_1 < (len(a_3): int) ==> (loc(a_3, k$1_1): Ref) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        (((0 <= invRecv2(o_3) && invRecv2(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange2(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv2(o_3)): Ref) == o_3) && QPMask[o_3, val] == PostMask[o_3, val] + FullPerm) && (!(((0 <= invRecv2(o_3) && invRecv2(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange2(o_3)) ==> QPMask[o_3, val] == PostMask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { PostMask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> PostMask[o_3, f_5] == QPMask[o_3, f_5]
      );
    PostMask := QPMask;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    assume 0 <= n;
    assume x + n <= (len(a_3): int);
    assume y + n <= (len(a_3): int);
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall k: Int :: { loc(a, k) } x <= k && k < x + n ==> loc(a, k).val == loc(a, y + k - x).val)
      if (*) {
        if (x <= k && k < x + n) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, k).val (longest-common-prefix.vpr@20.12--20.91) [107]"}
            HasDirectPerm(PostMask, (loc(a_3, k): Ref), val);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, y + k - x).val (longest-common-prefix.vpr@20.12--20.91) [108]"}
            HasDirectPerm(PostMask, (loc(a_3, y + k - x): Ref), val);
        }
        assume false;
      }
    assume (forall k_1: int ::
      { (loc(a_3, k_1): Ref) }
      x <= k_1 && k_1 < x + n ==> PostHeap[(loc(a_3, k_1): Ref), val] == PostHeap[(loc(a_3, y + k_1 - x): Ref), val]
    );
    assume state(PostHeap, PostMask);
    if (x + n < (len(a_3): int) && y + n < (len(a_3): int)) {

      // -- Check definedness of loc(a, x + n).val != loc(a, y + n).val
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, x + n).val (longest-common-prefix.vpr@26.12--26.87) [109]"}
          HasDirectPerm(PostMask, (loc(a_3, x + n): Ref), val);
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, y + n).val (longest-common-prefix.vpr@26.12--26.87) [110]"}
          HasDirectPerm(PostMask, (loc(a_3, y + n): Ref), val);
      assume PostHeap[(loc(a_3, x + n): Ref), val] != PostHeap[(loc(a_3, y + n): Ref), val];
    }
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Translating statement: n := 0 -- longest-common-prefix.vpr@28.4--28.10
    n := 0;
    assume state(Heap, Mask);

  // -- Translating statement: while (x + n < len(a) && (y + n < len(a) && loc(a, x + n).val == loc(a, y + n).val)) -- longest-common-prefix.vpr@29.4--36.5

    // -- Before loop head

      // -- Exhale loop invariant before loop
        assert {:msg "  Loop invariant n >= 0 might not hold on entry. Assertion n >= 0 might not hold. (longest-common-prefix.vpr@30.16--30.22) [111]"}
          n >= 0;
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver loc(a, k$2) is injective
          assert {:msg "  Loop invariant (forall k$2: Int :: { loc(a, k$2) } 0 <= k$2 && k$2 < len(a) ==> acc(loc(a, k$2).val, write)) might not hold on entry. Quantified resource loc(a, k$2).val might not be injective. (longest-common-prefix.vpr@31.16--31.25) [112]"}
            (forall k$2: int, k$2_1: int ::
            { neverTriggered4(k$2), neverTriggered4(k$2_1) }
            (((k$2 != k$2_1 && (0 <= k$2 && k$2 < (len(a_3): int))) && (0 <= k$2_1 && k$2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$2): Ref) != (loc(a_3, k$2_1): Ref)
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant (forall k$2: Int :: { loc(a, k$2) } 0 <= k$2 && k$2 < len(a) ==> acc(loc(a, k$2).val, write)) might not hold on entry. There might be insufficient permission to access loc(a, k$2).val (longest-common-prefix.vpr@31.16--31.25) [113]"}
            (forall k$2: int ::
            { (loc(a_3, k$2): Ref) } { (loc(a_3, k$2): Ref) }
            0 <= k$2 && k$2 < (len(a_3): int) ==> Mask[(loc(a_3, k$2): Ref), val] >= FullPerm
          );

        // -- assumptions for inverse of receiver loc(a, k$2)
          assume (forall k$2: int ::
            { (loc(a_3, k$2): Ref) } { (loc(a_3, k$2): Ref) }
            (0 <= k$2 && k$2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange4((loc(a_3, k$2): Ref)) && invRecv4((loc(a_3, k$2): Ref)) == k$2
          );
          assume (forall o_3: Ref ::
            { invRecv4(o_3) }
            (0 <= invRecv4(o_3) && invRecv4(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange4(o_3)) ==> (loc(a_3, invRecv4(o_3)): Ref) == o_3
          );

        // -- assume permission updates for field val
          assume (forall o_3: Ref ::
            { QPMask[o_3, val] }
            ((0 <= invRecv4(o_3) && invRecv4(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange4(o_3)) ==> (loc(a_3, invRecv4(o_3)): Ref) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!((0 <= invRecv4(o_3) && invRecv4(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange4(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assert {:msg "  Loop invariant x + n <= len(a) && y + n <= len(a) might not hold on entry. Assertion x + n <= len(a) might not hold. (longest-common-prefix.vpr@32.16--32.50) [114]"}
          x + n <= (len(a_3): int);
        assert {:msg "  Loop invariant x + n <= len(a) && y + n <= len(a) might not hold on entry. Assertion y + n <= len(a) might not hold. (longest-common-prefix.vpr@32.16--32.50) [115]"}
          y + n <= (len(a_3): int);
        if (*) {
          if (x <= k_4 && k_4 < x + n) {
            assert {:msg "  Loop invariant (forall k: Int :: { loc(a, k) } x <= k && k < x + n ==> loc(a, k).val == loc(a, y + k - x).val) might not hold on entry. Assertion loc(a, k).val == loc(a, y + k - x).val might not hold. (longest-common-prefix.vpr@33.16--33.95) [116]"}
              Heap[(loc(a_3, k_4): Ref), val] == Heap[(loc(a_3, y + k_4 - x): Ref), val];
          }
          assume false;
        }
        assume (forall k_5_1: int ::
          { (loc(a_3, k_5_1): Ref) }
          x <= k_5_1 && k_5_1 < x + n ==> Heap[(loc(a_3, k_5_1): Ref), val] == Heap[(loc(a_3, y + k_5_1 - x): Ref), val]
        );
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;

    // -- Havoc loop written variables (except locals)
      havoc n;

    // -- Check definedness of invariant
      if (*) {
        assume n >= 0;
        assume state(Heap, Mask);

        // -- Check definedness of (forall k$2: Int :: { loc(a, k$2) } 0 <= k$2 && k$2 < len(a) ==> acc(loc(a, k$2).val, write))
          if (*) {
            assume false;
          }
        havoc QPMask;
        assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, k$2).val might not be injective. (longest-common-prefix.vpr@31.16--31.25) [117]"}
          (forall k$2_2: int, k$2_2_1: int ::

          (((k$2_2 != k$2_2_1 && (0 <= k$2_2 && k$2_2 < (len(a_3): int))) && (0 <= k$2_2_1 && k$2_2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$2_2): Ref) != (loc(a_3, k$2_2_1): Ref)
        );

        // -- Define Inverse Function
          assume (forall k$2_2: int ::
            { (loc(a_3, k$2_2): Ref) } { (loc(a_3, k$2_2): Ref) }
            (0 <= k$2_2 && k$2_2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange5((loc(a_3, k$2_2): Ref)) && invRecv5((loc(a_3, k$2_2): Ref)) == k$2_2
          );
          assume (forall o_3: Ref ::
            { invRecv5(o_3) }
            ((0 <= invRecv5(o_3) && invRecv5(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange5(o_3) ==> (loc(a_3, invRecv5(o_3)): Ref) == o_3
          );

        // -- Assume set of fields is nonNull
          assume (forall k$2_2: int ::
            { (loc(a_3, k$2_2): Ref) } { (loc(a_3, k$2_2): Ref) }
            0 <= k$2_2 && k$2_2 < (len(a_3): int) ==> (loc(a_3, k$2_2): Ref) != null
          );

        // -- Define permissions
          assume (forall o_3: Ref ::
            { QPMask[o_3, val] }
            (((0 <= invRecv5(o_3) && invRecv5(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange5(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv5(o_3)): Ref) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!(((0 <= invRecv5(o_3) && invRecv5(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange5(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
          );
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
            f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        assume x + n <= (len(a_3): int);
        assume y + n <= (len(a_3): int);
        assume state(Heap, Mask);

        // -- Check definedness of (forall k: Int :: { loc(a, k) } x <= k && k < x + n ==> loc(a, k).val == loc(a, y + k - x).val)
          if (*) {
            if (x <= k_2 && k_2 < x + n) {
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, k).val (longest-common-prefix.vpr@33.16--33.95) [118]"}
                HasDirectPerm(Mask, (loc(a_3, k_2): Ref), val);
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, y + k - x).val (longest-common-prefix.vpr@33.16--33.95) [119]"}
                HasDirectPerm(Mask, (loc(a_3, y + k_2 - x): Ref), val);
            }
            assume false;
          }
        assume (forall k_7: int ::
          { (loc(a_3, k_7): Ref) }
          x <= k_7 && k_7 < x + n ==> Heap[(loc(a_3, k_7): Ref), val] == Heap[(loc(a_3, y + k_7 - x): Ref), val]
        );
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
        assume n >= 0;
        havoc QPMask;
        assert {:msg "  While statement might fail. Quantified resource loc(a, k$2).val might not be injective. (longest-common-prefix.vpr@31.16--31.25) [120]"}
          (forall k$2_3: int, k$2_3_1: int ::

          (((k$2_3 != k$2_3_1 && (0 <= k$2_3 && k$2_3 < (len(a_3): int))) && (0 <= k$2_3_1 && k$2_3_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$2_3): Ref) != (loc(a_3, k$2_3_1): Ref)
        );

        // -- Define Inverse Function
          assume (forall k$2_3: int ::
            { (loc(a_3, k$2_3): Ref) } { (loc(a_3, k$2_3): Ref) }
            (0 <= k$2_3 && k$2_3 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange6((loc(a_3, k$2_3): Ref)) && invRecv6((loc(a_3, k$2_3): Ref)) == k$2_3
          );
          assume (forall o_3: Ref ::
            { invRecv6(o_3) }
            ((0 <= invRecv6(o_3) && invRecv6(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange6(o_3) ==> (loc(a_3, invRecv6(o_3)): Ref) == o_3
          );

        // -- Assume set of fields is nonNull
          assume (forall k$2_3: int ::
            { (loc(a_3, k$2_3): Ref) } { (loc(a_3, k$2_3): Ref) }
            0 <= k$2_3 && k$2_3 < (len(a_3): int) ==> (loc(a_3, k$2_3): Ref) != null
          );

        // -- Define permissions
          assume (forall o_3: Ref ::
            { QPMask[o_3, val] }
            (((0 <= invRecv6(o_3) && invRecv6(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange6(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv6(o_3)): Ref) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!(((0 <= invRecv6(o_3) && invRecv6(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange6(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
          );
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
            f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assume state(Heap, Mask);
        assume x + n <= (len(a_3): int);
        assume y + n <= (len(a_3): int);
        assume (forall k_8: int ::
          { (loc(a_3, k_8): Ref) }
          x <= k_8 && k_8 < x + n ==> Heap[(loc(a_3, k_8): Ref), val] == Heap[(loc(a_3, y + k_8 - x): Ref), val]
        );
        assume state(Heap, Mask);
        // Check and assume guard

        // -- Check definedness of x + n < len(a) && (y + n < len(a) && loc(a, x + n).val == loc(a, y + n).val)
          if (x + n < (len(a_3): int)) {
            if (y + n < (len(a_3): int)) {
              assert {:msg "  While statement might fail. There might be insufficient permission to access loc(a, x + n).val (longest-common-prefix.vpr@29.11--29.86) [121]"}
                HasDirectPerm(Mask, (loc(a_3, x + n): Ref), val);
              assert {:msg "  While statement might fail. There might be insufficient permission to access loc(a, y + n).val (longest-common-prefix.vpr@29.11--29.86) [122]"}
                HasDirectPerm(Mask, (loc(a_3, y + n): Ref), val);
            }
          }
        assume x + n < (len(a_3): int) && (y + n < (len(a_3): int) && Heap[(loc(a_3, x + n): Ref), val] == Heap[(loc(a_3, y + n): Ref), val]);
        assume state(Heap, Mask);

        // -- Translate loop body

          // -- Translating statement: n := n + 1 -- longest-common-prefix.vpr@35.6--35.16
            n := n + 1;
            assume state(Heap, Mask);
        // Exhale invariant
        assert {:msg "  Loop invariant n >= 0 might not be preserved. Assertion n >= 0 might not hold. (longest-common-prefix.vpr@30.16--30.22) [123]"}
          n >= 0;
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver loc(a, k$2) is injective
          assert {:msg "  Loop invariant (forall k$2: Int :: { loc(a, k$2) } 0 <= k$2 && k$2 < len(a) ==> acc(loc(a, k$2).val, write)) might not be preserved. Quantified resource loc(a, k$2).val might not be injective. (longest-common-prefix.vpr@31.16--31.25) [124]"}
            (forall k$2_4: int, k$2_4_1: int ::
            { neverTriggered7(k$2_4), neverTriggered7(k$2_4_1) }
            (((k$2_4 != k$2_4_1 && (0 <= k$2_4 && k$2_4 < (len(a_3): int))) && (0 <= k$2_4_1 && k$2_4_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$2_4): Ref) != (loc(a_3, k$2_4_1): Ref)
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant (forall k$2: Int :: { loc(a, k$2) } 0 <= k$2 && k$2 < len(a) ==> acc(loc(a, k$2).val, write)) might not be preserved. There might be insufficient permission to access loc(a, k$2).val (longest-common-prefix.vpr@31.16--31.25) [125]"}
            (forall k$2_4: int ::
            { (loc(a_3, k$2_4): Ref) } { (loc(a_3, k$2_4): Ref) }
            0 <= k$2_4 && k$2_4 < (len(a_3): int) ==> Mask[(loc(a_3, k$2_4): Ref), val] >= FullPerm
          );

        // -- assumptions for inverse of receiver loc(a, k$2)
          assume (forall k$2_4: int ::
            { (loc(a_3, k$2_4): Ref) } { (loc(a_3, k$2_4): Ref) }
            (0 <= k$2_4 && k$2_4 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange7((loc(a_3, k$2_4): Ref)) && invRecv7((loc(a_3, k$2_4): Ref)) == k$2_4
          );
          assume (forall o_3: Ref ::
            { invRecv7(o_3) }
            (0 <= invRecv7(o_3) && invRecv7(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange7(o_3)) ==> (loc(a_3, invRecv7(o_3)): Ref) == o_3
          );

        // -- assume permission updates for field val
          assume (forall o_3: Ref ::
            { QPMask[o_3, val] }
            ((0 <= invRecv7(o_3) && invRecv7(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange7(o_3)) ==> (loc(a_3, invRecv7(o_3)): Ref) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!((0 <= invRecv7(o_3) && invRecv7(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange7(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
          );

        // -- assume permission updates for independent locations
          assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
            { QPMask[o_3, f_5] }
            f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
          );
        Mask := QPMask;
        assert {:msg "  Loop invariant x + n <= len(a) && y + n <= len(a) might not be preserved. Assertion x + n <= len(a) might not hold. (longest-common-prefix.vpr@32.16--32.50) [126]"}
          x + n <= (len(a_3): int);
        assert {:msg "  Loop invariant x + n <= len(a) && y + n <= len(a) might not be preserved. Assertion y + n <= len(a) might not hold. (longest-common-prefix.vpr@32.16--32.50) [127]"}
          y + n <= (len(a_3): int);
        if (*) {
          if (x <= k_9 && k_9 < x + n) {
            assert {:msg "  Loop invariant (forall k: Int :: { loc(a, k) } x <= k && k < x + n ==> loc(a, k).val == loc(a, y + k - x).val) might not be preserved. Assertion loc(a, k).val == loc(a, y + k - x).val might not hold. (longest-common-prefix.vpr@33.16--33.95) [128]"}
              Heap[(loc(a_3, k_9): Ref), val] == Heap[(loc(a_3, y + k_9 - x): Ref), val];
          }
          assume false;
        }
        assume (forall k_10_1: int ::
          { (loc(a_3, k_10_1): Ref) }
          x <= k_10_1 && k_10_1 < x + n ==> Heap[(loc(a_3, k_10_1): Ref), val] == Heap[(loc(a_3, y + k_10_1 - x): Ref), val]
        );
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Terminate execution
        assume false;
      }

    // -- Inhale loop invariant after loop, and assume guard
      assume !(x + n < (len(a_3): int) && (y + n < (len(a_3): int) && Heap[(loc(a_3, x + n): Ref), val] == Heap[(loc(a_3, y + n): Ref), val]));
      assume state(Heap, Mask);
      assume n >= 0;
      havoc QPMask;
      assert {:msg "  While statement might fail. Quantified resource loc(a, k$2).val might not be injective. (longest-common-prefix.vpr@31.16--31.25) [129]"}
        (forall k$2_5: int, k$2_5_1: int ::

        (((k$2_5 != k$2_5_1 && (0 <= k$2_5 && k$2_5 < (len(a_3): int))) && (0 <= k$2_5_1 && k$2_5_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$2_5): Ref) != (loc(a_3, k$2_5_1): Ref)
      );

      // -- Define Inverse Function
        assume (forall k$2_5: int ::
          { (loc(a_3, k$2_5): Ref) } { (loc(a_3, k$2_5): Ref) }
          (0 <= k$2_5 && k$2_5 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange8((loc(a_3, k$2_5): Ref)) && invRecv8((loc(a_3, k$2_5): Ref)) == k$2_5
        );
        assume (forall o_3: Ref ::
          { invRecv8(o_3) }
          ((0 <= invRecv8(o_3) && invRecv8(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange8(o_3) ==> (loc(a_3, invRecv8(o_3)): Ref) == o_3
        );

      // -- Assume set of fields is nonNull
        assume (forall k$2_5: int ::
          { (loc(a_3, k$2_5): Ref) } { (loc(a_3, k$2_5): Ref) }
          0 <= k$2_5 && k$2_5 < (len(a_3): int) ==> (loc(a_3, k$2_5): Ref) != null
        );

      // -- Define permissions
        assume (forall o_3: Ref ::
          { QPMask[o_3, val] }
          (((0 <= invRecv8(o_3) && invRecv8(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange8(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv8(o_3)): Ref) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!(((0 <= invRecv8(o_3) && invRecv8(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange8(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
        );
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
          f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      assume x + n <= (len(a_3): int);
      assume y + n <= (len(a_3): int);
      assume (forall k_11: int ::
        { (loc(a_3, k_11): Ref) }
        x <= k_11 && k_11 < x + n ==> Heap[(loc(a_3, k_11): Ref), val] == Heap[(loc(a_3, y + k_11 - x): Ref), val]
      );
      assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver loc(a, k$1) is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, k$1).val might not be injective. (longest-common-prefix.vpr@18.12--18.21) [130]"}
        (forall k$1_2: int, k$1_2_1: int ::
        { neverTriggered3(k$1_2), neverTriggered3(k$1_2_1) }
        (((k$1_2 != k$1_2_1 && (0 <= k$1_2 && k$1_2 < (len(a_3): int))) && (0 <= k$1_2_1 && k$1_2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, k$1_2): Ref) != (loc(a_3, k$1_2_1): Ref)
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of lcp might not hold. There might be insufficient permission to access loc(a, k$1).val (longest-common-prefix.vpr@18.12--18.21) [131]"}
        (forall k$1_2: int ::
        { (loc(a_3, k$1_2): Ref) } { (loc(a_3, k$1_2): Ref) }
        0 <= k$1_2 && k$1_2 < (len(a_3): int) ==> Mask[(loc(a_3, k$1_2): Ref), val] >= FullPerm
      );

    // -- assumptions for inverse of receiver loc(a, k$1)
      assume (forall k$1_2: int ::
        { (loc(a_3, k$1_2): Ref) } { (loc(a_3, k$1_2): Ref) }
        (0 <= k$1_2 && k$1_2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange3((loc(a_3, k$1_2): Ref)) && invRecv3((loc(a_3, k$1_2): Ref)) == k$1_2
      );
      assume (forall o_3: Ref ::
        { invRecv3(o_3) }
        (0 <= invRecv3(o_3) && invRecv3(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange3(o_3)) ==> (loc(a_3, invRecv3(o_3)): Ref) == o_3
      );

    // -- assume permission updates for field val
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        ((0 <= invRecv3(o_3) && invRecv3(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange3(o_3)) ==> (loc(a_3, invRecv3(o_3)): Ref) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!((0 <= invRecv3(o_3) && invRecv3(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange3(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
      );

    // -- assume permission updates for independent locations
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assert {:msg "  Postcondition of lcp might not hold. Assertion 0 <= n might not hold. (longest-common-prefix.vpr@19.12--19.56) [132]"}
      0 <= n;
    assert {:msg "  Postcondition of lcp might not hold. Assertion x + n <= len(a) might not hold. (longest-common-prefix.vpr@19.12--19.56) [133]"}
      x + n <= (len(a_3): int);
    assert {:msg "  Postcondition of lcp might not hold. Assertion y + n <= len(a) might not hold. (longest-common-prefix.vpr@19.12--19.56) [134]"}
      y + n <= (len(a_3): int);
    if (*) {
      if (x <= k_2_1 && k_2_1 < x + n) {
        assert {:msg "  Postcondition of lcp might not hold. Assertion loc(a, k).val == loc(a, y + k - x).val might not hold. (longest-common-prefix.vpr@20.12--20.91) [135]"}
          Heap[(loc(a_3, k_2_1): Ref), val] == Heap[(loc(a_3, y + k_2_1 - x): Ref), val];
      }
      assume false;
    }
    assume (forall k_3_1: int ::
      { (loc(a_3, k_3_1): Ref) }
      x <= k_3_1 && k_3_1 < x + n ==> Heap[(loc(a_3, k_3_1): Ref), val] == Heap[(loc(a_3, y + k_3_1 - x): Ref), val]
    );
    if (x + n < (len(a_3): int) && y + n < (len(a_3): int)) {
      assert {:msg "  Postcondition of lcp might not hold. Assertion loc(a, x + n).val != loc(a, y + n).val might not hold. (longest-common-prefix.vpr@26.12--26.87) [136]"}
        Heap[(loc(a_3, x + n): Ref), val] != Heap[(loc(a_3, y + n): Ref), val];
    }
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}
