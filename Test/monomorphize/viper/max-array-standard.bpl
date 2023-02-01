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

function  neverTriggered1(j_1: int): bool;
function  neverTriggered2(j$0_1: int): bool;
function  neverTriggered3(j$0_2: int): bool;
function  neverTriggered4(j$3: int): bool;
function  neverTriggered5(j$3_2: int): bool;
function  neverTriggered6(j$3_3: int): bool;
function  neverTriggered7(j$3_4: int): bool;
function  neverTriggered8(j$3_5: int): bool;
function  neverTriggered9(j_1: int): bool;
function  neverTriggered10(j_2: int): bool;
function  neverTriggered11(j$0: int): bool;
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
// Translation of method max
// ==================================================

procedure vmax(a_3: IArrayDomainType) returns (at: int)
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var j$1: int;
  var j$2: int;
  var k: int;
  var j$4: int;
  var j$5: int;
  var ExhaleHeap: HeapType;
  var j$4_1: int;
  var j$5_1: int;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var j$4_5: int;
  var j$5_5: int;
  var j$1_2: int;
  var j$2_2: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Checked inhaling of precondition

    // -- Check definedness of (forall j: Int :: { loc(a, j) } 0 <= j && j < len(a) ==> acc(loc(a, j).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j).val might not be injective. (max-array-standard.vpr@18.12--18.21) [155]"}
      (forall j_1: int, j_1_1: int ::

      (((j_1 != j_1_1 && (0 <= j_1 && j_1 < (len(a_3): int))) && (0 <= j_1_1 && j_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j_1): Ref) != (loc(a_3, j_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall j_1: int ::
        { (loc(a_3, j_1): Ref) } { (loc(a_3, j_1): Ref) }
        (0 <= j_1 && j_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange1((loc(a_3, j_1): Ref)) && invRecv1((loc(a_3, j_1): Ref)) == j_1
      );
      assume (forall o_3: Ref ::
        { invRecv1(o_3) }
        ((0 <= invRecv1(o_3) && invRecv1(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange1(o_3) ==> (loc(a_3, invRecv1(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall j_1: int ::
        { (loc(a_3, j_1): Ref) } { (loc(a_3, j_1): Ref) }
        0 <= j_1 && j_1 < (len(a_3): int) ==> (loc(a_3, j_1): Ref) != null
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

    // -- Check definedness of (forall j$0: Int :: { loc(a, j$0) } 0 <= j$0 && j$0 < len(a) ==> acc(loc(a, j$0).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$0).val might not be injective. (max-array-standard.vpr@19.12--19.37) [156]"}
      (forall j$0_1: int, j$0_1_1: int ::

      (((j$0_1 != j$0_1_1 && (0 <= j$0_1 && j$0_1 < (len(a_3): int))) && (0 <= j$0_1_1 && j$0_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$0_1): Ref) != (loc(a_3, j$0_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall j$0_1: int ::
        { (loc(a_3, j$0_1): Ref) } { (loc(a_3, j$0_1): Ref) }
        (0 <= j$0_1 && j$0_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange2((loc(a_3, j$0_1): Ref)) && invRecv2((loc(a_3, j$0_1): Ref)) == j$0_1
      );
      assume (forall o_3: Ref ::
        { invRecv2(o_3) }
        ((0 <= invRecv2(o_3) && invRecv2(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange2(o_3) ==> (loc(a_3, invRecv2(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall j$0_1: int ::
        { (loc(a_3, j$0_1): Ref) } { (loc(a_3, j$0_1): Ref) }
        0 <= j$0_1 && j$0_1 < (len(a_3): int) ==> (loc(a_3, j$0_1): Ref) != null
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

    // -- Check definedness of (forall j$1: Int :: { loc(a, j$1) } 0 <= j$1 && j$1 < len(a) ==> loc(a, j$1).val == old(loc(a, j$1).val))
      if (*) {
        if (0 <= j$1 && j$1 < (len(a_3): int)) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$1).val (max-array-standard.vpr@19.12--19.37) [157]"}
            HasDirectPerm(PostMask, (loc(a_3, j$1): Ref), val);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$1).val (max-array-standard.vpr@19.12--19.37) [158]"}
            HasDirectPerm(old(Mask), (loc(a_3, j$1): Ref), val);
        }
        assume false;
      }
    assume (forall j$1_1: int ::
      { (loc(a_3, j$1_1): Ref) }
      0 <= j$1_1 && j$1_1 < (len(a_3): int) ==> PostHeap[(loc(a_3, j$1_1): Ref), val] == old(Heap)[(loc(a_3, j$1_1): Ref), val]
    );
    assume state(PostHeap, PostMask);
    if ((len(a_3): int) == 0) {
      assume at == -1;
    } else {
      assume 0 <= at;
      assume at < (len(a_3): int);
    }
    assume state(PostHeap, PostMask);

    // -- Check definedness of (forall j$2: Int :: { loc(a, j$2) } 0 <= j$2 && j$2 < len(a) ==> loc(a, j$2).val <= loc(a, at).val)
      if (*) {
        if (0 <= j$2 && j$2 < (len(a_3): int)) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$2).val (max-array-standard.vpr@21.12--21.33) [159]"}
            HasDirectPerm(PostMask, (loc(a_3, j$2): Ref), val);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, at).val (max-array-standard.vpr@21.12--21.33) [160]"}
            HasDirectPerm(PostMask, (loc(a_3, at): Ref), val);
        }
        assume false;
      }
    assume (forall j$2_1: int ::
      { (loc(a_3, j$2_1): Ref) }
      0 <= j$2_1 && j$2_1 < (len(a_3): int) ==> PostHeap[(loc(a_3, j$2_1): Ref), val] <= PostHeap[(loc(a_3, at): Ref), val]
    );
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Translating statement: if (len(a) == 0) -- max-array-standard.vpr@23.3--40.4
    if ((len(a_3): int) == 0) {

      // -- Translating statement: at := -1 -- max-array-standard.vpr@24.5--24.13
        at := -1;
        assume state(Heap, Mask);
    } else {

      // -- Translating statement: at := 0 -- max-array-standard.vpr@26.5--26.12
        at := 0;
        assume state(Heap, Mask);

      // -- Translating statement: k := 1 -- max-array-standard.vpr@27.5--27.20
        k := 1;
        assume state(Heap, Mask);

      // -- Translating statement: while (k < len(a)) -- max-array-standard.vpr@28.5--39.6

        // -- Before loop head

          // -- Exhale loop invariant before loop
            assert {:msg "  Loop invariant 1 <= k && k <= len(a) might not hold on entry. Assertion 1 <= k might not hold. (max-array-standard.vpr@29.17--29.38) [161]"}
              1 <= k;
            assert {:msg "  Loop invariant 1 <= k && k <= len(a) might not hold on entry. Assertion k <= len(a) might not hold. (max-array-standard.vpr@29.17--29.38) [162]"}
              k <= (len(a_3): int);
            havoc QPMask;

            // -- check that the permission amount is positive


            // -- check if receiver loc(a, j$3) is injective
              assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not hold on entry. Quantified resource loc(a, j$3).val might not be injective. (max-array-standard.vpr@30.17--30.42) [163]"}
                (forall j$3: int, j$3_1: int ::
                { neverTriggered4(j$3), neverTriggered4(j$3_1) }
                (((j$3 != j$3_1 && (0 <= j$3 && j$3 < (len(a_3): int))) && (0 <= j$3_1 && j$3_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3): Ref) != (loc(a_3, j$3_1): Ref)
              );

            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not hold on entry. There might be insufficient permission to access loc(a, j$3).val (max-array-standard.vpr@30.17--30.42) [164]"}
                (forall j$3: int ::
                { (loc(a_3, j$3): Ref) } { (loc(a_3, j$3): Ref) }
                0 <= j$3 && j$3 < (len(a_3): int) ==> Mask[(loc(a_3, j$3): Ref), val] >= FullPerm
              );

            // -- assumptions for inverse of receiver loc(a, j$3)
              assume (forall j$3: int ::
                { (loc(a_3, j$3): Ref) } { (loc(a_3, j$3): Ref) }
                (0 <= j$3 && j$3 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange4((loc(a_3, j$3): Ref)) && invRecv4((loc(a_3, j$3): Ref)) == j$3
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
            if (*) {
              if (0 <= j$4 && j$4 < (len(a_3): int)) {
                assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not hold on entry. Assertion loc(a, j$4).val == old(loc(a, j$4).val) might not hold. (max-array-standard.vpr@30.17--30.42) [165]"}
                  Heap[(loc(a_3, j$4): Ref), val] == old(Heap)[(loc(a_3, j$4): Ref), val];
              }
              assume false;
            }
            assume (forall j$4_1_1: int ::
              { (loc(a_3, j$4_1_1): Ref) }
              0 <= j$4_1_1 && j$4_1_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_1_1): Ref), val] == old(Heap)[(loc(a_3, j$4_1_1): Ref), val]
            );
            assert {:msg "  Loop invariant 0 <= at && at < k might not hold on entry. Assertion 0 <= at might not hold. (max-array-standard.vpr@31.17--31.34) [166]"}
              0 <= at;
            assert {:msg "  Loop invariant 0 <= at && at < k might not hold on entry. Assertion at < k might not hold. (max-array-standard.vpr@31.17--31.34) [167]"}
              at < k;
            if (*) {
              if (0 <= j$5 && j$5 < k) {
                assert {:msg "  Loop invariant (forall j$5: Int :: { loc(a, j$5) } 0 <= j$5 && j$5 < k ==> loc(a, j$5).val <= loc(a, at).val) might not hold on entry. Assertion loc(a, j$5).val <= loc(a, at).val might not hold. (max-array-standard.vpr@32.17--32.33) [168]"}
                  Heap[(loc(a_3, j$5): Ref), val] <= Heap[(loc(a_3, at): Ref), val];
              }
              assume false;
            }
            assume (forall j$5_1_1: int ::
              { (loc(a_3, j$5_1_1): Ref) }
              0 <= j$5_1_1 && j$5_1_1 < k ==> Heap[(loc(a_3, j$5_1_1): Ref), val] <= Heap[(loc(a_3, at): Ref), val]
            );
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;

        // -- Havoc loop written variables (except locals)
          havoc k, at;

        // -- Check definedness of invariant
          if (*) {
            assume 1 <= k;
            assume k <= (len(a_3): int);
            assume state(Heap, Mask);

            // -- Check definedness of (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write))
              if (*) {
                assume false;
              }
            havoc QPMask;
            assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$3).val might not be injective. (max-array-standard.vpr@30.17--30.42) [169]"}
              (forall j$3_2: int, j$3_2_1: int ::

              (((j$3_2 != j$3_2_1 && (0 <= j$3_2 && j$3_2 < (len(a_3): int))) && (0 <= j$3_2_1 && j$3_2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3_2): Ref) != (loc(a_3, j$3_2_1): Ref)
            );

            // -- Define Inverse Function
              assume (forall j$3_2: int ::
                { (loc(a_3, j$3_2): Ref) } { (loc(a_3, j$3_2): Ref) }
                (0 <= j$3_2 && j$3_2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange5((loc(a_3, j$3_2): Ref)) && invRecv5((loc(a_3, j$3_2): Ref)) == j$3_2
              );
              assume (forall o_3: Ref ::
                { invRecv5(o_3) }
                ((0 <= invRecv5(o_3) && invRecv5(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange5(o_3) ==> (loc(a_3, invRecv5(o_3)): Ref) == o_3
              );

            // -- Assume set of fields is nonNull
              assume (forall j$3_2: int ::
                { (loc(a_3, j$3_2): Ref) } { (loc(a_3, j$3_2): Ref) }
                0 <= j$3_2 && j$3_2 < (len(a_3): int) ==> (loc(a_3, j$3_2): Ref) != null
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

            // -- Check definedness of (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val))
              if (*) {
                if (0 <= j$4_1 && j$4_1 < (len(a_3): int)) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$4).val (max-array-standard.vpr@30.17--30.42) [170]"}
                    HasDirectPerm(Mask, (loc(a_3, j$4_1): Ref), val);
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$4).val (max-array-standard.vpr@30.17--30.42) [171]"}
                    HasDirectPerm(old(Mask), (loc(a_3, j$4_1): Ref), val);
                }
                assume false;
              }
            assume (forall j$4_3: int ::
              { (loc(a_3, j$4_3): Ref) }
              0 <= j$4_3 && j$4_3 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_3): Ref), val] == old(Heap)[(loc(a_3, j$4_3): Ref), val]
            );
            assume state(Heap, Mask);
            assume 0 <= at;
            assume at < k;
            assume state(Heap, Mask);

            // -- Check definedness of (forall j$5: Int :: { loc(a, j$5) } 0 <= j$5 && j$5 < k ==> loc(a, j$5).val <= loc(a, at).val)
              if (*) {
                if (0 <= j$5_1 && j$5_1 < k) {
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$5).val (max-array-standard.vpr@32.17--32.33) [172]"}
                    HasDirectPerm(Mask, (loc(a_3, j$5_1): Ref), val);
                  assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, at).val (max-array-standard.vpr@32.17--32.33) [173]"}
                    HasDirectPerm(Mask, (loc(a_3, at): Ref), val);
                }
                assume false;
              }
            assume (forall j$5_3: int ::
              { (loc(a_3, j$5_3): Ref) }
              0 <= j$5_3 && j$5_3 < k ==> Heap[(loc(a_3, j$5_3): Ref), val] <= Heap[(loc(a_3, at): Ref), val]
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
            assume 1 <= k;
            assume k <= (len(a_3): int);
            havoc QPMask;
            assert {:msg "  While statement might fail. Quantified resource loc(a, j$3).val might not be injective. (max-array-standard.vpr@30.17--30.42) [174]"}
              (forall j$3_3: int, j$3_3_1: int ::

              (((j$3_3 != j$3_3_1 && (0 <= j$3_3 && j$3_3 < (len(a_3): int))) && (0 <= j$3_3_1 && j$3_3_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3_3): Ref) != (loc(a_3, j$3_3_1): Ref)
            );

            // -- Define Inverse Function
              assume (forall j$3_3: int ::
                { (loc(a_3, j$3_3): Ref) } { (loc(a_3, j$3_3): Ref) }
                (0 <= j$3_3 && j$3_3 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange6((loc(a_3, j$3_3): Ref)) && invRecv6((loc(a_3, j$3_3): Ref)) == j$3_3
              );
              assume (forall o_3: Ref ::
                { invRecv6(o_3) }
                ((0 <= invRecv6(o_3) && invRecv6(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange6(o_3) ==> (loc(a_3, invRecv6(o_3)): Ref) == o_3
              );

            // -- Assume set of fields is nonNull
              assume (forall j$3_3: int ::
                { (loc(a_3, j$3_3): Ref) } { (loc(a_3, j$3_3): Ref) }
                0 <= j$3_3 && j$3_3 < (len(a_3): int) ==> (loc(a_3, j$3_3): Ref) != null
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
            assume (forall j$4_4: int ::
              { (loc(a_3, j$4_4): Ref) }
              0 <= j$4_4 && j$4_4 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_4): Ref), val] == old(Heap)[(loc(a_3, j$4_4): Ref), val]
            );
            assume 0 <= at;
            assume at < k;
            assume (forall j$5_4: int ::
              { (loc(a_3, j$5_4): Ref) }
              0 <= j$5_4 && j$5_4 < k ==> Heap[(loc(a_3, j$5_4): Ref), val] <= Heap[(loc(a_3, at): Ref), val]
            );
            assume state(Heap, Mask);
            // Check and assume guard
            assume k < (len(a_3): int);
            assume state(Heap, Mask);

            // -- Translate loop body

              // -- Translating statement: if (loc(a, at).val < loc(a, k).val) -- max-array-standard.vpr@34.7--36.8

                // -- Check definedness of loc(a, at).val < loc(a, k).val
                  assert {:msg "  Conditional statement might fail. There might be insufficient permission to access loc(a, at).val (max-array-standard.vpr@34.11--34.41) [175]"}
                    HasDirectPerm(Mask, (loc(a_3, at): Ref), val);
                  assert {:msg "  Conditional statement might fail. There might be insufficient permission to access loc(a, k).val (max-array-standard.vpr@34.11--34.41) [176]"}
                    HasDirectPerm(Mask, (loc(a_3, k): Ref), val);
                if (Heap[(loc(a_3, at): Ref), val] < Heap[(loc(a_3, k): Ref), val]) {

                  // -- Translating statement: at := k -- max-array-standard.vpr@35.9--35.16
                    at := k;
                    assume state(Heap, Mask);
                }
                assume state(Heap, Mask);

              // -- Translating statement: k := k + 1 -- max-array-standard.vpr@38.7--38.17
                k := k + 1;
                assume state(Heap, Mask);
            // Exhale invariant
            assert {:msg "  Loop invariant 1 <= k && k <= len(a) might not be preserved. Assertion 1 <= k might not hold. (max-array-standard.vpr@29.17--29.38) [177]"}
              1 <= k;
            assert {:msg "  Loop invariant 1 <= k && k <= len(a) might not be preserved. Assertion k <= len(a) might not hold. (max-array-standard.vpr@29.17--29.38) [178]"}
              k <= (len(a_3): int);
            havoc QPMask;

            // -- check that the permission amount is positive


            // -- check if receiver loc(a, j$3) is injective
              assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not be preserved. Quantified resource loc(a, j$3).val might not be injective. (max-array-standard.vpr@30.17--30.42) [179]"}
                (forall j$3_4: int, j$3_4_1: int ::
                { neverTriggered7(j$3_4), neverTriggered7(j$3_4_1) }
                (((j$3_4 != j$3_4_1 && (0 <= j$3_4 && j$3_4 < (len(a_3): int))) && (0 <= j$3_4_1 && j$3_4_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3_4): Ref) != (loc(a_3, j$3_4_1): Ref)
              );

            // -- check if sufficient permission is held
              assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not be preserved. There might be insufficient permission to access loc(a, j$3).val (max-array-standard.vpr@30.17--30.42) [180]"}
                (forall j$3_4: int ::
                { (loc(a_3, j$3_4): Ref) } { (loc(a_3, j$3_4): Ref) }
                0 <= j$3_4 && j$3_4 < (len(a_3): int) ==> Mask[(loc(a_3, j$3_4): Ref), val] >= FullPerm
              );

            // -- assumptions for inverse of receiver loc(a, j$3)
              assume (forall j$3_4: int ::
                { (loc(a_3, j$3_4): Ref) } { (loc(a_3, j$3_4): Ref) }
                (0 <= j$3_4 && j$3_4 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange7((loc(a_3, j$3_4): Ref)) && invRecv7((loc(a_3, j$3_4): Ref)) == j$3_4
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
            if (*) {
              if (0 <= j$4_5 && j$4_5 < (len(a_3): int)) {
                assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not be preserved. Assertion loc(a, j$4).val == old(loc(a, j$4).val) might not hold. (max-array-standard.vpr@30.17--30.42) [181]"}
                  Heap[(loc(a_3, j$4_5): Ref), val] == old(Heap)[(loc(a_3, j$4_5): Ref), val];
              }
              assume false;
            }
            assume (forall j$4_6_1: int ::
              { (loc(a_3, j$4_6_1): Ref) }
              0 <= j$4_6_1 && j$4_6_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_6_1): Ref), val] == old(Heap)[(loc(a_3, j$4_6_1): Ref), val]
            );
            assert {:msg "  Loop invariant 0 <= at && at < k might not be preserved. Assertion 0 <= at might not hold. (max-array-standard.vpr@31.17--31.34) [182]"}
              0 <= at;
            assert {:msg "  Loop invariant 0 <= at && at < k might not be preserved. Assertion at < k might not hold. (max-array-standard.vpr@31.17--31.34) [183]"}
              at < k;
            if (*) {
              if (0 <= j$5_5 && j$5_5 < k) {
                assert {:msg "  Loop invariant (forall j$5: Int :: { loc(a, j$5) } 0 <= j$5 && j$5 < k ==> loc(a, j$5).val <= loc(a, at).val) might not be preserved. Assertion loc(a, j$5).val <= loc(a, at).val might not hold. (max-array-standard.vpr@32.17--32.33) [184]"}
                  Heap[(loc(a_3, j$5_5): Ref), val] <= Heap[(loc(a_3, at): Ref), val];
              }
              assume false;
            }
            assume (forall j$5_6_1: int ::
              { (loc(a_3, j$5_6_1): Ref) }
              0 <= j$5_6_1 && j$5_6_1 < k ==> Heap[(loc(a_3, j$5_6_1): Ref), val] <= Heap[(loc(a_3, at): Ref), val]
            );
            // Finish exhale
            havoc ExhaleHeap;
            assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
            Heap := ExhaleHeap;
            // Terminate execution
            assume false;
          }

        // -- Inhale loop invariant after loop, and assume guard
          assume !(k < (len(a_3): int));
          assume state(Heap, Mask);
          assume 1 <= k;
          assume k <= (len(a_3): int);
          havoc QPMask;
          assert {:msg "  While statement might fail. Quantified resource loc(a, j$3).val might not be injective. (max-array-standard.vpr@30.17--30.42) [185]"}
            (forall j$3_5: int, j$3_5_1: int ::

            (((j$3_5 != j$3_5_1 && (0 <= j$3_5 && j$3_5 < (len(a_3): int))) && (0 <= j$3_5_1 && j$3_5_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3_5): Ref) != (loc(a_3, j$3_5_1): Ref)
          );

          // -- Define Inverse Function
            assume (forall j$3_5: int ::
              { (loc(a_3, j$3_5): Ref) } { (loc(a_3, j$3_5): Ref) }
              (0 <= j$3_5 && j$3_5 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange8((loc(a_3, j$3_5): Ref)) && invRecv8((loc(a_3, j$3_5): Ref)) == j$3_5
            );
            assume (forall o_3: Ref ::
              { invRecv8(o_3) }
              ((0 <= invRecv8(o_3) && invRecv8(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange8(o_3) ==> (loc(a_3, invRecv8(o_3)): Ref) == o_3
            );

          // -- Assume set of fields is nonNull
            assume (forall j$3_5: int ::
              { (loc(a_3, j$3_5): Ref) } { (loc(a_3, j$3_5): Ref) }
              0 <= j$3_5 && j$3_5 < (len(a_3): int) ==> (loc(a_3, j$3_5): Ref) != null
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
          assume (forall j$4_7: int ::
            { (loc(a_3, j$4_7): Ref) }
            0 <= j$4_7 && j$4_7 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_7): Ref), val] == old(Heap)[(loc(a_3, j$4_7): Ref), val]
          );
          assume 0 <= at;
          assume at < k;
          assume (forall j$5_7: int ::
            { (loc(a_3, j$5_7): Ref) }
            0 <= j$5_7 && j$5_7 < k ==> Heap[(loc(a_3, j$5_7): Ref), val] <= Heap[(loc(a_3, at): Ref), val]
          );
          assume state(Heap, Mask);
        assume state(Heap, Mask);
    }
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver loc(a, j$0) is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$0).val might not be injective. (max-array-standard.vpr@19.12--19.21) [186]"}
        (forall j$0_2: int, j$0_2_1: int ::
        { neverTriggered3(j$0_2), neverTriggered3(j$0_2_1) }
        (((j$0_2 != j$0_2_1 && (0 <= j$0_2 && j$0_2 < (len(a_3): int))) && (0 <= j$0_2_1 && j$0_2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$0_2): Ref) != (loc(a_3, j$0_2_1): Ref)
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of max might not hold. There might be insufficient permission to access loc(a, j$0).val (max-array-standard.vpr@19.12--19.37) [187]"}
        (forall j$0_2: int ::
        { (loc(a_3, j$0_2): Ref) } { (loc(a_3, j$0_2): Ref) }
        0 <= j$0_2 && j$0_2 < (len(a_3): int) ==> Mask[(loc(a_3, j$0_2): Ref), val] >= FullPerm
      );

    // -- assumptions for inverse of receiver loc(a, j$0)
      assume (forall j$0_2: int ::
        { (loc(a_3, j$0_2): Ref) } { (loc(a_3, j$0_2): Ref) }
        (0 <= j$0_2 && j$0_2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange3((loc(a_3, j$0_2): Ref)) && invRecv3((loc(a_3, j$0_2): Ref)) == j$0_2
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
    if (*) {
      if (0 <= j$1_2 && j$1_2 < (len(a_3): int)) {
        assert {:msg "  Postcondition of max might not hold. Assertion loc(a, j$1).val == old(loc(a, j$1).val) might not hold. (max-array-standard.vpr@19.12--19.37) [188]"}
          Heap[(loc(a_3, j$1_2): Ref), val] == old(Heap)[(loc(a_3, j$1_2): Ref), val];
      }
      assume false;
    }
    assume (forall j$1_3_1: int ::
      { (loc(a_3, j$1_3_1): Ref) }
      0 <= j$1_3_1 && j$1_3_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$1_3_1): Ref), val] == old(Heap)[(loc(a_3, j$1_3_1): Ref), val]
    );
    if ((len(a_3): int) == 0) {
      assert {:msg "  Postcondition of max might not hold. Assertion at == -1 might not hold. (max-array-standard.vpr@20.12--20.61) [189]"}
        at == -1;
    } else {
      assert {:msg "  Postcondition of max might not hold. Assertion 0 <= at might not hold. (max-array-standard.vpr@20.12--20.61) [190]"}
        0 <= at;
      assert {:msg "  Postcondition of max might not hold. Assertion at < len(a) might not hold. (max-array-standard.vpr@20.12--20.61) [191]"}
        at < (len(a_3): int);
    }
    if (*) {
      if (0 <= j$2_2 && j$2_2 < (len(a_3): int)) {
        assert {:msg "  Postcondition of max might not hold. Assertion loc(a, j$2).val <= loc(a, at).val might not hold. (max-array-standard.vpr@21.12--21.33) [192]"}
          Heap[(loc(a_3, j$2_2): Ref), val] <= Heap[(loc(a_3, at): Ref), val];
      }
      assume false;
    }
    assume (forall j$2_3_1: int ::
      { (loc(a_3, j$2_3_1): Ref) }
      0 <= j$2_3_1 && j$2_3_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$2_3_1): Ref), val] <= Heap[(loc(a_3, at): Ref), val]
    );
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}

// ==================================================
// Translation of method client
// ==================================================

procedure client() returns ()
  modifies Heap, Mask;
{
  var a_3: IArrayDomainType;
  var QPMask: MaskType;
  var i_2: int;
  var PreCallHeap: HeapType;
  var PreCallMask: MaskType;
  var x: int;
  var ExhaleHeap: HeapType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: inhale len(a) == 3 -- max-array-standard.vpr@45.3--45.21
    assume (len(a_3): int) == 3;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall j: Int ::
  //     { loc(a, j) }
  //     0 <= j && j < len(a) ==> acc(loc(a, j).val, write)) -- max-array-standard.vpr@46.3--46.19

    // -- Check definedness of (forall j: Int :: { loc(a, j) } 0 <= j && j < len(a) ==> acc(loc(a, j).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Inhale might fail. Quantified resource loc(a, j).val might not be injective. (max-array-standard.vpr@46.10--46.19) [193]"}
      (forall j_1: int, j_1_1: int ::

      (((j_1 != j_1_1 && (0 <= j_1 && j_1 < (len(a_3): int))) && (0 <= j_1_1 && j_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j_1): Ref) != (loc(a_3, j_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall j_1: int ::
        { (loc(a_3, j_1): Ref) } { (loc(a_3, j_1): Ref) }
        (0 <= j_1 && j_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange9((loc(a_3, j_1): Ref)) && invRecv9((loc(a_3, j_1): Ref)) == j_1
      );
      assume (forall o_3: Ref ::
        { invRecv9(o_3) }
        ((0 <= invRecv9(o_3) && invRecv9(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange9(o_3) ==> (loc(a_3, invRecv9(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall j_1: int ::
        { (loc(a_3, j_1): Ref) } { (loc(a_3, j_1): Ref) }
        0 <= j_1 && j_1 < (len(a_3): int) ==> (loc(a_3, j_1): Ref) != null
      );

    // -- Define permissions
      assume (forall o_3: Ref ::
        { QPMask[o_3, val] }
        (((0 <= invRecv9(o_3) && invRecv9(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange9(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv9(o_3)): Ref) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!(((0 <= invRecv9(o_3) && invRecv9(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange9(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
      );
      assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
        { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
        f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale (forall i: Int ::
  //     { loc(a, i) }
  //     0 <= i && i < len(a) ==> loc(a, i).val == i) -- max-array-standard.vpr@47.3--47.70

    // -- Check definedness of (forall i: Int :: { loc(a, i) } 0 <= i && i < len(a) ==> loc(a, i).val == i)
      if (*) {
        if (0 <= i_2 && i_2 < (len(a_3): int)) {
          assert {:msg "  Inhale might fail. There might be insufficient permission to access loc(a, i).val (max-array-standard.vpr@47.10--47.70) [194]"}
            HasDirectPerm(Mask, (loc(a_3, i_2): Ref), val);
        }
        assume false;
      }
    assume (forall i_1_1: int ::
      { (loc(a_3, i_1_1): Ref) }
      0 <= i_1_1 && i_1_1 < (len(a_3): int) ==> Heap[(loc(a_3, i_1_1): Ref), val] == i_1_1
    );
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: x := max(a) -- max-array-standard.vpr@50.3--50.14
    PreCallHeap := Heap;
    PreCallMask := Mask;
    havoc x;

    // -- Exhaling precondition
      havoc QPMask;

      // -- check that the permission amount is positive


      // -- check if receiver loc(a, j) is injective
        assert {:msg "  The precondition of method max might not hold. Quantified resource loc(a, j).val might not be injective. (max-array-standard.vpr@50.3--50.14) [195]"}
          (forall j_2: int, j_2_1: int ::
          { neverTriggered10(j_2), neverTriggered10(j_2_1) }
          (((j_2 != j_2_1 && (0 <= j_2 && j_2 < (len(a_3): int))) && (0 <= j_2_1 && j_2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j_2): Ref) != (loc(a_3, j_2_1): Ref)
        );

      // -- check if sufficient permission is held
        assert {:msg "  The precondition of method max might not hold. There might be insufficient permission to access loc(a, j).val (max-array-standard.vpr@50.3--50.14) [196]"}
          (forall j_2: int ::
          { (loc(a_3, j_2): Ref) } { (loc(a_3, j_2): Ref) }
          0 <= j_2 && j_2 < (len(a_3): int) ==> Mask[(loc(a_3, j_2): Ref), val] >= FullPerm
        );

      // -- assumptions for inverse of receiver loc(a, j)
        assume (forall j_2: int ::
          { (loc(a_3, j_2): Ref) } { (loc(a_3, j_2): Ref) }
          (0 <= j_2 && j_2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange10((loc(a_3, j_2): Ref)) && invRecv10((loc(a_3, j_2): Ref)) == j_2
        );
        assume (forall o_3: Ref ::
          { invRecv10(o_3) }
          (0 <= invRecv10(o_3) && invRecv10(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange10(o_3)) ==> (loc(a_3, invRecv10(o_3)): Ref) == o_3
        );

      // -- assume permission updates for field val
        assume (forall o_3: Ref ::
          { QPMask[o_3, val] }
          ((0 <= invRecv10(o_3) && invRecv10(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange10(o_3)) ==> (loc(a_3, invRecv10(o_3)): Ref) == o_3 && QPMask[o_3, val] == Mask[o_3, val] - FullPerm) && (!((0 <= invRecv10(o_3) && invRecv10(o_3) < (len(a_3): int)) && (NoPerm < FullPerm && qpRange10(o_3))) ==> QPMask[o_3, val] == Mask[o_3, val])
        );

      // -- assume permission updates for independent locations
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { QPMask[o_3, f_5] }
          f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      // Finish exhale
      havoc ExhaleHeap;
      assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
      Heap := ExhaleHeap;

    // -- Inhaling postcondition
      havoc QPMask;
      assert {:msg "  Method call might fail. Quantified resource loc(a, j$0).val might not be injective. (max-array-standard.vpr@50.3--50.14) [197]"}
        (forall j$0: int, j$0_3: int ::

        (((j$0 != j$0_3 && (0 <= j$0 && j$0 < (len(a_3): int))) && (0 <= j$0_3 && j$0_3 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$0): Ref) != (loc(a_3, j$0_3): Ref)
      );

      // -- Define Inverse Function
        assume (forall j$0: int ::
          { (loc(a_3, j$0): Ref) } { (loc(a_3, j$0): Ref) }
          (0 <= j$0 && j$0 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange11((loc(a_3, j$0): Ref)) && invRecv11((loc(a_3, j$0): Ref)) == j$0
        );
        assume (forall o_3: Ref ::
          { invRecv11(o_3) }
          ((0 <= invRecv11(o_3) && invRecv11(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange11(o_3) ==> (loc(a_3, invRecv11(o_3)): Ref) == o_3
        );

      // -- Assume set of fields is nonNull
        assume (forall j$0: int ::
          { (loc(a_3, j$0): Ref) } { (loc(a_3, j$0): Ref) }
          0 <= j$0 && j$0 < (len(a_3): int) ==> (loc(a_3, j$0): Ref) != null
        );

      // -- Define permissions
        assume (forall o_3: Ref ::
          { QPMask[o_3, val] }
          (((0 <= invRecv11(o_3) && invRecv11(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange11(o_3) ==> (NoPerm < FullPerm ==> (loc(a_3, invRecv11(o_3)): Ref) == o_3) && QPMask[o_3, val] == Mask[o_3, val] + FullPerm) && (!(((0 <= invRecv11(o_3) && invRecv11(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange11(o_3)) ==> QPMask[o_3, val] == Mask[o_3, val])
        );
        assume (forall <A, B> o_3: Ref, f_5: (Field A B) ::
          { Mask[o_3, f_5] } { QPMask[o_3, f_5] }
          f_5 != val ==> Mask[o_3, f_5] == QPMask[o_3, f_5]
        );
      Mask := QPMask;
      assume state(Heap, Mask);
      assume (forall j$1_3: int ::
        { (loc(a_3, j$1_3): Ref) }
        0 <= j$1_3 && j$1_3 < (len(a_3): int) ==> Heap[(loc(a_3, j$1_3): Ref), val] == old(PreCallHeap)[(loc(a_3, j$1_3): Ref), val]
      );
      if ((len(a_3): int) == 0) {
        assume x == -1;
      } else {
        assume 0 <= x;
        assume x < (len(a_3): int);
      }
      assume (forall j$2_3: int ::
        { (loc(a_3, j$2_3): Ref) }
        0 <= j$2_3 && j$2_3 < (len(a_3): int) ==> Heap[(loc(a_3, j$2_3): Ref), val] <= Heap[(loc(a_3, x): Ref), val]
      );
      assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: assert loc(a, 0).val <= x -- max-array-standard.vpr@52.3--52.28

    // -- Check definedness of loc(a, 0).val <= x
      assert {:msg "  Assert might fail. There might be insufficient permission to access loc(a, 0).val (max-array-standard.vpr@52.10--52.28) [198]"}
        HasDirectPerm(Mask, (loc(a_3, 0): Ref), val);
    assert {:msg "  Assert might fail. Assertion loc(a, 0).val <= x might not hold. (max-array-standard.vpr@52.10--52.28) [199]"}
      Heap[(loc(a_3, 0): Ref), val] <= x;
    assume state(Heap, Mask);

  // -- Translating statement: assert x == loc(a, len(a) - 1).val -- max-array-standard.vpr@53.3--53.37

    // -- Check definedness of x == loc(a, len(a) - 1).val
      assert {:msg "  Assert might fail. There might be insufficient permission to access loc(a, len(a) - 1).val (max-array-standard.vpr@53.10--53.37) [200]"}
        HasDirectPerm(Mask, (loc(a_3, (len(a_3): int) - 1): Ref), val);
    assert {:msg "  Assert might fail. Assertion x == loc(a, len(a) - 1).val might not hold. (max-array-standard.vpr@53.10--53.37) [201]"}
      x == Heap[(loc(a_3, (len(a_3): int) - 1): Ref), val];
    assume state(Heap, Mask);

  // -- Translating statement: assert x == 2 -- max-array-standard.vpr@54.3--54.16
    assert {:msg "  Assert might fail. Assertion x == 2 might not hold. (max-array-standard.vpr@54.10--54.16) [202]"}
      x == 2;
    assume state(Heap, Mask);

  // -- Translating statement: assert loc(a, 1).val < x -- max-array-standard.vpr@55.3--55.27

    // -- Check definedness of loc(a, 1).val < x
      assert {:msg "  Assert might fail. There might be insufficient permission to access loc(a, 1).val (max-array-standard.vpr@55.10--55.27) [203]"}
        HasDirectPerm(Mask, (loc(a_3, 1): Ref), val);
    assert {:msg "  Assert might fail. Assertion loc(a, 1).val < x might not hold. (max-array-standard.vpr@55.10--55.27) [204]"}
      Heap[(loc(a_3, 1): Ref), val] < x;
    assume state(Heap, Mask);
}
