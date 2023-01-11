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

function  neverTriggered1(j$0_1: int): bool;
function  neverTriggered2(j$1_1: int): bool;
function  neverTriggered3(j$1_2: int): bool;
function  neverTriggered4(j$3: int): bool;
function  neverTriggered5(j$3_2: int): bool;
function  neverTriggered6(j$3_3: int): bool;
function  neverTriggered7(j$3_4: int): bool;
function  neverTriggered8(j$3_5: int): bool;
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
// Translation of method binary_search
// ==================================================

procedure binary_search(a_3: IArrayDomainType, key: int) returns (index: int)
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var i_2: int;
  var j: int;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var j$2: int;
  var i_3: int;
  var low: int;
  var high: int;
  var j$4: int;
  var i_6: int;
  var ExhaleHeap: HeapType;
  var j$4_1: int;
  var i_4: int;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var mid: int;
  var j$4_5: int;
  var i_11: int;
  var j$2_2: int;
  var i_4_1: int;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Checked inhaling of precondition

    // -- Check definedness of (forall j$0: Int :: { loc(a, j$0) } 0 <= j$0 && j$0 < len(a) ==> acc(loc(a, j$0).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$0).val might not be injective. (binary-search-array.vpr@10.12--10.21) [149]"}
      (forall j$0_1: int, j$0_1_1: int ::

      (((j$0_1 != j$0_1_1 && (0 <= j$0_1 && j$0_1 < (len(a_3): int))) && (0 <= j$0_1_1 && j$0_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$0_1): Ref) != (loc(a_3, j$0_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall j$0_1: int ::
        { (loc(a_3, j$0_1): Ref) } { (loc(a_3, j$0_1): Ref) }
        (0 <= j$0_1 && j$0_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange1((loc(a_3, j$0_1): Ref)) && invRecv1((loc(a_3, j$0_1): Ref)) == j$0_1
      );
      assume (forall o_3: Ref ::
        { invRecv1(o_3) }
        ((0 <= invRecv1(o_3) && invRecv1(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange1(o_3) ==> (loc(a_3, invRecv1(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall j$0_1: int ::
        { (loc(a_3, j$0_1): Ref) } { (loc(a_3, j$0_1): Ref) }
        0 <= j$0_1 && j$0_1 < (len(a_3): int) ==> (loc(a_3, j$0_1): Ref) != null
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

    // -- Check definedness of (forall i: Int, j: Int :: { loc(a, i), loc(a, j) } 0 <= i && (j < len(a) && i < j) ==> loc(a, i).val < loc(a, j).val)
      if (*) {
        if (0 <= i_2 && (j < (len(a_3): int) && i_2 < j)) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, i).val (binary-search-array.vpr@11.12--11.123) [150]"}
            HasDirectPerm(Mask, (loc(a_3, i_2): Ref), val);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j).val (binary-search-array.vpr@11.12--11.123) [151]"}
            HasDirectPerm(Mask, (loc(a_3, j): Ref), val);
        }
        assume false;
      }
    assume (forall i_1_1: int, j_1: int ::
      { (loc(a_3, i_1_1): Ref), (loc(a_3, j_1): Ref) }
      0 <= i_1_1 && (j_1 < (len(a_3): int) && i_1_1 < j_1) ==> Heap[(loc(a_3, i_1_1): Ref), val] < Heap[(loc(a_3, j_1): Ref), val]
    );
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

    // -- Check definedness of (forall j$1: Int :: { loc(a, j$1) } 0 <= j$1 && j$1 < len(a) ==> acc(loc(a, j$1).val, write))
      if (*) {
        assume false;
      }
    havoc QPMask;
    assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$1).val might not be injective. (binary-search-array.vpr@12.12--12.37) [152]"}
      (forall j$1_1: int, j$1_1_1: int ::

      (((j$1_1 != j$1_1_1 && (0 <= j$1_1 && j$1_1 < (len(a_3): int))) && (0 <= j$1_1_1 && j$1_1_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$1_1): Ref) != (loc(a_3, j$1_1_1): Ref)
    );

    // -- Define Inverse Function
      assume (forall j$1_1: int ::
        { (loc(a_3, j$1_1): Ref) } { (loc(a_3, j$1_1): Ref) }
        (0 <= j$1_1 && j$1_1 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange2((loc(a_3, j$1_1): Ref)) && invRecv2((loc(a_3, j$1_1): Ref)) == j$1_1
      );
      assume (forall o_3: Ref ::
        { invRecv2(o_3) }
        ((0 <= invRecv2(o_3) && invRecv2(o_3) < (len(a_3): int)) && NoPerm < FullPerm) && qpRange2(o_3) ==> (loc(a_3, invRecv2(o_3)): Ref) == o_3
      );

    // -- Assume set of fields is nonNull
      assume (forall j$1_1: int ::
        { (loc(a_3, j$1_1): Ref) } { (loc(a_3, j$1_1): Ref) }
        0 <= j$1_1 && j$1_1 < (len(a_3): int) ==> (loc(a_3, j$1_1): Ref) != null
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

    // -- Check definedness of (forall j$2: Int :: { loc(a, j$2) } 0 <= j$2 && j$2 < len(a) ==> loc(a, j$2).val == old(loc(a, j$2).val))
      if (*) {
        if (0 <= j$2 && j$2 < (len(a_3): int)) {
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$2).val (binary-search-array.vpr@12.12--12.37) [153]"}
            HasDirectPerm(PostMask, (loc(a_3, j$2): Ref), val);
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$2).val (binary-search-array.vpr@12.12--12.37) [154]"}
            HasDirectPerm(old(Mask), (loc(a_3, j$2): Ref), val);
        }
        assume false;
      }
    assume (forall j$2_1: int ::
      { (loc(a_3, j$2_1): Ref) }
      0 <= j$2_1 && j$2_1 < (len(a_3): int) ==> PostHeap[(loc(a_3, j$2_1): Ref), val] == old(Heap)[(loc(a_3, j$2_1): Ref), val]
    );
    assume state(PostHeap, PostMask);
    assume -1 <= index;
    assume index < (len(a_3): int);
    assume state(PostHeap, PostMask);
    if (0 <= index) {

      // -- Check definedness of loc(a, index).val == key
        assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, index).val (binary-search-array.vpr@14.12--14.51) [155]"}
          HasDirectPerm(PostMask, (loc(a_3, index): Ref), val);
      assume PostHeap[(loc(a_3, index): Ref), val] == key;
    }
    assume state(PostHeap, PostMask);
    if (-1 == index) {

      // -- Check definedness of (forall i: Int :: { loc(a, i) } 0 <= i && i < len(a) ==> loc(a, i).val != key)
        if (*) {
          if (0 <= i_3 && i_3 < (len(a_3): int)) {
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, i).val (binary-search-array.vpr@15.12--15.91) [156]"}
              HasDirectPerm(PostMask, (loc(a_3, i_3): Ref), val);
          }
          assume false;
        }
      assume (forall i_3_1: int ::
        { (loc(a_3, i_3_1): Ref) }
        0 <= i_3_1 && i_3_1 < (len(a_3): int) ==> PostHeap[(loc(a_3, i_3_1): Ref), val] != key
      );
    }
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Translating statement: low := 0 -- binary-search-array.vpr@17.3--17.20
    low := 0;
    assume state(Heap, Mask);

  // -- Translating statement: high := len(a) -- binary-search-array.vpr@18.3--18.26
    high := (len(a_3): int);
    assume state(Heap, Mask);

  // -- Translating statement: index := -1 -- binary-search-array.vpr@19.3--19.14
    index := -1;
    assume state(Heap, Mask);

  // -- Translating statement: while (low < high) -- binary-search-array.vpr@21.3--40.4

    // -- Before loop head

      // -- Exhale loop invariant before loop
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver loc(a, j$3) is injective
          assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not hold on entry. Quantified resource loc(a, j$3).val might not be injective. (binary-search-array.vpr@22.15--22.40) [157]"}
            (forall j$3: int, j$3_1: int ::
            { neverTriggered4(j$3), neverTriggered4(j$3_1) }
            (((j$3 != j$3_1 && (0 <= j$3 && j$3 < (len(a_3): int))) && (0 <= j$3_1 && j$3_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3): Ref) != (loc(a_3, j$3_1): Ref)
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not hold on entry. There might be insufficient permission to access loc(a, j$3).val (binary-search-array.vpr@22.15--22.40) [158]"}
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
            assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not hold on entry. Assertion loc(a, j$4).val == old(loc(a, j$4).val) might not hold. (binary-search-array.vpr@22.15--22.40) [159]"}
              Heap[(loc(a_3, j$4): Ref), val] == old(Heap)[(loc(a_3, j$4): Ref), val];
          }
          assume false;
        }
        assume (forall j$4_1_1: int ::
          { (loc(a_3, j$4_1_1): Ref) }
          0 <= j$4_1_1 && j$4_1_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_1_1): Ref), val] == old(Heap)[(loc(a_3, j$4_1_1): Ref), val]
        );
        assert {:msg "  Loop invariant 0 <= low && (low <= high && high <= len(a)) might not hold on entry. Assertion 0 <= low might not hold. (binary-search-array.vpr@23.15--23.56) [160]"}
          0 <= low;
        assert {:msg "  Loop invariant 0 <= low && (low <= high && high <= len(a)) might not hold on entry. Assertion low <= high might not hold. (binary-search-array.vpr@23.15--23.56) [161]"}
          low <= high;
        assert {:msg "  Loop invariant 0 <= low && (low <= high && high <= len(a)) might not hold on entry. Assertion high <= len(a) might not hold. (binary-search-array.vpr@23.15--23.56) [162]"}
          high <= (len(a_3): int);
        if (index == -1) {
          if (*) {
            if (0 <= i_6 && (i_6 < (len(a_3): int) && !(low <= i_6 && i_6 < high))) {
              assert {:msg "  Loop invariant index == -1 ==> (forall i: Int :: { loc(a, i) } 0 <= i && (i < len(a) && !(low <= i && i < high)) ==> loc(a, i).val != key) might not hold on entry. Assertion loc(a, i).val != key might not hold. (binary-search-array.vpr@24.15--24.133) [163]"}
                Heap[(loc(a_3, i_6): Ref), val] != key;
            }
            assume false;
          }
          assume (forall i_7_1: int ::
            { (loc(a_3, i_7_1): Ref) }
            0 <= i_7_1 && (i_7_1 < (len(a_3): int) && !(low <= i_7_1 && i_7_1 < high)) ==> Heap[(loc(a_3, i_7_1): Ref), val] != key
          );
        }
        assert {:msg "  Loop invariant -1 <= index && index < len(a) might not hold on entry. Assertion -1 <= index might not hold. (binary-search-array.vpr@25.15--25.44) [164]"}
          -1 <= index;
        assert {:msg "  Loop invariant -1 <= index && index < len(a) might not hold on entry. Assertion index < len(a) might not hold. (binary-search-array.vpr@25.15--25.44) [165]"}
          index < (len(a_3): int);
        if (0 <= index) {
          assert {:msg "  Loop invariant 0 <= index ==> loc(a, index).val == key might not hold on entry. Assertion loc(a, index).val == key might not hold. (binary-search-array.vpr@26.15--26.54) [166]"}
            Heap[(loc(a_3, index): Ref), val] == key;
        }
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;

    // -- Havoc loop written variables (except locals)
      havoc high, index, low;

    // -- Check definedness of invariant
      if (*) {

        // -- Check definedness of (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write))
          if (*) {
            assume false;
          }
        havoc QPMask;
        assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$3).val might not be injective. (binary-search-array.vpr@22.15--22.40) [167]"}
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
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$4).val (binary-search-array.vpr@22.15--22.40) [168]"}
                HasDirectPerm(Mask, (loc(a_3, j$4_1): Ref), val);
              assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, j$4).val (binary-search-array.vpr@22.15--22.40) [169]"}
                HasDirectPerm(old(Mask), (loc(a_3, j$4_1): Ref), val);
            }
            assume false;
          }
        assume (forall j$4_3: int ::
          { (loc(a_3, j$4_3): Ref) }
          0 <= j$4_3 && j$4_3 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_3): Ref), val] == old(Heap)[(loc(a_3, j$4_3): Ref), val]
        );
        assume state(Heap, Mask);
        assume 0 <= low;
        assume low <= high;
        assume high <= (len(a_3): int);
        assume state(Heap, Mask);
        if (index == -1) {

          // -- Check definedness of (forall i: Int :: { loc(a, i) } 0 <= i && (i < len(a) && !(low <= i && i < high)) ==> loc(a, i).val != key)
            if (*) {
              if (0 <= i_4 && (i_4 < (len(a_3): int) && !(low <= i_4 && i_4 < high))) {
                assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, i).val (binary-search-array.vpr@24.15--24.133) [170]"}
                  HasDirectPerm(Mask, (loc(a_3, i_4): Ref), val);
              }
              assume false;
            }
          assume (forall i_9: int ::
            { (loc(a_3, i_9): Ref) }
            0 <= i_9 && (i_9 < (len(a_3): int) && !(low <= i_9 && i_9 < high)) ==> Heap[(loc(a_3, i_9): Ref), val] != key
          );
        }
        assume state(Heap, Mask);
        assume -1 <= index;
        assume index < (len(a_3): int);
        assume state(Heap, Mask);
        if (0 <= index) {

          // -- Check definedness of loc(a, index).val == key
            assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access loc(a, index).val (binary-search-array.vpr@26.15--26.54) [171]"}
              HasDirectPerm(Mask, (loc(a_3, index): Ref), val);
          assume Heap[(loc(a_3, index): Ref), val] == key;
        }
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
        havoc QPMask;
        assert {:msg "  While statement might fail. Quantified resource loc(a, j$3).val might not be injective. (binary-search-array.vpr@22.15--22.40) [172]"}
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
        assume 0 <= low;
        assume low <= high;
        assume high <= (len(a_3): int);
        if (index == -1) {
          assume (forall i_10: int ::
            { (loc(a_3, i_10): Ref) }
            0 <= i_10 && (i_10 < (len(a_3): int) && !(low <= i_10 && i_10 < high)) ==> Heap[(loc(a_3, i_10): Ref), val] != key
          );
        }
        assume -1 <= index;
        assume index < (len(a_3): int);
        if (0 <= index) {
          assume Heap[(loc(a_3, index): Ref), val] == key;
        }
        assume state(Heap, Mask);
        // Check and assume guard
        assume low < high;
        assume state(Heap, Mask);

        // -- Translate loop body

          // -- Translating statement: mid := (low + high) / 2 -- binary-search-array.vpr@28.5--28.37
            mid := (low + high) div 2;
            assume state(Heap, Mask);

          // -- Translating statement: if (loc(a, mid).val < key) -- binary-search-array.vpr@30.5--39.6

            // -- Check definedness of loc(a, mid).val < key
              assert {:msg "  Conditional statement might fail. There might be insufficient permission to access loc(a, mid).val (binary-search-array.vpr@30.9--30.30) [173]"}
                HasDirectPerm(Mask, (loc(a_3, mid): Ref), val);
            if (Heap[(loc(a_3, mid): Ref), val] < key) {

              // -- Translating statement: low := mid + 1 -- binary-search-array.vpr@31.7--31.21
                low := mid + 1;
                assume state(Heap, Mask);
            } else {

              // -- Translating statement: if (key < loc(a, mid).val) -- binary-search-array.vpr@33.7--38.8

                // -- Check definedness of key < loc(a, mid).val
                  assert {:msg "  Conditional statement might fail. There might be insufficient permission to access loc(a, mid).val (binary-search-array.vpr@33.11--33.32) [174]"}
                    HasDirectPerm(Mask, (loc(a_3, mid): Ref), val);
                if (key < Heap[(loc(a_3, mid): Ref), val]) {

                  // -- Translating statement: high := mid -- binary-search-array.vpr@34.9--34.20
                    high := mid;
                    assume state(Heap, Mask);
                } else {

                  // -- Translating statement: index := mid -- binary-search-array.vpr@36.9--36.21
                    index := mid;
                    assume state(Heap, Mask);

                  // -- Translating statement: high := mid -- binary-search-array.vpr@37.9--37.20
                    high := mid;
                    assume state(Heap, Mask);
                }
                assume state(Heap, Mask);
            }
            assume state(Heap, Mask);
        // Exhale invariant
        havoc QPMask;

        // -- check that the permission amount is positive


        // -- check if receiver loc(a, j$3) is injective
          assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not be preserved. Quantified resource loc(a, j$3).val might not be injective. (binary-search-array.vpr@22.15--22.40) [175]"}
            (forall j$3_4: int, j$3_4_1: int ::
            { neverTriggered7(j$3_4), neverTriggered7(j$3_4_1) }
            (((j$3_4 != j$3_4_1 && (0 <= j$3_4 && j$3_4 < (len(a_3): int))) && (0 <= j$3_4_1 && j$3_4_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$3_4): Ref) != (loc(a_3, j$3_4_1): Ref)
          );

        // -- check if sufficient permission is held
          assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not be preserved. There might be insufficient permission to access loc(a, j$3).val (binary-search-array.vpr@22.15--22.40) [176]"}
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
            assert {:msg "  Loop invariant (forall j$3: Int :: { loc(a, j$3) } 0 <= j$3 && j$3 < len(a) ==> acc(loc(a, j$3).val, write)) && (forall j$4: Int :: { loc(a, j$4) } 0 <= j$4 && j$4 < len(a) ==> loc(a, j$4).val == old(loc(a, j$4).val)) might not be preserved. Assertion loc(a, j$4).val == old(loc(a, j$4).val) might not hold. (binary-search-array.vpr@22.15--22.40) [177]"}
              Heap[(loc(a_3, j$4_5): Ref), val] == old(Heap)[(loc(a_3, j$4_5): Ref), val];
          }
          assume false;
        }
        assume (forall j$4_6_1: int ::
          { (loc(a_3, j$4_6_1): Ref) }
          0 <= j$4_6_1 && j$4_6_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$4_6_1): Ref), val] == old(Heap)[(loc(a_3, j$4_6_1): Ref), val]
        );
        assert {:msg "  Loop invariant 0 <= low && (low <= high && high <= len(a)) might not be preserved. Assertion 0 <= low might not hold. (binary-search-array.vpr@23.15--23.56) [178]"}
          0 <= low;
        assert {:msg "  Loop invariant 0 <= low && (low <= high && high <= len(a)) might not be preserved. Assertion low <= high might not hold. (binary-search-array.vpr@23.15--23.56) [179]"}
          low <= high;
        assert {:msg "  Loop invariant 0 <= low && (low <= high && high <= len(a)) might not be preserved. Assertion high <= len(a) might not hold. (binary-search-array.vpr@23.15--23.56) [180]"}
          high <= (len(a_3): int);
        if (index == -1) {
          if (*) {
            if (0 <= i_11 && (i_11 < (len(a_3): int) && !(low <= i_11 && i_11 < high))) {
              assert {:msg "  Loop invariant index == -1 ==> (forall i: Int :: { loc(a, i) } 0 <= i && (i < len(a) && !(low <= i && i < high)) ==> loc(a, i).val != key) might not be preserved. Assertion loc(a, i).val != key might not hold. (binary-search-array.vpr@24.15--24.133) [181]"}
                Heap[(loc(a_3, i_11): Ref), val] != key;
            }
            assume false;
          }
          assume (forall i_12_1: int ::
            { (loc(a_3, i_12_1): Ref) }
            0 <= i_12_1 && (i_12_1 < (len(a_3): int) && !(low <= i_12_1 && i_12_1 < high)) ==> Heap[(loc(a_3, i_12_1): Ref), val] != key
          );
        }
        assert {:msg "  Loop invariant -1 <= index && index < len(a) might not be preserved. Assertion -1 <= index might not hold. (binary-search-array.vpr@25.15--25.44) [182]"}
          -1 <= index;
        assert {:msg "  Loop invariant -1 <= index && index < len(a) might not be preserved. Assertion index < len(a) might not hold. (binary-search-array.vpr@25.15--25.44) [183]"}
          index < (len(a_3): int);
        if (0 <= index) {
          assert {:msg "  Loop invariant 0 <= index ==> loc(a, index).val == key might not be preserved. Assertion loc(a, index).val == key might not hold. (binary-search-array.vpr@26.15--26.54) [184]"}
            Heap[(loc(a_3, index): Ref), val] == key;
        }
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Terminate execution
        assume false;
      }

    // -- Inhale loop invariant after loop, and assume guard
      assume !(low < high);
      assume state(Heap, Mask);
      havoc QPMask;
      assert {:msg "  While statement might fail. Quantified resource loc(a, j$3).val might not be injective. (binary-search-array.vpr@22.15--22.40) [185]"}
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
      assume 0 <= low;
      assume low <= high;
      assume high <= (len(a_3): int);
      if (index == -1) {
        assume (forall i_13: int ::
          { (loc(a_3, i_13): Ref) }
          0 <= i_13 && (i_13 < (len(a_3): int) && !(low <= i_13 && i_13 < high)) ==> Heap[(loc(a_3, i_13): Ref), val] != key
        );
      }
      assume -1 <= index;
      assume index < (len(a_3): int);
      if (0 <= index) {
        assume Heap[(loc(a_3, index): Ref), val] == key;
      }
      assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    havoc QPMask;

    // -- check that the permission amount is positive


    // -- check if receiver loc(a, j$1) is injective
      assert {:msg "  Contract might not be well-formed. Quantified resource loc(a, j$1).val might not be injective. (binary-search-array.vpr@12.12--12.21) [186]"}
        (forall j$1_2: int, j$1_2_1: int ::
        { neverTriggered3(j$1_2), neverTriggered3(j$1_2_1) }
        (((j$1_2 != j$1_2_1 && (0 <= j$1_2 && j$1_2 < (len(a_3): int))) && (0 <= j$1_2_1 && j$1_2_1 < (len(a_3): int))) && NoPerm < FullPerm) && NoPerm < FullPerm ==> (loc(a_3, j$1_2): Ref) != (loc(a_3, j$1_2_1): Ref)
      );

    // -- check if sufficient permission is held
      assert {:msg "  Postcondition of binary_search might not hold. There might be insufficient permission to access loc(a, j$1).val (binary-search-array.vpr@12.12--12.37) [187]"}
        (forall j$1_2: int ::
        { (loc(a_3, j$1_2): Ref) } { (loc(a_3, j$1_2): Ref) }
        0 <= j$1_2 && j$1_2 < (len(a_3): int) ==> Mask[(loc(a_3, j$1_2): Ref), val] >= FullPerm
      );

    // -- assumptions for inverse of receiver loc(a, j$1)
      assume (forall j$1_2: int ::
        { (loc(a_3, j$1_2): Ref) } { (loc(a_3, j$1_2): Ref) }
        (0 <= j$1_2 && j$1_2 < (len(a_3): int)) && NoPerm < FullPerm ==> qpRange3((loc(a_3, j$1_2): Ref)) && invRecv3((loc(a_3, j$1_2): Ref)) == j$1_2
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
      if (0 <= j$2_2 && j$2_2 < (len(a_3): int)) {
        assert {:msg "  Postcondition of binary_search might not hold. Assertion loc(a, j$2).val == old(loc(a, j$2).val) might not hold. (binary-search-array.vpr@12.12--12.37) [188]"}
          Heap[(loc(a_3, j$2_2): Ref), val] == old(Heap)[(loc(a_3, j$2_2): Ref), val];
      }
      assume false;
    }
    assume (forall j$2_3_1: int ::
      { (loc(a_3, j$2_3_1): Ref) }
      0 <= j$2_3_1 && j$2_3_1 < (len(a_3): int) ==> Heap[(loc(a_3, j$2_3_1): Ref), val] == old(Heap)[(loc(a_3, j$2_3_1): Ref), val]
    );
    assert {:msg "  Postcondition of binary_search might not hold. Assertion -1 <= index might not hold. (binary-search-array.vpr@13.12--13.41) [189]"}
      -1 <= index;
    assert {:msg "  Postcondition of binary_search might not hold. Assertion index < len(a) might not hold. (binary-search-array.vpr@13.12--13.41) [190]"}
      index < (len(a_3): int);
    if (0 <= index) {
      assert {:msg "  Postcondition of binary_search might not hold. Assertion loc(a, index).val == key might not hold. (binary-search-array.vpr@14.12--14.51) [191]"}
        Heap[(loc(a_3, index): Ref), val] == key;
    }
    if (-1 == index) {
      if (*) {
        if (0 <= i_4_1 && i_4_1 < (len(a_3): int)) {
          assert {:msg "  Postcondition of binary_search might not hold. Assertion loc(a, i).val != key might not hold. (binary-search-array.vpr@15.12--15.91) [192]"}
            Heap[(loc(a_3, i_4_1): Ref), val] != key;
        }
        assume false;
      }
      assume (forall i_5_1: int ::
        { (loc(a_3, i_5_1): Ref) }
        0 <= i_5_1 && i_5_1 < (len(a_3): int) ==> Heap[(loc(a_3, i_5_1): Ref), val] != key
      );
    }
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}
