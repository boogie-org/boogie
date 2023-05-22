// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function  state(Heap: HeapType, Mask: MaskType): bool;

// ==================================================
// Preamble of Heap module.
// ==================================================

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType;

function  succHeap(Heap0: HeapType, Heap1: HeapType): bool;
function  succHeapTrans(Heap0: HeapType, Heap1: HeapType): bool;
function  IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;

function  readHeap<A, B>(HeapType: HeapType, obj: Ref, f_1: (Field A B)): B;
function  updHeap<A, B>(HeapType: HeapType, obj: Ref, f_1: (Field A B), y: B): HeapType;
function  IsPredicateField<A, B>(f_1: (Field A B)): bool;
function  IsWandField<A, B>(f_1: (Field A B)): bool;
function  getPredicateId<A, B>(f_1: (Field A B)): int;
// ==================================================
// Read and update axioms for the heap
// ==================================================


// ==================================================
// Preamble of Permission module.
// ==================================================

type Perm = real;
type MaskType;
var Mask: MaskType;
const ZeroMask: MaskType;
type PMaskType;
const ZeroPMask: PMaskType;
function  PredicateMaskField<A>(f_5: (Field A FrameType)): Field A PMaskType;
function  WandMaskField<A>(f_5: (Field A FrameType)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function  Perm(a: real, b: real): Perm;
// ==================================================
// read and update permission mask
// ==================================================

function  readMask<A, B>(MaskType: MaskType, obj: Ref, f_1: (Field A B)): Perm;
function  updMask<A, B>(MaskType: MaskType, obj: Ref, f_1: (Field A B), y: Perm): MaskType;

// ==================================================
// read and update known-folded mask
// ==================================================

function  readPMask<A, B>(PMaskType: PMaskType, obj: Ref, f_1: (Field A B)): bool;
function  updPMask<A, B>(PMaskType: PMaskType, obj: Ref, f_1: (Field A B), y: bool): PMaskType;

function  GoodMask(Mask: MaskType): bool;
function  HasDirectPerm<A, B>(Mask: MaskType, o_2: Ref, f_4: (Field A B)): bool;

function  sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
function  neverTriggered1(y_1: Ref): bool;
function  neverTriggered2(y_3: Ref): bool;
function  neverTriggered3(y_6: Ref): bool;
function  neverTriggered4(y_8: Ref): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function  invRecv1(recv: Ref): Ref;
function  invRecv2(x_1_1: Ref): Ref;
function  invRecv3(recv: Ref): Ref;
function  invRecv4(x_2_1: Ref): Ref;
// ==================================================
// Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale
// ==================================================

function  qpRange1(recv: Ref): bool;
function  qpRange2(x_1_1: Ref): bool;
function  qpRange3(recv: Ref): bool;
function  qpRange4(x_2_1: Ref): bool;

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

// Knowledge that two identical instances of the same predicate cannot be inside each other

// ==================================================
// Translation of all fields
// ==================================================

const unique f_7: Field NormalField int;
axiom !IsPredicateField(f_7);
axiom !IsWandField(f_7);
const unique g: Field NormalField int;
axiom !IsPredicateField(g);
axiom !IsWandField(g);

// ==================================================
// Translation of predicate P
// ==================================================

type PredicateType_P;
function  P(x: Ref): Field PredicateType_P FrameType;
function  P#sm(x: Ref): Field PredicateType_P PMaskType;
function  P#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  P#everUsed<A>(pred: (Field A FrameType)): bool;

// ==================================================
// Translation of method m
// ==================================================

procedure m(x: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var QPMask: MaskType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);

  // -- Assumptions about method arguments
    //assume readHeap(Heap, x, $allocated);

  // -- Initializing of old state

    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);

  // -- Translating statement: inhale acc(P(x), write) -- simple.vpr@7.5--7.16
    perm := FullPerm;
    Mask := updMask(Mask, null, P(x), readMask(Mask, null, P(x)) + perm);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: inhale acc(x.f, write) -- simple.vpr@8.5--8.20
    perm := FullPerm;
    assume x != null;
    Mask := updMask(Mask, x, f_7, readMask(Mask, x, f_7) + perm);
    assume state(Heap, Mask);
}
