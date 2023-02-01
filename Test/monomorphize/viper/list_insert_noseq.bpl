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

// Function heights (higher height means its body is available earlier):
// - height 0: head
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
// Preamble of Wand Module.
// ==================================================

type WandType_wand;
function  wand(arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm): Field WandType_wand int;
function  wand#sm(arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm): Field WandType_wand PMaskType;
function  wand#ft(arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm): Field WandType_wand FrameType;
axiom (forall arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm ::
  { wand(arg1, arg2, arg3, arg4) }
  IsWandField(wand(arg1, arg2, arg3, arg4))
);
axiom (forall arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm ::
  { wand#ft(arg1, arg2, arg3, arg4) }
  IsWandField(wand#ft(arg1, arg2, arg3, arg4))
);
axiom (forall arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm ::
  { wand(arg1, arg2, arg3, arg4) }
  !IsPredicateField(wand(arg1, arg2, arg3, arg4))
);
axiom (forall arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm ::
  { wand#ft(arg1, arg2, arg3, arg4) }
  !IsPredicateField(wand#ft(arg1, arg2, arg3, arg4))
);
axiom (forall arg1: Ref, arg2: Perm, arg3: Ref, arg4: Perm ::
  { WandMaskField(wand#ft(arg1, arg2, arg3, arg4)) }
  wand#sm(arg1, arg2, arg3, arg4) == WandMaskField(wand#ft(arg1, arg2, arg3, arg4))
);

// ==================================================
// Translation of all fields
// ==================================================

const unique val: Field NormalField int;
axiom !IsPredicateField(val);
axiom !IsWandField(val);
const unique next: Field NormalField Ref;
axiom !IsPredicateField(next);
axiom !IsWandField(next);

// ==================================================
// Translation of function head
// ==================================================

// Uninterpreted function definitions
function  head(Heap: HeapType, xs: Ref): int;
function  head'(Heap: HeapType, xs: Ref): int;
axiom (forall Heap: HeapType, xs: Ref ::
  { head(Heap, xs) }
  head(Heap, xs) == head'(Heap, xs) && dummyFunction(head#triggerStateless(xs))
);
axiom (forall Heap: HeapType, xs: Ref ::
  { head'(Heap, xs) }
  dummyFunction(head#triggerStateless(xs))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, xs: Ref ::
  { state(Heap, Mask), head(Heap, xs) } { state(Heap, Mask), head#triggerStateless(xs), List#trigger(Heap, List(xs)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 0 ==> head(Heap, xs) == Heap[xs, val]
);

// Framing axioms
function  head#frame(frame: FrameType, xs: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, xs: Ref ::
  { state(Heap, Mask), head'(Heap, xs) }
  state(Heap, Mask) ==> head'(Heap, xs) == head#frame(Heap[null, List(xs)], xs)
);

// Trigger function (controlling recursive postconditions)
function  head#trigger(frame: FrameType, xs: Ref): bool;

// State-independent trigger function
function  head#triggerStateless(xs: Ref): int;

// Check contract well-formedness and postcondition
procedure head#definedness(xs: Ref) returns (Result: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var UnfoldingHeap: HeapType;
  var UnfoldingMask: MaskType;
  var newPMask: PMaskType;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[xs, $allocated];
    assume AssumeFunctionsAbove == 0;

  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);

  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, List(xs)] := Mask[null, List(xs)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Check definedness of function body

    // -- Check definedness of (unfolding acc(List(xs), write) in xs.val)
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume List#trigger(UnfoldingHeap, List(xs));
      assume UnfoldingHeap[null, List(xs)] == CombineFrames(FrameFragment(UnfoldingHeap[xs, val]), CombineFrames(FrameFragment(UnfoldingHeap[xs, next]), FrameFragment((if UnfoldingHeap[xs, next] != null then UnfoldingHeap[null, List(UnfoldingHeap[xs, next])] else EmptyFrame))));
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access List(xs) (list_insert_noseq.vpr@24.1--26.33) [236]"}
          perm <= UnfoldingMask[null, List(xs)];
      }
      UnfoldingMask[null, List(xs)] := UnfoldingMask[null, List(xs)] - perm;
      perm := FullPerm;
      assume xs != null;
      UnfoldingMask[xs, val] := UnfoldingMask[xs, val] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      perm := FullPerm;
      assume xs != null;
      UnfoldingMask[xs, next] := UnfoldingMask[xs, next] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      if (UnfoldingHeap[xs, next] != null) {
        perm := FullPerm;
        UnfoldingMask[null, List(UnfoldingHeap[xs, next])] := UnfoldingMask[null, List(UnfoldingHeap[xs, next])] + perm;

        // -- Extra unfolding of predicate
          assume InsidePredicate(List(xs), UnfoldingHeap[null, List(xs)], List(UnfoldingHeap[xs, next]), UnfoldingHeap[null, List(UnfoldingHeap[xs, next])]);
        assume state(UnfoldingHeap, UnfoldingMask);
      }
      assume state(UnfoldingHeap, UnfoldingMask);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access xs.val (list_insert_noseq.vpr@24.1--26.33) [237]"}
        HasDirectPerm(UnfoldingMask, xs, val);

      // -- Free assumptions (exp module)
        Heap[null, List#sm(xs)][xs, val] := true;
        Heap[null, List#sm(xs)][xs, next] := true;
        if (Heap[xs, next] != null) {
          havoc newPMask;
          assume (forall <A, B> o_3: Ref, f_7: (Field A B) ::
            { newPMask[o_3, f_7] }
            Heap[null, List#sm(xs)][o_3, f_7] || Heap[null, List#sm(Heap[xs, next])][o_3, f_7] ==> newPMask[o_3, f_7]
          );
          Heap[null, List#sm(xs)] := newPMask;
        }
        assume state(Heap, Mask);

  // -- Translate function body
    Result := Heap[xs, val];
}

// ==================================================
// Translation of predicate List
// ==================================================

type PredicateType_List;
function  List(xs: Ref): Field PredicateType_List FrameType;
function  List#sm(xs: Ref): Field PredicateType_List PMaskType;
axiom (forall xs: Ref ::
  { PredicateMaskField(List(xs)) }
  PredicateMaskField(List(xs)) == List#sm(xs)
);
axiom (forall xs: Ref ::
  { List(xs) }
  IsPredicateField(List(xs))
);
axiom (forall xs: Ref ::
  { List(xs) }
  getPredicateId(List(xs)) == 0
);
function  List#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  List#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall xs: Ref, xs2: Ref ::
  { List(xs), List(xs2) }
  List(xs) == List(xs2) ==> xs == xs2
);
axiom (forall xs: Ref, xs2: Ref ::
  { List#sm(xs), List#sm(xs2) }
  List#sm(xs) == List#sm(xs2) ==> xs == xs2
);

axiom (forall Heap: HeapType, xs: Ref ::
  { List#trigger(Heap, List(xs)) }
  List#everUsed(List(xs))
);

procedure List#definedness(xs: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;

  // -- Check definedness of predicate body of List

    // -- Initializing the state
      Mask := ZeroMask;
      assume state(Heap, Mask);
      assume AssumeFunctionsAbove == -1;
      assume Heap[xs, $allocated];
    perm := FullPerm;
    assume xs != null;
    Mask[xs, val] := Mask[xs, val] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    assume xs != null;
    Mask[xs, next] := Mask[xs, next] + perm;
    assume state(Heap, Mask);

    // -- Check definedness of xs.next != null
      assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access xs.next (list_insert_noseq.vpr@14.1--16.2) [238]"}
        HasDirectPerm(Mask, xs, next);
    if (Heap[xs, next] != null) {

      // -- Check definedness of acc(List(xs.next), write)
        assert {:msg "  Predicate might not be well-formed. There might be insufficient permission to access xs.next (list_insert_noseq.vpr@14.1--16.2) [239]"}
          HasDirectPerm(Mask, xs, next);
      perm := FullPerm;
      Mask[null, List(Heap[xs, next])] := Mask[null, List(Heap[xs, next])] + perm;
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method insert
// ==================================================

procedure insert(xs: Ref, x: int) returns (i: int)
  modifies Heap, Mask;
{
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var crt: Ref;
  var nxt: Ref;
  var node: Ref;
  var newVersion: FrameType;
  var Ops_1Heap: HeapType;
  var Ops_1Mask: MaskType;
  var b_1_1: bool;
  var UsedHeap: HeapType;
  var UsedMask: MaskType;
  var b_2: bool;
  var Labellhs1Mask: MaskType;
  var Labellhs1Heap: HeapType;
  var boolCur: bool;
  var Used_1Heap: HeapType;
  var Used_1Mask: MaskType;
  var b_2_1: bool;
  var arg: Ref;
  var neededTransfer: Perm;
  var initNeededTransfer: Perm;
  var accVar2: bool;
  var maskTransfer: Perm;
  var takeTransfer: Perm;
  var TempMask: MaskType;
  var newPMask: PMaskType;
  var b_3: bool;
  var ResultHeap: HeapType;
  var ResultMask: MaskType;
  var WandDefLHSHeap: HeapType;
  var WandDefLHSMask: MaskType;
  var Labellhs3Mask: MaskType;
  var Labellhs3Heap: HeapType;
  var WandDefRHSHeap: HeapType;
  var WandDefRHSMask: MaskType;
  var loopHeap: HeapType;
  var loopMask: MaskType;
  var oldCrt: Ref;
  var prev: Ref;
  var Ops_3Heap: HeapType;
  var Ops_3Mask: MaskType;
  var b_5: bool;
  var Used_2Heap: HeapType;
  var Used_2Mask: MaskType;
  var b_4: bool;
  var Labellhs4Mask: MaskType;
  var Labellhs4Heap: HeapType;
  var boolCur_1: bool;
  var Used_3Heap: HeapType;
  var Used_3Mask: MaskType;
  var b_6: bool;
  var rcvLocal: Ref;
  var b_7: bool;
  var Result_1Heap: HeapType;
  var Result_1Mask: MaskType;
  var b_8: bool;
  var Result_2Heap: HeapType;
  var Result_2Mask: MaskType;
  var arg_1: Ref;
  var b_9: bool;
  var Result_3Heap: HeapType;
  var Result_3Mask: MaskType;
  var b_10: bool;
  var Result_4Heap: HeapType;
  var Result_4Mask: MaskType;
  var freshVersion: FrameType;
  var Used_4Heap: HeapType;
  var Used_4Mask: MaskType;
  var b_11: bool;
  var Labellhs7Mask: MaskType;
  var Labellhs7Heap: HeapType;
  var b_12: bool;
  var Result_5Heap: HeapType;
  var Result_5Mask: MaskType;
  var Used_5Heap: HeapType;
  var Used_5Mask: MaskType;
  var b_13: bool;
  var arg_2: Ref;
  var b_14: bool;
  var Result_6Heap: HeapType;
  var Result_6Mask: MaskType;
  var Used_6Heap: HeapType;
  var Used_6Mask: MaskType;
  var b_15: bool;
  var arg_3: Ref;
  var b_16: bool;
  var Result_7Heap: HeapType;
  var Result_7Mask: MaskType;
  var freshObj: Ref;

  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;

  // -- Assumptions about method arguments
    assume Heap[xs, $allocated];

  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, List(xs)] := Mask[null, List(xs)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

    // -- Check definedness of head(xs) < x
      if (*) {
        // Exhale precondition of function application
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function head might not hold. There might be insufficient permission to access List(xs) (list_insert_noseq.vpr@33.12--33.20) [240]"}
            perm <= Mask[null, List(xs)];
        }
        Mask[null, List(xs)] := Mask[null, List(xs)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
    assume head(Heap, xs) < x;
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
    PostMask[null, List(xs)] := PostMask[null, List(xs)] + perm;
    assume state(PostHeap, PostMask);
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }

  // -- Assumptions about local variables
    assume Heap[crt, $allocated];
    assume Heap[nxt, $allocated];
    assume Heap[node, $allocated];

  // -- Translating statement: i := 0 -- list_insert_noseq.vpr@39.3--39.9
    i := 0;
    assume state(Heap, Mask);

  // -- Translating statement: unfold acc(List(xs), write) -- list_insert_noseq.vpr@44.3--44.18
    assume List#trigger(Heap, List(xs));
    assume Heap[null, List(xs)] == CombineFrames(FrameFragment(Heap[xs, val]), CombineFrames(FrameFragment(Heap[xs, next]), FrameFragment((if Heap[xs, next] != null then Heap[null, List(Heap[xs, next])] else EmptyFrame))));
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding List(xs) might fail. There might be insufficient permission to access List(xs) (list_insert_noseq.vpr@44.3--44.18) [242]"}
        perm <= Mask[null, List(xs)];
    }
    Mask[null, List(xs)] := Mask[null, List(xs)] - perm;

    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, List(xs))) {
        havoc newVersion;
        Heap[null, List(xs)] := newVersion;
      }
    perm := FullPerm;
    assume xs != null;
    Mask[xs, val] := Mask[xs, val] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    assume xs != null;
    Mask[xs, next] := Mask[xs, next] + perm;
    assume state(Heap, Mask);
    if (Heap[xs, next] != null) {
      perm := FullPerm;
      Mask[null, List(Heap[xs, next])] := Mask[null, List(Heap[xs, next])] + perm;

      // -- Extra unfolding of predicate
        assume InsidePredicate(List(xs), Heap[null, List(xs)], List(Heap[xs, next]), Heap[null, List(Heap[xs, next])]);
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: crt := xs -- list_insert_noseq.vpr@45.3--45.12
    crt := xs;
    assume state(Heap, Mask);

  // -- Translating statement: nxt := xs.next -- list_insert_noseq.vpr@46.3--46.17

    // -- Check definedness of xs.next
      assert {:msg "  Assignment might fail. There might be insufficient permission to access xs.next (list_insert_noseq.vpr@46.3--46.17) [246]"}
        HasDirectPerm(Mask, xs, next);
    nxt := Heap[xs, next];
    assume state(Heap, Mask);

  // -- Translating statement: package acc(List(crt), write) --* acc(List(xs), write) {
  //
  // } -- list_insert_noseq.vpr@48.3--48.18
    havoc Ops_1Heap;
    Ops_1Mask := ZeroMask;
    b_1_1 := b_1_1 && state(Ops_1Heap, Ops_1Mask);
    havoc UsedHeap;
    UsedMask := ZeroMask;
    b_2 := b_2 && state(UsedHeap, UsedMask);
    // Inhaling left hand side of current wand into hypothetical state
    if (b_1_1) {
      perm := FullPerm;
      b_1_1 := b_1_1;
      Ops_1Mask[null, List(crt)] := Ops_1Mask[null, List(crt)] + perm;
      b_1_1 := b_1_1 && state(Ops_1Heap, Ops_1Mask);
    }
    b_1_1 := b_1_1 && state(Ops_1Heap, Ops_1Mask);

    // -- Translating statement: label lhs1 -- list_insert_noseq.vpr@48.11--48.18
      lhs1:
      Labellhs1Mask := Ops_1Mask;
      Labellhs1Heap := Ops_1Heap;
      b_1_1 := b_1_1 && state(Ops_1Heap, Ops_1Mask);
    boolCur := true;
    // Translating exec of non-ghost operationacc(List(xs), write)
    havoc Used_1Heap;
    Used_1Mask := ZeroMask;
    b_2_1 := b_2_1 && state(Used_1Heap, Used_1Mask);

    // -- Transfer of acc(List(xs), write)
      arg := xs;
      neededTransfer := FullPerm;
      initNeededTransfer := Used_1Mask[null, List(arg)] + neededTransfer;
      assert {:msg "  Packaging wand might fail. Fraction acc(List(xs), write) might be negative. (list_insert_noseq.vpr@48.3--48.18) [247]"}
        neededTransfer >= 0.000000000;

      // -- transfer code for top state of stack
        // accumulate constraints which need to be satisfied for transfer to occur
        accVar2 := true;
        // actual code for the transfer from current state on stack
        if ((((b_1_1 && b_1_1) && b_2_1) && accVar2) && neededTransfer > 0.000000000) {
          maskTransfer := Ops_1Mask[null, List(arg)];
          if (neededTransfer <= maskTransfer) {
            takeTransfer := neededTransfer;
          } else {
            takeTransfer := maskTransfer;
          }
          if (takeTransfer > 0.000000000) {
            neededTransfer := neededTransfer - takeTransfer;
            Used_1Mask[null, List(arg)] := Used_1Mask[null, List(arg)] + takeTransfer;
            b_2_1 := b_2_1 && state(Used_1Heap, Used_1Mask);
            TempMask := ZeroMask;
            TempMask[null, List(arg)] := FullPerm;
            b_2_1 := b_2_1 && IdenticalOnKnownLocations(Ops_1Heap, Used_1Heap, TempMask);
            Ops_1Mask[null, List(arg)] := Ops_1Mask[null, List(arg)] - takeTransfer;
          }
        }

      // -- transfer code for top state of stack
        // accumulate constraints which need to be satisfied for transfer to occur
        accVar2 := true;
        // actual code for the transfer from current state on stack
        if ((((b_1_1 && b_1_1) && b_2_1) && accVar2) && neededTransfer > 0.000000000) {
          maskTransfer := Mask[null, List(arg)];
          if (neededTransfer <= maskTransfer) {
            takeTransfer := neededTransfer;
          } else {
            takeTransfer := maskTransfer;
          }
          if (takeTransfer > 0.000000000) {
            neededTransfer := neededTransfer - takeTransfer;
            Used_1Mask[null, List(arg)] := Used_1Mask[null, List(arg)] + takeTransfer;
            b_2_1 := b_2_1 && state(Used_1Heap, Used_1Mask);
            TempMask := ZeroMask;
            TempMask[null, List(arg)] := FullPerm;
            b_2_1 := b_2_1 && IdenticalOnKnownLocations(Heap, Used_1Heap, TempMask);
            Mask[null, List(arg)] := Mask[null, List(arg)] - takeTransfer;
            havoc newPMask;
            assume (forall <A, B> o_4: Ref, f_8: (Field A B) ::
              { newPMask[o_4, f_8] }
              Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)][o_4, f_8] || Heap[null, List#sm(xs)][o_4, f_8] ==> newPMask[o_4, f_8]
            );
            Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)] := newPMask;
          }
        }
      assert {:msg "  Packaging wand might fail. There might be insufficient permission to access List(xs) (list_insert_noseq.vpr@48.3--48.18) [248]"}
        (b_1_1 && b_1_1) && b_2_1 ==> neededTransfer == 0.000000000 && Used_1Mask[null, List(arg)] == initNeededTransfer;

      // -- Creating state which is the sum of the two previously built up states
        b_3 := b_1_1 && b_2_1;
        b_3 := b_3 && state(ResultHeap, ResultMask);
        b_3 := b_3 && sumMask(ResultMask, Ops_1Mask, Used_1Mask);
        b_3 := (b_3 && IdenticalOnKnownLocations(Ops_1Heap, ResultHeap, Ops_1Mask)) && IdenticalOnKnownLocations(Used_1Heap, ResultHeap, Used_1Mask);
        b_3 := b_3 && state(ResultHeap, ResultMask);
      b_1_1 := b_1_1 && b_3;
    Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] + FullPerm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: while (nxt != null && head(nxt) < x) -- list_insert_noseq.vpr@54.3--77.4

    // -- Before loop head

      // -- Exhale loop invariant before loop
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(crt.val, write) && acc(crt.next, write) might not hold on entry. There might be insufficient permission to access crt.val (list_insert_noseq.vpr@57.15--57.44) [249]"}
            perm <= Mask[crt, val];
        }
        Mask[crt, val] := Mask[crt, val] - perm;
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(crt.val, write) && acc(crt.next, write) might not hold on entry. There might be insufficient permission to access crt.next (list_insert_noseq.vpr@57.15--57.44) [250]"}
            perm <= Mask[crt, next];
        }
        Mask[crt, next] := Mask[crt, next] - perm;
        assert {:msg "  Loop invariant nxt == crt.next might not hold on entry. Assertion nxt == crt.next might not hold. (list_insert_noseq.vpr@58.15--58.30) [251]"}
          nxt == Heap[crt, next];
        if (nxt != null) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Loop invariant nxt != null ==> acc(List(nxt), write) might not hold on entry. There might be insufficient permission to access List(nxt) (list_insert_noseq.vpr@60.15--60.47) [252]"}
              perm <= Mask[null, List(nxt)];
          }
          Mask[null, List(nxt)] := Mask[null, List(nxt)] - perm;
        }
        // permLe
        assert {:msg "  Loop invariant acc(List(crt), write) --* acc(List(xs), write) might not hold on entry. Magic wand instance not found. (list_insert_noseq.vpr@61.15--61.22) [253]"}
          FullPerm <= Mask[null, wand(crt, FullPerm, xs, FullPerm)];
        Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] - FullPerm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;

    // -- Havoc loop written variables (except locals)
      havoc i, nxt, crt;
      assume Heap[nxt, $allocated];
      assume Heap[crt, $allocated];

    // -- Check definedness of invariant
      if (*) {
        perm := FullPerm;
        assume crt != null;
        Mask[crt, val] := Mask[crt, val] + perm;
        assume state(Heap, Mask);
        perm := FullPerm;
        assume crt != null;
        Mask[crt, next] := Mask[crt, next] + perm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);

        // -- Check definedness of nxt == crt.next
          assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access crt.next (list_insert_noseq.vpr@58.15--58.30) [254]"}
            HasDirectPerm(Mask, crt, next);
        assume nxt == Heap[crt, next];
        assume state(Heap, Mask);
        if (nxt != null) {
          perm := FullPerm;
          Mask[null, List(nxt)] := Mask[null, List(nxt)] + perm;
          assume state(Heap, Mask);
        }
        assume state(Heap, Mask);

        // -- Check definedness of acc(List(crt), write) --* acc(List(xs), write)
          if (*) {
            havoc WandDefLHSHeap;
            WandDefLHSMask := ZeroMask;
            perm := FullPerm;
            WandDefLHSMask[null, List(crt)] := WandDefLHSMask[null, List(crt)] + perm;
            assume state(WandDefLHSHeap, WandDefLHSMask);
            assume state(WandDefLHSHeap, WandDefLHSMask);

            // -- Translating statement: label lhs3 -- list_insert_noseq.vpr@61.15--61.22
              lhs3:
              Labellhs3Mask := WandDefLHSMask;
              Labellhs3Heap := WandDefLHSHeap;
              assume state(WandDefLHSHeap, WandDefLHSMask);
            havoc WandDefRHSHeap;
            WandDefRHSMask := ZeroMask;
            perm := FullPerm;
            WandDefRHSMask[null, List(xs)] := WandDefRHSMask[null, List(xs)] + perm;
            assume state(WandDefRHSHeap, WandDefRHSMask);
            assume state(WandDefRHSHeap, WandDefRHSMask);
            assume false;
          }
        Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] + FullPerm;
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
        perm := FullPerm;
        assume crt != null;
        Mask[crt, val] := Mask[crt, val] + perm;
        assume state(Heap, Mask);
        perm := FullPerm;
        assume crt != null;
        Mask[crt, next] := Mask[crt, next] + perm;
        assume state(Heap, Mask);
        assume nxt == Heap[crt, next];
        if (nxt != null) {
          perm := FullPerm;
          Mask[null, List(nxt)] := Mask[null, List(nxt)] + perm;
          assume state(Heap, Mask);
        }
        Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] + FullPerm;
        assume state(Heap, Mask);
        assume state(Heap, Mask);
        // Check and assume guard

        // -- Check definedness of nxt != null && head(nxt) < x
          if (nxt != null) {
            if (*) {
              // Exhale precondition of function application
              perm := FullPerm;
              if (perm != NoPerm) {
                assert {:msg "  Precondition of function head might not hold. There might be insufficient permission to access List(nxt) (list_insert_noseq.vpr@54.25--54.34) [255]"}
                  perm <= Mask[null, List(nxt)];
              }
              Mask[null, List(nxt)] := Mask[null, List(nxt)] - perm;
              // Finish exhale
              havoc ExhaleHeap;
              assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
              Heap := ExhaleHeap;
              // Stop execution
              assume false;
            }
          }
        assume nxt != null && head(Heap, nxt) < x;
        assume state(Heap, Mask);

        // -- Translate loop body

          // -- Assumptions about local variables
            assume Heap[oldCrt, $allocated];
            assume Heap[prev, $allocated];

          // -- Translating statement: oldCrt := crt -- list_insert_noseq.vpr@65.5--65.27
            oldCrt := crt;
            assume state(Heap, Mask);

          // -- Translating statement: prev := crt -- list_insert_noseq.vpr@66.5--66.25
            prev := crt;
            assume state(Heap, Mask);

          // -- Translating statement: unfold acc(List(nxt), write) -- list_insert_noseq.vpr@68.5--68.21
            assume List#trigger(Heap, List(nxt));
            assume Heap[null, List(nxt)] == CombineFrames(FrameFragment(Heap[nxt, val]), CombineFrames(FrameFragment(Heap[nxt, next]), FrameFragment((if Heap[nxt, next] != null then Heap[null, List(Heap[nxt, next])] else EmptyFrame))));
            perm := FullPerm;
            if (perm != NoPerm) {
              assert {:msg "  Unfolding List(nxt) might fail. There might be insufficient permission to access List(nxt) (list_insert_noseq.vpr@68.5--68.21) [256]"}
                perm <= Mask[null, List(nxt)];
            }
            Mask[null, List(nxt)] := Mask[null, List(nxt)] - perm;

            // -- Update version of predicate
              if (!HasDirectPerm(Mask, null, List(nxt))) {
                havoc newVersion;
                Heap[null, List(nxt)] := newVersion;
              }
            perm := FullPerm;
            assume nxt != null;
            Mask[nxt, val] := Mask[nxt, val] + perm;
            assume state(Heap, Mask);
            perm := FullPerm;
            assume nxt != null;
            Mask[nxt, next] := Mask[nxt, next] + perm;
            assume state(Heap, Mask);
            if (Heap[nxt, next] != null) {
              perm := FullPerm;
              Mask[null, List(Heap[nxt, next])] := Mask[null, List(Heap[nxt, next])] + perm;

              // -- Extra unfolding of predicate
                assume InsidePredicate(List(nxt), Heap[null, List(nxt)], List(Heap[nxt, next]), Heap[null, List(Heap[nxt, next])]);
              assume state(Heap, Mask);
            }
            assume state(Heap, Mask);
            assume state(Heap, Mask);

          // -- Translating statement: crt := nxt -- list_insert_noseq.vpr@69.5--69.15
            crt := nxt;
            assume state(Heap, Mask);

          // -- Translating statement: nxt := nxt.next -- list_insert_noseq.vpr@70.5--70.20

            // -- Check definedness of nxt.next
              assert {:msg "  Assignment might fail. There might be insufficient permission to access nxt.next (list_insert_noseq.vpr@70.5--70.20) [257]"}
                HasDirectPerm(Mask, nxt, next);
            nxt := Heap[nxt, next];
            assume state(Heap, Mask);

          // -- Translating statement: i := i + 1 -- list_insert_noseq.vpr@71.5--71.15
            i := i + 1;
            assume state(Heap, Mask);

          // -- Translating statement: package acc(List(crt), write) --* acc(List(xs), write) {
  //   fold acc(List(prev), write)
  //   apply acc(List(oldCrt), write) --* acc(List(xs), write)
  // } -- list_insert_noseq.vpr@73.5--76.6
            havoc Ops_3Heap;
            Ops_3Mask := ZeroMask;
            b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
            havoc Used_2Heap;
            Used_2Mask := ZeroMask;
            b_4 := b_4 && state(Used_2Heap, Used_2Mask);
            // Inhaling left hand side of current wand into hypothetical state
            if (b_5) {
              perm := FullPerm;
              b_5 := b_5;
              Ops_3Mask[null, List(crt)] := Ops_3Mask[null, List(crt)] + perm;
              b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
            }
            b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);

            // -- Translating statement: label lhs4 -- list_insert_noseq.vpr@73.13--73.22
              lhs4:
              Labellhs4Mask := Ops_3Mask;
              Labellhs4Heap := Ops_3Heap;
              b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
            boolCur_1 := true;
            if (b_5) {

              // -- Translating statement: fold acc(List(prev), write) -- list_insert_noseq.vpr@74.9--74.24
                havoc Used_3Heap;
                Used_3Mask := ZeroMask;
                b_6 := b_6 && state(Used_3Heap, Used_3Mask);

                // -- Transfer of acc(prev.val, write)
                  rcvLocal := prev;
                  neededTransfer := FullPerm;
                  initNeededTransfer := Used_3Mask[rcvLocal, val] + neededTransfer;
                  assert {:msg "  Folding List(prev) might fail. Fraction acc(prev.val, write) might be negative. (list_insert_noseq.vpr@74.9--74.24) [258]"}
                    neededTransfer >= 0.000000000;

                  // -- transfer code for top state of stack
                    // accumulate constraints which need to be satisfied for transfer to occur
                    accVar2 := true;
                    // actual code for the transfer from current state on stack
                    if (((b_5 && b_6) && accVar2) && neededTransfer > 0.000000000) {
                      maskTransfer := Ops_3Mask[rcvLocal, val];
                      if (neededTransfer <= maskTransfer) {
                        takeTransfer := neededTransfer;
                      } else {
                        takeTransfer := maskTransfer;
                      }
                      if (takeTransfer > 0.000000000) {
                        neededTransfer := neededTransfer - takeTransfer;
                        Used_3Mask[rcvLocal, val] := Used_3Mask[rcvLocal, val] + takeTransfer;
                        b_6 := b_6 && state(Used_3Heap, Used_3Mask);
                        b_6 := b_6 && Ops_3Heap[rcvLocal, val] == Used_3Heap[rcvLocal, val];
                        Ops_3Mask[rcvLocal, val] := Ops_3Mask[rcvLocal, val] - takeTransfer;
                      }
                    }

                  // -- transfer code for top state of stack
                    // accumulate constraints which need to be satisfied for transfer to occur
                    accVar2 := true;
                    // actual code for the transfer from current state on stack
                    if (((b_5 && b_6) && accVar2) && neededTransfer > 0.000000000) {
                      maskTransfer := Mask[rcvLocal, val];
                      if (neededTransfer <= maskTransfer) {
                        takeTransfer := neededTransfer;
                      } else {
                        takeTransfer := maskTransfer;
                      }
                      if (takeTransfer > 0.000000000) {
                        neededTransfer := neededTransfer - takeTransfer;
                        Used_3Mask[rcvLocal, val] := Used_3Mask[rcvLocal, val] + takeTransfer;
                        b_6 := b_6 && state(Used_3Heap, Used_3Mask);
                        b_6 := b_6 && Heap[rcvLocal, val] == Used_3Heap[rcvLocal, val];
                        Mask[rcvLocal, val] := Mask[rcvLocal, val] - takeTransfer;
                        Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)][prev, val] := true;
                      }
                    }
                  assert {:msg "  Folding List(prev) might fail. There might be insufficient permission to access prev.val (list_insert_noseq.vpr@74.9--74.24) [259]"}
                    b_5 && b_6 ==> neededTransfer == 0.000000000 && Used_3Mask[rcvLocal, val] == initNeededTransfer;

                  // -- Creating state which is the sum of the two previously built up states
                    b_7 := b_5 && b_6;
                    b_7 := b_7 && state(Result_1Heap, Result_1Mask);
                    b_7 := b_7 && sumMask(Result_1Mask, Ops_3Mask, Used_3Mask);
                    b_7 := (b_7 && IdenticalOnKnownLocations(Ops_3Heap, Result_1Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_3Heap, Result_1Heap, Used_3Mask);
                    b_7 := b_7 && state(Result_1Heap, Result_1Mask);
                  b_5 := b_5 && b_7;
                b_5 := b_5 && b_6;
                b_5 := b_5 && Used_3Heap == Ops_3Heap;

                // -- Transfer of acc(prev.next, write)
                  rcvLocal := prev;
                  neededTransfer := FullPerm;
                  initNeededTransfer := Used_3Mask[rcvLocal, next] + neededTransfer;
                  assert {:msg "  Folding List(prev) might fail. Fraction acc(prev.next, write) might be negative. (list_insert_noseq.vpr@74.9--74.24) [260]"}
                    neededTransfer >= 0.000000000;

                  // -- transfer code for top state of stack
                    // accumulate constraints which need to be satisfied for transfer to occur
                    accVar2 := true;
                    // actual code for the transfer from current state on stack
                    if (((b_5 && b_6) && accVar2) && neededTransfer > 0.000000000) {
                      maskTransfer := Ops_3Mask[rcvLocal, next];
                      if (neededTransfer <= maskTransfer) {
                        takeTransfer := neededTransfer;
                      } else {
                        takeTransfer := maskTransfer;
                      }
                      if (takeTransfer > 0.000000000) {
                        neededTransfer := neededTransfer - takeTransfer;
                        Used_3Mask[rcvLocal, next] := Used_3Mask[rcvLocal, next] + takeTransfer;
                        b_6 := b_6 && state(Used_3Heap, Used_3Mask);
                        b_6 := b_6 && Ops_3Heap[rcvLocal, next] == Used_3Heap[rcvLocal, next];
                        Ops_3Mask[rcvLocal, next] := Ops_3Mask[rcvLocal, next] - takeTransfer;
                      }
                    }

                  // -- transfer code for top state of stack
                    // accumulate constraints which need to be satisfied for transfer to occur
                    accVar2 := true;
                    // actual code for the transfer from current state on stack
                    if (((b_5 && b_6) && accVar2) && neededTransfer > 0.000000000) {
                      maskTransfer := Mask[rcvLocal, next];
                      if (neededTransfer <= maskTransfer) {
                        takeTransfer := neededTransfer;
                      } else {
                        takeTransfer := maskTransfer;
                      }
                      if (takeTransfer > 0.000000000) {
                        neededTransfer := neededTransfer - takeTransfer;
                        Used_3Mask[rcvLocal, next] := Used_3Mask[rcvLocal, next] + takeTransfer;
                        b_6 := b_6 && state(Used_3Heap, Used_3Mask);
                        b_6 := b_6 && Heap[rcvLocal, next] == Used_3Heap[rcvLocal, next];
                        Mask[rcvLocal, next] := Mask[rcvLocal, next] - takeTransfer;
                        Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)][prev, next] := true;
                      }
                    }
                  assert {:msg "  Folding List(prev) might fail. There might be insufficient permission to access prev.next (list_insert_noseq.vpr@74.9--74.24) [261]"}
                    b_5 && b_6 ==> neededTransfer == 0.000000000 && Used_3Mask[rcvLocal, next] == initNeededTransfer;

                  // -- Creating state which is the sum of the two previously built up states
                    b_8 := b_5 && b_6;
                    b_8 := b_8 && state(Result_2Heap, Result_2Mask);
                    b_8 := b_8 && sumMask(Result_2Mask, Ops_3Mask, Used_3Mask);
                    b_8 := (b_8 && IdenticalOnKnownLocations(Ops_3Heap, Result_2Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_3Heap, Result_2Heap, Used_3Mask);
                    b_8 := b_8 && state(Result_2Heap, Result_2Mask);
                  b_5 := b_5 && b_8;
                b_5 := b_5 && b_6;
                b_5 := b_5 && Used_3Heap == Ops_3Heap;
                if (b_5 ==> Result_2Heap[prev, next] != null) {

                  // -- Transfer of acc(List(prev.next), write)

                    // -- checking if access predicate defined in used state
                      if (b_5 && b_6) {
                        if (b_5) {

                          // -- Check definedness of acc(List(prev.next), write)
                            assert {:msg "  Folding List(prev) might fail. There might be insufficient permission to access prev.next (list_insert_noseq.vpr@74.9--74.24) [262]"}
                              HasDirectPerm(Result_2Mask, prev, next);
                        }
                      }
                    arg_1 := Result_2Heap[prev, next];
                    neededTransfer := FullPerm;
                    initNeededTransfer := Used_3Mask[null, List(arg_1)] + neededTransfer;
                    assert {:msg "  Folding List(prev) might fail. Fraction acc(List(prev.next), write) might be negative. (list_insert_noseq.vpr@74.9--74.24) [263]"}
                      neededTransfer >= 0.000000000;

                    // -- transfer code for top state of stack
                      // accumulate constraints which need to be satisfied for transfer to occur
                      accVar2 := true;
                      // actual code for the transfer from current state on stack
                      if (((b_5 && b_6) && accVar2) && neededTransfer > 0.000000000) {
                        maskTransfer := Ops_3Mask[null, List(arg_1)];
                        if (neededTransfer <= maskTransfer) {
                          takeTransfer := neededTransfer;
                        } else {
                          takeTransfer := maskTransfer;
                        }
                        if (takeTransfer > 0.000000000) {
                          neededTransfer := neededTransfer - takeTransfer;
                          Used_3Mask[null, List(arg_1)] := Used_3Mask[null, List(arg_1)] + takeTransfer;
                          b_6 := b_6 && state(Used_3Heap, Used_3Mask);
                          TempMask := ZeroMask;
                          TempMask[null, List(arg_1)] := FullPerm;
                          b_6 := b_6 && IdenticalOnKnownLocations(Ops_3Heap, Used_3Heap, TempMask);
                          Ops_3Mask[null, List(arg_1)] := Ops_3Mask[null, List(arg_1)] - takeTransfer;
                        }
                      }

                    // -- transfer code for top state of stack
                      // accumulate constraints which need to be satisfied for transfer to occur
                      accVar2 := true;
                      // actual code for the transfer from current state on stack
                      if (((b_5 && b_6) && accVar2) && neededTransfer > 0.000000000) {
                        maskTransfer := Mask[null, List(arg_1)];
                        if (neededTransfer <= maskTransfer) {
                          takeTransfer := neededTransfer;
                        } else {
                          takeTransfer := maskTransfer;
                        }
                        if (takeTransfer > 0.000000000) {
                          neededTransfer := neededTransfer - takeTransfer;
                          Used_3Mask[null, List(arg_1)] := Used_3Mask[null, List(arg_1)] + takeTransfer;
                          b_6 := b_6 && state(Used_3Heap, Used_3Mask);
                          TempMask := ZeroMask;
                          TempMask[null, List(arg_1)] := FullPerm;
                          b_6 := b_6 && IdenticalOnKnownLocations(Heap, Used_3Heap, TempMask);
                          Mask[null, List(arg_1)] := Mask[null, List(arg_1)] - takeTransfer;
                          havoc newPMask;
                          assume (forall <A, B> o_5: Ref, f_9: (Field A B) ::
                            { newPMask[o_5, f_9] }
                            Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)][o_5, f_9] || Heap[null, List#sm(Heap[prev, next])][o_5, f_9] ==> newPMask[o_5, f_9]
                          );
                          Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)] := newPMask;
                        }
                      }
                    assert {:msg "  Folding List(prev) might fail. There might be insufficient permission to access List(prev.next) (list_insert_noseq.vpr@74.9--74.24) [264]"}
                      b_5 && b_6 ==> neededTransfer == 0.000000000 && Used_3Mask[null, List(arg_1)] == initNeededTransfer;

                    // -- Creating state which is the sum of the two previously built up states
                      b_9 := b_5 && b_6;
                      b_9 := b_9 && state(Result_3Heap, Result_3Mask);
                      b_9 := b_9 && sumMask(Result_3Mask, Ops_3Mask, Used_3Mask);
                      b_9 := (b_9 && IdenticalOnKnownLocations(Ops_3Heap, Result_3Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_3Heap, Result_3Heap, Used_3Mask);
                      b_9 := b_9 && state(Result_3Heap, Result_3Mask);
                    b_5 := b_5 && b_9;
                  b_5 := b_5 && b_6;
                  b_5 := b_5 && Used_3Heap == Ops_3Heap;
                }

                // -- Creating state which is the sum of the two previously built up states
                  b_10 := b_5 && b_6;
                  b_10 := b_10 && state(Result_4Heap, Result_4Mask);
                  b_10 := b_10 && sumMask(Result_4Mask, Ops_3Mask, Used_3Mask);
                  b_10 := (b_10 && IdenticalOnKnownLocations(Ops_3Heap, Result_4Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_3Heap, Result_4Heap, Used_3Mask);
                  b_10 := b_10 && state(Result_4Heap, Result_4Mask);
                b_5 := b_5 && b_10;
                perm := FullPerm;
                b_5 := b_5;
                Ops_3Mask[null, List(prev)] := Ops_3Mask[null, List(prev)] + perm;
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
                assume List#trigger(Ops_3Heap, List(prev));
                assume Ops_3Heap[null, List(prev)] == CombineFrames(FrameFragment(Ops_3Heap[prev, val]), CombineFrames(FrameFragment(Ops_3Heap[prev, next]), FrameFragment((if Ops_3Heap[prev, next] != null then Ops_3Heap[null, List(Ops_3Heap[prev, next])] else EmptyFrame))));
                if (!HasDirectPerm(Ops_3Mask, null, List(prev))) {
                  Ops_3Heap[null, List#sm(prev)] := ZeroPMask;
                  havoc freshVersion;
                  Ops_3Heap[null, List(prev)] := freshVersion;
                }
                Ops_3Heap[null, List#sm(prev)][prev, val] := true;
                Ops_3Heap[null, List#sm(prev)][prev, next] := true;
                if (Ops_3Heap[prev, next] != null) {
                  havoc newPMask;
                  assume (forall <A, B> o_6: Ref, f_10: (Field A B) ::
                    { newPMask[o_6, f_10] }
                    Ops_3Heap[null, List#sm(prev)][o_6, f_10] || Ops_3Heap[null, List#sm(Ops_3Heap[prev, next])][o_6, f_10] ==> newPMask[o_6, f_10]
                  );
                  Ops_3Heap[null, List#sm(prev)] := newPMask;
                }
                assume state(Ops_3Heap, Ops_3Mask);
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
            }
            if (b_5) {

              // -- Translating statement: apply acc(List(oldCrt), write) --* acc(List(xs), write) -- list_insert_noseq.vpr@75.9--75.50

                // -- check if wand is held and remove an instance
                  havoc Used_4Heap;
                  Used_4Mask := ZeroMask;
                  b_11 := b_11 && state(Used_4Heap, Used_4Mask);

                  // -- Transfer of acc(List(oldCrt), write) --* acc(List(xs), write)

                    // -- checking if access predicate defined in used state
                      if (b_5 && b_11) {
                        if (b_5) {

                          // -- Check definedness of acc(List(oldCrt), write) --* acc(List(xs), write)
                            if (*) {
                              havoc WandDefLHSHeap;
                              WandDefLHSMask := ZeroMask;
                              perm := FullPerm;
                              WandDefLHSMask[null, List(oldCrt)] := WandDefLHSMask[null, List(oldCrt)] + perm;
                              assume state(WandDefLHSHeap, WandDefLHSMask);
                              assume state(WandDefLHSHeap, WandDefLHSMask);

                              // -- Translating statement: label lhs7 -- list_insert_noseq.vpr@75.15--75.50
                                lhs7:
                                Labellhs7Mask := WandDefLHSMask;
                                Labellhs7Heap := WandDefLHSHeap;
                                assume state(WandDefLHSHeap, WandDefLHSMask);
                              havoc WandDefRHSHeap;
                              WandDefRHSMask := ZeroMask;
                              perm := FullPerm;
                              WandDefRHSMask[null, List(xs)] := WandDefRHSMask[null, List(xs)] + perm;
                              assume state(WandDefRHSHeap, WandDefRHSMask);
                              assume state(WandDefRHSHeap, WandDefRHSMask);
                              assume false;
                            }
                        }
                      }
                    neededTransfer := 1.000000000;
                    initNeededTransfer := Used_4Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] + neededTransfer;
                    assert {:msg "  Applying wand might fail. Fraction acc(List(oldCrt), write) --* acc(List(xs), write) might be negative. (list_insert_noseq.vpr@75.9--75.50) [265]"}
                      neededTransfer >= 0.000000000;

                    // -- transfer code for top state of stack
                      // accumulate constraints which need to be satisfied for transfer to occur
                      accVar2 := true;
                      // actual code for the transfer from current state on stack
                      if (((b_5 && b_11) && accVar2) && neededTransfer > 0.000000000) {
                        maskTransfer := Ops_3Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)];
                        if (neededTransfer <= maskTransfer) {
                          takeTransfer := neededTransfer;
                        } else {
                          takeTransfer := maskTransfer;
                        }
                        if (takeTransfer > 0.000000000) {
                          neededTransfer := neededTransfer - takeTransfer;
                          Used_4Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] := Used_4Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] + takeTransfer;
                          b_11 := b_11 && state(Used_4Heap, Used_4Mask);
                          Ops_3Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] := Ops_3Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] - takeTransfer;
                        }
                      }

                    // -- transfer code for top state of stack
                      // accumulate constraints which need to be satisfied for transfer to occur
                      accVar2 := true;
                      // actual code for the transfer from current state on stack
                      if (((b_5 && b_11) && accVar2) && neededTransfer > 0.000000000) {
                        maskTransfer := Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)];
                        if (neededTransfer <= maskTransfer) {
                          takeTransfer := neededTransfer;
                        } else {
                          takeTransfer := maskTransfer;
                        }
                        if (takeTransfer > 0.000000000) {
                          neededTransfer := neededTransfer - takeTransfer;
                          Used_4Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] := Used_4Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] + takeTransfer;
                          b_11 := b_11 && state(Used_4Heap, Used_4Mask);
                          Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] := Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] - takeTransfer;
                        }
                      }
                    assert {:msg "  Applying wand might fail. Magic wand instance not found. (list_insert_noseq.vpr@75.9--75.50) [266]"}
                      b_5 && b_11 ==> neededTransfer == 0.000000000 && Used_4Mask[null, wand(oldCrt, FullPerm, xs, FullPerm)] == initNeededTransfer;

                    // -- Creating state which is the sum of the two previously built up states
                      b_12 := b_5 && b_11;
                      b_12 := b_12 && state(Result_5Heap, Result_5Mask);
                      b_12 := b_12 && sumMask(Result_5Mask, Ops_3Mask, Used_4Mask);
                      b_12 := (b_12 && IdenticalOnKnownLocations(Ops_3Heap, Result_5Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_4Heap, Result_5Heap, Used_4Mask);
                      b_12 := b_12 && state(Result_5Heap, Result_5Mask);
                    b_5 := b_5 && b_12;
                  b_5 := b_5 && b_11;
                  b_5 := b_5 && Used_4Heap == Ops_3Heap;
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);

                // -- check if LHS holds and remove permissions
                  havoc Used_5Heap;
                  Used_5Mask := ZeroMask;
                  b_13 := b_13 && state(Used_5Heap, Used_5Mask);

                  // -- Transfer of acc(List(oldCrt), write)
                    arg_2 := oldCrt;
                    neededTransfer := FullPerm;
                    initNeededTransfer := Used_5Mask[null, List(arg_2)] + neededTransfer;
                    assert {:msg "  Applying wand might fail. Fraction acc(List(oldCrt), write) might be negative. (list_insert_noseq.vpr@75.9--75.50) [267]"}
                      neededTransfer >= 0.000000000;

                    // -- transfer code for top state of stack
                      // accumulate constraints which need to be satisfied for transfer to occur
                      accVar2 := true;
                      // actual code for the transfer from current state on stack
                      if (((b_5 && b_13) && accVar2) && neededTransfer > 0.000000000) {
                        maskTransfer := Ops_3Mask[null, List(arg_2)];
                        if (neededTransfer <= maskTransfer) {
                          takeTransfer := neededTransfer;
                        } else {
                          takeTransfer := maskTransfer;
                        }
                        if (takeTransfer > 0.000000000) {
                          neededTransfer := neededTransfer - takeTransfer;
                          Used_5Mask[null, List(arg_2)] := Used_5Mask[null, List(arg_2)] + takeTransfer;
                          b_13 := b_13 && state(Used_5Heap, Used_5Mask);
                          TempMask := ZeroMask;
                          TempMask[null, List(arg_2)] := FullPerm;
                          b_13 := b_13 && IdenticalOnKnownLocations(Ops_3Heap, Used_5Heap, TempMask);
                          Ops_3Mask[null, List(arg_2)] := Ops_3Mask[null, List(arg_2)] - takeTransfer;
                        }
                      }

                    // -- transfer code for top state of stack
                      // accumulate constraints which need to be satisfied for transfer to occur
                      accVar2 := true;
                      // actual code for the transfer from current state on stack
                      if (((b_5 && b_13) && accVar2) && neededTransfer > 0.000000000) {
                        maskTransfer := Mask[null, List(arg_2)];
                        if (neededTransfer <= maskTransfer) {
                          takeTransfer := neededTransfer;
                        } else {
                          takeTransfer := maskTransfer;
                        }
                        if (takeTransfer > 0.000000000) {
                          neededTransfer := neededTransfer - takeTransfer;
                          Used_5Mask[null, List(arg_2)] := Used_5Mask[null, List(arg_2)] + takeTransfer;
                          b_13 := b_13 && state(Used_5Heap, Used_5Mask);
                          TempMask := ZeroMask;
                          TempMask[null, List(arg_2)] := FullPerm;
                          b_13 := b_13 && IdenticalOnKnownLocations(Heap, Used_5Heap, TempMask);
                          Mask[null, List(arg_2)] := Mask[null, List(arg_2)] - takeTransfer;
                          havoc newPMask;
                          assume (forall <A, B> o_7: Ref, f_11: (Field A B) ::
                            { newPMask[o_7, f_11] }
                            Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)][o_7, f_11] || Heap[null, List#sm(oldCrt)][o_7, f_11] ==> newPMask[o_7, f_11]
                          );
                          Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)] := newPMask;
                        }
                      }
                    assert {:msg "  Applying wand might fail. There might be insufficient permission to access List(oldCrt) (list_insert_noseq.vpr@75.9--75.50) [268]"}
                      b_5 && b_13 ==> neededTransfer == 0.000000000 && Used_5Mask[null, List(arg_2)] == initNeededTransfer;

                    // -- Creating state which is the sum of the two previously built up states
                      b_14 := b_5 && b_13;
                      b_14 := b_14 && state(Result_6Heap, Result_6Mask);
                      b_14 := b_14 && sumMask(Result_6Mask, Ops_3Mask, Used_5Mask);
                      b_14 := (b_14 && IdenticalOnKnownLocations(Ops_3Heap, Result_6Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_5Heap, Result_6Heap, Used_5Mask);
                      b_14 := b_14 && state(Result_6Heap, Result_6Mask);
                    b_5 := b_5 && b_14;
                  b_5 := b_5 && b_13;
                  b_5 := b_5 && Used_5Heap == Ops_3Heap;
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);

                // -- inhale the RHS of the wand
                  perm := FullPerm;
                  b_5 := b_5;
                  Ops_3Mask[null, List(xs)] := Ops_3Mask[null, List(xs)] + perm;
                  b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
                  b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
                havoc ExhaleHeap;
                assume IdenticalOnKnownLocations(Ops_3Heap, ExhaleHeap, Ops_3Mask);
                Ops_3Heap := ExhaleHeap;
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
                b_5 := b_5 && state(Ops_3Heap, Ops_3Mask);
            }
            // Translating exec of non-ghost operationacc(List(xs), write)
            havoc Used_6Heap;
            Used_6Mask := ZeroMask;
            b_15 := b_15 && state(Used_6Heap, Used_6Mask);

            // -- Transfer of acc(List(xs), write)
              arg_3 := xs;
              neededTransfer := FullPerm;
              initNeededTransfer := Used_6Mask[null, List(arg_3)] + neededTransfer;
              assert {:msg "  Packaging wand might fail. Fraction acc(List(xs), write) might be negative. (list_insert_noseq.vpr@73.5--76.6) [269]"}
                neededTransfer >= 0.000000000;

              // -- transfer code for top state of stack
                // accumulate constraints which need to be satisfied for transfer to occur
                accVar2 := true;
                // actual code for the transfer from current state on stack
                if ((((b_5 && b_5) && b_15) && accVar2) && neededTransfer > 0.000000000) {
                  maskTransfer := Ops_3Mask[null, List(arg_3)];
                  if (neededTransfer <= maskTransfer) {
                    takeTransfer := neededTransfer;
                  } else {
                    takeTransfer := maskTransfer;
                  }
                  if (takeTransfer > 0.000000000) {
                    neededTransfer := neededTransfer - takeTransfer;
                    Used_6Mask[null, List(arg_3)] := Used_6Mask[null, List(arg_3)] + takeTransfer;
                    b_15 := b_15 && state(Used_6Heap, Used_6Mask);
                    TempMask := ZeroMask;
                    TempMask[null, List(arg_3)] := FullPerm;
                    b_15 := b_15 && IdenticalOnKnownLocations(Ops_3Heap, Used_6Heap, TempMask);
                    Ops_3Mask[null, List(arg_3)] := Ops_3Mask[null, List(arg_3)] - takeTransfer;
                  }
                }

              // -- transfer code for top state of stack
                // accumulate constraints which need to be satisfied for transfer to occur
                accVar2 := true;
                // actual code for the transfer from current state on stack
                if ((((b_5 && b_5) && b_15) && accVar2) && neededTransfer > 0.000000000) {
                  maskTransfer := Mask[null, List(arg_3)];
                  if (neededTransfer <= maskTransfer) {
                    takeTransfer := neededTransfer;
                  } else {
                    takeTransfer := maskTransfer;
                  }
                  if (takeTransfer > 0.000000000) {
                    neededTransfer := neededTransfer - takeTransfer;
                    Used_6Mask[null, List(arg_3)] := Used_6Mask[null, List(arg_3)] + takeTransfer;
                    b_15 := b_15 && state(Used_6Heap, Used_6Mask);
                    TempMask := ZeroMask;
                    TempMask[null, List(arg_3)] := FullPerm;
                    b_15 := b_15 && IdenticalOnKnownLocations(Heap, Used_6Heap, TempMask);
                    Mask[null, List(arg_3)] := Mask[null, List(arg_3)] - takeTransfer;
                    havoc newPMask;
                    assume (forall <A, B> o_8: Ref, f_12: (Field A B) ::
                      { newPMask[o_8, f_12] }
                      Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)][o_8, f_12] || Heap[null, List#sm(xs)][o_8, f_12] ==> newPMask[o_8, f_12]
                    );
                    Heap[null, wand#sm(crt, FullPerm, xs, FullPerm)] := newPMask;
                  }
                }
              assert {:msg "  Packaging wand might fail. There might be insufficient permission to access List(xs) (list_insert_noseq.vpr@73.5--76.6) [270]"}
                (b_5 && b_5) && b_15 ==> neededTransfer == 0.000000000 && Used_6Mask[null, List(arg_3)] == initNeededTransfer;

              // -- Creating state which is the sum of the two previously built up states
                b_16 := b_5 && b_15;
                b_16 := b_16 && state(Result_7Heap, Result_7Mask);
                b_16 := b_16 && sumMask(Result_7Mask, Ops_3Mask, Used_6Mask);
                b_16 := (b_16 && IdenticalOnKnownLocations(Ops_3Heap, Result_7Heap, Ops_3Mask)) && IdenticalOnKnownLocations(Used_6Heap, Result_7Heap, Used_6Mask);
                b_16 := b_16 && state(Result_7Heap, Result_7Mask);
              b_5 := b_5 && b_16;
            Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] + FullPerm;
            assume state(Heap, Mask);
            assume state(Heap, Mask);
            assume state(Heap, Mask);
        // Exhale invariant
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(crt.val, write) && acc(crt.next, write) might not be preserved. There might be insufficient permission to access crt.val (list_insert_noseq.vpr@57.15--57.44) [271]"}
            perm <= Mask[crt, val];
        }
        Mask[crt, val] := Mask[crt, val] - perm;
        perm := FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Loop invariant acc(crt.val, write) && acc(crt.next, write) might not be preserved. There might be insufficient permission to access crt.next (list_insert_noseq.vpr@57.15--57.44) [272]"}
            perm <= Mask[crt, next];
        }
        Mask[crt, next] := Mask[crt, next] - perm;
        assert {:msg "  Loop invariant nxt == crt.next might not be preserved. Assertion nxt == crt.next might not hold. (list_insert_noseq.vpr@58.15--58.30) [273]"}
          nxt == Heap[crt, next];
        if (nxt != null) {
          perm := FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Loop invariant nxt != null ==> acc(List(nxt), write) might not be preserved. There might be insufficient permission to access List(nxt) (list_insert_noseq.vpr@60.15--60.47) [274]"}
              perm <= Mask[null, List(nxt)];
          }
          Mask[null, List(nxt)] := Mask[null, List(nxt)] - perm;
        }
        // permLe
        assert {:msg "  Loop invariant acc(List(crt), write) --* acc(List(xs), write) might not be preserved. Magic wand instance not found. (list_insert_noseq.vpr@61.15--61.22) [275]"}
          FullPerm <= Mask[null, wand(crt, FullPerm, xs, FullPerm)];
        Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] - FullPerm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Terminate execution
        assume false;
      }

    // -- Inhale loop invariant after loop, and assume guard
      assume !(nxt != null && head(Heap, nxt) < x);
      assume state(Heap, Mask);
      perm := FullPerm;
      assume crt != null;
      Mask[crt, val] := Mask[crt, val] + perm;
      assume state(Heap, Mask);
      perm := FullPerm;
      assume crt != null;
      Mask[crt, next] := Mask[crt, next] + perm;
      assume state(Heap, Mask);
      assume nxt == Heap[crt, next];
      if (nxt != null) {
        perm := FullPerm;
        Mask[null, List(nxt)] := Mask[null, List(nxt)] + perm;
        assume state(Heap, Mask);
      }
      Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] + FullPerm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: node := new(val, next) -- list_insert_noseq.vpr@81.3--81.7
    havoc freshObj;
    assume freshObj != null && !Heap[freshObj, $allocated];
    Heap[freshObj, $allocated] := true;
    node := freshObj;
    Mask[node, val] := Mask[node, val] + FullPerm;
    Mask[node, next] := Mask[node, next] + FullPerm;
    assume state(Heap, Mask);

  // -- Translating statement: node.val := x -- list_insert_noseq.vpr@82.3--82.16
    assert {:msg "  Assignment might fail. There might be insufficient permission to access node.val (list_insert_noseq.vpr@82.3--82.16) [276]"}
      FullPerm == Mask[node, val];
    Heap[node, val] := x;
    assume state(Heap, Mask);

  // -- Translating statement: node.next := nxt -- list_insert_noseq.vpr@83.3--83.19
    assert {:msg "  Assignment might fail. There might be insufficient permission to access node.next (list_insert_noseq.vpr@83.3--83.19) [277]"}
      FullPerm == Mask[node, next];
    Heap[node, next] := nxt;
    assume state(Heap, Mask);

  // -- Translating statement: fold acc(List(node), write) -- list_insert_noseq.vpr@84.3--84.18
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(node) might fail. There might be insufficient permission to access node.val (list_insert_noseq.vpr@84.3--84.18) [279]"}
        perm <= Mask[node, val];
    }
    Mask[node, val] := Mask[node, val] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(node) might fail. There might be insufficient permission to access node.next (list_insert_noseq.vpr@84.3--84.18) [281]"}
        perm <= Mask[node, next];
    }
    Mask[node, next] := Mask[node, next] - perm;
    if (Heap[node, next] != null) {
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding List(node) might fail. There might be insufficient permission to access List(node.next) (list_insert_noseq.vpr@84.3--84.18) [283]"}
          perm <= Mask[null, List(Heap[node, next])];
      }
      Mask[null, List(Heap[node, next])] := Mask[null, List(Heap[node, next])] - perm;

      // -- Record predicate instance information
        assume InsidePredicate(List(node), Heap[null, List(node)], List(Heap[node, next]), Heap[null, List(Heap[node, next])]);
    }
    perm := FullPerm;
    Mask[null, List(node)] := Mask[null, List(node)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume List#trigger(Heap, List(node));
    assume Heap[null, List(node)] == CombineFrames(FrameFragment(Heap[node, val]), CombineFrames(FrameFragment(Heap[node, next]), FrameFragment((if Heap[node, next] != null then Heap[null, List(Heap[node, next])] else EmptyFrame))));
    if (!HasDirectPerm(Mask, null, List(node))) {
      Heap[null, List#sm(node)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, List(node)] := freshVersion;
    }
    Heap[null, List#sm(node)][node, val] := true;
    Heap[null, List#sm(node)][node, next] := true;
    if (Heap[node, next] != null) {
      havoc newPMask;
      assume (forall <A, B> o_9: Ref, f_13: (Field A B) ::
        { newPMask[o_9, f_13] }
        Heap[null, List#sm(node)][o_9, f_13] || Heap[null, List#sm(Heap[node, next])][o_9, f_13] ==> newPMask[o_9, f_13]
      );
      Heap[null, List#sm(node)] := newPMask;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: crt.next := node -- list_insert_noseq.vpr@89.3--89.19
    assert {:msg "  Assignment might fail. There might be insufficient permission to access crt.next (list_insert_noseq.vpr@89.3--89.19) [285]"}
      FullPerm == Mask[crt, next];
    Heap[crt, next] := node;
    assume state(Heap, Mask);

  // -- Translating statement: fold acc(List(crt), write) -- list_insert_noseq.vpr@90.3--90.17
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(crt) might fail. There might be insufficient permission to access crt.val (list_insert_noseq.vpr@90.3--90.17) [287]"}
        perm <= Mask[crt, val];
    }
    Mask[crt, val] := Mask[crt, val] - perm;
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding List(crt) might fail. There might be insufficient permission to access crt.next (list_insert_noseq.vpr@90.3--90.17) [289]"}
        perm <= Mask[crt, next];
    }
    Mask[crt, next] := Mask[crt, next] - perm;
    if (Heap[crt, next] != null) {
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding List(crt) might fail. There might be insufficient permission to access List(crt.next) (list_insert_noseq.vpr@90.3--90.17) [291]"}
          perm <= Mask[null, List(Heap[crt, next])];
      }
      Mask[null, List(Heap[crt, next])] := Mask[null, List(Heap[crt, next])] - perm;

      // -- Record predicate instance information
        assume InsidePredicate(List(crt), Heap[null, List(crt)], List(Heap[crt, next]), Heap[null, List(Heap[crt, next])]);
    }
    perm := FullPerm;
    Mask[null, List(crt)] := Mask[null, List(crt)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume List#trigger(Heap, List(crt));
    assume Heap[null, List(crt)] == CombineFrames(FrameFragment(Heap[crt, val]), CombineFrames(FrameFragment(Heap[crt, next]), FrameFragment((if Heap[crt, next] != null then Heap[null, List(Heap[crt, next])] else EmptyFrame))));
    if (!HasDirectPerm(Mask, null, List(crt))) {
      Heap[null, List#sm(crt)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, List(crt)] := freshVersion;
    }
    Heap[null, List#sm(crt)][crt, val] := true;
    Heap[null, List#sm(crt)][crt, next] := true;
    if (Heap[crt, next] != null) {
      havoc newPMask;
      assume (forall <A, B> o_10: Ref, f_14: (Field A B) ::
        { newPMask[o_10, f_14] }
        Heap[null, List#sm(crt)][o_10, f_14] || Heap[null, List#sm(Heap[crt, next])][o_10, f_14] ==> newPMask[o_10, f_14]
      );
      Heap[null, List#sm(crt)] := newPMask;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Translating statement: apply acc(List(crt), write) --* acc(List(xs), write) -- list_insert_noseq.vpr@95.3--95.16

    // -- check if wand is held and remove an instance
      // permLe
      assert {:msg "  Applying wand might fail. Magic wand instance not found. (list_insert_noseq.vpr@95.3--95.16) [293]"}
        FullPerm <= Mask[null, wand(crt, FullPerm, xs, FullPerm)];
      Mask[null, wand(crt, FullPerm, xs, FullPerm)] := Mask[null, wand(crt, FullPerm, xs, FullPerm)] - FullPerm;
    assume state(Heap, Mask);

    // -- check if LHS holds and remove permissions
      perm := FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Applying wand might fail. There might be insufficient permission to access List(crt) (list_insert_noseq.vpr@95.3--95.16) [295]"}
          perm <= Mask[null, List(crt)];
      }
      Mask[null, List(crt)] := Mask[null, List(crt)] - perm;
    assume state(Heap, Mask);

    // -- inhale the RHS of the wand
      perm := FullPerm;
      Mask[null, List(xs)] := Mask[null, List(xs)] + perm;
      assume state(Heap, Mask);
      assume state(Heap, Mask);
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
    assume state(Heap, Mask);

  // -- Exhaling postcondition
    perm := FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of insert might not hold. There might be insufficient permission to access List(xs) (list_insert_noseq.vpr@34.11--34.24) [297]"}
        perm <= Mask[null, List(xs)];
    }
    Mask[null, List(xs)] := Mask[null, List(xs)] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}
