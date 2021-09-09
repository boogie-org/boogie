// RUN: %parallel-boogie "%s" | %OutputCheck "%s"

// ==================================================
// Preamble of State module.
// ==================================================

function state(Heap: HeapType, Mask: MaskType): bool;

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
function succHeap(Heap0: HeapType, Heap1: HeapType): bool;
function succHeapTrans(Heap0: HeapType, Heap1: HeapType): bool;
function IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function IsPredicateField<A, B>(f_1: (Field A B)): bool;
function IsWandField<A, B>(f_1: (Field A B)): bool;
function getPredicateId<A, B>(f_1: (Field A B)): int;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[null, pm_f], IsPredicateField(pm_f) }
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
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);
// Updated Heaps are Successor Heaps
axiom (forall <A, B> Heap: HeapType, o: Ref, f_2: (Field A B), v: B ::
  { Heap[o, f_2:=v] }
  succHeap(Heap, Heap[o, f_2:=v])
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
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == NoPerm
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function PredicateMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
function WandMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function Perm(a: real, b: real): Perm;
function GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  GoodMask(Mask) ==> Mask[o_1, f_3] >= NoPerm && ((GoodMask(Mask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> Mask[o_1, f_3] <= FullPerm)
);
function HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> Mask[o_1, f_3] > NoPerm
);
function sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
);

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 0: length
const AssumeFunctionsAbove: int;
// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function FrameFragment<T>(t: T): FrameType;
function ConditionalFrame(p: Perm, f_5: FrameType): FrameType;
function dummyFunction<T>(t: T): bool;
function CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p: Perm, f_5: FrameType ::
  { ConditionalFrame(p, f_5) }
  ConditionalFrame(p, f_5) == (if p > 0.000000000 then f_5 else EmptyFrame)
);
// Function for recording enclosure of one predicate instance in another
function InsidePredicate<A, B>(p: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType): bool;
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
// Translation of domain MyType
// ==================================================

// The type for domain MyType
type MyTypeDomainType T;

// Translation of domain function get
function get<T>(x: T): T;

// Translation of domain axiom not_id
axiom (forall <T> x_1: T ::
  { (get(x_1): T) }
  (get(x_1): T) != x_1
);

// ==================================================
// Translation of all fields
// ==================================================

const unique f_6: Field NormalField int;
axiom !IsPredicateField(f_6);
axiom !IsWandField(f_6);
const unique next: Field NormalField Ref;
axiom !IsPredicateField(next);
axiom !IsWandField(next);

// ==================================================
// Translation of function length
// ==================================================

// Uninterpreted function definitions
function length(Heap: HeapType, x_1: Ref): int;
function length'(Heap: HeapType, x_1: Ref): int;
axiom (forall Heap: HeapType, x_1: Ref ::
  { length(Heap, x_1) }
  length(Heap, x_1) == length'(Heap, x_1) && dummyFunction(length#triggerStateless(x_1))
);
axiom (forall Heap: HeapType, x_1: Ref ::
  { length'(Heap, x_1) }
  dummyFunction(length#triggerStateless(x_1))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, x_1: Ref ::
  { state(Heap, Mask), length(Heap, x_1) } { state(Heap, Mask), length#triggerStateless(x_1), list#trigger(Heap, list(x_1)) }
  state(Heap, Mask) && AssumeFunctionsAbove < 0 ==> length(Heap, x_1) == 1 + (if Heap[x_1, next] != null then length'(Heap, Heap[x_1, next]) else 0)
);

// Framing axioms
function length#frame(frame: FrameType, x_1: Ref): int;
axiom (forall Heap: HeapType, Mask: MaskType, x_1: Ref ::
  { state(Heap, Mask), length'(Heap, x_1) } { state(Heap, Mask), length#triggerStateless(x_1), list#trigger(Heap, list(x_1)) }
  state(Heap, Mask) ==> length'(Heap, x_1) == length#frame(Heap[null, list(x_1)], x_1)
);

// Trigger function (controlling recursive postconditions)
function length#trigger(frame: FrameType, x_1: Ref): bool;

// State-independent trigger function
function length#triggerStateless(x_1: Ref): int;

// Check contract well-formedness and postcondition
procedure length#definedness(x_1: Ref) returns (Result: int)
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
    assume Heap[x_1, $allocated];
    assume AssumeFunctionsAbove == 0;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, list(x_1)] := Mask[null, list(x_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Check definedness of function body
    
    // -- Check definedness of 1 + (unfolding acc(list(x), write) in (x.next != null ? length(x.next) : 0))
      UnfoldingHeap := Heap;
      UnfoldingMask := Mask;
      assume list#trigger(UnfoldingHeap, list(x_1));
      assume UnfoldingHeap[null, list(x_1)] == CombineFrames(FrameFragment(UnfoldingHeap[x_1, f_6]), CombineFrames(FrameFragment(UnfoldingHeap[x_1, next]), FrameFragment((if UnfoldingHeap[x_1, next] != null then UnfoldingHeap[null, list(UnfoldingHeap[x_1, next])] else EmptyFrame))));
      // Phase 1: pure assertions and fixed permissions
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access list(x). (predicate_exhale.vpr@15.1) [77]"}
          perm <= UnfoldingMask[null, list(x_1)];
      }
      UnfoldingMask[null, list(x_1)] := UnfoldingMask[null, list(x_1)] - perm;
      perm := FullPerm;
      assume x_1 != null;
      UnfoldingMask[x_1, f_6] := UnfoldingMask[x_1, f_6] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      perm := FullPerm;
      assume x_1 != null;
      UnfoldingMask[x_1, next] := UnfoldingMask[x_1, next] + perm;
      assume state(UnfoldingHeap, UnfoldingMask);
      if (UnfoldingHeap[x_1, next] != null) {
        perm := FullPerm;
        UnfoldingMask[null, list(UnfoldingHeap[x_1, next])] := UnfoldingMask[null, list(UnfoldingHeap[x_1, next])] + perm;
        
        // -- Extra unfolding of predicate
          assume InsidePredicate(list(x_1), UnfoldingHeap[null, list(x_1)], list(UnfoldingHeap[x_1, next]), UnfoldingHeap[null, list(UnfoldingHeap[x_1, next])]);
        assume state(UnfoldingHeap, UnfoldingMask);
      }
      assume state(UnfoldingHeap, UnfoldingMask);
      assert {:msg "  Function might not be well-formed. There might be insufficient permission to access x.next. (predicate_exhale.vpr@15.1) [78]"}
        HasDirectPerm(UnfoldingMask, x_1, next);
      if (UnfoldingHeap[x_1, next] != null) {
        assert {:msg "  Function might not be well-formed. There might be insufficient permission to access x.next. (predicate_exhale.vpr@15.1) [79]"}
          HasDirectPerm(UnfoldingMask, x_1, next);
        if (*) {
          // Exhale precondition of function application
          // Phase 1: pure assertions and fixed permissions
          perm := NoPerm;
          perm := perm + FullPerm;
          if (perm != NoPerm) {
            assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access list(x.next). (predicate_exhale.vpr@18.48) [80]"}
              perm <= UnfoldingMask[null, list(UnfoldingHeap[x_1, next])];
          }
          UnfoldingMask[null, list(UnfoldingHeap[x_1, next])] := UnfoldingMask[null, list(UnfoldingHeap[x_1, next])] - perm;
          // Finish exhale
          havoc ExhaleHeap;
          assume IdenticalOnKnownLocations(UnfoldingHeap, ExhaleHeap, UnfoldingMask);
          UnfoldingHeap := ExhaleHeap;
          // Stop execution
          assume false;
        } else {
          // Enable postcondition for recursive call
          assume length#trigger(UnfoldingHeap[null, list(UnfoldingHeap[x_1, next])], UnfoldingHeap[x_1, next]);
        }
      }
      
      // -- Free assumptions
        Heap[null, list#sm(x_1)][x_1, f_6] := true;
        Heap[null, list#sm(x_1)][x_1, next] := true;
        if (Heap[x_1, next] != null) {
          havoc newPMask;
          assume (forall <A, B> o_2: Ref, f_7: (Field A B) ::
            { newPMask[o_2, f_7] }
            Heap[null, list#sm(x_1)][o_2, f_7] || Heap[null, list#sm(Heap[x_1, next])][o_2, f_7] ==> newPMask[o_2, f_7]
          );
          Heap[null, list#sm(x_1)] := newPMask;
        }
        assume state(Heap, Mask);
      
      // -- Free assumptions
        Heap[null, list#sm(x_1)][x_1, f_6] := true;
        Heap[null, list#sm(x_1)][x_1, next] := true;
        if (Heap[x_1, next] != null) {
          havoc newPMask;
          assume (forall <A, B> o_3: Ref, f_8: (Field A B) ::
            { newPMask[o_3, f_8] }
            Heap[null, list#sm(x_1)][o_3, f_8] || Heap[null, list#sm(Heap[x_1, next])][o_3, f_8] ==> newPMask[o_3, f_8]
          );
          Heap[null, list#sm(x_1)] := newPMask;
        }
        assume state(Heap, Mask);
      assume state(Heap, Mask);
  
  // -- Translate function body
    Result := 1 + (if Heap[x_1, next] != null then length(Heap, Heap[x_1, next]) else 0);
}

// ==================================================
// Translation of predicate list
// ==================================================

type PredicateType_list;
function list(x_1: Ref): Field PredicateType_list FrameType;
function list#sm(x_1: Ref): Field PredicateType_list PMaskType;
axiom (forall x_1: Ref ::
  { PredicateMaskField(list(x_1)) }
  PredicateMaskField(list(x_1)) == list#sm(x_1)
);
axiom (forall x_1: Ref ::
  { list(x_1) }
  IsPredicateField(list(x_1))
);
axiom (forall x_1: Ref ::
  { list(x_1) }
  getPredicateId(list(x_1)) == 0
);
function list#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function list#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall x_1: Ref, x2: Ref ::
  { list(x_1), list(x2) }
  list(x_1) == list(x2) ==> x_1 == x2
);
axiom (forall x_1: Ref, x2: Ref ::
  { list#sm(x_1), list#sm(x2) }
  list#sm(x_1) == list#sm(x2) ==> x_1 == x2
);

axiom (forall Heap: HeapType, x_1: Ref ::
  { list#trigger(Heap, list(x_1)) }
  list#everUsed(list(x_1))
);

// ==================================================
// Translation of method test1
// ==================================================

procedure test1(x_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var newVersion: FrameType;
  var freshVersion: FrameType;
  var newPMask: PMaskType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[x_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, list(x_1)] := Mask[null, list(x_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: inhale length(x) == 7 -- predicate_exhale.vpr@28.3
    
    // -- Check definedness of length(x) == 7
      if (*) {
        // Exhale precondition of function application
        // Phase 1: pure assertions and fixed permissions
        perm := NoPerm;
        perm := perm + FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access list(x). (predicate_exhale.vpr@28.10) [81]"}
            perm <= Mask[null, list(x_1)];
        }
        Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume length(Heap, x_1) == 7;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(list(x), write) -- predicate_exhale.vpr@30.3
    assume list#trigger(Heap, list(x_1));
    assume Heap[null, list(x_1)] == CombineFrames(FrameFragment(Heap[x_1, f_6]), CombineFrames(FrameFragment(Heap[x_1, next]), FrameFragment((if Heap[x_1, next] != null then Heap[null, list(Heap[x_1, next])] else EmptyFrame))));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding list(x) might fail. There might be insufficient permission to access list(x). (predicate_exhale.vpr@30.3) [83]"}
        perm <= Mask[null, list(x_1)];
    }
    Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, list(x_1))) {
        havoc newVersion;
        Heap[null, list(x_1)] := newVersion;
      }
    perm := FullPerm;
    assume x_1 != null;
    Mask[x_1, f_6] := Mask[x_1, f_6] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    assume x_1 != null;
    Mask[x_1, next] := Mask[x_1, next] + perm;
    assume state(Heap, Mask);
    if (Heap[x_1, next] != null) {
      perm := FullPerm;
      Mask[null, list(Heap[x_1, next])] := Mask[null, list(Heap[x_1, next])] + perm;
      
      // -- Extra unfolding of predicate
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale x.next != null && x.f == 5 -- predicate_exhale.vpr@31.3
    
    // -- Check definedness of x.next != null
      assert {:msg "  Inhale might fail. There might be insufficient permission to access x.next. (predicate_exhale.vpr@31.3) [84]"}
        HasDirectPerm(Mask, x_1, next);
      assume state(Heap, Mask);
    assume Heap[x_1, next] != null;
    assume state(Heap, Mask);
    
    // -- Check definedness of x.f == 5
      assert {:msg "  Inhale might fail. There might be insufficient permission to access x.f. (predicate_exhale.vpr@31.3) [85]"}
        HasDirectPerm(Mask, x_1, f_6);
      assume state(Heap, Mask);
    assume Heap[x_1, f_6] == 5;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(list(x), write) -- predicate_exhale.vpr@32.3
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding list(x) might fail. There might be insufficient permission to access x.f. (predicate_exhale.vpr@32.3) [87]"}
        perm <= Mask[x_1, f_6];
    }
    Mask[x_1, f_6] := Mask[x_1, f_6] - perm;
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding list(x) might fail. There might be insufficient permission to access x.next. (predicate_exhale.vpr@32.3) [89]"}
        perm <= Mask[x_1, next];
    }
    Mask[x_1, next] := Mask[x_1, next] - perm;
    if (Heap[x_1, next] != null) {
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding list(x) might fail. There might be insufficient permission to access list(x.next). (predicate_exhale.vpr@32.3) [91]"}
          perm <= Mask[null, list(Heap[x_1, next])];
      }
      Mask[null, list(Heap[x_1, next])] := Mask[null, list(Heap[x_1, next])] - perm;
      
      // -- Record predicate instance information
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
    }
    // Phase 2: abstract read permissions (and scaled abstract read permissions)
    if (Heap[x_1, next] != null) {
      
      // -- Record predicate instance information
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
    }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    if (Heap[x_1, next] != null) {
      
      // -- Record predicate instance information
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
    }
    perm := FullPerm;
    Mask[null, list(x_1)] := Mask[null, list(x_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume list#trigger(Heap, list(x_1));
    assume Heap[null, list(x_1)] == CombineFrames(FrameFragment(Heap[x_1, f_6]), CombineFrames(FrameFragment(Heap[x_1, next]), FrameFragment((if Heap[x_1, next] != null then Heap[null, list(Heap[x_1, next])] else EmptyFrame))));
    if (!HasDirectPerm(Mask, null, list(x_1))) {
      Heap[null, list#sm(x_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, list(x_1)] := freshVersion;
    }
    Heap[null, list#sm(x_1)][x_1, f_6] := true;
    Heap[null, list#sm(x_1)][x_1, next] := true;
    if (Heap[x_1, next] != null) {
      havoc newPMask;
      assume (forall <A, B> o_4: Ref, f_9: (Field A B) ::
        { newPMask[o_4, f_9] }
        Heap[null, list#sm(x_1)][o_4, f_9] || Heap[null, list#sm(Heap[x_1, next])][o_4, f_9] ==> newPMask[o_4, f_9]
      );
      Heap[null, list#sm(x_1)] := newPMask;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert length(x) == 7 -- predicate_exhale.vpr@34.3
    
    // -- Check definedness of length(x) == 7
      if (*) {
        // Exhale precondition of function application
        // Phase 1: pure assertions and fixed permissions
        perm := NoPerm;
        perm := perm + FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access list(x). (predicate_exhale.vpr@34.10) [92]"}
            perm <= Mask[null, list(x_1)];
        }
        Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion length(x) == 7 might not hold. (predicate_exhale.vpr@34.3) [93]"}
      length(Heap, x_1) == 7;
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(list(x), write) -- predicate_exhale.vpr@36.3
    assume list#trigger(Heap, list(x_1));
    assume Heap[null, list(x_1)] == CombineFrames(FrameFragment(Heap[x_1, f_6]), CombineFrames(FrameFragment(Heap[x_1, next]), FrameFragment((if Heap[x_1, next] != null then Heap[null, list(Heap[x_1, next])] else EmptyFrame))));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding list(x) might fail. There might be insufficient permission to access list(x). (predicate_exhale.vpr@36.3) [95]"}
        perm <= Mask[null, list(x_1)];
    }
    Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, list(x_1))) {
        havoc newVersion;
        Heap[null, list(x_1)] := newVersion;
      }
    perm := FullPerm;
    assume x_1 != null;
    Mask[x_1, f_6] := Mask[x_1, f_6] + perm;
    assume state(Heap, Mask);
    perm := FullPerm;
    assume x_1 != null;
    Mask[x_1, next] := Mask[x_1, next] + perm;
    assume state(Heap, Mask);
    if (Heap[x_1, next] != null) {
      perm := FullPerm;
      Mask[null, list(Heap[x_1, next])] := Mask[null, list(Heap[x_1, next])] + perm;
      
      // -- Extra unfolding of predicate
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
      assume state(Heap, Mask);
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert x.f == 5 -- predicate_exhale.vpr@37.3
    
    // -- Check definedness of x.f == 5
      assert {:msg "  Assert might fail. There might be insufficient permission to access x.f. (predicate_exhale.vpr@37.3) [96]"}
        HasDirectPerm(Mask, x_1, f_6);
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion x.f == 5 might not hold. (predicate_exhale.vpr@37.3) [97]"}
      Heap[x_1, f_6] == 5;
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(list(x), write) -- predicate_exhale.vpr@38.3
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding list(x) might fail. There might be insufficient permission to access x.f. (predicate_exhale.vpr@38.3) [99]"}
        perm <= Mask[x_1, f_6];
    }
    Mask[x_1, f_6] := Mask[x_1, f_6] - perm;
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding list(x) might fail. There might be insufficient permission to access x.next. (predicate_exhale.vpr@38.3) [101]"}
        perm <= Mask[x_1, next];
    }
    Mask[x_1, next] := Mask[x_1, next] - perm;
    if (Heap[x_1, next] != null) {
      perm := NoPerm;
      perm := perm + FullPerm;
      if (perm != NoPerm) {
        assert {:msg "  Folding list(x) might fail. There might be insufficient permission to access list(x.next). (predicate_exhale.vpr@38.3) [103]"}
          perm <= Mask[null, list(Heap[x_1, next])];
      }
      Mask[null, list(Heap[x_1, next])] := Mask[null, list(Heap[x_1, next])] - perm;
      
      // -- Record predicate instance information
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
    }
    // Phase 2: abstract read permissions (and scaled abstract read permissions)
    if (Heap[x_1, next] != null) {
      
      // -- Record predicate instance information
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
    }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    if (Heap[x_1, next] != null) {
      
      // -- Record predicate instance information
        assume InsidePredicate(list(x_1), Heap[null, list(x_1)], list(Heap[x_1, next]), Heap[null, list(Heap[x_1, next])]);
    }
    perm := FullPerm;
    Mask[null, list(x_1)] := Mask[null, list(x_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume list#trigger(Heap, list(x_1));
    assume Heap[null, list(x_1)] == CombineFrames(FrameFragment(Heap[x_1, f_6]), CombineFrames(FrameFragment(Heap[x_1, next]), FrameFragment((if Heap[x_1, next] != null then Heap[null, list(Heap[x_1, next])] else EmptyFrame))));
    if (!HasDirectPerm(Mask, null, list(x_1))) {
      Heap[null, list#sm(x_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, list(x_1)] := freshVersion;
    }
    Heap[null, list#sm(x_1)][x_1, f_6] := true;
    Heap[null, list#sm(x_1)][x_1, next] := true;
    if (Heap[x_1, next] != null) {
      havoc newPMask;
      assume (forall <A, B> o_5: Ref, f_10: (Field A B) ::
        { newPMask[o_5, f_10] }
        Heap[null, list#sm(x_1)][o_5, f_10] || Heap[null, list#sm(Heap[x_1, next])][o_5, f_10] ==> newPMask[o_5, f_10]
      );
      Heap[null, list#sm(x_1)] := newPMask;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert length(x) == 7 -- predicate_exhale.vpr@40.3
    
    // -- Check definedness of length(x) == 7
      if (*) {
        // Exhale precondition of function application
        // Phase 1: pure assertions and fixed permissions
        perm := NoPerm;
        perm := perm + FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access list(x). (predicate_exhale.vpr@40.10) [104]"}
            perm <= Mask[null, list(x_1)];
        }
        Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion length(x) == 7 might not hold. (predicate_exhale.vpr@40.3) [105]"}
      length(Heap, x_1) == 7;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(list(x), write) -- predicate_exhale.vpr@42.3
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Exhale might fail. There might be insufficient permission to access list(x). (predicate_exhale.vpr@42.3) [107]"}
        perm <= Mask[null, list(x_1)];
    }
    Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(list(x), write) -- predicate_exhale.vpr@43.3
    perm := FullPerm;
    Mask[null, list(x_1)] := Mask[null, list(x_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert length(x) == 7 -- predicate_exhale.vpr@45.3
    
    // -- Check definedness of length(x) == 7
      if (*) {
        // Exhale precondition of function application
        // Phase 1: pure assertions and fixed permissions
        perm := NoPerm;
        perm := perm + FullPerm;
        if (perm != NoPerm) {
          assert {:msg "  Precondition of function length might not hold. There might be insufficient permission to access list(x). (predicate_exhale.vpr@45.10) [108]"}
            perm <= Mask[null, list(x_1)];
        }
        Mask[null, list(x_1)] := Mask[null, list(x_1)] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    // CHECK-L: Assert might fail. Assertion length(x) == 7 might not hold. (predicate_exhale.vpr@45.3) [109]
    assert {:msg "Assert might fail. Assertion length(x) == 7 might not hold. (predicate_exhale.vpr@45.3) [109]"}
      length(Heap, x_1) == 7;
    assume state(Heap, Mask);
}