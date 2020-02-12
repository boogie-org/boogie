// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
// Dafny program verifier version 0.92, Copyright (c) 2003-2008, Microsoft.
// Command Line Options: /trace /typeEncoding:arguments /print:test.bpl test.dfy

type ref;

const null: ref;

type Set T = [T]bool;
function Set#Empty<T>() returns (Set T);
function Set#Singleton<T>(T) returns (Set T);
function Set#UnionOne<T>(Set T, T) returns (Set T);
function Set#Union<T>(Set T, Set T) returns (Set T);
function Set#Intersection<T>(Set T, Set T) returns (Set T);
function Set#Difference<T>(Set T, Set T) returns (Set T);
function Set#Subset<T>(Set T, Set T) returns (bool);
function Set#Equal<T>(Set T, Set T) returns (bool);
function Set#Disjoint<T>(Set T, Set T) returns (bool);

type Seq _;
function Seq#Length<T>(Seq T) returns (int);
function Seq#Empty<T>() returns (Seq T);
function Seq#Singleton<T>(T) returns (Seq T);
function Seq#Build<T>(s: Seq T, index: int, val: T, newLength: int) returns (Seq T);
function Seq#Append<T>(Seq T, Seq T) returns (Seq T);
function Seq#Index<T>(Seq T, int) returns (T);
function Seq#Contains<T>(Seq T, T) returns (bool);
function Seq#Equal<T>(Seq T, Seq T) returns (bool);
function Seq#SameUntil<T>(Seq T, Seq T, int) returns (bool);
function Seq#Take<T>(s:Seq T, howMany: int) returns (Seq T);
function Seq#Drop<T>(s:Seq T, howMany: int) returns (Seq T);

type Field _;
type HeapType = <alpha>[ref,Field alpha]alpha;
function $IsGoodHeap(HeapType) returns (bool);
var $Heap: HeapType where $IsGoodHeap($Heap);
const alloc: Field bool;
function $HeapSucc(HeapType, HeapType) returns (bool);

const unique Node.list: Field (Seq ref);
const unique Node.footprint: Field [ref]bool;
const unique Node.data: Field ref;
const unique Node.next: Field ref;
function Node.Valid($heap: HeapType, this: ref) returns (bool);




axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);

axiom (forall $Heap: HeapType, this: ref :: { Node.Valid($Heap, this) } this != null && $IsGoodHeap($Heap) ==> Node.Valid($Heap, this) == ($Heap[this, Node.footprint][this] && !$Heap[this, Node.footprint][null] && (forall n: ref :: $Heap[this, Node.footprint][n] ==> $Heap[n, Node.footprint][n] && !$Heap[n, Node.footprint][null] && Set#Subset($Heap[n, Node.footprint], $Heap[this, Node.footprint]) && ($Heap[n, Node.next] == null ==> Seq#Equal($Heap[n, Node.list], Seq#Build(Seq#Empty(), 0, $Heap[n, Node.data], 1))) && ($Heap[n, Node.next] != null ==> $Heap[n, Node.footprint][$Heap[n, Node.next]] && Set#Subset($Heap[$Heap[n, Node.next], Node.footprint], $Heap[n, Node.footprint]) && !$Heap[$Heap[n, Node.next], Node.footprint][n] && Seq#Equal($Heap[n, Node.list], Seq#Append(Seq#Build(Seq#Empty(), 0, $Heap[n, Node.data], 1), $Heap[$Heap[n, Node.next], Node.list])))) && ($Heap[this, Node.next] != null ==> Node.Valid($Heap, $Heap[this, Node.next]))));




procedure Node.ReverseInPlace(this: ref where this != null && $Heap[this, alloc]) returns (reverse: ref where reverse == null || $Heap[reverse, alloc]);
  // user-defined preconditions
  free requires Node.Valid($Heap, this);
  requires $Heap[this, Node.footprint][this];
  requires !$Heap[this, Node.footprint][null];
  requires $Heap[this, Node.next] != null ==> Node.Valid($Heap, $Heap[this, Node.next]);
  modifies $Heap;
  // frame condition
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$Node.Valid(this: ref where this != null && $Heap[this, alloc]);





implementation Node.ReverseInPlace(this: ref) returns (reverse: ref)
{
  var current: ref where current == null || $Heap[current, alloc], $PreLoopHeap0: HeapType, nx: ref where nx == null || $Heap[nx, alloc];

    // ----- var-declaration statement ----- test.dfy(28,9)
    current := $Heap[this, Node.next];


    // ----- assignment statement ----- test.dfy(29,13)
    reverse := this;
    // ----- assignment statement ----- test.dfy(30,18)
    $Heap[reverse, Node.next] := null;
    assume $IsGoodHeap($Heap);



    // ----- assignment statement ----- test.dfy(31,23)
    $Heap[reverse, Node.footprint] := // Set#UnionOne(Set#Empty(), reverse);
                                      Set#Singleton(reverse);

    assert current == null;
}


