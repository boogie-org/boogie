// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff NoErrors.expect "%t"
// ----------- BEGIN PRELUDE


type elements;

type name;

const $CALL: name;

const $REQ: name;

const $ENS: name;

const $PACK: name;

const $UNPACK: name;

const $HEAD: name;

const $THROW: name;

var $RefHeap: [ref, name]ref;

var $IntHeap: [ref, name]int;

var $RealHeap: [ref, name]real;

var $BoolHeap: [ref, name]bool;

var $ArrayHeap: [ref, name]elements;

const $allocated: name;

const $elements: name;

function $ArrayLength(ref) returns (int);

function $RefArrayGet(elements, int) returns (ref);

function $RefArraySet(elements, int, ref) returns (elements);

function $IntArrayGet(elements, int) returns (value: int);

function $IntArraySet(elements, int, int) returns (elements);

function $RealArrayGet(elements, int) returns (value: real);

function $RealArraySet(elements, int, real) returns (elements);

function $BoolArrayGet(elements, int) returns (value: bool);

function $BoolArraySet(elements, int, bool) returns (elements);

function $ArrayArrayGet(elements, int) returns (value: elements);

function $ArrayArraySet(elements, int, elements) returns (elements);

axiom (forall A: elements, i: int, x: ref :: $RefArrayGet($RefArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: ref :: i != j ==> $RefArrayGet($RefArraySet(A, i, x), j) == $RefArrayGet(A, j));

axiom (forall A: elements, i: int, x: int :: $IntArrayGet($IntArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: int :: i != j ==> $IntArrayGet($IntArraySet(A, i, x), j) == $IntArrayGet(A, j));

axiom (forall A: elements, i: int, x: real :: $RealArrayGet($RealArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: real :: i != j ==> $RealArrayGet($RealArraySet(A, i, x), j) == $RealArrayGet(A, j));

axiom (forall A: elements, i: int, x: bool :: $BoolArrayGet($BoolArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: bool :: i != j ==> $BoolArrayGet($BoolArraySet(A, i, x), j) == $BoolArrayGet(A, j));

axiom (forall A: elements, i: int, x: elements :: $ArrayArrayGet($ArrayArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: elements :: i != j ==> $ArrayArrayGet($ArrayArraySet(A, i, x), j) == $ArrayArrayGet(A, j));

axiom (forall a: ref :: 0 <= $ArrayLength(a));

function $typeof(ref) returns (name);

function $BoolIs(bool, name) returns (bool);

function $RealIs(real, name) returns (bool);

function $IntIs(int, name) returns (bool);

const System.Int16: name;

const System.Int32: name;

const System.Int64: name;

const System.Int16.MinValue: int;

const System.Int16.MaxValue: int;

const System.Int32.MinValue: int;

const System.Int32.MaxValue: int;

const System.Int64.MinValue: int;

const System.Int64.MaxValue: int;

axiom System.Int64.MinValue < System.Int32.MinValue;

axiom System.Int32.MinValue < System.Int16.MinValue;

axiom System.Int16.MinValue < System.Int16.MaxValue;

axiom System.Int16.MaxValue < System.Int32.MaxValue;

axiom System.Int32.MaxValue < System.Int64.MaxValue;

axiom (forall i: int :: $IntIs(i, System.Int16) <==> System.Int16.MinValue <= i && i <= System.Int16.MaxValue);

axiom (forall i: int :: $IntIs(i, System.Int32) <==> System.Int32.MinValue <= i && i <= System.Int32.MaxValue);

axiom (forall i: int :: $IntIs(i, System.Int64) <==> System.Int64.MinValue <= i && i <= System.Int64.MaxValue);

function $RefIs(ref, name) returns (bool);

axiom (forall o: ref, T: name :: $RefIs(o, T) <==> o == null || $typeof(o) <: T);

axiom (forall o: ref, T: name :: $RefIs(o, $NotNull(T)) <==> o != null && $RefIs(o, T));

axiom (forall a: ref, T: name, i: int, $ArrayHeap: [ref, name]elements :: $RefIs(a, $IntArray(T)) && a != null ==> $IntIs($IntArrayGet($ArrayHeap[a, $elements], i), T));

axiom (forall a: ref, T: name, i: int, $ArrayHeap: [ref, name]elements  :: $RefIs(a, $RealArray(T)) && a != null ==> $RealIs($RealArrayGet($ArrayHeap[a, $elements], i), T));

axiom (forall a: ref, T: name, i: int, $ArrayHeap: [ref, name]elements  :: $RefIs(a, $BoolArray(T)) && a != null ==> $BoolIs($BoolArrayGet($ArrayHeap[a, $elements], i), T));

axiom (forall a: ref, T: name, i: int, $ArrayHeap: [ref, name]elements  :: $RefIs(a, $RefArray(T)) && a != null ==> $RefIs($RefArrayGet($ArrayHeap[a, $elements], i), T));

function $NotNull(name) returns (name);

function $IntArray(name) returns (name);

function $BoolArray(name) returns (name);

function $RealArray(name) returns (name);

function $RefArray(name) returns (name);
// ----------- END PRELUDE
const Bag.a: name;

const Bag.n: name;

const Bag: name;





procedure Bag..ctor$(this: ref, initialElements$in: ref);






procedure System.Object..ctor(this: ref);



procedure System.Array.CopyTo$System.Array$System.Int32(this: ref, array$in: ref, index$in: int);



procedure Bag..ctor$$System.Int32$System.Int32(this: ref, initialElements$in: ref, start$in: int, howMany$in: int);
  requires 0 <= howMany$in;
  requires start$in + howMany$in <= $ArrayLength(initialElements$in);
  modifies $IntHeap, $RefHeap;



implementation Bag..ctor$$System.Int32$System.Int32(this: ref, initialElements$in: ref, start$in: int, howMany$in: int)
{
  var initialElements: ref, start: int, howMany: int, stack0i: int, stack0o: ref, stack1i: int, stack2i: int;

  entry:
    assume $RefIs(this, $NotNull(Bag));
    initialElements := initialElements$in;
    assume $RefIs(initialElements, $NotNull($IntArray(System.Int32)));
    start := start$in;
    assume $IntIs(start, System.Int32);
    howMany := howMany$in;
    assume $IntIs(howMany, System.Int32);
    goto block165;

  block165:
    call System.Object..ctor(this);
    $IntHeap[this, Bag.n] := howMany;
    stack0i := howMany;
    havoc stack0o;
    assume $BoolHeap[stack0o, $allocated] == true && $ArrayLength(stack0o) == stack0i;
    $RefHeap[this, Bag.a] := stack0o;
    stack0o := $RefHeap[this, Bag.a];
    stack1i := 0;
    stack2i := start + howMany;
    call System.Array.Copy$System.Array$System.Int32$System.Array$System.Int32$System.Int32(initialElements, start, stack0o, stack1i, stack2i);
    assert this != null;
    assert 0 <= $IntHeap[this, Bag.n] && $IntHeap[this, Bag.n] <= $ArrayLength($RefHeap[this, Bag.a]);
    return;
}



procedure System.Array.Copy$System.Array$System.Int32$System.Array$System.Int32$System.Int32(sourceArray$in: ref, sourceIndex$in: int, destinationArray$in: ref, destinationIndex$in: int, length$in: int);



procedure Bag.Add$System.Int32(this: ref, x$in: int);
  modifies $ArrayHeap, $IntHeap;



implementation Bag.Add$System.Int32(this: ref, x$in: int)
{
  var x: int, stack0i: int, stack1o: ref, stack1i: int, stack0b: bool, stack0o: ref, stack2i: int, b: ref;

  entry:
    assume $RefIs(this, $NotNull(Bag));
    x := x$in;
    assume $IntIs(x, System.Int32);
    assert this != null;
    assume 0 <= $IntHeap[this, Bag.n] && $IntHeap[this, Bag.n] <= $ArrayLength($RefHeap[this, Bag.a]);
    goto block205;

  block205:
    stack0i := $IntHeap[this, Bag.n];
    stack1o := $RefHeap[this, Bag.a];
    stack1i := $ArrayLength(stack1o);
    stack1i := stack1i;
    stack0b := stack0i != stack1i;
    goto trueblock208, falseblock206;

  trueblock208:
    assume stack0b == true;
assume false;
//    goto block208;
return;

  falseblock206:
    assume stack0b == false;
    goto block206;

  block206:
//    assert label-([$PACK@0:3:4425:0], $IntHeap[this, Bag.n] <= 2 * $ArrayLength($RefHeap[this, Bag.a]));
    stack0i := 2;
    stack1o := $RefHeap[this, Bag.a];
    stack1i := $ArrayLength(stack1o);
    stack1i := stack1i;
    stack0i := stack0i * stack1i;
    stack0i := stack0i;
    assert $IntHeap[this, Bag.n] <= stack0i;
//    havoc b;
//    assume $BoolHeap[b, $allocated] == true && $ArrayLength(b) == stack0i;
//    assert label-([$PACK@0:3:4427:0], $IntHeap[this, Bag.n] <= $ArrayLength(b));
//    stack0o := $RefHeap[this, Bag.a];
//    stack1i := 0;
//    call [$CALL@0:7:39:0] System.Array.CopyTo$System.Array$System.Int32(stack0o, b, stack1i);
//    $RefHeap[this, Bag.a] := b;
//    assert label-([$PACK@0:3:4428:0], $IntHeap[this, Bag.n] <= $ArrayLength($RefHeap[this, Bag.a]));
//    goto block208;
    return;

  block208:
    stack0o := $RefHeap[this, Bag.a];
    stack1i := $IntHeap[this, Bag.n];
    $ArrayHeap[stack0o, $elements] := $IntArraySet($ArrayHeap[stack0o, $elements], stack1i, x);
    stack0o := this;
    stack1o := stack0o;
    stack1i := $IntHeap[stack1o, Bag.n];
    stack2i := 1;
    stack1i := stack1i + stack2i;
    $IntHeap[stack0o, Bag.n] := stack1i;
    assert this != null;
    assert 0 <= $IntHeap[this, Bag.n];
    assert $IntHeap[this, Bag.n] <= $ArrayLength($RefHeap[this, Bag.a]);
    return;

}



procedure Bag.ExtractMin(this: ref) returns ($result: int);
  modifies $IntHeap, $ArrayHeap;



implementation Bag.ExtractMin(this: ref) returns ($result: int)
{
  var m: int, mindex: int, i: int, stack0i: int, stack0b: bool, stack0o: ref, stack1o: ref, stack1i: int, stack2i: int, CS$00000003$00000000: int;

  entry:
    assume $RefIs(this, $NotNull(Bag));
    assert this != null;
    assume 0 <= $IntHeap[this, Bag.n] && $IntHeap[this, Bag.n] <= $ArrayLength($RefHeap[this, Bag.a]);
    goto block282;

  block282:
    m := 2147483647;
    mindex := 0;
    i := 1;
    goto block286;

  block285:
    stack0i := 1;
    stack0i := i + stack0i;
    i := stack0i;
    goto block286;

  block286:
    stack0i := $IntHeap[this, Bag.n];
    stack0b := i <= stack0i;
    goto trueblock283, falseblock287;

  trueblock283:
    assume stack0b == true;
    goto block283;

  falseblock287:
    assume stack0b == false;
    goto block287;

  block283:
    stack0o := $RefHeap[this, Bag.a];
    stack0i := $IntArrayGet($ArrayHeap[stack0o, $elements], i);
    stack0b := stack0i >= m;
    goto trueblock285, falseblock284;

  block287:
    stack0o := this;
    stack1o := stack0o;
    stack1i := $IntHeap[stack1o, Bag.n];
    stack2i := 1;
    stack1i := stack1i - stack2i;
    $IntHeap[stack0o, Bag.n] := stack1i;
    stack0o := $RefHeap[this, Bag.a];
    stack1o := $RefHeap[this, Bag.a];
    stack2i := $IntHeap[this, Bag.n];
    stack1i := $IntArrayGet($ArrayHeap[stack1o, $elements], stack2i);
    $ArrayHeap[stack0o, $elements] := $IntArraySet($ArrayHeap[stack0o, $elements], mindex, stack1i);
    CS$00000003$00000000 := m;
    goto block289;

  trueblock285:
    assume stack0b == true;
    goto block285;

  falseblock284:
    assume stack0b == false;
    goto block284;

  block284:
    mindex := i;
    stack0o := $RefHeap[this, Bag.a];
    m := $IntArrayGet($ArrayHeap[stack0o, $elements], i);
    goto block285;

  block289:
    $result := CS$00000003$00000000;
    assert this != null;
    assert 0 <= $IntHeap[this, Bag.n] && $IntHeap[this, Bag.n] <= $ArrayLength($RefHeap[this, Bag.a]);
    return;
}

type ref;
const null : ref;
