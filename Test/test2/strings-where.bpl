// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type elements;

type struct;

var $Heap: [ref,name]any where IsHeap($Heap);
function cast<S,T>(S) returns (T);
function IsHeap(h: [ref,name]any) returns (bool);

const unique $allocated: name;

const unique $elements: name;

const unique $inv: name;

const unique $writable: name;

const unique $sharingMode: name;

const unique $SharingMode_Unshared: name;

const unique $SharingMode_LockProtected: name;

function ClassRepr(class: name) returns (ref);

axiom (forall c0: name, c1: name :: c0 != c1 ==> ClassRepr(c0) != ClassRepr(c1));

axiom (forall T: name :: !($typeof(ClassRepr(T)) <: System.Object));

axiom (forall T: name :: ClassRepr(T) != null);

axiom (forall T: name, h: [ref,name]any :: { h[ClassRepr(T), $writable] } IsHeap(h) ==> cast(h[ClassRepr(T), $writable]):bool);

function IsDirectlyModifiableField(f: name) returns (bool);

axiom !IsDirectlyModifiableField($allocated);

axiom IsDirectlyModifiableField($elements);

axiom !IsDirectlyModifiableField($inv);

axiom !IsDirectlyModifiableField($writable);

function IsStaticField(f: name) returns (bool);

axiom !IsStaticField($allocated);

axiom !IsStaticField($elements);

axiom !IsStaticField($inv);

axiom !IsStaticField($writable);

function ValueArrayGet(elements, int) returns (any);

function ValueArraySet(elements, int, any) returns (elements);

function RefArrayGet(elements, int) returns (ref);

function RefArraySet(elements, int, ref) returns (elements);

axiom (forall A: elements, i: int, x: any :: ValueArrayGet(ValueArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: any :: i != j ==> ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j));

axiom (forall A: elements, i: int, x: ref :: RefArrayGet(RefArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: ref :: i != j ==> RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j));

function ArrayIndex(arr: ref, dim: int, indexAtDim: int, remainingIndexContribution: int) returns (int);

axiom (forall a: ref, d: int, x: int, y: int, x': int, y': int :: ArrayIndex(a, d, x, y) == ArrayIndex(a, d, x', y') ==> x == x' && y == y');

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,name]any :: $typeof(a) <: RefArray(T, r) ==> $Is(RefArrayGet(cast(heap[a, $elements]):elements, i), T));

function $Rank(ref) returns (int);

axiom (forall a: ref :: 1 <= $Rank(a));

axiom (forall a: ref, T: name, r: int :: { $Is(a, ValueArray(T, r)) } $Is(a, ValueArray(T, r)) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $Is(a, RefArray(T, r)) } $Is(a, RefArray(T, r)) ==> $Rank(a) == r);

function $Length(ref) returns (int);

axiom (forall a: ref :: { $Length(a) } 0 <= $Length(a));

function $DimLength(ref, int) returns (int);

axiom (forall a: ref, i: int :: 0 <= $DimLength(a, i));

axiom (forall a: ref :: $Rank(a) == 1 ==> $DimLength(a, 0) == $Length(a));

function $LBound(ref, int) returns (int);

function $UBound(ref, int) returns (int);

axiom (forall a: ref, i: int :: { $LBound(a, i) } $LBound(a, i) == 0);

axiom (forall a: ref, i: int :: { $UBound(a, i) } $UBound(a, i) == $DimLength(a, i) - 1);

const unique System.Array: name;

axiom $IsClass(System.Array);

axiom System.Array <: System.Object;

function $ElementType(name) returns (name);

function ValueArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { ValueArray(T, r) } ValueArray(T, r) <: System.Array);

function RefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { RefArray(T, r) } RefArray(T, r) <: System.Array);

axiom (forall T: name, U: name, r: int :: U <: T ==> RefArray(U, r) <: RefArray(T, r));

axiom (forall A: name, r: int :: $ElementType(ValueArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(RefArray(A, r)) == A);

axiom (forall A: name, r: int, T: name :: { T <: RefArray(A, r) } T <: RefArray(A, r) ==> T == RefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: ValueArray(A, r) } T <: ValueArray(A, r) ==> T == ValueArray(A, r));

axiom (forall A: name, r: int, T: name :: RefArray(A, r) <: T ==> System.Array <: T || (T == RefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: ValueArray(A, r) <: T ==> System.Array <: T || T == ValueArray(A, r));

function $ArrayPtr(elementType: name) returns (name);

function $StructGet(struct, name) returns (any);

function $StructSet(struct, name, any) returns (struct);

axiom (forall s: struct, f: name, x: any :: $StructGet($StructSet(s, f, x), f) == x);

axiom (forall s: struct, f: name, f': name, x: any :: f != f' ==> $StructGet($StructSet(s, f, x), f') == $StructGet(s, f'));

function ZeroInit(s: struct, typ: name) returns (bool);

function $typeof(ref) returns (name);

function Implements(class: name, interface: name) returns (bool);

axiom (forall T: name, J: name :: { Implements(T, J) } Implements(T, J) ==> T <: J);

function InterfaceExtends(subIntf: name, superIntf: name) returns (bool);

axiom (forall J: name, K: name :: { InterfaceExtends(J, K) } InterfaceExtends(J, K) ==> J <: K);

function $IsClass(name) returns (bool);

axiom (forall C: name :: { $IsClass(C) } $IsClass(C) ==> C <: C);

function AsDirectSubClass(sub: name, base: name) returns (sub': name);

function OneClassDown(sub: name, base: name) returns (directSub: name);

axiom (forall A: name, B: name, C: name :: { C <: AsDirectSubClass(B, A) } C <: AsDirectSubClass(B, A) ==> OneClassDown(C, A) == B);

function $IsInterface(name) returns (bool);

axiom (forall J: name :: { $IsInterface(J) } $IsInterface(J) ==> J <: System.Object);

function $IsValueType(name) returns (bool);

axiom (forall T: name :: $IsValueType(T) ==> (forall U: name :: T <: U ==> T == U) && (forall U: name :: U <: T ==> T == U));

const unique System.Object: name;

axiom $IsClass(System.Object);

function $IsTokenForType(struct, name) returns (bool);

function TypeObject(name) returns (ref);

const unique System.Type: name;

axiom System.Type <: System.Object;

axiom (forall T: name :: { TypeObject(T) } $IsNotNull(TypeObject(T), System.Type));

function $Is(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $Is(o, T) } $Is(o, T) <==> o == null || $typeof(o) <: T);

function $IsNotNull(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $IsNotNull(o, T) } $IsNotNull(o, T) <==> o != null && $Is(o, T));

function $As(ref, name) returns (ref);

axiom (forall o: ref, T: name :: $Is(o, T) ==> $As(o, T) == o);

axiom (forall o: ref, T: name :: !$Is(o, T) ==> $As(o, T) == null);

axiom (forall heap: [ref,name]any, o: ref, A: name, r: int :: $Is(o, RefArray(A, r)) ==> heap[o, $inv] == $typeof(o));

axiom (forall heap: [ref,name]any, o: ref, A: name, r: int :: $Is(o, ValueArray(A, r)) ==> heap[o, $inv] == $typeof(o));

function IsAllocated(h: [ref,name]any, o: any) returns (bool);

axiom (forall h: [ref,name]any, o: ref, f: name :: { IsAllocated(h, h[o, f]) } IsHeap(h) ==> IsAllocated(h, h[o, f]));

axiom (forall h: [ref,name]any, s: struct, f: name :: { IsAllocated(h, $StructGet(s, f)) } IsAllocated(h, s) ==> IsAllocated(h, $StructGet(s, f)));

axiom (forall h: [ref,name]any, e: elements, i: int :: { IsAllocated(h, RefArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, RefArrayGet(e, i)));

axiom (forall h: [ref,name]any, o: ref :: { h[o, $allocated] } IsAllocated(h, o) ==> cast(h[o, $allocated]):bool);

axiom (forall h: [ref,name]any, c: name :: { h[ClassRepr(c), $allocated] } IsHeap(h) ==> cast(h[ClassRepr(c), $allocated]):bool);

function DeclType(field: name) returns (class: name);

function AsNonNullRefField(field: name, T: name) returns (f: name);

function AsRefField(field: name, T: name) returns (f: name);

function AsRangeField(field: name, T: name) returns (f: name);

axiom (forall f: name, T: name :: { AsNonNullRefField(f, T) } AsNonNullRefField(f, T) == f ==> AsRefField(f, T) == f);

axiom (forall h: [ref,name]any, o: ref, f: name, T: name :: { h[o, AsRefField(f, T)] } IsHeap(h) ==> $Is(cast(h[o, AsRefField(f, T)]):ref, T));

axiom (forall h: [ref,name]any, o: ref, f: name, T: name :: { h[o, AsNonNullRefField(f, T)] } IsHeap(h) ==> cast(h[o, AsNonNullRefField(f, T)]):ref != null);

axiom (forall h: [ref,name]any, o: ref, f: name, T: name :: { h[o, AsRangeField(f, T)] } IsHeap(h) ==> InRange(cast(h[o, AsRangeField(f, T)]):int, T));

const unique System.String: name;

axiom (forall h: [ref,name]any, s: ref :: IsHeap(h) && $typeof(s) == System.String ==> h[s, $inv] == $typeof(s) && cast(h[s, $writable]):bool);

function AsOwnedField(f: name) returns (name);

axiom (forall h: [ref,name]any, o: ref, f: name :: { h[o, AsOwnedField(f)] } IsHeap(h) && cast(h[o, $inv]):name <: DeclType(AsOwnedField(f)) ==> cast(h[o, AsOwnedField(f)]):ref == null || $typeof(cast(h[o, AsOwnedField(f)]):ref) == System.String || !cast(h[cast(h[o, AsOwnedField(f)]):ref, $writable]):bool);

axiom (forall h: [ref,name]any, o: ref :: { h[o, $writable] } IsHeap(h) && !cast(h[o, $writable]):bool ==> cast(h[o, $inv]):name == $typeof(o));

function Box(any, ref) returns (ref);

function Unbox(ref) returns (any);

axiom (forall x: any, p: ref :: { Unbox(Box(x, p)) } Unbox(Box(x, p)) == x);

axiom (forall heap: [ref,name]any, x: any, p: ref :: { heap[Box(x, p), $inv] } IsHeap(heap) ==> heap[Box(x, p), $inv] == $typeof(Box(x, p)));

function UnboxedType(ref) returns (name);

function BoxTester(p: ref, typ: name) returns (ref);

axiom (forall p: ref, typ: name :: { BoxTester(p, typ) } UnboxedType(p) == typ <==> BoxTester(p, typ) != null);

const unique System.Int16: name;

axiom $IsValueType(System.Int16);

const unique System.Int32: name;

axiom $IsValueType(System.Int32);

const unique System.Int64: name;

axiom $IsValueType(System.Int64);

const unique System.Byte: name;

axiom $IsValueType(System.Byte);

const unique System.Int16.MinValue: int;

const unique System.Int16.MaxValue: int;

const unique System.Int32.MinValue: int;

const unique System.Int32.MaxValue: int;

const unique System.Int64.MinValue: int;

const unique System.Int64.MaxValue: int;

axiom System.Int64.MinValue < System.Int32.MinValue;

axiom System.Int32.MinValue < System.Int16.MinValue;

axiom System.Int16.MinValue < System.Int16.MaxValue;

axiom System.Int16.MaxValue < System.Int32.MaxValue;

axiom System.Int32.MaxValue < System.Int64.MaxValue;

function InRange(i: int, T: name) returns (bool);

axiom (forall i: int :: InRange(i, System.Int16) <==> System.Int16.MinValue <= i && i <= System.Int16.MaxValue);

axiom (forall i: int :: InRange(i, System.Int32) <==> System.Int32.MinValue <= i && i <= System.Int32.MaxValue);

axiom (forall i: int :: InRange(i, System.Int64) <==> System.Int64.MinValue <= i && i <= System.Int64.MaxValue);

axiom (forall i: int :: { InRange(i, System.Byte) } InRange(i, System.Byte) <==> 0 <= i && i < 256);

function $RealToInt(real) returns (int);

function $IntToReal(int) returns (real);

function $SizeIs(name, int) returns (bool);

function $IfThenElse(bool, any, any) returns (any);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } b ==> $IfThenElse(b, x, y) == x);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } !b ==> $IfThenElse(b, x, y) == y);

function #neg(int) returns (int);

function #rneg(real) returns (real);

function #rdiv(real, real) returns (real);

function #and(int, int) returns (int);

function #or(int, int) returns (int);

function #xor(int, int) returns (int);

function #shl(int, int) returns (int);

function #shr(int, int) returns (int);

axiom (forall x: int, y: int :: { x mod y } { x div y } x mod y == x - x div y * y);

axiom (forall x: int, y: int :: { x mod y } 0 <= x && 0 < y ==> 0 <= x mod y && x mod y < y);

axiom (forall x: int, y: int :: { x mod y } 0 <= x && y < 0 ==> 0 <= x mod y && x mod y < 0 - y);

axiom (forall x: int, y: int :: { x mod y } x <= 0 && 0 < y ==> 0 - y < x mod y && x mod y <= 0);

axiom (forall x: int, y: int :: { x mod y } x <= 0 && y < 0 ==> y < x mod y && x mod y <= 0);

axiom (forall x: int, y: int :: { (x + y) mod y } 0 <= x && 0 <= y ==> (x + y) mod y == x mod y);

axiom (forall x: int, y: int :: { (y + x) mod y } 0 <= x && 0 <= y ==> (y + x) mod y == x mod y);

axiom (forall x: int, y: int :: { (x - y) mod y } 0 <= x - y && 0 <= y ==> (x - y) mod y == x mod y);

axiom (forall a: int, b: int, d: int :: { a mod d,b mod d } 2 <= d && a mod d == b mod d && a < b ==> a + d <= b);

axiom (forall i: int :: { #shl(i, 0) } #shl(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shl(i, j + 1) == #shl(i, j) * 2);

axiom (forall i: int :: { #shr(i, 0) } #shr(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shr(i, j + 1) == #shr(i, j) div 2);

const unique $UnknownRef: ref;

const unique System.IComparable: name;

const unique Microsoft.Singularity.Applications.ThreadTest: name;

const unique System.Threading.Thread: name;

const unique System.Collections.IEnumerable: name;

const unique System.Threading.ThreadStart: name;

const unique System.ICloneable: name;

const unique System.MulticastDelegate: name;

const unique System.Delegate: name;

const unique $stringLiteral0: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral0, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral0, $allocated]):bool) && $IsNotNull($stringLiteral0, System.String) && $Length($stringLiteral0) == 13;

const unique $stringLiteral1: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral1, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral1, $allocated]):bool) && $IsNotNull($stringLiteral1, System.String) && $Length($stringLiteral1) == 14;

const unique $stringLiteral2: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral2, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral2, $allocated]):bool) && $IsNotNull($stringLiteral2, System.String) && $Length($stringLiteral2) == 11;

const unique $stringLiteral3: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral3, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral3, $allocated]):bool) && $IsNotNull($stringLiteral3, System.String) && $Length($stringLiteral3) == 18;

const unique $stringLiteral4: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral4, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral4, $allocated]):bool) && $IsNotNull($stringLiteral4, System.String) && $Length($stringLiteral4) == 19;

const unique $stringLiteral5: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral5, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral5, $allocated]):bool) && $IsNotNull($stringLiteral5, System.String) && $Length($stringLiteral5) == 14;

const unique $stringLiteral6: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral6, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral6, $allocated]):bool) && $IsNotNull($stringLiteral6, System.String) && $Length($stringLiteral6) == 15;

const unique $stringLiteral7: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral7, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral7, $allocated]):bool) && $IsNotNull($stringLiteral7, System.String) && $Length($stringLiteral7) == 11;

const unique $stringLiteral8: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral8, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral8, $allocated]):bool) && $IsNotNull($stringLiteral8, System.String) && $Length($stringLiteral8) == 19;

const unique $stringLiteral9: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral9, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral9, $allocated]):bool) && $IsNotNull($stringLiteral9, System.String) && $Length($stringLiteral9) == 20;

const unique $stringLiteral10: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral10, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral10, $allocated]):bool) && $IsNotNull($stringLiteral10, System.String) && $Length($stringLiteral10) == 22;

const unique $stringLiteral11: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral11, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral11, $allocated]):bool) && $IsNotNull($stringLiteral11, System.String) && $Length($stringLiteral11) == 21;

const unique $stringLiteral12: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral12, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral12, $allocated]):bool) && $IsNotNull($stringLiteral12, System.String) && $Length($stringLiteral12) == 23;

const unique $stringLiteral13: ref;

axiom (forall heap: [ref,name]any :: { cast(heap[$stringLiteral13, $allocated]):bool } IsHeap(heap) ==> cast(heap[$stringLiteral13, $allocated]):bool) && $IsNotNull($stringLiteral13, System.String) && $Length($stringLiteral13) == 22;

axiom $IsClass(Microsoft.Singularity.Applications.ThreadTest);

axiom Microsoft.Singularity.Applications.ThreadTest <: System.Object && AsDirectSubClass(Microsoft.Singularity.Applications.ThreadTest, System.Object) == Microsoft.Singularity.Applications.ThreadTest;

axiom (forall $K: name :: { Microsoft.Singularity.Applications.ThreadTest <: $K } Microsoft.Singularity.Applications.ThreadTest <: $K <==> Microsoft.Singularity.Applications.ThreadTest == $K || System.Object <: $K);

function Inv_Microsoft.Singularity.Applications.ThreadTest(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_Microsoft.Singularity.Applications.ThreadTest(this, heap) } Inv_Microsoft.Singularity.Applications.ThreadTest(this, heap) <==> true);

axiom (forall $o: ref, heap: [ref,name]any :: { cast(heap[$o, $inv]):name <: Microsoft.Singularity.Applications.ThreadTest } { Inv_Microsoft.Singularity.Applications.ThreadTest($o, heap) } IsHeap(heap) && cast(heap[$o, $inv]):name <: Microsoft.Singularity.Applications.ThreadTest ==> Inv_Microsoft.Singularity.Applications.ThreadTest($o, heap));

procedure Microsoft.Singularity.Applications.ThreadTest.FirstThreadMethod();
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Microsoft.Singularity.Applications.ThreadTest.FirstThreadMethod()
{
  var stack0o: ref, i: int, stack0i: int, stack0b: bool, local1: int, $Heap$block1513$LoopPreheader: [ref,name]any;

  entry:
    assume IsHeap($Heap);
    goto block1479;

  block1479:
    goto block1496;

  block1496:
    // ----- load constant First thread!  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(21,13)
    stack0o := $stringLiteral0;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(21,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- load constant First thread!   ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(22,13)
    stack0o := $stringLiteral1;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(22,13)
    call Microsoft.Singularity.DebugStub.Print$System.String(stack0o);
    // ----- load constant 0  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(24,18)
    i := 0;
    goto block1513$LoopPreheader;

  block1513:
    // ----- default loop invariant: $inv field  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(24,29)
    assert (forall $o: ref :: $Heap$block1513$LoopPreheader[$o, $inv] == $Heap[$o, $inv] || cast($Heap$block1513$LoopPreheader[$o, $allocated]):bool != true);
    assert (forall $o: ref :: cast($Heap$block1513$LoopPreheader[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
    // ----- load constant 10  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(24,29)
    stack0i := 10;
    // ----- binary operator  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(24,29)
    stack0b := i >= stack0i;
    // ----- branch  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(24,29)
    goto true1513to1547, false1513to1530;

  true1513to1547:
    assume stack0b == true;
    goto block1547;

  false1513to1530:
    assume stack0b == false;
    goto block1530;

  block1547:
    // ----- load constant First thread done!  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(29,13)
    stack0o := $stringLiteral3;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(29,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- load constant First thread done!   ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(30,13)
    stack0o := $stringLiteral4;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(30,13)
    call Microsoft.Singularity.DebugStub.Print$System.String(stack0o);
    // ----- return  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(31,10)
    return;

  block1530:
    // ----- load constant [0] ...      ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(25,17)
    stack0o := $stringLiteral2;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(25,17)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(26,17)
    call System.Threading.Thread.Yield();
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(24,37)
    local1 := i;
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local1 + stack0i;
    // ----- copy
    i := stack0i;
    // ----- copy
    stack0i := local1;
    // ----- branch
    goto block1513;

  block1513$LoopPreheader:
    $Heap$block1513$LoopPreheader := $Heap;
    goto block1513;

}



axiom $IsClass(System.String);

axiom System.String <: System.Object && AsDirectSubClass(System.String, System.Object) == System.String;

axiom $IsInterface(System.IComparable);

axiom (forall $K: name :: { System.IComparable <: $K } System.IComparable <: $K <==> System.IComparable == $K || System.Object == $K);

axiom Implements(System.String, System.IComparable);

axiom $IsInterface(System.ICloneable);

axiom (forall $K: name :: { System.ICloneable <: $K } System.ICloneable <: $K <==> System.ICloneable == $K || System.Object == $K);

axiom Implements(System.String, System.ICloneable);

axiom $IsInterface(System.Collections.IEnumerable);

axiom (forall $K: name :: { System.Collections.IEnumerable <: $K } System.Collections.IEnumerable <: $K <==> System.Collections.IEnumerable == $K || System.Object == $K);

axiom Implements(System.String, System.Collections.IEnumerable);

axiom (forall $K: name :: { System.String <: $K } System.String <: $K <==> System.String == $K || System.Object <: $K || System.IComparable <: $K || System.ICloneable <: $K || System.Collections.IEnumerable <: $K);

axiom (forall $U: name :: { $U <: System.String } $U <: System.String ==> $U == System.String);

function Inv_System.String(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_System.String(this, heap) } Inv_System.String(this, heap) <==> true);

axiom (forall $o: ref, heap: [ref,name]any :: { cast(heap[$o, $inv]):name <: System.String } { Inv_System.String($o, heap) } IsHeap(heap) && cast(heap[$o, $inv]):name <: System.String ==> Inv_System.String($o, heap));

procedure System.Console.WriteLine$System.String(value$in: ref);
  requires value$in == null || (cast($Heap[value$in, $writable]):bool == true && cast($Heap[value$in, $inv]):name == $typeof(value$in));
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Microsoft.Singularity.DebugStub.Print$System.String(value$in: ref);
  requires value$in == null || (cast($Heap[value$in, $writable]):bool == true && cast($Heap[value$in, $inv]):name == $typeof(value$in));
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure System.Threading.Thread.Yield();
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Microsoft.Singularity.Applications.ThreadTest.SecondThreadMethod();
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Microsoft.Singularity.Applications.ThreadTest.SecondThreadMethod()
{
  var stack0o: ref, i: int, stack0i: int, stack0b: bool, local1: int, $Heap$block2516$LoopPreheader: [ref,name]any;

  entry:
    assume IsHeap($Heap);
    goto block2482;

  block2482:
    goto block2499;

  block2499:
    // ----- load constant Second thread!  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(35,13)
    stack0o := $stringLiteral5;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(35,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- load constant Second thread!   ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(36,13)
    stack0o := $stringLiteral6;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(36,13)
    call Microsoft.Singularity.DebugStub.Print$System.String(stack0o);
    // ----- load constant 0  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(38,18)
    i := 0;
    goto block2516$LoopPreheader;

  block2516:
    // ----- default loop invariant: $inv field  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(38,29)
    assert (forall $o: ref :: $Heap$block2516$LoopPreheader[$o, $inv] == $Heap[$o, $inv] || cast($Heap$block2516$LoopPreheader[$o, $allocated]):bool != true);
    assert (forall $o: ref :: cast($Heap$block2516$LoopPreheader[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
    // ----- load constant 10  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(38,29)
    stack0i := 10;
    // ----- binary operator  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(38,29)
    stack0b := i >= stack0i;
    // ----- branch  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(38,29)
    goto true2516to2550, false2516to2533;

  true2516to2550:
    assume stack0b == true;
    goto block2550;

  false2516to2533:
    assume stack0b == false;
    goto block2533;

  block2550:
    // ----- load constant Second thread done!  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(44,13)
    stack0o := $stringLiteral8;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(44,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- load constant Second thread done!   ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(45,13)
    stack0o := $stringLiteral9;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(45,13)
    call Microsoft.Singularity.DebugStub.Print$System.String(stack0o);
    // ----- return  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(46,10)
    return;

  block2533:
    // ----- load constant     ... [1]  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(40,17)
    stack0o := $stringLiteral7;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(40,17)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(41,17)
    call System.Threading.Thread.Yield();
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(38,37)
    local1 := i;
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local1 + stack0i;
    // ----- copy
    i := stack0i;
    // ----- copy
    stack0i := local1;
    // ----- branch
    goto block2516;

  block2516$LoopPreheader:
    $Heap$block2516$LoopPreheader := $Heap;
    goto block2516;

}



procedure Microsoft.Singularity.Applications.ThreadTest.Main$System.String.array(args$in: ref) returns ($result: int);
  requires args$in == null || (cast($Heap[args$in, $writable]):bool == true && cast($Heap[args$in, $inv]):name == $typeof(args$in));
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Microsoft.Singularity.Applications.ThreadTest.Main$System.String.array(args$in: ref) returns ($result: int)
{
  var args: ref, stack0o: ref, stack1o: ref, stack50000o: ref, t1: ref, t2: ref, i: int, stack0i: int, stack0b: bool, local3: int, return.value: int, SS$Display.Return.Local: int, $Heap$block3825$LoopPreheader: [ref,name]any;

  entry:
    assume IsHeap($Heap);
    args := args$in;
    assume $Is(args, RefArray(System.String, 1));
    assume cast($Heap[args$in, $allocated]):bool == true;
    goto block3791;

  block3791:
    goto block3808;

  block3808:
    stack0o := null;
    // ----- load function  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    havoc stack1o;
    // ----- new object  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    havoc stack50000o;
    assume cast($Heap[stack50000o, $allocated]):bool == false && stack50000o != null && $typeof(stack50000o) == System.Threading.ThreadStart;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    assert stack50000o != null;
    call System.Threading.ThreadStart..ctor$System.Object$System.IntPtr(stack50000o, stack0o, stack1o);
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    stack0o := stack50000o;
    // ----- new object  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    havoc stack50000o;
    assume cast($Heap[stack50000o, $allocated]):bool == false && stack50000o != null && $typeof(stack50000o) == System.Threading.Thread;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    assert stack50000o != null;
    call System.Threading.Thread..ctor$System.Threading.ThreadStart(stack50000o, stack0o);
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    stack0o := stack50000o;
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(51,13)
    t1 := stack0o;
    stack0o := null;
    // ----- load function  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    havoc stack1o;
    // ----- new object  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    havoc stack50000o;
    assume cast($Heap[stack50000o, $allocated]):bool == false && stack50000o != null && $typeof(stack50000o) == System.Threading.ThreadStart;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    assert stack50000o != null;
    call System.Threading.ThreadStart..ctor$System.Object$System.IntPtr(stack50000o, stack0o, stack1o);
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    stack0o := stack50000o;
    // ----- new object  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    havoc stack50000o;
    assume cast($Heap[stack50000o, $allocated]):bool == false && stack50000o != null && $typeof(stack50000o) == System.Threading.Thread;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    assert stack50000o != null;
    call System.Threading.Thread..ctor$System.Threading.ThreadStart(stack50000o, stack0o);
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    stack0o := stack50000o;
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(52,13)
    t2 := stack0o;
    // ----- load constant Starting first thread.  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(54,13)
    stack0o := $stringLiteral10;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(54,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(55,13)
    assert t1 != null;
    call System.Threading.Thread.Start(t1);
    // ----- load constant Started first thread.  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(56,13)
    stack0o := $stringLiteral11;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(56,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- load constant Starting second thread.  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(58,13)
    stack0o := $stringLiteral12;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(58,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(59,13)
    assert t2 != null;
    call System.Threading.Thread.Start(t2);
    // ----- load constant Started second thread.  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(60,13)
    stack0o := $stringLiteral13;
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(60,13)
    call System.Console.WriteLine$System.String(stack0o);
    // ----- load constant 0  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(62,18)
    i := 0;
    goto block3825$LoopPreheader;

  block3825:
    // ----- default loop invariant: $inv field  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(62,29)
    assert (forall $o: ref :: $Heap$block3825$LoopPreheader[$o, $inv] == $Heap[$o, $inv] || cast($Heap$block3825$LoopPreheader[$o, $allocated]):bool != true);
    assert (forall $o: ref :: cast($Heap$block3825$LoopPreheader[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
    // ----- load constant 30  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(62,29)
    stack0i := 30;
    // ----- binary operator  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(62,29)
    stack0b := i >= stack0i;
    // ----- branch  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(62,29)
    goto true3825to3859, false3825to3842;

  true3825to3859:
    assume stack0b == true;
    goto block3859;

  false3825to3842:
    assume stack0b == false;
    goto block3842;

  block3859:
    // ----- load constant 0  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(66,13)
    return.value := 0;
    // ----- branch
    goto block3876;

  block3842:
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(64,17)
    call System.Threading.Thread.Yield();
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(62,37)
    local3 := i;
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local3 + stack0i;
    // ----- copy
    i := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block3825;

  block3876:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(67,10)
    stack0i := return.value;
    // ----- return  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(67,10)
    $result := stack0i;
    return;

  block3825$LoopPreheader:
    $Heap$block3825$LoopPreheader := $Heap;
    goto block3825;

}



axiom $IsClass(System.Threading.ThreadStart);

axiom $IsClass(System.MulticastDelegate);

axiom $IsClass(System.Delegate);

axiom System.Delegate <: System.Object && AsDirectSubClass(System.Delegate, System.Object) == System.Delegate;

axiom Implements(System.Delegate, System.ICloneable);

axiom (forall $K: name :: { System.Delegate <: $K } System.Delegate <: $K <==> System.Delegate == $K || System.Object <: $K || System.ICloneable <: $K);

function Inv_System.Delegate(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_System.Delegate(this, heap) } Inv_System.Delegate(this, heap) <==> true);

axiom (forall $o: ref, heap: [ref,name]any :: { cast(heap[$o, $inv]):name <: System.Delegate } { Inv_System.Delegate($o, heap) } IsHeap(heap) && cast(heap[$o, $inv]):name <: System.Delegate ==> Inv_System.Delegate($o, heap));

axiom System.MulticastDelegate <: System.Delegate && AsDirectSubClass(System.MulticastDelegate, System.Delegate) == System.MulticastDelegate;

axiom (forall $K: name :: { System.MulticastDelegate <: $K } System.MulticastDelegate <: $K <==> System.MulticastDelegate == $K || System.Delegate <: $K);

function Inv_System.MulticastDelegate(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_System.MulticastDelegate(this, heap) } Inv_System.MulticastDelegate(this, heap) <==> true);

axiom (forall $o: ref, heap: [ref,name]any :: { cast(heap[$o, $inv]):name <: System.MulticastDelegate } { Inv_System.MulticastDelegate($o, heap) } IsHeap(heap) && cast(heap[$o, $inv]):name <: System.MulticastDelegate ==> Inv_System.MulticastDelegate($o, heap));

axiom System.Threading.ThreadStart <: System.MulticastDelegate && AsDirectSubClass(System.Threading.ThreadStart, System.MulticastDelegate) == System.Threading.ThreadStart;

axiom (forall $K: name :: { System.Threading.ThreadStart <: $K } System.Threading.ThreadStart <: $K <==> System.Threading.ThreadStart == $K || System.MulticastDelegate <: $K);

axiom (forall $U: name :: { $U <: System.Threading.ThreadStart } $U <: System.Threading.ThreadStart ==> $U == System.Threading.ThreadStart);

function Inv_System.Threading.ThreadStart(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_System.Threading.ThreadStart(this, heap) } Inv_System.Threading.ThreadStart(this, heap) <==> true);

axiom (forall $o: ref, heap: [ref,name]any :: { cast(heap[$o, $inv]):name <: System.Threading.ThreadStart } { Inv_System.Threading.ThreadStart($o, heap) } IsHeap(heap) && cast(heap[$o, $inv]):name <: System.Threading.ThreadStart ==> Inv_System.Threading.ThreadStart($o, heap));

procedure System.Threading.ThreadStart..ctor$System.Object$System.IntPtr(this: ref, object$in: ref, method$in: ref);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);
  ensures cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == System.Threading.ThreadStart;



axiom $IsClass(System.Threading.Thread);

axiom System.Threading.Thread <: System.Object && AsDirectSubClass(System.Threading.Thread, System.Object) == System.Threading.Thread;

axiom (forall $K: name :: { System.Threading.Thread <: $K } System.Threading.Thread <: $K <==> System.Threading.Thread == $K || System.Object <: $K);

axiom (forall $U: name :: { $U <: System.Threading.Thread } $U <: System.Threading.Thread ==> $U == System.Threading.Thread);

function Inv_System.Threading.Thread(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_System.Threading.Thread(this, heap) } Inv_System.Threading.Thread(this, heap) <==> true);

axiom (forall $o: ref, heap: [ref,name]any :: { cast(heap[$o, $inv]):name <: System.Threading.Thread } { Inv_System.Threading.Thread($o, heap) } IsHeap(heap) && cast(heap[$o, $inv]):name <: System.Threading.Thread ==> Inv_System.Threading.Thread($o, heap));

procedure System.Threading.Thread..ctor$System.Threading.ThreadStart(this: ref, start$in: ref);
  requires start$in == null || (cast($Heap[start$in, $writable]):bool == true && cast($Heap[start$in, $inv]):name == $typeof(start$in));
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && ($o != this || !(System.Threading.Thread <: DeclType($f))) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);
  ensures cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == System.Threading.Thread;
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;



procedure System.Threading.Thread.Start(this: ref);
  requires cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == $typeof(this);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Microsoft.Singularity.Applications.ThreadTest..ctor(this: ref);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && ($o != this || !(Microsoft.Singularity.Applications.ThreadTest <: DeclType($f))) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);
  ensures cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == Microsoft.Singularity.Applications.ThreadTest;
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;



implementation Microsoft.Singularity.Applications.ThreadTest..ctor(this: ref)
{

  entry:
    assume IsHeap($Heap);
    assume $IsNotNull(this, Microsoft.Singularity.Applications.ThreadTest);
    assume cast($Heap[this, $allocated]):bool == true;
    assume cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == System.Object;
    goto block4777;

  block4777:
    goto block4794;

  block4794:
    // ----- call  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(17,18)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return  ----- C:\Maf\Singularity\base\Applications\Tests\ThreadTest\ThreadTest.cs(17,28)
    assert this != null;
    assert cast($Heap[this, $writable]):bool == true && System.Object <: cast($Heap[this, $inv]):name;
    assert cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == System.Object;
    assert Inv_Microsoft.Singularity.Applications.ThreadTest(this, $Heap);
    $Heap[this, $inv] := Microsoft.Singularity.Applications.ThreadTest;
    return;

}



procedure System.Object..ctor(this: ref);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated]):bool == true && cast(old($Heap)[$o, $writable]):bool == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && ($o != this || !(System.Object <: DeclType($f))) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated]):bool != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated]):bool ==> cast($Heap[$o, $allocated]):bool);
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);
  ensures cast($Heap[this, $writable]):bool == true && cast($Heap[this, $inv]):name == System.Object;
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;



type ref, name, any;
const null : ref;
