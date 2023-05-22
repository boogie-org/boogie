// Dafny 3.7.3.40719
// Command Line Options: /compile:0 /print:Composite.dfy.bpl
// RUN: %parallel-boogie /noVerify "%s" > "%t"

type Ty;

type TyTag;

type TyTagFamily;

type char;

type ref;

type Box;

type ClassName;

type HandleType;

type DatatypeType;

type DtCtorId;

type LayerType;

type Field _;

type NameFamily;

type TickType;

type Seq _;

type Map _ _;

type IMap _ _;

const $$Language$Dafny: bool;

axiom $$Language$Dafny;

type Bv0 = int;

const unique TBool: Ty;

axiom Tag(TBool) == TagBool;

const unique TChar: Ty;

axiom Tag(TChar) == TagChar;

const unique TInt: Ty;

axiom Tag(TInt) == TagInt;

const unique TReal: Ty;

axiom Tag(TReal) == TagReal;

const unique TORDINAL: Ty;

axiom Tag(TORDINAL) == TagORDINAL;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

function TBitvector(int) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

function TSet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

function TISet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

function TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

function TSeq(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

function TMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

function TIMap(Ty, Ty) : Ty;

function Inv0_TBitvector(Ty) : int;

function Inv0_TSet(Ty) : Ty;

function Inv0_TISet(Ty) : Ty;

function Inv0_TSeq(Ty) : Ty;

function Inv0_TMultiSet(Ty) : Ty;

function Inv0_TMap(Ty) : Ty;

function Inv1_TMap(Ty) : Ty;

function Inv0_TIMap(Ty) : Ty;

function Inv1_TIMap(Ty) : Ty;

function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

function TagFamily(Ty) : TyTagFamily;

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

function {:identity} Lit<T>(x: T) : T;

axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

function {:identity} LitInt(x: int) : int;

axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);

axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)));

function {:identity} LitReal(x: real) : real;

axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x);

axiom (forall n: int ::
  { char#FromInt(n) }
  0 <= n && n < 65536 ==> char#ToInt(char#FromInt(n)) == n);

function char#FromInt(int) : char;

axiom (forall ch: char ::
  { char#ToInt(ch) }
  char#FromInt(char#ToInt(ch)) == ch
     && 0 <= char#ToInt(ch)
     && char#ToInt(ch) < 65536);

function char#ToInt(char) : int;

axiom (forall a: char, b: char ::
  { char#Plus(a, b) }
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

function char#Plus(char, char) : char;

axiom (forall a: char, b: char ::
  { char#Minus(a, b) }
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

function char#Minus(char, char) : char;

const null: ref;

const $ArbitraryBoxValue: Box;

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);

function $Box<T>(T) : Box;

function $Unbox<T>(Box) : T;

function $IsBox<T>(T, Ty) : bool;

function $IsAllocBox<T>(T, Ty, Heap) : bool;

axiom (forall bx: Box ::
  { $IsBox(bx, TInt) }
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, TInt));

axiom (forall bx: Box ::
  { $IsBox(bx, TReal) }
  $IsBox(bx, TReal)
     ==> $Box($Unbox(bx): real) == bx && $Is($Unbox(bx): real, TReal));

axiom (forall bx: Box ::
  { $IsBox(bx, TBool) }
  $IsBox(bx, TBool)
     ==> $Box($Unbox(bx): bool) == bx && $Is($Unbox(bx): bool, TBool));

axiom (forall bx: Box ::
  { $IsBox(bx, TChar) }
  $IsBox(bx, TChar)
     ==> $Box($Unbox(bx): char) == bx && $Is($Unbox(bx): char, TChar));

axiom (forall bx: Box ::
  { $IsBox(bx, TBitvector(0)) }
  $IsBox(bx, TBitvector(0))
     ==> $Box($Unbox(bx): Bv0) == bx && $Is($Unbox(bx): Set Box, TBitvector(0)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TSet(t)) }
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set Box) == bx && $Is($Unbox(bx): Set Box, TSet(t)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TISet(t)) }
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet Box) == bx && $Is($Unbox(bx): ISet Box, TISet(t)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TMultiSet(t)) }
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet Box) == bx
       && $Is($Unbox(bx): MultiSet Box, TMultiSet(t)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TSeq(t)) }
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq Box) == bx && $Is($Unbox(bx): Seq Box, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty ::
  { $IsBox(bx, TMap(s, t)) }
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map Box Box) == bx && $Is($Unbox(bx): Map Box Box, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty ::
  { $IsBox(bx, TIMap(s, t)) }
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap Box Box) == bx
       && $Is($Unbox(bx): IMap Box Box, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty ::
  { $IsBox($Box(v), t) }
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap ::
  { $IsAllocBox($Box(v), t, h) }
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

axiom (forall v: Set Box, t0: Ty ::
  { $Is(v, TSet(t0)) }
  $Is(v, TSet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: ISet Box, t0: Ty ::
  { $Is(v, TISet(t0)) }
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty ::
  { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty ::
  { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq Box, t0: Ty ::
  { $Is(v, TSeq(t0)) }
  $Is(v, TSeq(t0))
     <==> (forall i: int ::
      { Seq#Index(v, i) }
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx] ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1))
     ==> $Is(Map#Domain(v), TSet(t0))
       && $Is(Map#Values(v), TSet(t1))
       && $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1))
     ==> $Is(IMap#Domain(v), TISet(t0))
       && $Is(IMap#Values(v), TISet(t1))
       && $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));

function $Is<T>(T, Ty) : bool;

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h));

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL ::
  { $IsAlloc(v, TORDINAL, h) }
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Bv0, h: Heap ::
  { $IsAlloc(v, TBitvector(0), h) }
  $IsAlloc(v, TBitvector(0), h));

axiom (forall v: Set Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TSet(t0), h) }
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TISet(t0), h) }
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TMultiSet(t0), h) }
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TSeq(t0), h) }
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int ::
      { Seq#Index(v, i) }
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TMap(t0, t1), h) }
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx]
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TIMap(t0, t1), h) }
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

function $IsAlloc<T>(T, Ty, Heap) : bool;

axiom (forall ty: Ty ::
  { $AlwaysAllocated(ty) }
  $AlwaysAllocated(ty)
     ==> (forall h: Heap, v: Box ::
      { $IsAllocBox(v, ty, h) }
      $IsBox(v, ty) ==> $IsAllocBox(v, ty, h)));

function $AlwaysAllocated(Ty) : bool;

function $OlderTag(Heap) : bool;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

function Tclass._System.object?() : Ty;

function Tclass._System.Tuple2(Ty, Ty) : Ty;

function dtype(ref) : Ty;

function TypeTuple(a: ClassName, b: ClassName) : ClassName;

function TypeTupleCar(ClassName) : ClassName;

function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName ::
  { TypeTuple(a, b) }
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

function SetRef_to_SetBox(s: [ref]bool) : Set Box;

axiom (forall s: [ref]bool, bx: Box ::
  { SetRef_to_SetBox(s)[bx] }
  SetRef_to_SetBox(s)[bx] == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool ::
  { SetRef_to_SetBox(s) }
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

function DatatypeCtorId(DatatypeType) : DtCtorId;

function DtRank(DatatypeType) : int;

function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

function ORD#IsNat(ORDINAL) : bool;

function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int ::
  { ORD#FromNat(n) }
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL ::
  { ORD#Offset(o) } { ORD#IsNat(o) }
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

function ORD#Less(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Less(o, p) }
  (ORD#Less(o, p) ==> o != p)
     && (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o, p))
     && (ORD#IsNat(o) && ORD#IsNat(p)
       ==> ORD#Less(o, p) == (ORD#Offset(o) < ORD#Offset(p)))
     && (ORD#Less(o, p) && ORD#IsNat(p) ==> ORD#IsNat(o)));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Less(o, p), ORD#Less(p, o) }
  ORD#Less(o, p) || o == p || ORD#Less(p, o));

axiom (forall o: ORDINAL, p: ORDINAL, r: ORDINAL ::
  { ORD#Less(o, p), ORD#Less(p, r) } { ORD#Less(o, p), ORD#Less(o, r) }
  ORD#Less(o, p) && ORD#Less(p, r) ==> ORD#Less(o, r));

function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#LessThanLimit(o, p) }
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Plus(o, p) }
  (ORD#IsNat(ORD#Plus(o, p)) ==> ORD#IsNat(o) && ORD#IsNat(p))
     && (ORD#IsNat(p)
       ==> ORD#IsNat(ORD#Plus(o, p)) == ORD#IsNat(o)
         && ORD#Offset(ORD#Plus(o, p)) == ORD#Offset(o) + ORD#Offset(p)));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Plus(o, p) }
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p)))
     && (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Plus(o, p) }
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p)
     && (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Minus(o, p) }
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> ORD#IsNat(ORD#Minus(o, p)) == ORD#IsNat(o)
       && ORD#Offset(ORD#Minus(o, p)) == ORD#Offset(o) - ORD#Offset(p));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Minus(o, p) }
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> (p == ORD#FromNat(0) && ORD#Minus(o, p) == o)
       || (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n
     ==> ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Plus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && m + n <= ORD#Offset(o)
     ==> ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Minus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(n - m))));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));

const $ModuleContextHeight: int;

const $FunctionContextHeight: int;

const $LZ: LayerType;

function $LS(LayerType) : LayerType;

function AsFuelBottom(LayerType) : LayerType;

function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType ::
  { AtLayer(f, ly) }
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType ::
  { AtLayer(f, $LS(ly)) }
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

axiom FDim(alloc) == 0;

function FDim<T>(Field T) : int;

function IndexField(int) : Field Box;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

function IndexField_Inverse<T>(Field T) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field Box, int) : Field Box;

axiom (forall f: Field Box, i: int ::
  { MultiIndexField(f, i) }
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

function MultiIndexField_Inverse0<T>(Field T) : Field T;

function MultiIndexField_Inverse1<T>(Field T) : int;

axiom (forall f: Field Box, i: int ::
  { MultiIndexField(f, i) }
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

function DeclType<T>(Field T) : ClassName;

axiom DeclName(alloc) == allocName;

function DeclName<T>(Field T) : NameFamily;

function FieldOfDecl<alpha>(ClassName, NameFamily) : Field alpha;

axiom (forall<T> cl: ClassName, nm: NameFamily ::
  { FieldOfDecl(cl, nm): Field T }
  DeclType(FieldOfDecl(cl, nm): Field T) == cl
     && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

axiom $IsGhostField(alloc);

axiom (forall h: Heap, k: Heap ::
  { $HeapSuccGhost(h, k) }
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall<alpha> o: ref, f: Field alpha ::
        { read(k, o, f) }
        !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

function $IsGhostField<T>(Field T) : bool;

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty ::
  { $HeapSucc(h, k), $IsAlloc(v, t, h) }
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty ::
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) }
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field bool;

const unique allocName: NameFamily;

axiom (forall o: ref :: 0 <= _System.array.Length(o));

function _System.array.Length(a: ref) : int;

function Int(x: real) : int;

axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));

function Real(x: int) : real;

axiom (forall x: int :: { Real(x): real } Real(x): real == real(x));

axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref]<alpha>[Field alpha]alpha;

function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
{
  H[r][f]
}

function {:inline} update<alpha>(H: Heap, r: ref, f: Field alpha, v: alpha) : Heap
{
  H[r := H[r][f := v]]
}

function $IsGoodHeap(Heap) : bool;

function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap;

axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap) : bool;

axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha ::
  { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap ::
  { $HeapSucc(a, b), $HeapSucc(b, c) }
  a != c ==> $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap ::
  { $HeapSucc(h, k) }
  $HeapSucc(h, k)
     ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

function $HeapSuccGhost(Heap, Heap) : bool;

var $Tick: TickType;

procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==>
      $o == this || rds[$Box($o)] || nw[$Box($o)]
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==>
      rds[$Box($o)] && !modi[$Box($o)] && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || modi[$Box($o)]
         || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
   returns (s: Set Box);
  ensures (forall bx: Box ::
    { s[bx] }
    s[bx]
       <==> read(newHeap, this, NW)[bx]
         || (
          $Unbox(bx) != null
           && !read(prevHeap, $Unbox(bx): ref, alloc)
           && read(newHeap, $Unbox(bx): ref, alloc)));



type Set T = [T]bool;

function Set#Card<T>(Set T) : int;

axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>() : Set T;

axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

axiom (forall<T> s: Set T ::
  { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

function Set#Singleton<T>(T) : Set T;

axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

axiom (forall<T> r: T, o: T ::
  { Set#Singleton(r)[o] }
  Set#Singleton(r)[o] <==> r == o);

axiom (forall<T> r: T ::
  { Set#Card(Set#Singleton(r)) }
  Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T) : Set T;

axiom (forall<T> a: Set T, x: T, o: T ::
  { Set#UnionOne(a, x)[o] }
  Set#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) } Set#UnionOne(a, x)[x]);

axiom (forall<T> a: Set T, x: T, y: T ::
  { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);

axiom (forall<T> a: Set T, x: T ::
  { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall<T> a: Set T, x: T ::
  { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T ::
  { Set#Union(a, b)[o] }
  Set#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Union(a, b) }
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

function Set#Intersection<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T ::
  { Set#Intersection(a, b)[o] }
  Set#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T ::
  { Set#Difference(a, b)[o] }
  Set#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Subset(a, b) }
  Set#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function Set#Equal<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Equal(a, b) }
  Set#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: Set T, b: Set T :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Disjoint(a, b) }
  Set#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

type ISet T = [T]bool;

function ISet#Empty<T>() : Set T;

axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);

function ISet#UnionOne<T>(ISet T, T) : ISet T;

axiom (forall<T> a: ISet T, x: T, o: T ::
  { ISet#UnionOne(a, x)[o] }
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall<T> a: ISet T, x: T, y: T ::
  { ISet#UnionOne(a, x), a[y] }
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T ::
  { ISet#Union(a, b)[o] }
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T ::
  { ISet#Union(a, b), a[y] }
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { ISet#Union(a, b), b[y] }
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Union(a, b) }
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T ::
  { ISet#Intersection(a, b)[o] }
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Union(ISet#Union(a, b), b) }
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { ISet#Union(a, ISet#Union(a, b)) }
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Intersection(ISet#Intersection(a, b), b) }
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Intersection(a, ISet#Intersection(a, b)) }
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

function ISet#Difference<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T ::
  { ISet#Difference(a, b)[o] }
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T ::
  { ISet#Difference(a, b), b[y] }
  b[y] ==> !ISet#Difference(a, b)[y]);

function ISet#Subset<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Subset(a, b) }
  ISet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function ISet#Equal<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Equal(a, b) }
  ISet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Equal(a, b) }
  ISet#Equal(a, b) ==> a == b);

function ISet#Disjoint<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Disjoint(a, b) }
  ISet#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int ::
  { Math#min(a, b) }
  Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

function $IsGoodMultiSet<T>(ms: MultiSet T) : bool;

axiom (forall<T> ms: MultiSet T ::
  { $IsGoodMultiSet(ms) }
  $IsGoodMultiSet(ms)
     <==> (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

function MultiSet#Card<T>(MultiSet T) : int;

axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall<T> s: MultiSet T, x: T, n: int ::
  { MultiSet#Card(s[x := n]) }
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>() : MultiSet T;

axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);

axiom (forall<T> s: MultiSet T ::
  { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T) : MultiSet T;

axiom (forall<T> r: T, o: T ::
  { MultiSet#Singleton(r)[o] }
  (MultiSet#Singleton(r)[o] == 1 <==> r == o)
     && (MultiSet#Singleton(r)[o] == 0 <==> r != o));

axiom (forall<T> r: T ::
  { MultiSet#Singleton(r) }
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

function MultiSet#UnionOne<T>(MultiSet T, T) : MultiSet T;

axiom (forall<T> a: MultiSet T, x: T, o: T ::
  { MultiSet#UnionOne(a, x)[o] }
  0 < MultiSet#UnionOne(a, x)[o] <==> o == x || 0 < a[o]);

axiom (forall<T> a: MultiSet T, x: T ::
  { MultiSet#UnionOne(a, x) }
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);

axiom (forall<T> a: MultiSet T, x: T, y: T ::
  { MultiSet#UnionOne(a, x), a[y] }
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T, y: T ::
  { MultiSet#UnionOne(a, x), a[y] }
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T ::
  { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

function MultiSet#Union<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T ::
  { MultiSet#Union(a, b)[o] }
  MultiSet#Union(a, b)[o] == a[o] + b[o]);

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Union(a, b)) }
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T ::
  { MultiSet#Intersection(a, b)[o] }
  MultiSet#Intersection(a, b)[o] == Math#min(a[o], b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

function MultiSet#Difference<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T ::
  { MultiSet#Difference(a, b)[o] }
  MultiSet#Difference(a, b)[o] == Math#clip(a[o] - b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T, y: T ::
  { MultiSet#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0);

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

function MultiSet#Subset<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Subset(a, b) }
  MultiSet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Equal(a, b) }
  MultiSet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] == b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Equal(a, b) }
  MultiSet#Equal(a, b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Disjoint(a, b) }
  MultiSet#Disjoint(a, b)
     <==> (forall o: T :: { a[o] } { b[o] } a[o] == 0 || b[o] == 0));

function MultiSet#FromSet<T>(Set T) : MultiSet T;

axiom (forall<T> s: Set T, a: T ::
  { MultiSet#FromSet(s)[a] }
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a])
     && (MultiSet#FromSet(s)[a] == 1 <==> s[a]));

axiom (forall<T> s: Set T ::
  { MultiSet#Card(MultiSet#FromSet(s)) }
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

axiom (forall<T>  ::
  MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);

function MultiSet#FromSeq<T>(Seq T) : MultiSet T;

axiom (forall<T> s: Seq T ::
  { MultiSet#FromSeq(s) }
  $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall<T> s: Seq T ::
  { MultiSet#Card(MultiSet#FromSeq(s)) }
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall<T> s: Seq T, v: T ::
  { MultiSet#FromSeq(Seq#Build(s, v)) }
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall<T> a: Seq T, b: Seq T ::
  { MultiSet#FromSeq(Seq#Append(a, b)) }
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#FromSeq(Seq#Update(s, i, v))[x]
       == MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))),
        MultiSet#Singleton(v))[x]);

axiom (forall<T> s: Seq T, x: T ::
  { MultiSet#FromSeq(s)[x] }
  (exists i: int ::
      { Seq#Index(s, i) }
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#FromSeq(s)[x]);

function Seq#Length<T>(Seq T) : int;

axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>() : Seq T;

axiom (forall<T>  :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);

axiom (forall<T> s: Seq T ::
  { Seq#Length(s) }
  Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T) : Seq T;

axiom (forall<T> t: T ::
  { Seq#Length(Seq#Singleton(t)) }
  Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T) : Seq T;

function Seq#Build_inv0<T>(s: Seq T) : Seq T;

function Seq#Build_inv1<T>(s: Seq T) : T;

axiom (forall<T> s: Seq T, val: T ::
  { Seq#Build(s, val) }
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall<T> s: Seq T, v: T ::
  { Seq#Build(s, v) }
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T ::
  { Seq#Index(Seq#Build(s, v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s: Seq Box, bx: Box, t: Ty ::
  { $Is(Seq#Build(s, bx), TSeq(t)) }
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq Box;

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType ::
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) }
  $IsGoodHeap(heap) && 0 <= len
     ==> Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) == len);

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int ::
  { Seq#Index(Seq#Create(ty, heap, len, init), i) }
  $IsGoodHeap(heap) && 0 <= i && i < len
     ==> Seq#Index(Seq#Create(ty, heap, len, init), i)
       == Apply1(TInt, TSeq(ty), heap, init, $Box(i)));

function Seq#Append<T>(Seq T, Seq T) : Seq T;

axiom (forall<T> s0: Seq T, s1: Seq T ::
  { Seq#Length(Seq#Append(s0, s1)) }
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int) : T;

axiom (forall<T> t: T ::
  { Seq#Index(Seq#Singleton(t), 0) }
  Seq#Index(Seq#Singleton(t), 0) == t);

axiom (forall<T> s0: Seq T, s1: Seq T, n: int ::
  { Seq#Index(Seq#Append(s0, s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T) : Seq T;

axiom (forall<T> s: Seq T, i: int, v: T ::
  { Seq#Length(Seq#Update(s, i, v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Index(Seq#Update(s, i, v), n) }
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

function Seq#Contains<T>(Seq T, T) : bool;

axiom (forall<T> s: Seq T, x: T ::
  { Seq#Contains(s, x) }
  Seq#Contains(s, x)
     <==> (exists i: int ::
      { Seq#Index(s, i) }
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Contains(Seq#Build(s, v), x) }
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int ::
      { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int ::
      { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T ::
  { Seq#Equal(s0, s1) }
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int ::
        { Seq#Index(s0, j) } { Seq#Index(s1, j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T, n: int ::
  { Seq#SameUntil(s0, s1, n) }
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int ::
      { Seq#Index(s0, j) } { Seq#Index(s1, j) }
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

function Seq#Take<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Length(Seq#Take(s, n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) }
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Length(Seq#Drop(s, n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25} { Seq#Index(Seq#Drop(s, n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall<T> s: Seq T, n: int, k: int ::
  {:weight 25} { Seq#Index(s, k), Seq#Drop(s, n) }
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall<T> s: Seq T, t: Seq T, n: int ::
  { Seq#Take(Seq#Append(s, t), n) } { Seq#Drop(Seq#Append(s, t), n) }
  n == Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == s && Seq#Drop(Seq#Append(s, t), n) == t);

function Seq#FromArray(h: Heap, a: ref) : Seq Box;

axiom (forall h: Heap, a: ref ::
  { Seq#Length(Seq#FromArray(h, a)) }
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref ::
  { Seq#FromArray(h, a) }
  (forall i: int ::
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq Box, i) }
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));

axiom (forall h0: Heap, h1: Heap, a: ref ::
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
     ==> Seq#FromArray(h0, a) == Seq#FromArray(h1, a));

axiom (forall h: Heap, i: int, v: Box, a: ref ::
  { Seq#FromArray(update(h, a, IndexField(i), v), a) }
  0 <= i && i < _System.array.Length(a)
     ==> Seq#FromArray(update(h, a, IndexField(i), v), a)
       == Seq#Update(Seq#FromArray(h, a), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall h: Heap, a: ref, n0: int, n1: int ::
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)));

axiom (forall<T> s: Seq T, v: T, n: int ::
  { Seq#Drop(Seq#Build(s, v), n) }
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

function Seq#Rank<T>(Seq T) : int;

axiom (forall s: Seq Box, i: int ::
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int ::
  { Seq#Rank(Seq#Drop(s, i)) }
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int ::
  { Seq#Rank(Seq#Take(s, i)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int, j: int ::
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Drop(s, n) }
  n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Take(s, n) }
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall<T> s: Seq T, m: int, n: int ::
  { Seq#Drop(Seq#Drop(s, m), n) }
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Elements<U,V>(Map U V) : [U]V;

function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall<U,V> m: Map U V ::
  { Map#Card(m) }
  Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall<U,V> m: Map U V ::
  { Map#Domain(m) }
  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));

axiom (forall<U,V> m: Map U V ::
  { Map#Values(m) }
  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));

axiom (forall<U,V> m: Map U V ::
  { Map#Items(m) }
  m == Map#Empty()
     || (exists k: Box, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U,V> m: Map U V ::
  { Set#Card(Map#Domain(m)) }
  Set#Card(Map#Domain(m)) == Map#Card(m));

axiom (forall<U,V> m: Map U V ::
  { Set#Card(Map#Values(m)) }
  Set#Card(Map#Values(m)) <= Map#Card(m));

axiom (forall<U,V> m: Map U V ::
  { Set#Card(Map#Items(m)) }
  Set#Card(Map#Items(m)) == Map#Card(m));

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V ::
  { Map#Values(m)[v] }
  Map#Values(m)[v]
     == (exists u: U ::
      { Map#Domain(m)[u] } { Map#Elements(m)[u] }
      Map#Domain(m)[u] && v == Map#Elements(m)[u]));

function Map#Items<U,V>(Map U V) : Set Box;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

function _System.Tuple2._0(DatatypeType) : Box;

function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map Box Box, item: Box ::
  { Map#Items(m)[item] }
  Map#Items(m)[item]
     <==> Map#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && Map#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

function Map#Empty<U,V>() : Map U V;

axiom (forall<U,V> u: U ::
  { Map#Domain(Map#Empty(): Map U V)[u] }
  !Map#Domain(Map#Empty(): Map U V)[u]);

function Map#Glue<U,V>([U]bool, [U]V, Ty) : Map U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall a: [Box]bool, b: [Box]Box, t0: Ty, t1: Ty ::
  { Map#Glue(a, b, TMap(t0, t1)) }
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));

function Map#Build<U,V>(Map U V, U, V) : Map U V;

axiom (forall<U,V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u
       ==> Map#Domain(Map#Build(m, u, v))[u'] && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u']
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall<U,V> m: Map U V, u: U, v: V ::
  { Map#Card(Map#Build(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall<U,V> m: Map U V, u: U, v: V ::
  { Map#Card(Map#Build(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

function Map#Merge<U,V>(Map U V, Map U V) : Map U V;

axiom (forall<U,V> m: Map U V, n: Map U V ::
  { Map#Domain(Map#Merge(m, n)) }
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

axiom (forall<U,V> m: Map U V, n: Map U V, u: U ::
  { Map#Elements(Map#Merge(m, n))[u] }
  Map#Domain(Map#Merge(m, n))[u]
     ==> (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u])
       && (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract<U,V>(Map U V, Set U) : Map U V;

axiom (forall<U,V> m: Map U V, s: Set U ::
  { Map#Domain(Map#Subtract(m, s)) }
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

axiom (forall<U,V> m: Map U V, s: Set U, u: U ::
  { Map#Elements(Map#Subtract(m, s))[u] }
  Map#Domain(Map#Subtract(m, s))[u]
     ==> Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

function Map#Equal<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V ::
  { Map#Equal(m, m') }
  Map#Equal(m, m')
     <==> (forall u: U :: Map#Domain(m)[u] == Map#Domain(m')[u])
       && (forall u: U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall<U,V> m: Map U V, m': Map U V ::
  { Map#Equal(m, m') }
  Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
  Map#Disjoint(m, m')
     <==> (forall o: U ::
      { Map#Domain(m)[o] } { Map#Domain(m')[o] }
      !Map#Domain(m)[o] || !Map#Domain(m')[o]));

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

axiom (forall<U,V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() || (exists k: U :: IMap#Domain(m)[k]));

axiom (forall<U,V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() || (exists v: V :: IMap#Values(m)[v]));

axiom (forall<U,V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty()
     || (exists k: Box, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U,V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());

axiom (forall<U,V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());

axiom (forall<U,V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V ::
  { IMap#Values(m)[v] }
  IMap#Values(m)[v]
     == (exists u: U ::
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box ::
  { IMap#Items(m)[item] }
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && IMap#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

function IMap#Empty<U,V>() : IMap U V;

axiom (forall<U,V> u: U ::
  { IMap#Domain(IMap#Empty(): IMap U V)[u] }
  !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U,V>([U]bool, [U]V, Ty) : IMap U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Domain(IMap#Glue(a, b, t)) }
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Elements(IMap#Glue(a, b, t)) }
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall a: [Box]bool, b: [Box]Box, t0: Ty, t1: Ty ::
  { IMap#Glue(a, b, TIMap(t0, t1)) }
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(Map#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

function IMap#Build<U,V>(IMap U V, U, V) : IMap U V;

axiom (forall<U,V> m: IMap U V, u: U, u': U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u'] }
    { IMap#Elements(IMap#Build(m, u, v))[u'] }
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

function IMap#Equal<U,V>(IMap U V, IMap U V) : bool;

axiom (forall<U,V> m: IMap U V, m': IMap U V ::
  { IMap#Equal(m, m') }
  IMap#Equal(m, m')
     <==> (forall u: U :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: U ::
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall<U,V> m: IMap U V, m': IMap U V ::
  { IMap#Equal(m, m') }
  IMap#Equal(m, m') ==> m == m');

function IMap#Merge<U,V>(IMap U V, IMap U V) : IMap U V;

axiom (forall<U,V> m: IMap U V, n: IMap U V ::
  { IMap#Domain(IMap#Merge(m, n)) }
  IMap#Domain(IMap#Merge(m, n)) == Set#Union(IMap#Domain(m), IMap#Domain(n)));

axiom (forall<U,V> m: IMap U V, n: IMap U V, u: U ::
  { IMap#Elements(IMap#Merge(m, n))[u] }
  IMap#Domain(IMap#Merge(m, n))[u]
     ==> (!IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u])
       && (IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract<U,V>(IMap U V, Set U) : IMap U V;

axiom (forall<U,V> m: IMap U V, s: Set U ::
  { IMap#Domain(IMap#Subtract(m, s)) }
  IMap#Domain(IMap#Subtract(m, s)) == Set#Difference(IMap#Domain(m), s));

axiom (forall<U,V> m: IMap U V, s: Set U, u: U ::
  { IMap#Elements(IMap#Subtract(m, s))[u] }
  IMap#Domain(IMap#Subtract(m, s))[u]
     ==> IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);

function INTERNAL_add_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_add_boogie(x, y): int }
  INTERNAL_add_boogie(x, y): int == x + y);

function INTERNAL_sub_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_sub_boogie(x, y): int }
  INTERNAL_sub_boogie(x, y): int == x - y);

function INTERNAL_mul_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_mul_boogie(x, y): int }
  INTERNAL_mul_boogie(x, y): int == x * y);

function INTERNAL_div_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_div_boogie(x, y): int }
  INTERNAL_div_boogie(x, y): int == x div y);

function INTERNAL_mod_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_mod_boogie(x, y): int }
  INTERNAL_mod_boogie(x, y): int == x mod y);

function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool }
  INTERNAL_lt_boogie(x, y): bool == (x < y));

function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool }
  INTERNAL_le_boogie(x, y): bool == (x <= y));

function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool }
  INTERNAL_gt_boogie(x, y): bool == (x > y));

function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool }
  INTERNAL_ge_boogie(x, y): bool == (x >= y));

function Mul(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Mul(x, y): int } Mul(x, y): int == x * y);

function Div(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Div(x, y): int } Div(x, y): int == x div y);

function Mod(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Mod(x, y): int } Mod(x, y): int == x mod y);

function Add(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Add(x, y): int } Add(x, y): int == x + y);

function Sub(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Sub(x, y): int } Sub(x, y): int == x - y);

function Tclass._System.nat() : Ty;

const unique Tagclass._System.nat: TyTag;

// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat
   && TagFamily(Tclass._System.nat()) == tytagFamily$nat;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.nat()) }
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// _System.nat: subset type $Is
axiom (forall x#0: int ::
  { $Is(x#0, Tclass._System.nat()) }
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// _System.nat: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap ::
  { $IsAlloc(x#0, Tclass._System.nat(), $h) }
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object?: ClassName;

const unique Tagclass._System.object?: TyTag;

// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?
   && TagFamily(Tclass._System.object?()) == tytagFamily$object;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.object?()) }
  $IsBox(bx, Tclass._System.object?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object?()));

// object: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._System.object?()) }
  $Is($o, Tclass._System.object?()));

// object: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._System.object?(), $h) }
  $IsAlloc($o, Tclass._System.object?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$_System.object(ty: Ty) : bool;

function Tclass._System.object() : Ty;

const unique Tagclass._System.object: TyTag;

// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object
   && TagFamily(Tclass._System.object()) == tytagFamily$object;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.object()) }
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// _System.object: non-null type $Is
axiom (forall c#0: ref ::
  { $Is(c#0, Tclass._System.object()) }
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

// _System.object: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap ::
  { $IsAlloc(c#0, Tclass._System.object(), $h) }
  $IsAlloc(c#0, Tclass._System.object(), $h)
     <==> $IsAlloc(c#0, Tclass._System.object?(), $h));

const unique class._System.array?: ClassName;

function Tclass._System.array?(Ty) : Ty;

const unique Tagclass._System.array?: TyTag;

// Tclass._System.array? Tag
axiom (forall _System.array$arg: Ty ::
  { Tclass._System.array?(_System.array$arg) }
  Tag(Tclass._System.array?(_System.array$arg)) == Tagclass._System.array?
     && TagFamily(Tclass._System.array?(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array?_0(Ty) : Ty;

// Tclass._System.array? injectivity 0
axiom (forall _System.array$arg: Ty ::
  { Tclass._System.array?(_System.array$arg) }
  Tclass._System.array?_0(Tclass._System.array?(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array?
axiom (forall _System.array$arg: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.array?(_System.array$arg)) }
  $IsBox(bx, Tclass._System.array?(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array?(_System.array$arg)));

// array.: Type axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int ::
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       &&
      0 <= $i0
       && $i0 < _System.array.Length($o)
     ==> $IsBox(read($h, $o, IndexField($i0)), _System.array$arg));

// array.: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int ::
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       &&
      0 <= $i0
       && $i0 < _System.array.Length($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, IndexField($i0)), _System.array$arg, $h));

// array: Class $Is
axiom (forall _System.array$arg: Ty, $o: ref ::
  { $Is($o, Tclass._System.array?(_System.array$arg)) }
  $Is($o, Tclass._System.array?(_System.array$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(_System.array$arg));

// array: Class $IsAlloc
axiom (forall _System.array$arg: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h) }
  $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h)
     <==> $o == null || read($h, $o, alloc));

// array.Length: Type axiom
axiom (forall _System.array$arg: Ty, $o: ref ::
  { _System.array.Length($o), Tclass._System.array?(_System.array$arg) }
  $o != null && dtype($o) == Tclass._System.array?(_System.array$arg)
     ==> $Is(_System.array.Length($o), TInt));

// array.Length: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref ::
  { _System.array.Length($o), read($h, $o, alloc), Tclass._System.array?(_System.array$arg) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array.Length($o), TInt, $h));

function Tclass._System.array(Ty) : Ty;

const unique Tagclass._System.array: TyTag;

// Tclass._System.array Tag
axiom (forall _System.array$arg: Ty ::
  { Tclass._System.array(_System.array$arg) }
  Tag(Tclass._System.array(_System.array$arg)) == Tagclass._System.array
     && TagFamily(Tclass._System.array(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array_0(Ty) : Ty;

// Tclass._System.array injectivity 0
axiom (forall _System.array$arg: Ty ::
  { Tclass._System.array(_System.array$arg) }
  Tclass._System.array_0(Tclass._System.array(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array
axiom (forall _System.array$arg: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.array(_System.array$arg)) }
  $IsBox(bx, Tclass._System.array(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array(_System.array$arg)));

// _System.array: non-null type $Is
axiom (forall _System.array$arg: Ty, c#0: ref ::
  { $Is(c#0, Tclass._System.array(_System.array$arg)) }
  $Is(c#0, Tclass._System.array(_System.array$arg))
     <==> $Is(c#0, Tclass._System.array?(_System.array$arg)) && c#0 != null);

// _System.array: non-null type $IsAlloc
axiom (forall _System.array$arg: Ty, c#0: ref, $h: Heap ::
  { $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h) }
  $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array?(_System.array$arg), $h));

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc1: TyTag;

// Tclass._System.___hFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hFunc1(#$T0, #$R) }
  Tag(Tclass._System.___hFunc1(#$T0, #$R)) == Tagclass._System.___hFunc1
     && TagFamily(Tclass._System.___hFunc1(#$T0, #$R)) == tytagFamily$_#Func1);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hFunc1(#$T0, #$R) }
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hFunc1(#$T0, #$R) }
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set Box) : HandleType;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    heap: Heap,
    h: [Heap,Box]Box,
    r: [Heap,Box]bool,
    rd: [Heap,Box]Set Box,
    bx0: Box ::
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) }
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty,
    t1: Ty,
    heap: Heap,
    h: [Heap,Box]Box,
    r: [Heap,Box]bool,
    rd: [Heap,Box]Set Box,
    bx0: Box ::
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) }
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty,
    t1: Ty,
    heap: Heap,
    h: [Heap,Box]Box,
    r: [Heap,Box]bool,
    rd: [Heap,Box]Set Box,
    bx0: Box,
    bx: Box ::
  { Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] }
  Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] == rd[heap, bx0][bx]);

function {:inline} Requires1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

function {:inline} Reads1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box ::
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) }
    { Reads1(t0, t1, heap, f, bx0) }
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set Box)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box ::
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) }
    { Requires1(t0, t1, heap, f, bx0) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
     ==> Requires1(t0, t1, $OneHeap, f, bx0) == Requires1(t0, t1, heap, f, bx0));

axiom (forall f: HandleType, t0: Ty, t1: Ty ::
  { $Is(f, Tclass._System.___hFunc1(t0, t1)) }
  $Is(f, Tclass._System.___hFunc1(t0, t1))
     <==> (forall h: Heap, bx0: Box ::
      { Apply1(t0, t1, h, f, bx0) }
      $IsGoodHeap(h) && $IsBox(bx0, t0) && Requires1(t0, t1, h, f, bx0)
         ==> $IsBox(Apply1(t0, t1, h, f, bx0), t1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty ::
  { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) }
  $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall bx: Box ::
        { $IsBox(bx, u0) } { $IsBox(bx, t0) }
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box ::
        { $IsBox(bx, t1) } { $IsBox(bx, u1) }
        $IsBox(bx, t1) ==> $IsBox(bx, u1))
     ==> $Is(f, Tclass._System.___hFunc1(u0, u1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
       <==> (forall bx0: Box ::
        { Apply1(t0, t1, h, f, bx0) } { Reads1(t0, t1, h, f, bx0) }
        $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
           ==> (forall r: ref ::
            { Reads1(t0, t1, h, f, bx0)[$Box(r)] }
            r != null && Reads1(t0, t1, h, f, bx0)[$Box(r)] ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
     ==> (forall bx0: Box ::
      { Apply1(t0, t1, h, f, bx0) }
      $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
         ==> $IsAllocBox(Apply1(t0, t1, h, f, bx0), t1, h)));

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc1: TyTag;

// Tclass._System.___hPartialFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc1(#$T0, #$R) }
  Tag(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == Tagclass._System.___hPartialFunc1
     && TagFamily(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == tytagFamily$_#PartialFunc1);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc1(#$T0, #$R) }
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc1(#$T0, #$R) }
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// _System._#PartialFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box ::
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set Box)));

// _System._#PartialFunc1: subset type $IsAlloc
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc1(#$T0, #$R), $h));

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc1: TyTag;

// Tclass._System.___hTotalFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc1(#$T0, #$R) }
  Tag(Tclass._System.___hTotalFunc1(#$T0, #$R)) == Tagclass._System.___hTotalFunc1
     && TagFamily(Tclass._System.___hTotalFunc1(#$T0, #$R)) == tytagFamily$_#TotalFunc1);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc1(#$T0, #$R) }
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc1(#$T0, #$R) }
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// _System._#TotalFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && (forall x0#0: Box ::
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

// _System._#TotalFunc1: subset type $IsAlloc
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h));

function Tclass._System.___hFunc0(Ty) : Ty;

const unique Tagclass._System.___hFunc0: TyTag;

// Tclass._System.___hFunc0 Tag
axiom (forall #$R: Ty ::
  { Tclass._System.___hFunc0(#$R) }
  Tag(Tclass._System.___hFunc0(#$R)) == Tagclass._System.___hFunc0
     && TagFamily(Tclass._System.___hFunc0(#$R)) == tytagFamily$_#Func0);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty ::
  { Tclass._System.___hFunc0(#$R) }
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) }
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set Box) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set Box;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box ::
  { Apply0(t0, heap, Handle0(h, r, rd)) }
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box ::
  { Requires0(t0, heap, Handle0(h, r, rd)) }
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box, bx: Box ::
  { Reads0(t0, heap, Handle0(h, r, rd))[bx] }
  Reads0(t0, heap, Handle0(h, r, rd))[bx] == rd[heap][bx]);

function {:inline} Requires0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

function {:inline} Reads0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0
axiom (forall t0: Ty, heap: Heap, f: HandleType ::
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) }
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set Box)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType ::
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) }
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
     ==> Requires0(t0, $OneHeap, f) == Requires0(t0, heap, f));

axiom (forall f: HandleType, t0: Ty ::
  { $Is(f, Tclass._System.___hFunc0(t0)) }
  $Is(f, Tclass._System.___hFunc0(t0))
     <==> (forall h: Heap ::
      { Apply0(t0, h, f) }
      $IsGoodHeap(h) && Requires0(t0, h, f) ==> $IsBox(Apply0(t0, h, f), t0)));

axiom (forall f: HandleType, t0: Ty, u0: Ty ::
  { $Is(f, Tclass._System.___hFunc0(t0)), $Is(f, Tclass._System.___hFunc0(u0)) }
  $Is(f, Tclass._System.___hFunc0(t0))
       && (forall bx: Box ::
        { $IsBox(bx, t0) } { $IsBox(bx, u0) }
        $IsBox(bx, t0) ==> $IsBox(bx, u0))
     ==> $Is(f, Tclass._System.___hFunc0(u0)));

axiom (forall f: HandleType, t0: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc0(t0), h)
       <==> Requires0(t0, h, f)
         ==> (forall r: ref ::
          { Reads0(t0, h, f)[$Box(r)] }
          r != null && Reads0(t0, h, f)[$Box(r)] ==> read(h, r, alloc))));

axiom (forall f: HandleType, t0: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc0(t0), h)
     ==>
    Requires0(t0, h, f)
     ==> $IsAllocBox(Apply0(t0, h, f), t0, h));

function Tclass._System.___hPartialFunc0(Ty) : Ty;

const unique Tagclass._System.___hPartialFunc0: TyTag;

// Tclass._System.___hPartialFunc0 Tag
axiom (forall #$R: Ty ::
  { Tclass._System.___hPartialFunc0(#$R) }
  Tag(Tclass._System.___hPartialFunc0(#$R)) == Tagclass._System.___hPartialFunc0
     && TagFamily(Tclass._System.___hPartialFunc0(#$R)) == tytagFamily$_#PartialFunc0);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty ::
  { Tclass._System.___hPartialFunc0(#$R) }
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// _System._#PartialFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set Box));

// _System._#PartialFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc0(#$R), $h));

function Tclass._System.___hTotalFunc0(Ty) : Ty;

const unique Tagclass._System.___hTotalFunc0: TyTag;

// Tclass._System.___hTotalFunc0 Tag
axiom (forall #$R: Ty ::
  { Tclass._System.___hTotalFunc0(#$R) }
  Tag(Tclass._System.___hTotalFunc0(#$R)) == Tagclass._System.___hTotalFunc0
     && TagFamily(Tclass._System.___hTotalFunc0(#$R)) == tytagFamily$_#TotalFunc0);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty ::
  { Tclass._System.___hTotalFunc0(#$R) }
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// _System._#TotalFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) && Requires0(#$R, $OneHeap, f#0));

// _System._#TotalFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box ::
  { #_System._tuple#2._#Make2(a#0#0#0, a#0#1#0) }
  DatatypeCtorId(#_System._tuple#2._#Make2(a#0#0#0, a#0#1#0))
     == ##_System._tuple#2._#Make2);

const unique ##_System._tuple#2._#Make2: DtCtorId;

function _System.Tuple2.___hMake2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _System.Tuple2.___hMake2_q(d) }
  _System.Tuple2.___hMake2_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#2._#Make2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _System.Tuple2.___hMake2_q(d) }
  _System.Tuple2.___hMake2_q(d)
     ==> (exists a#1#0#0: Box, a#1#1#0: Box ::
      d == #_System._tuple#2._#Make2(a#1#0#0, a#1#1#0)));

const unique Tagclass._System.Tuple2: TyTag;

// Tclass._System.Tuple2 Tag
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty ::
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) }
  Tag(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == Tagclass._System.Tuple2
     && TagFamily(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == tytagFamily$_tuple#2);

function Tclass._System.Tuple2_0(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 0
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty ::
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) }
  Tclass._System.Tuple2_0(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T0);

function Tclass._System.Tuple2_1(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 1
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty ::
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) }
  Tclass._System.Tuple2_1(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T1);

// Box/unbox axiom for Tclass._System.Tuple2
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) }
  $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType,
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)));

// Constructor $Is
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#2#0#0: Box, a#2#1#0: Box ::
  { $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0),
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) }
  $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0),
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#2#0#0, _System._tuple#2$T0) && $IsBox(a#2#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty,
    _System._tuple#2$T1: Ty,
    a#2#0#0: Box,
    a#2#1#0: Box,
    $h: Heap ::
  { $IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0),
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1),
      $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0),
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1),
        $h)
       <==> $IsAllocBox(a#2#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#2#1#0, _System._tuple#2$T1, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T0: Ty, $h: Heap ::
  { $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h) }
  $IsGoodHeap($h)
       &&
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T1: Ty ::
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) }
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T1: Ty, $h: Heap ::
  { $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h) }
  $IsGoodHeap($h)
       &&
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T0: Ty ::
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) }
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h));

// Constructor literal
axiom (forall a#3#0#0: Box, a#3#1#0: Box ::
  { #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0)) }
  #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0))
     == Lit(#_System._tuple#2._#Make2(a#3#0#0, a#3#1#0)));

// Constructor injectivity
axiom (forall a#4#0#0: Box, a#4#1#0: Box ::
  { #_System._tuple#2._#Make2(a#4#0#0, a#4#1#0) }
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#4#0#0, a#4#1#0)) == a#4#0#0);

// Inductive rank
axiom (forall a#5#0#0: Box, a#5#1#0: Box ::
  { #_System._tuple#2._#Make2(a#5#0#0, a#5#1#0) }
  BoxRank(a#5#0#0) < DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)));

// Constructor injectivity
axiom (forall a#6#0#0: Box, a#6#1#0: Box ::
  { #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0) }
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)) == a#6#1#0);

// Inductive rank
axiom (forall a#7#0#0: Box, a#7#1#0: Box ::
  { #_System._tuple#2._#Make2(a#7#0#0, a#7#1#0) }
  BoxRank(a#7#1#0) < DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)));

// Depth-one case-split function
function $IsA#_System.Tuple2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_System.Tuple2(d) }
  $IsA#_System.Tuple2(d) ==> _System.Tuple2.___hMake2_q(d));

// Questionmark data type disjunctivity
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, d: DatatypeType ::
  { _System.Tuple2.___hMake2_q(d), $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) }
  $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> _System.Tuple2.___hMake2_q(d));

// Datatype extensional equality declaration
function _System.Tuple2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#2._#Make2
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _System.Tuple2#Equal(a, b) }
  true
     ==> (_System.Tuple2#Equal(a, b)
       <==> _System.Tuple2._0(a) == _System.Tuple2._0(b)
         && _System.Tuple2._1(a) == _System.Tuple2._1(b)));

// Datatype extensionality axiom: _System._tuple#2
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _System.Tuple2#Equal(a, b) }
  _System.Tuple2#Equal(a, b) <==> a == b);

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType;

// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;

const unique ##_System._tuple#0._#Make0: DtCtorId;

function _System.Tuple0.___hMake0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _System.Tuple0.___hMake0_q(d) }
  _System.Tuple0.___hMake0_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#0._#Make0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _System.Tuple0.___hMake0_q(d) }
  _System.Tuple0.___hMake0_q(d) ==> d == #_System._tuple#0._#Make0());

function Tclass._System.Tuple0() : Ty;

const unique Tagclass._System.Tuple0: TyTag;

// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0
   && TagFamily(Tclass._System.Tuple0()) == tytagFamily$_tuple#0;

// Box/unbox axiom for Tclass._System.Tuple0
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.Tuple0()) }
  $IsBox(bx, Tclass._System.Tuple0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple0()));

// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.Tuple0(), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.Tuple0(), $h));

// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());

// Depth-one case-split function
function $IsA#_System.Tuple0(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_System.Tuple0(d) }
  $IsA#_System.Tuple0(d) ==> _System.Tuple0.___hMake0_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _System.Tuple0.___hMake0_q(d), $Is(d, Tclass._System.Tuple0()) }
  $Is(d, Tclass._System.Tuple0()) ==> _System.Tuple0.___hMake0_q(d));

// Datatype extensional equality declaration
function _System.Tuple0#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#0._#Make0
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _System.Tuple0#Equal(a, b) }
  true ==> (_System.Tuple0#Equal(a, b) <==> true));

// Datatype extensionality axiom: _System._tuple#0
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _System.Tuple0#Equal(a, b) }
  _System.Tuple0#Equal(a, b) <==> a == b);

const unique class._System.Tuple0: ClassName;

const unique class._module.Composite?: ClassName;

function Tclass._module.Composite?() : Ty;

const unique Tagclass._module.Composite?: TyTag;

// Tclass._module.Composite? Tag
axiom Tag(Tclass._module.Composite?()) == Tagclass._module.Composite?
   && TagFamily(Tclass._module.Composite?()) == tytagFamily$Composite;

// Box/unbox axiom for Tclass._module.Composite?
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Composite?()) }
  $IsBox(bx, Tclass._module.Composite?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Composite?()));

// Composite: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.Composite?()) }
  $Is($o, Tclass._module.Composite?())
     <==> $o == null || dtype($o) == Tclass._module.Composite?());

// Composite: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Composite?(), $h) }
  $IsAlloc($o, Tclass._module.Composite?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Composite.left) == 0
   && FieldOfDecl(class._module.Composite?, field$left) == _module.Composite.left
   && !$IsGhostField(_module.Composite.left);

const _module.Composite.left: Field ref;

// Composite.left: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.left) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Composite?()
     ==> $Is(read($h, $o, _module.Composite.left), Tclass._module.Composite?()));

// Composite.left: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.left) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Composite?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Composite.left), Tclass._module.Composite?(), $h));

axiom FDim(_module.Composite.right) == 0
   && FieldOfDecl(class._module.Composite?, field$right) == _module.Composite.right
   && !$IsGhostField(_module.Composite.right);

const _module.Composite.right: Field ref;

// Composite.right: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.right) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Composite?()
     ==> $Is(read($h, $o, _module.Composite.right), Tclass._module.Composite?()));

// Composite.right: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.right) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Composite?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Composite.right), Tclass._module.Composite?(), $h));

axiom FDim(_module.Composite.parent) == 0
   && FieldOfDecl(class._module.Composite?, field$parent) == _module.Composite.parent
   && !$IsGhostField(_module.Composite.parent);

const _module.Composite.parent: Field ref;

// Composite.parent: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.parent) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Composite?()
     ==> $Is(read($h, $o, _module.Composite.parent), Tclass._module.Composite?()));

// Composite.parent: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.parent) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Composite?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Composite.parent), Tclass._module.Composite?(), $h));

axiom FDim(_module.Composite.val) == 0
   && FieldOfDecl(class._module.Composite?, field$val) == _module.Composite.val
   && !$IsGhostField(_module.Composite.val);

const _module.Composite.val: Field int;

// Composite.val: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.val) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Composite?()
     ==> $Is(read($h, $o, _module.Composite.val), TInt));

// Composite.val: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.val) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Composite?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Composite.val), TInt, $h));

axiom FDim(_module.Composite.sum) == 0
   && FieldOfDecl(class._module.Composite?, field$sum) == _module.Composite.sum
   && !$IsGhostField(_module.Composite.sum);

const _module.Composite.sum: Field int;

// Composite.sum: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.sum) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Composite?()
     ==> $Is(read($h, $o, _module.Composite.sum), TInt));

// Composite.sum: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Composite.sum) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Composite?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Composite.sum), TInt, $h));

// function declaration for _module.Composite.Valid
function _module.Composite.Valid($heap: Heap, this: ref, S#0: Set Box) : bool;

function _module.Composite.Valid#canCall($heap: Heap, this: ref, S#0: Set Box) : bool;

function Tclass._module.Composite() : Ty;

const unique Tagclass._module.Composite: TyTag;

// Tclass._module.Composite Tag
axiom Tag(Tclass._module.Composite()) == Tagclass._module.Composite
   && TagFamily(Tclass._module.Composite()) == tytagFamily$Composite;

// Box/unbox axiom for Tclass._module.Composite
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Composite()) }
  $IsBox(bx, Tclass._module.Composite())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Composite()));

// frame axiom for _module.Composite.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref, S#0: Set Box ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Composite.Valid($h1, this, S#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.Composite())
       && (_module.Composite.Valid#canCall($h0, this, S#0)
         || $Is(S#0, TSet(Tclass._module.Composite())))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && (
            $o == this
             || $o == read($h0, this, _module.Composite.parent)
             || $o == read($h0, this, _module.Composite.left)
             || $o == read($h0, this, _module.Composite.right))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Composite.Valid($h0, this, S#0)
       == _module.Composite.Valid($h1, this, S#0));

// consequence axiom for _module.Composite.Valid
axiom 1 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, S#0: Set Box ::
    { _module.Composite.Valid($Heap, this, S#0) }
    _module.Composite.Valid#canCall($Heap, this, S#0)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Composite())
           && $IsAlloc(this, Tclass._module.Composite(), $Heap)
           && $Is(S#0, TSet(Tclass._module.Composite())))
       ==> true);

function _module.Composite.Valid#requires(Heap, ref, Set Box) : bool;

// #requires axiom for _module.Composite.Valid
axiom (forall $Heap: Heap, this: ref, S#0: Set Box ::
  { _module.Composite.Valid#requires($Heap, this, S#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.Composite())
       && $IsAlloc(this, Tclass._module.Composite(), $Heap)
       && $Is(S#0, TSet(Tclass._module.Composite()))
     ==> _module.Composite.Valid#requires($Heap, this, S#0) == true);

// definition axiom for _module.Composite.Valid (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, S#0: Set Box ::
    { _module.Composite.Valid($Heap, this, S#0), $IsGoodHeap($Heap) }
    _module.Composite.Valid#canCall($Heap, this, S#0)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Composite())
           && $IsAlloc(this, Tclass._module.Composite(), $Heap)
           && $Is(S#0, TSet(Tclass._module.Composite())))
       ==> _module.Composite.Valid($Heap, this, S#0)
         == (
          S#0[$Box(this)]
           && (read($Heap, this, _module.Composite.parent) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.parent))]
               && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                   == this
                 || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
                   == this))
           && (read($Heap, this, _module.Composite.left) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.left))]
               && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
                 == this
               && read($Heap, this, _module.Composite.left)
                 != read($Heap, this, _module.Composite.right))
           && (read($Heap, this, _module.Composite.right) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.right))]
               && read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
                 == this
               && read($Heap, this, _module.Composite.left)
                 != read($Heap, this, _module.Composite.right))
           && read($Heap, this, _module.Composite.sum)
             == read($Heap, this, _module.Composite.val)
               + (if read($Heap, this, _module.Composite.left) == null
                 then 0
                 else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
               + (if read($Heap, this, _module.Composite.right) == null
                 then 0
                 else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum))));

procedure {:verboseName "Composite.Valid (well-formedness)"} CheckWellformed$$_module.Composite.Valid(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box where $Is(S#0, TSet(Tclass._module.Composite())));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Composite.Valid (well-formedness)"} CheckWellformed$$_module.Composite.Valid(this: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var newtype$check#0: ref;
  var newtype$check#1: ref;
  var newtype$check#2: ref;
  var newtype$check#3: ref;
  var newtype$check#4: ref;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;
  var b$reqreads#7: bool;
  var b$reqreads#8: bool;
  var b$reqreads#9: bool;
  var b$reqreads#10: bool;
  var b$reqreads#11: bool;
  var b$reqreads#12: bool;
  var b$reqreads#13: bool;
  var b$reqreads#14: bool;
  var b$reqreads#15: bool;
  var b$reqreads#16: bool;
  var b$reqreads#17: bool;
  var b$reqreads#18: bool;
  var b$reqreads#19: bool;
  var b$reqreads#20: bool;
  var b$reqreads#21: bool;
  var b$reqreads#22: bool;
  var b$reqreads#23: bool;
  var b$reqreads#24: bool;
  var b$reqreads#25: bool;
  var b$reqreads#26: bool;
  var b$reqreads#27: bool;
  var b$reqreads#28: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;
    b$reqreads#7 := true;
    b$reqreads#8 := true;
    b$reqreads#9 := true;
    b$reqreads#10 := true;
    b$reqreads#11 := true;
    b$reqreads#12 := true;
    b$reqreads#13 := true;
    b$reqreads#14 := true;
    b$reqreads#15 := true;
    b$reqreads#16 := true;
    b$reqreads#17 := true;
    b$reqreads#18 := true;
    b$reqreads#19 := true;
    b$reqreads#20 := true;
    b$reqreads#21 := true;
    b$reqreads#22 := true;
    b$reqreads#23 := true;
    b$reqreads#24 := true;
    b$reqreads#25 := true;
    b$reqreads#26 := true;
    b$reqreads#27 := true;
    b$reqreads#28 := true;

    // AddWellformednessCheck for function Valid
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || $o == read($Heap, this, _module.Composite.parent)
           || $o == read($Heap, this, _module.Composite.left)
           || $o == read($Heap, this, _module.Composite.right));
    b$reqreads#0 := $_Frame[this, _module.Composite.parent];
    b$reqreads#1 := $_Frame[this, _module.Composite.left];
    b$reqreads#2 := $_Frame[this, _module.Composite.right];
    assert b$reqreads#0;
    assert b$reqreads#1;
    assert b$reqreads#2;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this
               || $o == read($Heap, this, _module.Composite.parent)
               || $o == read($Heap, this, _module.Composite.left)
               || $o == read($Heap, this, _module.Composite.right));
        if (S#0[$Box(this)])
        {
            b$reqreads#3 := $_Frame[this, _module.Composite.parent];
            newtype$check#0 := null;
            if (read($Heap, this, _module.Composite.parent) != null)
            {
                b$reqreads#4 := $_Frame[this, _module.Composite.parent];
                if (S#0[$Box(read($Heap, this, _module.Composite.parent))])
                {
                    b$reqreads#5 := $_Frame[this, _module.Composite.parent];
                    assert read($Heap, this, _module.Composite.parent) != null;
                    b$reqreads#6 := $_Frame[read($Heap, this, _module.Composite.parent), _module.Composite.left];
                    if (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                       != this)
                    {
                        b$reqreads#7 := $_Frame[this, _module.Composite.parent];
                        assert read($Heap, this, _module.Composite.parent) != null;
                        b$reqreads#8 := $_Frame[read($Heap, this, _module.Composite.parent), _module.Composite.right];
                    }
                }
            }
        }

        if (S#0[$Box(this)]
           && (read($Heap, this, _module.Composite.parent) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.parent))]
               && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                   == this
                 || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
                   == this)))
        {
            b$reqreads#9 := $_Frame[this, _module.Composite.left];
            newtype$check#1 := null;
            if (read($Heap, this, _module.Composite.left) != null)
            {
                b$reqreads#10 := $_Frame[this, _module.Composite.left];
                if (S#0[$Box(read($Heap, this, _module.Composite.left))])
                {
                    b$reqreads#11 := $_Frame[this, _module.Composite.left];
                    assert read($Heap, this, _module.Composite.left) != null;
                    b$reqreads#12 := $_Frame[read($Heap, this, _module.Composite.left), _module.Composite.parent];
                }

                if (S#0[$Box(read($Heap, this, _module.Composite.left))]
                   && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
                     == this)
                {
                    b$reqreads#13 := $_Frame[this, _module.Composite.left];
                    b$reqreads#14 := $_Frame[this, _module.Composite.right];
                }
            }
        }

        if (S#0[$Box(this)]
           && (read($Heap, this, _module.Composite.parent) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.parent))]
               && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                   == this
                 || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
                   == this))
           && (read($Heap, this, _module.Composite.left) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.left))]
               && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
                 == this
               && read($Heap, this, _module.Composite.left)
                 != read($Heap, this, _module.Composite.right)))
        {
            b$reqreads#15 := $_Frame[this, _module.Composite.right];
            newtype$check#2 := null;
            if (read($Heap, this, _module.Composite.right) != null)
            {
                b$reqreads#16 := $_Frame[this, _module.Composite.right];
                if (S#0[$Box(read($Heap, this, _module.Composite.right))])
                {
                    b$reqreads#17 := $_Frame[this, _module.Composite.right];
                    assert read($Heap, this, _module.Composite.right) != null;
                    b$reqreads#18 := $_Frame[read($Heap, this, _module.Composite.right), _module.Composite.parent];
                }

                if (S#0[$Box(read($Heap, this, _module.Composite.right))]
                   && read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
                     == this)
                {
                    b$reqreads#19 := $_Frame[this, _module.Composite.left];
                    b$reqreads#20 := $_Frame[this, _module.Composite.right];
                }
            }
        }

        if (S#0[$Box(this)]
           && (read($Heap, this, _module.Composite.parent) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.parent))]
               && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                   == this
                 || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
                   == this))
           && (read($Heap, this, _module.Composite.left) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.left))]
               && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
                 == this
               && read($Heap, this, _module.Composite.left)
                 != read($Heap, this, _module.Composite.right))
           && (read($Heap, this, _module.Composite.right) != null
             ==> S#0[$Box(read($Heap, this, _module.Composite.right))]
               && read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
                 == this
               && read($Heap, this, _module.Composite.left)
                 != read($Heap, this, _module.Composite.right)))
        {
            b$reqreads#21 := $_Frame[this, _module.Composite.sum];
            b$reqreads#22 := $_Frame[this, _module.Composite.val];
            b$reqreads#23 := $_Frame[this, _module.Composite.left];
            newtype$check#3 := null;
            if (read($Heap, this, _module.Composite.left) == null)
            {
            }
            else
            {
                b$reqreads#24 := $_Frame[this, _module.Composite.left];
                assert read($Heap, this, _module.Composite.left) != null;
                b$reqreads#25 := $_Frame[read($Heap, this, _module.Composite.left), _module.Composite.sum];
            }

            b$reqreads#26 := $_Frame[this, _module.Composite.right];
            newtype$check#4 := null;
            if (read($Heap, this, _module.Composite.right) == null)
            {
            }
            else
            {
                b$reqreads#27 := $_Frame[this, _module.Composite.right];
                assert read($Heap, this, _module.Composite.right) != null;
                b$reqreads#28 := $_Frame[read($Heap, this, _module.Composite.right), _module.Composite.sum];
            }
        }

        assume _module.Composite.Valid($Heap, this, S#0)
           == (
            S#0[$Box(this)]
             && (read($Heap, this, _module.Composite.parent) != null
               ==> S#0[$Box(read($Heap, this, _module.Composite.parent))]
                 && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                     == this
                   || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
                     == this))
             && (read($Heap, this, _module.Composite.left) != null
               ==> S#0[$Box(read($Heap, this, _module.Composite.left))]
                 && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
                   == this
                 && read($Heap, this, _module.Composite.left)
                   != read($Heap, this, _module.Composite.right))
             && (read($Heap, this, _module.Composite.right) != null
               ==> S#0[$Box(read($Heap, this, _module.Composite.right))]
                 && read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
                   == this
                 && read($Heap, this, _module.Composite.left)
                   != read($Heap, this, _module.Composite.right))
             && read($Heap, this, _module.Composite.sum)
               == read($Heap, this, _module.Composite.val)
                 + (if read($Heap, this, _module.Composite.left) == null
                   then 0
                   else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
                 + (if read($Heap, this, _module.Composite.right) == null
                   then 0
                   else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum)));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Composite.Valid($Heap, this, S#0), TBool);
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
        assert b$reqreads#10;
        assert b$reqreads#11;
        assert b$reqreads#12;
        assert b$reqreads#13;
        assert b$reqreads#14;
        assert b$reqreads#15;
        assert b$reqreads#16;
        assert b$reqreads#17;
        assert b$reqreads#18;
        assert b$reqreads#19;
        assert b$reqreads#20;
        assert b$reqreads#21;
        assert b$reqreads#22;
        assert b$reqreads#23;
        assert b$reqreads#24;
        assert b$reqreads#25;
        assert b$reqreads#26;
        assert b$reqreads#27;
        assert b$reqreads#28;
    }
}



// function declaration for _module.Composite.Acyclic
function _module.Composite.Acyclic($ly: LayerType, $heap: Heap, this: ref, S#0: Set Box) : bool;

function _module.Composite.Acyclic#canCall($heap: Heap, this: ref, S#0: Set Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, S#0: Set Box ::
  { _module.Composite.Acyclic($LS($ly), $Heap, this, S#0) }
  _module.Composite.Acyclic($LS($ly), $Heap, this, S#0)
     == _module.Composite.Acyclic($ly, $Heap, this, S#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, S#0: Set Box ::
  { _module.Composite.Acyclic(AsFuelBottom($ly), $Heap, this, S#0) }
  _module.Composite.Acyclic($ly, $Heap, this, S#0)
     == _module.Composite.Acyclic($LZ, $Heap, this, S#0));

// frame axiom for _module.Composite.Acyclic
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, S#0: Set Box ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Composite.Acyclic($ly, $h1, this, S#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.Composite())
       && (_module.Composite.Acyclic#canCall($h0, this, S#0)
         || $Is(S#0, TSet(Tclass._module.Composite())))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && S#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Composite.Acyclic($ly, $h0, this, S#0)
       == _module.Composite.Acyclic($ly, $h1, this, S#0));

// consequence axiom for _module.Composite.Acyclic
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, S#0: Set Box ::
    { _module.Composite.Acyclic($ly, $Heap, this, S#0) }
    _module.Composite.Acyclic#canCall($Heap, this, S#0)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Composite())
           && $IsAlloc(this, Tclass._module.Composite(), $Heap)
           && $Is(S#0, TSet(Tclass._module.Composite())))
       ==> true);

function _module.Composite.Acyclic#requires(LayerType, Heap, ref, Set Box) : bool;

// #requires axiom for _module.Composite.Acyclic
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, S#0: Set Box ::
  { _module.Composite.Acyclic#requires($ly, $Heap, this, S#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.Composite())
       && $IsAlloc(this, Tclass._module.Composite(), $Heap)
       && $Is(S#0, TSet(Tclass._module.Composite()))
     ==> _module.Composite.Acyclic#requires($ly, $Heap, this, S#0) == true);

// definition axiom for _module.Composite.Acyclic (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, S#0: Set Box ::
    { _module.Composite.Acyclic($LS($ly), $Heap, this, S#0), $IsGoodHeap($Heap) }
    _module.Composite.Acyclic#canCall($Heap, this, S#0)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Composite())
           && $IsAlloc(this, Tclass._module.Composite(), $Heap)
           && $Is(S#0, TSet(Tclass._module.Composite())))
       ==> (S#0[$Box(this)]
           ==>
          read($Heap, this, _module.Composite.parent) != null
           ==> _module.Composite.Acyclic#canCall($Heap,
            read($Heap, this, _module.Composite.parent),
            Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))))
         && _module.Composite.Acyclic($LS($ly), $Heap, this, S#0)
           == (S#0[$Box(this)]
             && (read($Heap, this, _module.Composite.parent) != null
               ==> _module.Composite.Acyclic($ly,
                $Heap,
                read($Heap, this, _module.Composite.parent),
                Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))))));

procedure {:verboseName "Composite.Acyclic (well-formedness)"} CheckWellformed$$_module.Composite.Acyclic(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box where $Is(S#0, TSet(Tclass._module.Composite())));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Composite.Acyclic (well-formedness)"} CheckWellformed$$_module.Composite.Acyclic(this: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: ref;
  var ##S#0: Set Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Acyclic
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
        if (S#0[$Box(this)])
        {
            b$reqreads#0 := $_Frame[this, _module.Composite.parent];
            newtype$check#0 := null;
            if (read($Heap, this, _module.Composite.parent) != null)
            {
                b$reqreads#1 := $_Frame[this, _module.Composite.parent];
                assert read($Heap, this, _module.Composite.parent) != null;
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(read($Heap, this, _module.Composite.parent), Tclass._module.Composite?(), $Heap);
                ##S#0 := Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##S#0, TSet(Tclass._module.Composite()), $Heap);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha ::
                  $o != null && read($Heap, $o, alloc) && ##S#0[$Box($o)] ==> $_Frame[$o, $f]);
                assert (Set#Subset(##S#0, S#0) && !Set#Subset(S#0, ##S#0))
                   || (Set#Equal(##S#0, S#0) && Set#Subset(##S#0, S#0) && !Set#Subset(S#0, ##S#0));
                assume _module.Composite.Acyclic#canCall($Heap,
                  read($Heap, this, _module.Composite.parent),
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))));
            }
        }

        assume _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
           == (S#0[$Box(this)]
             && (read($Heap, this, _module.Composite.parent) != null
               ==> _module.Composite.Acyclic($LS($LZ),
                $Heap,
                read($Heap, this, _module.Composite.parent),
                Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))))));
        assume S#0[$Box(this)]
           ==>
          read($Heap, this, _module.Composite.parent) != null
           ==> _module.Composite.Acyclic#canCall($Heap,
            read($Heap, this, _module.Composite.parent),
            Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Composite.Acyclic($LS($LZ), $Heap, this, S#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



procedure {:verboseName "Composite.Init (well-formedness)"} CheckWellFormed$$_module.Composite.Init(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    x#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Composite.Init (call)"} Call$$_module.Composite.Init(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    x#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     && (_module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       ==> _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this))));
  free ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     &&
    _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     &&
    Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(read($Heap, this, _module.Composite.parent))]
         && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
             == this
           || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
             == this))
     && (read($Heap, this, _module.Composite.left) != null
       ==> Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(read($Heap, this, _module.Composite.left))]
         && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
           == this
         && read($Heap, this, _module.Composite.left)
           != read($Heap, this, _module.Composite.right))
     && (read($Heap, this, _module.Composite.right) != null
       ==> Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(read($Heap, this, _module.Composite.right))]
         && read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
           == this
         && read($Heap, this, _module.Composite.left)
           != read($Heap, this, _module.Composite.right))
     && read($Heap, this, _module.Composite.sum)
       == read($Heap, this, _module.Composite.val)
         + (if read($Heap, this, _module.Composite.left) == null
           then 0
           else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
         + (if read($Heap, this, _module.Composite.right) == null
           then 0
           else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum));
  free ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     &&
    _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     &&
    Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> _module.Composite.Acyclic($LS($LZ),
        $Heap,
        read($Heap, this, _module.Composite.parent),
        Set#Difference(Set#UnionOne(Set#Empty(): Set Box, $Box(this)),
          Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  ensures read($Heap, this, _module.Composite.val) == x#0;
  ensures read($Heap, this, _module.Composite.parent) == null;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Composite.Init (correctness)"} Impl$$_module.Composite.Init(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     && (_module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       ==> _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this))));
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(this)];
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.parent) != null
         ==> Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(read($Heap, this, _module.Composite.parent))]);
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.parent) != null
         ==> read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
             == this
           || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
             == this);
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.left) != null
         ==> Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(read($Heap, this, _module.Composite.left))]);
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.left) != null
         ==> read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
           == this);
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.left) != null
         ==> read($Heap, this, _module.Composite.left)
           != read($Heap, this, _module.Composite.right));
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.right) != null
         ==> Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(read($Heap, this, _module.Composite.right))]);
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.right) != null
         ==> read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
           == this);
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.right) != null
         ==> read($Heap, this, _module.Composite.left)
           != read($Heap, this, _module.Composite.right));
  ensures _module.Composite.Valid#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Valid($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || read($Heap, this, _module.Composite.sum)
         == read($Heap, this, _module.Composite.val)
           + (if read($Heap, this, _module.Composite.left) == null
             then 0
             else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
           + (if read($Heap, this, _module.Composite.right) == null
             then 0
             else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum));
  ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(this)];
  ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.parent) != null
         ==> _module.Composite.Acyclic($LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.Composite.parent),
          Set#Difference(Set#UnionOne(Set#Empty(): Set Box, $Box(this)),
            Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  ensures read($Heap, this, _module.Composite.val) == x#0;
  ensures read($Heap, this, _module.Composite.parent) == null;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Composite.Init (correctness)"} Impl$$_module.Composite.Init(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref;
  var newtype$check#1: ref;
  var $rhs#1: ref;
  var newtype$check#2: ref;
  var $rhs#2: ref;
  var newtype$check#3: ref;
  var $rhs#3: int;
  var $rhs#4: int;

    // AddMethodImpl: Init, Impl$$_module.Composite.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(32,12)
    assume true;
    assert $_Frame[this, _module.Composite.parent];
    newtype$check#1 := null;
    assume true;
    $rhs#0 := null;
    $Heap := update($Heap, this, _module.Composite.parent, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(33,10)
    assume true;
    assert $_Frame[this, _module.Composite.left];
    newtype$check#2 := null;
    assume true;
    $rhs#1 := null;
    $Heap := update($Heap, this, _module.Composite.left, $rhs#1);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(34,11)
    assume true;
    assert $_Frame[this, _module.Composite.right];
    newtype$check#3 := null;
    assume true;
    $rhs#2 := null;
    $Heap := update($Heap, this, _module.Composite.right, $rhs#2);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(35,9)
    assume true;
    assert $_Frame[this, _module.Composite.val];
    assume true;
    $rhs#3 := x#0;
    $Heap := update($Heap, this, _module.Composite.val, $rhs#3);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(36,9)
    assume true;
    assert $_Frame[this, _module.Composite.sum];
    assume true;
    $rhs#4 := read($Heap, this, _module.Composite.val);
    $Heap := update($Heap, this, _module.Composite.sum, $rhs#4);
    assume $IsGoodHeap($Heap);
}



procedure {:verboseName "Composite.Update (well-formedness)"} CheckWellFormed$$_module.Composite.Update(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    x#0: int,
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Composite.Update (well-formedness)"} CheckWellFormed$$_module.Composite.Update(this: ref, x#0: int, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##S#0: Set Box;
  var c#0: ref;
  var ##S#1: Set Box;
  var c#2: ref;
  var ##S#2: Set Box;
  var c#4: ref;
  var c#6: ref;

    // AddMethodImpl: Update, CheckWellFormed$$_module.Composite.Update
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume S#0[$Box(this)];
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Composite?(), $Heap);
    ##S#0 := S#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##S#0, TSet(Tclass._module.Composite()), $Heap);
    assume _module.Composite.Acyclic#canCall($Heap, this, S#0);
    assume _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0);
    havoc c#0;
    assume $Is(c#0, Tclass._module.Composite())
       && $IsAlloc(c#0, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#0)];
        assert c#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#0, Tclass._module.Composite?(), $Heap);
        ##S#1 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#1, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#0, S#0);
        assume _module.Composite.Valid($Heap, c#0, S#0);
    }
    else
    {
        assume S#0[$Box(c#0)] ==> _module.Composite.Valid($Heap, c#0, S#0);
    }

    assume (forall c#1: ref ::
      { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
      $Is(c#1, Tclass._module.Composite())
         ==>
        S#0[$Box(c#1)]
         ==> _module.Composite.Valid($Heap, c#1, S#0));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#2;
    assume $Is(c#2, Tclass._module.Composite())
       && $IsAlloc(c#2, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#2)];
        assert c#2 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#2, Tclass._module.Composite?(), $Heap);
        ##S#2 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#2, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#2, S#0);
        assume _module.Composite.Valid($Heap, c#2, S#0);
    }
    else
    {
        assume S#0[$Box(c#2)] ==> _module.Composite.Valid($Heap, c#2, S#0);
    }

    assume (forall c#3: ref ::
      { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
      $Is(c#3, Tclass._module.Composite())
         ==>
        S#0[$Box(c#3)]
         ==> _module.Composite.Valid($Heap, c#3, S#0));
    havoc c#4;
    assume $Is(c#4, Tclass._module.Composite())
       && $IsAlloc(c#4, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#4)];
        assert c#4 != null;
        assert c#4 != null;
        assert $IsAlloc(c#4, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#4, _module.Composite.left)
           == read(old($Heap), c#4, _module.Composite.left);
        assert c#4 != null;
        assert c#4 != null;
        assert $IsAlloc(c#4, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#4, _module.Composite.right)
           == read(old($Heap), c#4, _module.Composite.right);
        assert c#4 != null;
        assert c#4 != null;
        assert $IsAlloc(c#4, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#4, _module.Composite.parent)
           == read(old($Heap), c#4, _module.Composite.parent);
    }
    else
    {
        assume S#0[$Box(c#4)]
           ==> read($Heap, c#4, _module.Composite.left)
               == read(old($Heap), c#4, _module.Composite.left)
             && read($Heap, c#4, _module.Composite.right)
               == read(old($Heap), c#4, _module.Composite.right)
             && read($Heap, c#4, _module.Composite.parent)
               == read(old($Heap), c#4, _module.Composite.parent);
    }

    assume (forall c#5: ref ::
      { read(old($Heap), c#5, _module.Composite.parent) }
        { read($Heap, c#5, _module.Composite.parent) }
        { read(old($Heap), c#5, _module.Composite.right) }
        { read($Heap, c#5, _module.Composite.right) }
        { read(old($Heap), c#5, _module.Composite.left) }
        { read($Heap, c#5, _module.Composite.left) }
        { S#0[$Box(c#5)] }
      $Is(c#5, Tclass._module.Composite())
         ==> (S#0[$Box(c#5)]
             ==> read($Heap, c#5, _module.Composite.left)
               == read(old($Heap), c#5, _module.Composite.left))
           && (S#0[$Box(c#5)]
             ==> read($Heap, c#5, _module.Composite.right)
               == read(old($Heap), c#5, _module.Composite.right))
           && (S#0[$Box(c#5)]
             ==> read($Heap, c#5, _module.Composite.parent)
               == read(old($Heap), c#5, _module.Composite.parent)));
    havoc c#6;
    assume $Is(c#6, Tclass._module.Composite())
       && $IsAlloc(c#6, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#6)];
        assume c#6 != this;
        assert c#6 != null;
        assert c#6 != null;
        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#6, _module.Composite.val)
           == read(old($Heap), c#6, _module.Composite.val);
    }
    else
    {
        assume S#0[$Box(c#6)] && c#6 != this
           ==> read($Heap, c#6, _module.Composite.val)
             == read(old($Heap), c#6, _module.Composite.val);
    }

    assume (forall c#7: ref ::
      { read(old($Heap), c#7, _module.Composite.val) }
        { read($Heap, c#7, _module.Composite.val) }
        { S#0[$Box(c#7)] }
      $Is(c#7, Tclass._module.Composite())
         ==>
        S#0[$Box(c#7)] && c#7 != this
         ==> read($Heap, c#7, _module.Composite.val)
           == read(old($Heap), c#7, _module.Composite.val));
    assume read($Heap, this, _module.Composite.val) == x#0;
}



procedure {:verboseName "Composite.Update (call)"} Call$$_module.Composite.Update(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    x#0: int,
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0) || S#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
       || (read($Heap, this, _module.Composite.parent) != null
         ==> _module.Composite.Acyclic($LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.Composite.parent),
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)]
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid#canCall($Heap, c#3, S#0));
  ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, S#0));
  free ensures true;
  ensures (forall c#5: ref ::
    { read(old($Heap), c#5, _module.Composite.parent) }
      { read($Heap, c#5, _module.Composite.parent) }
      { read(old($Heap), c#5, _module.Composite.right) }
      { read($Heap, c#5, _module.Composite.right) }
      { read(old($Heap), c#5, _module.Composite.left) }
      { read($Heap, c#5, _module.Composite.left) }
      { S#0[$Box(c#5)] }
    $Is(c#5, Tclass._module.Composite())
       ==> (S#0[$Box(c#5)]
           ==> read($Heap, c#5, _module.Composite.left)
             == read(old($Heap), c#5, _module.Composite.left))
         && (S#0[$Box(c#5)]
           ==> read($Heap, c#5, _module.Composite.right)
             == read(old($Heap), c#5, _module.Composite.right))
         && (S#0[$Box(c#5)]
           ==> read($Heap, c#5, _module.Composite.parent)
             == read(old($Heap), c#5, _module.Composite.parent)));
  free ensures true;
  ensures (forall c#7: ref ::
    { read(old($Heap), c#7, _module.Composite.val) }
      { read($Heap, c#7, _module.Composite.val) }
      { S#0[$Box(c#7)] }
    $Is(c#7, Tclass._module.Composite())
       ==>
      S#0[$Box(c#7)] && c#7 != this
       ==> read($Heap, c#7, _module.Composite.val)
         == read(old($Heap), c#7, _module.Composite.val));
  free ensures true;
  ensures read($Heap, this, _module.Composite.val) == x#0;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Composite.Update (correctness)"} Impl$$_module.Composite.Update(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    x#0: int,
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(this)];
  free requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     &&
    _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
     &&
    S#0[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> _module.Composite.Acyclic($LS($LZ),
        $Heap,
        read($Heap, this, _module.Composite.parent),
        Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)]
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid#canCall($Heap, c#3, S#0));
  ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, S#0));
  free ensures true;
  ensures (forall c#5: ref ::
    { read(old($Heap), c#5, _module.Composite.parent) }
      { read($Heap, c#5, _module.Composite.parent) }
      { read(old($Heap), c#5, _module.Composite.right) }
      { read($Heap, c#5, _module.Composite.right) }
      { read(old($Heap), c#5, _module.Composite.left) }
      { read($Heap, c#5, _module.Composite.left) }
      { S#0[$Box(c#5)] }
    $Is(c#5, Tclass._module.Composite())
       ==> (S#0[$Box(c#5)]
           ==> read($Heap, c#5, _module.Composite.left)
             == read(old($Heap), c#5, _module.Composite.left))
         && (S#0[$Box(c#5)]
           ==> read($Heap, c#5, _module.Composite.right)
             == read(old($Heap), c#5, _module.Composite.right))
         && (S#0[$Box(c#5)]
           ==> read($Heap, c#5, _module.Composite.parent)
             == read(old($Heap), c#5, _module.Composite.parent)));
  free ensures true;
  ensures (forall c#7: ref ::
    { read(old($Heap), c#7, _module.Composite.val) }
      { read($Heap, c#7, _module.Composite.val) }
      { S#0[$Box(c#7)] }
    $Is(c#7, Tclass._module.Composite())
       ==>
      S#0[$Box(c#7)] && c#7 != this
       ==> read($Heap, c#7, _module.Composite.val)
         == read(old($Heap), c#7, _module.Composite.val));
  free ensures true;
  ensures read($Heap, this, _module.Composite.val) == x#0;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Composite.Update (correctness)"} Impl$$_module.Composite.Update(this: ref, x#0: int, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var delta#0: int;
  var $rhs#0: int;
  var delta##0: int;
  var U##0: Set Box;
  var S##0: Set Box;

    // AddMethodImpl: Update, Impl$$_module.Composite.Update
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(48,15)
    assume true;
    assume true;
    delta#0 := x#0 - read($Heap, this, _module.Composite.val);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(49,9)
    assume true;
    assert $_Frame[this, _module.Composite.val];
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap, this, _module.Composite.val, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(50,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    delta##0 := delta#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##0 := S#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##0 := S#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           &&
          U##0[$Box($o)]
           && $f == _module.Composite.sum
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Adjust(this, delta##0, U##0, S##0);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "Composite.Add (well-formedness)"} CheckWellFormed$$_module.Composite.Add(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap),
    child#0: ref
       where $Is(child#0, Tclass._module.Composite())
         && $IsAlloc(child#0, Tclass._module.Composite(), $Heap),
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(U#0, TSet(Tclass._module.Composite()), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Composite.Add (well-formedness)"} CheckWellFormed$$_module.Composite.Add(this: ref, S#0: Set Box, child#0: ref, U#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##S#0: Set Box;
  var c#0: ref;
  var ##S#1: Set Box;
  var c#2: ref;
  var ##S#2: Set Box;
  var newtype$check#0: ref;
  var newtype$check#1: ref;
  var newtype$check#2: ref;
  var c#4: ref;
  var newtype$check#3: ref;
  var newtype$check#4: ref;
  var c#6: ref;
  var c#8: ref;
  var ##S#3: Set Box;

    // AddMethodImpl: Add, CheckWellFormed$$_module.Composite.Add
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)] || $o == child#0);
    assume S#0[$Box(this)];
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Composite?(), $Heap);
    ##S#0 := S#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##S#0, TSet(Tclass._module.Composite()), $Heap);
    assume _module.Composite.Acyclic#canCall($Heap, this, S#0);
    assume _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0);
    havoc c#0;
    assume $Is(c#0, Tclass._module.Composite())
       && $IsAlloc(c#0, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#0)];
        assert c#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#0, Tclass._module.Composite?(), $Heap);
        ##S#1 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#1, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#0, S#0);
        assume _module.Composite.Valid($Heap, c#0, S#0);
    }
    else
    {
        assume S#0[$Box(c#0)] ==> _module.Composite.Valid($Heap, c#0, S#0);
    }

    assume (forall c#1: ref ::
      { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
      $Is(c#1, Tclass._module.Composite())
         ==>
        S#0[$Box(c#1)]
         ==> _module.Composite.Valid($Heap, c#1, S#0));
    assume U#0[$Box(child#0)];
    havoc c#2;
    assume $Is(c#2, Tclass._module.Composite())
       && $IsAlloc(c#2, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume U#0[$Box(c#2)];
        assert c#2 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#2, Tclass._module.Composite?(), $Heap);
        ##S#2 := U#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#2, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#2, U#0);
        assume _module.Composite.Valid($Heap, c#2, U#0);
    }
    else
    {
        assume U#0[$Box(c#2)] ==> _module.Composite.Valid($Heap, c#2, U#0);
    }

    assume (forall c#3: ref ::
      { _module.Composite.Valid($Heap, c#3, U#0) } { U#0[$Box(c#3)] }
      $Is(c#3, Tclass._module.Composite())
         ==>
        U#0[$Box(c#3)]
         ==> _module.Composite.Valid($Heap, c#3, U#0));
    assume Set#Disjoint(S#0, U#0);
    if (*)
    {
        newtype$check#0 := null;
        assume read($Heap, this, _module.Composite.left) == null;
    }
    else
    {
        assume read($Heap, this, _module.Composite.left) != null;
        newtype$check#1 := null;
        assume read($Heap, this, _module.Composite.right) == null;
    }

    assert child#0 != null;
    newtype$check#2 := null;
    assume read($Heap, child#0, _module.Composite.parent) == null;
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)] || $o == child#0);
    assume $HeapSucc(old($Heap), $Heap);
    assert child#0 != null;
    assert child#0 != null;
    assert $IsAlloc(child#0, Tclass._module.Composite(), old($Heap));
    assume read($Heap, child#0, _module.Composite.left)
       == read(old($Heap), child#0, _module.Composite.left);
    assert child#0 != null;
    assert child#0 != null;
    assert $IsAlloc(child#0, Tclass._module.Composite(), old($Heap));
    assume read($Heap, child#0, _module.Composite.right)
       == read(old($Heap), child#0, _module.Composite.right);
    assert child#0 != null;
    assert child#0 != null;
    assert $IsAlloc(child#0, Tclass._module.Composite(), old($Heap));
    assume read($Heap, child#0, _module.Composite.val)
       == read(old($Heap), child#0, _module.Composite.val);
    havoc c#4;
    assume $Is(c#4, Tclass._module.Composite())
       && $IsAlloc(c#4, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#4)];
        assume c#4 != this;
        assert c#4 != null;
        assert c#4 != null;
        assert $IsAlloc(c#4, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#4, _module.Composite.left)
           == read(old($Heap), c#4, _module.Composite.left);
        assert c#4 != null;
        assert c#4 != null;
        assert $IsAlloc(c#4, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#4, _module.Composite.right)
           == read(old($Heap), c#4, _module.Composite.right);
    }
    else
    {
        assume S#0[$Box(c#4)] && c#4 != this
           ==> read($Heap, c#4, _module.Composite.left)
               == read(old($Heap), c#4, _module.Composite.left)
             && read($Heap, c#4, _module.Composite.right)
               == read(old($Heap), c#4, _module.Composite.right);
    }

    assume (forall c#5: ref ::
      { read(old($Heap), c#5, _module.Composite.right) }
        { read($Heap, c#5, _module.Composite.right) }
        { read(old($Heap), c#5, _module.Composite.left) }
        { read($Heap, c#5, _module.Composite.left) }
        { S#0[$Box(c#5)] }
      $Is(c#5, Tclass._module.Composite())
         ==> (S#0[$Box(c#5)] && c#5 != this
             ==> read($Heap, c#5, _module.Composite.left)
               == read(old($Heap), c#5, _module.Composite.left))
           && (S#0[$Box(c#5)] && c#5 != this
             ==> read($Heap, c#5, _module.Composite.right)
               == read(old($Heap), c#5, _module.Composite.right)));
    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Composite(), old($Heap));
        newtype$check#3 := null;
        assume read(old($Heap), this, _module.Composite.left) != null;
        assert $IsAlloc(this, Tclass._module.Composite(), old($Heap));
        assume read($Heap, this, _module.Composite.left)
           == read(old($Heap), this, _module.Composite.left);
    }
    else
    {
        assume read(old($Heap), this, _module.Composite.left) != null
           ==> read($Heap, this, _module.Composite.left)
             == read(old($Heap), this, _module.Composite.left);
    }

    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Composite(), old($Heap));
        newtype$check#4 := null;
        assume read(old($Heap), this, _module.Composite.right) != null;
        assert $IsAlloc(this, Tclass._module.Composite(), old($Heap));
        assume read($Heap, this, _module.Composite.right)
           == read(old($Heap), this, _module.Composite.right);
    }
    else
    {
        assume read(old($Heap), this, _module.Composite.right) != null
           ==> read($Heap, this, _module.Composite.right)
             == read(old($Heap), this, _module.Composite.right);
    }

    havoc c#6;
    assume $Is(c#6, Tclass._module.Composite())
       && $IsAlloc(c#6, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#6)];
        assert c#6 != null;
        assert c#6 != null;
        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#6, _module.Composite.parent)
           == read(old($Heap), c#6, _module.Composite.parent);
        assert c#6 != null;
        assert c#6 != null;
        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#6, _module.Composite.val)
           == read(old($Heap), c#6, _module.Composite.val);
    }
    else
    {
        assume S#0[$Box(c#6)]
           ==> read($Heap, c#6, _module.Composite.parent)
               == read(old($Heap), c#6, _module.Composite.parent)
             && read($Heap, c#6, _module.Composite.val)
               == read(old($Heap), c#6, _module.Composite.val);
    }

    assume (forall c#7: ref ::
      { read(old($Heap), c#7, _module.Composite.val) }
        { read($Heap, c#7, _module.Composite.val) }
        { read(old($Heap), c#7, _module.Composite.parent) }
        { read($Heap, c#7, _module.Composite.parent) }
        { S#0[$Box(c#7)] }
      $Is(c#7, Tclass._module.Composite())
         ==> (S#0[$Box(c#7)]
             ==> read($Heap, c#7, _module.Composite.parent)
               == read(old($Heap), c#7, _module.Composite.parent))
           && (S#0[$Box(c#7)]
             ==> read($Heap, c#7, _module.Composite.val)
               == read(old($Heap), c#7, _module.Composite.val)));
    assert child#0 != null;
    assume read($Heap, child#0, _module.Composite.parent) == this;
    havoc c#8;
    assume $Is(c#8, Tclass._module.Composite())
       && $IsAlloc(c#8, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume Set#Union(S#0, U#0)[$Box(c#8)];
        assert c#8 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#8, Tclass._module.Composite?(), $Heap);
        ##S#3 := Set#Union(S#0, U#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#3, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#8, Set#Union(S#0, U#0));
        assume _module.Composite.Valid($Heap, c#8, Set#Union(S#0, U#0));
    }
    else
    {
        assume Set#Union(S#0, U#0)[$Box(c#8)]
           ==> _module.Composite.Valid($Heap, c#8, Set#Union(S#0, U#0));
    }

    assume (forall c#9: ref ::
      {:autotriggers false}
      $Is(c#9, Tclass._module.Composite())
         ==>
        Set#Union(S#0, U#0)[$Box(c#9)]
         ==> _module.Composite.Valid($Heap, c#9, Set#Union(S#0, U#0)));
}



procedure {:verboseName "Composite.Add (call)"} Call$$_module.Composite.Add(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap),
    child#0: ref
       where $Is(child#0, Tclass._module.Composite())
         && $IsAlloc(child#0, Tclass._module.Composite(), $Heap),
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(U#0, TSet(Tclass._module.Composite()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0) || S#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
       || (read($Heap, this, _module.Composite.parent) != null
         ==> _module.Composite.Acyclic($LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.Composite.parent),
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)]
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  requires U#0[$Box(child#0)];
  requires (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, U#0) } { U#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      U#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, U#0));
  requires Set#Disjoint(S#0, U#0);
  requires read($Heap, this, _module.Composite.left) == null
     || read($Heap, this, _module.Composite.right) == null;
  requires read($Heap, child#0, _module.Composite.parent) == null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, child#0, _module.Composite.left)
     == read(old($Heap), child#0, _module.Composite.left);
  ensures read($Heap, child#0, _module.Composite.right)
     == read(old($Heap), child#0, _module.Composite.right);
  ensures read($Heap, child#0, _module.Composite.val)
     == read(old($Heap), child#0, _module.Composite.val);
  free ensures true;
  ensures (forall c#5: ref ::
    { read(old($Heap), c#5, _module.Composite.right) }
      { read($Heap, c#5, _module.Composite.right) }
      { read(old($Heap), c#5, _module.Composite.left) }
      { read($Heap, c#5, _module.Composite.left) }
      { S#0[$Box(c#5)] }
    $Is(c#5, Tclass._module.Composite())
       ==> (S#0[$Box(c#5)] && c#5 != this
           ==> read($Heap, c#5, _module.Composite.left)
             == read(old($Heap), c#5, _module.Composite.left))
         && (S#0[$Box(c#5)] && c#5 != this
           ==> read($Heap, c#5, _module.Composite.right)
             == read(old($Heap), c#5, _module.Composite.right)));
  free ensures true;
  ensures read(old($Heap), this, _module.Composite.left) != null
     ==> read($Heap, this, _module.Composite.left)
       == read(old($Heap), this, _module.Composite.left);
  free ensures true;
  ensures read(old($Heap), this, _module.Composite.right) != null
     ==> read($Heap, this, _module.Composite.right)
       == read(old($Heap), this, _module.Composite.right);
  free ensures true;
  ensures (forall c#7: ref ::
    { read(old($Heap), c#7, _module.Composite.val) }
      { read($Heap, c#7, _module.Composite.val) }
      { read(old($Heap), c#7, _module.Composite.parent) }
      { read($Heap, c#7, _module.Composite.parent) }
      { S#0[$Box(c#7)] }
    $Is(c#7, Tclass._module.Composite())
       ==> (S#0[$Box(c#7)]
           ==> read($Heap, c#7, _module.Composite.parent)
             == read(old($Heap), c#7, _module.Composite.parent))
         && (S#0[$Box(c#7)]
           ==> read($Heap, c#7, _module.Composite.val)
             == read(old($Heap), c#7, _module.Composite.val)));
  free ensures true;
  ensures read($Heap, child#0, _module.Composite.parent) == this;
  free ensures (forall c#9: ref ::
    $Is(c#9, Tclass._module.Composite())
       ==>
      Set#Union(S#0, U#0)[$Box(c#9)]
       ==> _module.Composite.Valid#canCall($Heap, c#9, Set#Union(S#0, U#0)));
  ensures (forall c#9: ref ::
    {:autotriggers false}
    $Is(c#9, Tclass._module.Composite())
       ==>
      Set#Union(S#0, U#0)[$Box(c#9)]
       ==> _module.Composite.Valid($Heap, c#9, Set#Union(S#0, U#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)] || $o == child#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Composite.Add (correctness)"} Impl$$_module.Composite.Add(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap),
    child#0: ref
       where $Is(child#0, Tclass._module.Composite())
         && $IsAlloc(child#0, Tclass._module.Composite(), $Heap),
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(U#0, TSet(Tclass._module.Composite()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(this)];
  free requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     &&
    _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
     &&
    S#0[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> _module.Composite.Acyclic($LS($LZ),
        $Heap,
        read($Heap, this, _module.Composite.parent),
        Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)]
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  requires U#0[$Box(child#0)];
  requires (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, U#0) } { U#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      U#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, U#0));
  requires Set#Disjoint(S#0, U#0);
  requires read($Heap, this, _module.Composite.left) == null
     || read($Heap, this, _module.Composite.right) == null;
  requires read($Heap, child#0, _module.Composite.parent) == null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, child#0, _module.Composite.left)
     == read(old($Heap), child#0, _module.Composite.left);
  ensures read($Heap, child#0, _module.Composite.right)
     == read(old($Heap), child#0, _module.Composite.right);
  ensures read($Heap, child#0, _module.Composite.val)
     == read(old($Heap), child#0, _module.Composite.val);
  free ensures true;
  ensures (forall c#5: ref ::
    { read(old($Heap), c#5, _module.Composite.right) }
      { read($Heap, c#5, _module.Composite.right) }
      { read(old($Heap), c#5, _module.Composite.left) }
      { read($Heap, c#5, _module.Composite.left) }
      { S#0[$Box(c#5)] }
    $Is(c#5, Tclass._module.Composite())
       ==> (S#0[$Box(c#5)] && c#5 != this
           ==> read($Heap, c#5, _module.Composite.left)
             == read(old($Heap), c#5, _module.Composite.left))
         && (S#0[$Box(c#5)] && c#5 != this
           ==> read($Heap, c#5, _module.Composite.right)
             == read(old($Heap), c#5, _module.Composite.right)));
  free ensures true;
  ensures read(old($Heap), this, _module.Composite.left) != null
     ==> read($Heap, this, _module.Composite.left)
       == read(old($Heap), this, _module.Composite.left);
  free ensures true;
  ensures read(old($Heap), this, _module.Composite.right) != null
     ==> read($Heap, this, _module.Composite.right)
       == read(old($Heap), this, _module.Composite.right);
  free ensures true;
  ensures (forall c#7: ref ::
    { read(old($Heap), c#7, _module.Composite.val) }
      { read($Heap, c#7, _module.Composite.val) }
      { read(old($Heap), c#7, _module.Composite.parent) }
      { read($Heap, c#7, _module.Composite.parent) }
      { S#0[$Box(c#7)] }
    $Is(c#7, Tclass._module.Composite())
       ==> (S#0[$Box(c#7)]
           ==> read($Heap, c#7, _module.Composite.parent)
             == read(old($Heap), c#7, _module.Composite.parent))
         && (S#0[$Box(c#7)]
           ==> read($Heap, c#7, _module.Composite.val)
             == read(old($Heap), c#7, _module.Composite.val)));
  free ensures true;
  ensures read($Heap, child#0, _module.Composite.parent) == this;
  free ensures (forall c#9: ref ::
    $Is(c#9, Tclass._module.Composite())
       ==>
      Set#Union(S#0, U#0)[$Box(c#9)]
       ==> _module.Composite.Valid#canCall($Heap, c#9, Set#Union(S#0, U#0)));
  ensures (forall c#9: ref ::
    {:autotriggers false}
    $Is(c#9, Tclass._module.Composite())
       ==>
      Set#Union(S#0, U#0)[$Box(c#9)]
       ==> _module.Composite.Valid($Heap, c#9, Set#Union(S#0, U#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)] || $o == child#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Composite.Add (correctness)"} Impl$$_module.Composite.Add(this: ref, S#0: Set Box, child#0: ref, U#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#5: ref;
  var $rhs#0_0: ref;
  var $rhs#1_0: ref;
  var $rhs#0: ref;
  var delta##0: int;
  var U##0: Set Box;
  var S##0: Set Box;

    // AddMethodImpl: Add, Impl$$_module.Composite.Add
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)] || $o == child#0);
    $_reverifyPost := false;
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(73,5)
    newtype$check#5 := null;
    assume true;
    if (read($Heap, this, _module.Composite.left) == null)
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(74,12)
        assume true;
        assert $_Frame[this, _module.Composite.left];
        assume true;
        $rhs#0_0 := child#0;
        $Heap := update($Heap, this, _module.Composite.left, $rhs#0_0);
        assume $IsGoodHeap($Heap);
    }
    else
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(76,13)
        assume true;
        assert $_Frame[this, _module.Composite.right];
        assume true;
        $rhs#1_0 := child#0;
        $Heap := update($Heap, this, _module.Composite.right, $rhs#1_0);
        assume $IsGoodHeap($Heap);
    }

    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(78,18)
    assert child#0 != null;
    assume true;
    assert $_Frame[child#0, _module.Composite.parent];
    assume true;
    $rhs#0 := this;
    $Heap := update($Heap, child#0, _module.Composite.parent, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(79,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert child#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    delta##0 := read($Heap, child#0, _module.Composite.sum);
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##0 := S#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##0 := Set#Union(S#0, U#0);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           &&
          U##0[$Box($o)]
           && $f == _module.Composite.sum
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Adjust(this, delta##0, U##0, S##0);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "Composite.Dislodge (well-formedness)"} CheckWellFormed$$_module.Composite.Dislodge(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Composite.Dislodge (well-formedness)"} CheckWellFormed$$_module.Composite.Dislodge(this: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##S#0: Set Box;
  var c#0: ref;
  var ##S#1: Set Box;
  var c#2: ref;
  var ##S#2: Set Box;
  var c#4: ref;
  var c#6: ref;
  var newtype$check#0: ref;
  var c#8: ref;
  var newtype$check#1: ref;
  var c#10: ref;
  var newtype$check#2: ref;
  var ##S#3: Set Box;

    // AddMethodImpl: Dislodge, CheckWellFormed$$_module.Composite.Dislodge
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume S#0[$Box(this)];
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Composite?(), $Heap);
    ##S#0 := S#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##S#0, TSet(Tclass._module.Composite()), $Heap);
    assume _module.Composite.Acyclic#canCall($Heap, this, S#0);
    assume _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0);
    havoc c#0;
    assume $Is(c#0, Tclass._module.Composite())
       && $IsAlloc(c#0, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#0)];
        assert c#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#0, Tclass._module.Composite?(), $Heap);
        ##S#1 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#1, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#0, S#0);
        assume _module.Composite.Valid($Heap, c#0, S#0);
    }
    else
    {
        assume S#0[$Box(c#0)] ==> _module.Composite.Valid($Heap, c#0, S#0);
    }

    assume (forall c#1: ref ::
      { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
      $Is(c#1, Tclass._module.Composite())
         ==>
        S#0[$Box(c#1)]
         ==> _module.Composite.Valid($Heap, c#1, S#0));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#2;
    assume $Is(c#2, Tclass._module.Composite())
       && $IsAlloc(c#2, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#2)];
        assert c#2 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#2, Tclass._module.Composite?(), $Heap);
        ##S#2 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#2, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#2, S#0);
        assume _module.Composite.Valid($Heap, c#2, S#0);
    }
    else
    {
        assume S#0[$Box(c#2)] ==> _module.Composite.Valid($Heap, c#2, S#0);
    }

    assume (forall c#3: ref ::
      { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
      $Is(c#3, Tclass._module.Composite())
         ==>
        S#0[$Box(c#3)]
         ==> _module.Composite.Valid($Heap, c#3, S#0));
    havoc c#4;
    assume $Is(c#4, Tclass._module.Composite())
       && $IsAlloc(c#4, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#4)];
        assert c#4 != null;
        assert c#4 != null;
        assert $IsAlloc(c#4, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#4, _module.Composite.val)
           == read(old($Heap), c#4, _module.Composite.val);
    }
    else
    {
        assume S#0[$Box(c#4)]
           ==> read($Heap, c#4, _module.Composite.val)
             == read(old($Heap), c#4, _module.Composite.val);
    }

    assume (forall c#5: ref ::
      { read(old($Heap), c#5, _module.Composite.val) }
        { read($Heap, c#5, _module.Composite.val) }
        { S#0[$Box(c#5)] }
      $Is(c#5, Tclass._module.Composite())
         ==>
        S#0[$Box(c#5)]
         ==> read($Heap, c#5, _module.Composite.val)
           == read(old($Heap), c#5, _module.Composite.val));
    havoc c#6;
    assume $Is(c#6, Tclass._module.Composite())
       && $IsAlloc(c#6, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#6)];
        assume c#6 != this;
        assert c#6 != null;
        assert c#6 != null;
        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
        assume read($Heap, c#6, _module.Composite.parent)
           == read(old($Heap), c#6, _module.Composite.parent);
    }
    else
    {
        assume S#0[$Box(c#6)] && c#6 != this
           ==> read($Heap, c#6, _module.Composite.parent)
             == read(old($Heap), c#6, _module.Composite.parent);
    }

    assume (forall c#7: ref ::
      { read(old($Heap), c#7, _module.Composite.parent) }
        { read($Heap, c#7, _module.Composite.parent) }
        { S#0[$Box(c#7)] }
      $Is(c#7, Tclass._module.Composite())
         ==>
        S#0[$Box(c#7)] && c#7 != this
         ==> read($Heap, c#7, _module.Composite.parent)
           == read(old($Heap), c#7, _module.Composite.parent));
    newtype$check#0 := null;
    assume read($Heap, this, _module.Composite.parent) == null;
    havoc c#8;
    assume $Is(c#8, Tclass._module.Composite())
       && $IsAlloc(c#8, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#8)];
        if (*)
        {
            assert c#8 != null;
            assert c#8 != null;
            assert $IsAlloc(c#8, Tclass._module.Composite(), old($Heap));
            assume read($Heap, c#8, _module.Composite.left)
               == read(old($Heap), c#8, _module.Composite.left);
        }
        else
        {
            assume read($Heap, c#8, _module.Composite.left)
               != read(old($Heap), c#8, _module.Composite.left);
            assert c#8 != null;
            assert $IsAlloc(c#8, Tclass._module.Composite(), old($Heap));
            assume read(old($Heap), c#8, _module.Composite.left) == this;
            assert c#8 != null;
            newtype$check#1 := null;
            assume read($Heap, c#8, _module.Composite.left) == null;
        }
    }
    else
    {
        assume S#0[$Box(c#8)]
           ==> read($Heap, c#8, _module.Composite.left)
               == read(old($Heap), c#8, _module.Composite.left)
             || (read(old($Heap), c#8, _module.Composite.left) == this
               && read($Heap, c#8, _module.Composite.left) == null);
    }

    assume (forall c#9: ref ::
      { read(old($Heap), c#9, _module.Composite.left) }
        { read($Heap, c#9, _module.Composite.left) }
        { S#0[$Box(c#9)] }
      $Is(c#9, Tclass._module.Composite())
         ==>
        S#0[$Box(c#9)]
         ==> read($Heap, c#9, _module.Composite.left)
             == read(old($Heap), c#9, _module.Composite.left)
           || (read(old($Heap), c#9, _module.Composite.left) == this
             && read($Heap, c#9, _module.Composite.left) == null));
    havoc c#10;
    assume $Is(c#10, Tclass._module.Composite())
       && $IsAlloc(c#10, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#10)];
        if (*)
        {
            assert c#10 != null;
            assert c#10 != null;
            assert $IsAlloc(c#10, Tclass._module.Composite(), old($Heap));
            assume read($Heap, c#10, _module.Composite.right)
               == read(old($Heap), c#10, _module.Composite.right);
        }
        else
        {
            assume read($Heap, c#10, _module.Composite.right)
               != read(old($Heap), c#10, _module.Composite.right);
            assert c#10 != null;
            assert $IsAlloc(c#10, Tclass._module.Composite(), old($Heap));
            assume read(old($Heap), c#10, _module.Composite.right) == this;
            assert c#10 != null;
            newtype$check#2 := null;
            assume read($Heap, c#10, _module.Composite.right) == null;
        }
    }
    else
    {
        assume S#0[$Box(c#10)]
           ==> read($Heap, c#10, _module.Composite.right)
               == read(old($Heap), c#10, _module.Composite.right)
             || (read(old($Heap), c#10, _module.Composite.right) == this
               && read($Heap, c#10, _module.Composite.right) == null);
    }

    assume (forall c#11: ref ::
      { read(old($Heap), c#11, _module.Composite.right) }
        { read($Heap, c#11, _module.Composite.right) }
        { S#0[$Box(c#11)] }
      $Is(c#11, Tclass._module.Composite())
         ==>
        S#0[$Box(c#11)]
         ==> read($Heap, c#11, _module.Composite.right)
             == read(old($Heap), c#11, _module.Composite.right)
           || (read(old($Heap), c#11, _module.Composite.right) == this
             && read($Heap, c#11, _module.Composite.right) == null));
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Composite?(), $Heap);
    ##S#3 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    // assume allocatedness for argument to function
    assume $IsAlloc(##S#3, TSet(Tclass._module.Composite()), $Heap);
    assume _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
    assume _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
}



procedure {:verboseName "Composite.Dislodge (call)"} Call$$_module.Composite.Dislodge(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0) || S#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
       || (read($Heap, this, _module.Composite.parent) != null
         ==> _module.Composite.Acyclic($LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.Composite.parent),
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)]
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid#canCall($Heap, c#3, S#0));
  ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, S#0));
  free ensures true;
  ensures (forall c#5: ref ::
    { read(old($Heap), c#5, _module.Composite.val) }
      { read($Heap, c#5, _module.Composite.val) }
      { S#0[$Box(c#5)] }
    $Is(c#5, Tclass._module.Composite())
       ==>
      S#0[$Box(c#5)]
       ==> read($Heap, c#5, _module.Composite.val)
         == read(old($Heap), c#5, _module.Composite.val));
  free ensures true;
  ensures (forall c#7: ref ::
    { read(old($Heap), c#7, _module.Composite.parent) }
      { read($Heap, c#7, _module.Composite.parent) }
      { S#0[$Box(c#7)] }
    $Is(c#7, Tclass._module.Composite())
       ==>
      S#0[$Box(c#7)] && c#7 != this
       ==> read($Heap, c#7, _module.Composite.parent)
         == read(old($Heap), c#7, _module.Composite.parent));
  free ensures true;
  ensures read($Heap, this, _module.Composite.parent) == null;
  free ensures true;
  ensures (forall c#9: ref ::
    { read(old($Heap), c#9, _module.Composite.left) }
      { read($Heap, c#9, _module.Composite.left) }
      { S#0[$Box(c#9)] }
    $Is(c#9, Tclass._module.Composite())
       ==>
      S#0[$Box(c#9)]
       ==> read($Heap, c#9, _module.Composite.left)
           == read(old($Heap), c#9, _module.Composite.left)
         || (read(old($Heap), c#9, _module.Composite.left) == this
           && read($Heap, c#9, _module.Composite.left) == null));
  free ensures true;
  ensures (forall c#11: ref ::
    { read(old($Heap), c#11, _module.Composite.right) }
      { read($Heap, c#11, _module.Composite.right) }
      { S#0[$Box(c#11)] }
    $Is(c#11, Tclass._module.Composite())
       ==>
      S#0[$Box(c#11)]
       ==> read($Heap, c#11, _module.Composite.right)
           == read(old($Heap), c#11, _module.Composite.right)
         || (read(old($Heap), c#11, _module.Composite.right) == this
           && read($Heap, c#11, _module.Composite.right) == null));
  free ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
  free ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     &&
    _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     &&
    Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> _module.Composite.Acyclic($LS($LZ),
        $Heap,
        read($Heap, this, _module.Composite.parent),
        Set#Difference(Set#UnionOne(Set#Empty(): Set Box, $Box(this)),
          Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Composite.Dislodge (correctness)"} Impl$$_module.Composite.Dislodge(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(this)];
  free requires _module.Composite.Acyclic#canCall($Heap, this, S#0)
     &&
    _module.Composite.Acyclic($LS($LZ), $Heap, this, S#0)
     &&
    S#0[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> _module.Composite.Acyclic($LS($LZ),
        $Heap,
        read($Heap, this, _module.Composite.parent),
        Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)]
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid#canCall($Heap, c#3, S#0));
  ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, S#0));
  free ensures true;
  ensures (forall c#5: ref ::
    { read(old($Heap), c#5, _module.Composite.val) }
      { read($Heap, c#5, _module.Composite.val) }
      { S#0[$Box(c#5)] }
    $Is(c#5, Tclass._module.Composite())
       ==>
      S#0[$Box(c#5)]
       ==> read($Heap, c#5, _module.Composite.val)
         == read(old($Heap), c#5, _module.Composite.val));
  free ensures true;
  ensures (forall c#7: ref ::
    { read(old($Heap), c#7, _module.Composite.parent) }
      { read($Heap, c#7, _module.Composite.parent) }
      { S#0[$Box(c#7)] }
    $Is(c#7, Tclass._module.Composite())
       ==>
      S#0[$Box(c#7)] && c#7 != this
       ==> read($Heap, c#7, _module.Composite.parent)
         == read(old($Heap), c#7, _module.Composite.parent));
  free ensures true;
  ensures read($Heap, this, _module.Composite.parent) == null;
  free ensures true;
  ensures (forall c#9: ref ::
    { read(old($Heap), c#9, _module.Composite.left) }
      { read($Heap, c#9, _module.Composite.left) }
      { S#0[$Box(c#9)] }
    $Is(c#9, Tclass._module.Composite())
       ==>
      S#0[$Box(c#9)]
       ==> read($Heap, c#9, _module.Composite.left)
           == read(old($Heap), c#9, _module.Composite.left)
         || (read(old($Heap), c#9, _module.Composite.left) == this
           && read($Heap, c#9, _module.Composite.left) == null));
  free ensures true;
  ensures (forall c#11: ref ::
    { read(old($Heap), c#11, _module.Composite.right) }
      { read($Heap, c#11, _module.Composite.right) }
      { S#0[$Box(c#11)] }
    $Is(c#11, Tclass._module.Composite())
       ==>
      S#0[$Box(c#11)]
       ==> read($Heap, c#11, _module.Composite.right)
           == read(old($Heap), c#11, _module.Composite.right)
         || (read(old($Heap), c#11, _module.Composite.right) == this
           && read($Heap, c#11, _module.Composite.right) == null));
  free ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
  ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || Set#UnionOne(Set#Empty(): Set Box, $Box(this))[$Box(this)];
  ensures _module.Composite.Acyclic#canCall($Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
       || (read($Heap, this, _module.Composite.parent) != null
         ==> _module.Composite.Acyclic($LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.Composite.parent),
          Set#Difference(Set#UnionOne(Set#Empty(): Set Box, $Box(this)),
            Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Composite.Dislodge (correctness)"} Impl$$_module.Composite.Dislodge(this: ref, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#0: ref
     where $Is(p#0, Tclass._module.Composite?())
       && $IsAlloc(p#0, Tclass._module.Composite?(), $Heap);
  var $rhs#0: ref;
  var newtype$check#3: ref;
  var newtype$check#4: ref;
  var $rhs#0_0_0: ref;
  var newtype$check#0_0_0: ref;
  var $rhs#0_1_0: ref;
  var newtype$check#0_1_0: ref;
  var delta#0_0: int;
  var delta##0_0: int;
  var U##0_0: Set Box;
  var S##0_0: Set Box;

    // AddMethodImpl: Dislodge, Impl$$_module.Composite.Dislodge
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(94,11)
    assume true;
    assume true;
    p#0 := read($Heap, this, _module.Composite.parent);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(95,12)
    assume true;
    assert $_Frame[this, _module.Composite.parent];
    newtype$check#3 := null;
    assume true;
    $rhs#0 := null;
    $Heap := update($Heap, this, _module.Composite.parent, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(96,5)
    newtype$check#4 := null;
    assume true;
    if (p#0 != null)
    {
        // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(97,7)
        assert p#0 != null;
        assume true;
        if (read($Heap, p#0, _module.Composite.left) == this)
        {
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(98,16)
            assert p#0 != null;
            assume true;
            assert $_Frame[p#0, _module.Composite.left];
            newtype$check#0_0_0 := null;
            assume true;
            $rhs#0_0_0 := null;
            $Heap := update($Heap, p#0, _module.Composite.left, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
        }
        else
        {
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(100,17)
            assert p#0 != null;
            assume true;
            assert $_Frame[p#0, _module.Composite.right];
            newtype$check#0_1_0 := null;
            assume true;
            $rhs#0_1_0 := null;
            $Heap := update($Heap, p#0, _module.Composite.right, $rhs#0_1_0);
            assume $IsGoodHeap($Heap);
        }

        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(102,17)
        assume true;
        assume true;
        delta#0_0 := 0 - read($Heap, this, _module.Composite.sum);
        // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(103,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert p#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        delta##0_0 := delta#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        U##0_0 := Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
        assume true;
        // ProcessCallStmt: CheckSubrange
        S##0_0 := S#0;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null
               && read($Heap, $o, alloc)
               &&
              U##0_0[$Box($o)]
               && $f == _module.Composite.sum
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Composite.Adjust(p#0, delta##0_0, U##0_0, S##0_0);
        // TrCallStmt: After ProcessCallStmt
    }
    else
    {
    }
}



procedure {:verboseName "Composite.Adjust (well-formedness)"} CheckWellFormed$$_module.Composite.Adjust(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    delta#0: int,
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(U#0, TSet(Tclass._module.Composite()), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Composite.Adjust (well-formedness)"} CheckWellFormed$$_module.Composite.Adjust(this: ref, delta#0: int, U#0: Set Box, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##S#0: Set Box;
  var c#0: ref;
  var ##S#1: Set Box;
  var newtype$check#0: ref;
  var newtype$check#1: ref;
  var newtype$check#2: ref;
  var newtype$check#3: ref;
  var newtype$check#4: ref;
  var c#2: ref;
  var ##S#2: Set Box;

    // AddMethodImpl: Adjust, CheckWellFormed$$_module.Composite.Adjust
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> U#0[$Box($o)] && $f == _module.Composite.sum);
    assume Set#Subset(U#0, S#0);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Composite?(), $Heap);
    ##S#0 := U#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##S#0, TSet(Tclass._module.Composite()), $Heap);
    assume _module.Composite.Acyclic#canCall($Heap, this, U#0);
    assume _module.Composite.Acyclic($LS($LZ), $Heap, this, U#0);
    havoc c#0;
    assume $Is(c#0, Tclass._module.Composite())
       && $IsAlloc(c#0, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#0)];
        assume c#0 != this;
        assert c#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#0, Tclass._module.Composite?(), $Heap);
        ##S#1 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#1, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#0, S#0);
        assume _module.Composite.Valid($Heap, c#0, S#0);
    }
    else
    {
        assume S#0[$Box(c#0)] && c#0 != this ==> _module.Composite.Valid($Heap, c#0, S#0);
    }

    assume (forall c#1: ref ::
      { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
      $Is(c#1, Tclass._module.Composite())
         ==>
        S#0[$Box(c#1)] && c#1 != this
         ==> _module.Composite.Valid($Heap, c#1, S#0));
    if (*)
    {
        newtype$check#0 := null;
        assume read($Heap, this, _module.Composite.parent) != null;
        assume S#0[$Box(read($Heap, this, _module.Composite.parent))];
        assert read($Heap, this, _module.Composite.parent) != null;
        if (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
           != this)
        {
            assert read($Heap, this, _module.Composite.parent) != null;
        }

        assume read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
             == this
           || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
             == this;
    }
    else
    {
        assume read($Heap, this, _module.Composite.parent) != null
           ==> S#0[$Box(read($Heap, this, _module.Composite.parent))]
             && (read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
                 == this
               || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
                 == this);
    }

    if (*)
    {
        newtype$check#1 := null;
        assume read($Heap, this, _module.Composite.left) != null;
        assume S#0[$Box(read($Heap, this, _module.Composite.left))];
        assert read($Heap, this, _module.Composite.left) != null;
        assume read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
           == this;
        assume read($Heap, this, _module.Composite.left)
           != read($Heap, this, _module.Composite.right);
    }
    else
    {
        assume read($Heap, this, _module.Composite.left) != null
           ==> S#0[$Box(read($Heap, this, _module.Composite.left))]
             && read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
               == this
             && read($Heap, this, _module.Composite.left)
               != read($Heap, this, _module.Composite.right);
    }

    if (*)
    {
        newtype$check#2 := null;
        assume read($Heap, this, _module.Composite.right) != null;
        assume S#0[$Box(read($Heap, this, _module.Composite.right))];
        assert read($Heap, this, _module.Composite.right) != null;
        assume read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
           == this;
        assume read($Heap, this, _module.Composite.left)
           != read($Heap, this, _module.Composite.right);
    }
    else
    {
        assume read($Heap, this, _module.Composite.right) != null
           ==> S#0[$Box(read($Heap, this, _module.Composite.right))]
             && read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
               == this
             && read($Heap, this, _module.Composite.left)
               != read($Heap, this, _module.Composite.right);
    }

    newtype$check#3 := null;
    if (read($Heap, this, _module.Composite.left) == null)
    {
    }
    else
    {
        assert read($Heap, this, _module.Composite.left) != null;
    }

    newtype$check#4 := null;
    if (read($Heap, this, _module.Composite.right) == null)
    {
    }
    else
    {
        assert read($Heap, this, _module.Composite.right) != null;
    }

    assume read($Heap, this, _module.Composite.sum) + delta#0
       == read($Heap, this, _module.Composite.val)
         + (if read($Heap, this, _module.Composite.left) == null
           then 0
           else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
         + (if read($Heap, this, _module.Composite.right) == null
           then 0
           else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || U#0[$Box($o)]);
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || (U#0[$Box($o)] && $f == _module.Composite.sum));
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#2;
    assume $Is(c#2, Tclass._module.Composite())
       && $IsAlloc(c#2, Tclass._module.Composite(), $Heap);
    if (*)
    {
        assume S#0[$Box(c#2)];
        assert c#2 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(c#2, Tclass._module.Composite?(), $Heap);
        ##S#2 := S#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##S#2, TSet(Tclass._module.Composite()), $Heap);
        assume _module.Composite.Valid#canCall($Heap, c#2, S#0);
        assume _module.Composite.Valid($Heap, c#2, S#0);
    }
    else
    {
        assume S#0[$Box(c#2)] ==> _module.Composite.Valid($Heap, c#2, S#0);
    }

    assume (forall c#3: ref ::
      { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
      $Is(c#3, Tclass._module.Composite())
         ==>
        S#0[$Box(c#3)]
         ==> _module.Composite.Valid($Heap, c#3, S#0));
}



procedure {:verboseName "Composite.Adjust (call)"} Call$$_module.Composite.Adjust(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    delta#0: int,
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(U#0, TSet(Tclass._module.Composite()), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap));
  // user-defined preconditions
  requires Set#Subset(U#0, S#0);
  requires _module.Composite.Acyclic#canCall($Heap, this, U#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, U#0) || U#0[$Box(this)];
  requires _module.Composite.Acyclic#canCall($Heap, this, U#0)
     ==> _module.Composite.Acyclic($LS($LZ), $Heap, this, U#0)
       || (read($Heap, this, _module.Composite.parent) != null
         ==> _module.Composite.Acyclic($LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.Composite.parent),
          Set#Difference(U#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)] && c#1 != this
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  requires read($Heap, this, _module.Composite.parent) != null
     ==> S#0[$Box(read($Heap, this, _module.Composite.parent))];
  requires read($Heap, this, _module.Composite.parent) != null
     ==> read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
         == this
       || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
         == this;
  requires read($Heap, this, _module.Composite.left) != null
     ==> S#0[$Box(read($Heap, this, _module.Composite.left))];
  requires read($Heap, this, _module.Composite.left) != null
     ==> read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
       == this;
  requires read($Heap, this, _module.Composite.left) != null
     ==> read($Heap, this, _module.Composite.left)
       != read($Heap, this, _module.Composite.right);
  requires read($Heap, this, _module.Composite.right) != null
     ==> S#0[$Box(read($Heap, this, _module.Composite.right))];
  requires read($Heap, this, _module.Composite.right) != null
     ==> read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
       == this;
  requires read($Heap, this, _module.Composite.right) != null
     ==> read($Heap, this, _module.Composite.left)
       != read($Heap, this, _module.Composite.right);
  requires read($Heap, this, _module.Composite.sum) + delta#0
     == read($Heap, this, _module.Composite.val)
       + (if read($Heap, this, _module.Composite.left) == null
         then 0
         else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
       + (if read($Heap, this, _module.Composite.right) == null
         then 0
         else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid#canCall($Heap, c#3, S#0));
  ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, S#0));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || U#0[$Box($o)]);
  // frame condition: field granularity
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || (U#0[$Box($o)] && $f == _module.Composite.sum));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Composite.Adjust (correctness)"} Impl$$_module.Composite.Adjust(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Composite())
         && $IsAlloc(this, Tclass._module.Composite(), $Heap),
    delta#0: int,
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(U#0, TSet(Tclass._module.Composite()), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Composite()))
         && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  requires Set#Subset(U#0, S#0);
  free requires _module.Composite.Acyclic#canCall($Heap, this, U#0)
     &&
    _module.Composite.Acyclic($LS($LZ), $Heap, this, U#0)
     &&
    U#0[$Box(this)]
     && (read($Heap, this, _module.Composite.parent) != null
       ==> _module.Composite.Acyclic($LS($LZ),
        $Heap,
        read($Heap, this, _module.Composite.parent),
        Set#Difference(U#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
  requires (forall c#1: ref ::
    { _module.Composite.Valid($Heap, c#1, S#0) } { S#0[$Box(c#1)] }
    $Is(c#1, Tclass._module.Composite())
       ==>
      S#0[$Box(c#1)] && c#1 != this
       ==> _module.Composite.Valid($Heap, c#1, S#0));
  requires read($Heap, this, _module.Composite.parent) != null
     ==> S#0[$Box(read($Heap, this, _module.Composite.parent))];
  requires read($Heap, this, _module.Composite.parent) != null
     ==> read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.left)
         == this
       || read($Heap, read($Heap, this, _module.Composite.parent), _module.Composite.right)
         == this;
  requires read($Heap, this, _module.Composite.left) != null
     ==> S#0[$Box(read($Heap, this, _module.Composite.left))];
  requires read($Heap, this, _module.Composite.left) != null
     ==> read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.parent)
       == this;
  requires read($Heap, this, _module.Composite.left) != null
     ==> read($Heap, this, _module.Composite.left)
       != read($Heap, this, _module.Composite.right);
  requires read($Heap, this, _module.Composite.right) != null
     ==> S#0[$Box(read($Heap, this, _module.Composite.right))];
  requires read($Heap, this, _module.Composite.right) != null
     ==> read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.parent)
       == this;
  requires read($Heap, this, _module.Composite.right) != null
     ==> read($Heap, this, _module.Composite.left)
       != read($Heap, this, _module.Composite.right);
  requires read($Heap, this, _module.Composite.sum) + delta#0
     == read($Heap, this, _module.Composite.val)
       + (if read($Heap, this, _module.Composite.left) == null
         then 0
         else read($Heap, read($Heap, this, _module.Composite.left), _module.Composite.sum))
       + (if read($Heap, this, _module.Composite.right) == null
         then 0
         else read($Heap, read($Heap, this, _module.Composite.right), _module.Composite.sum));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid#canCall($Heap, c#3, S#0));
  ensures (forall c#3: ref ::
    { _module.Composite.Valid($Heap, c#3, S#0) } { S#0[$Box(c#3)] }
    $Is(c#3, Tclass._module.Composite())
       ==>
      S#0[$Box(c#3)]
       ==> _module.Composite.Valid($Heap, c#3, S#0));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || U#0[$Box($o)]);
  // frame condition: field granularity
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || (U#0[$Box($o)] && $f == _module.Composite.sum));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Composite.Adjust (correctness)"} Impl$$_module.Composite.Adjust(this: ref, delta#0: int, U#0: Set Box, S#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#0: ref
     where $Is(p#0, Tclass._module.Composite?())
       && $IsAlloc(p#0, Tclass._module.Composite?(), $Heap);
  var T#0: Set Box
     where $Is(T#0, TSet(Tclass._module.Composite()))
       && $IsAlloc(T#0, TSet(Tclass._module.Composite()), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var newtype$check#5: ref;
  var ##S#3: Set Box;
  var c#4: ref;
  var ##S#4: Set Box;
  var newtype$check#6: ref;
  var newtype$check#7: ref;
  var newtype$check#8: ref;
  var c#6: ref;
  var newtype$check#9: ref;
  var $decr$loop#00: Set Box;
  var $rhs#0_0: int;

    // AddMethodImpl: Adjust, Impl$$_module.Composite.Adjust
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> U#0[$Box($o)] && $f == _module.Composite.sum);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(122,23)
    assume true;
    assume true;
    p#0 := this;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(123,17)
    assume true;
    assume true;
    T#0 := U#0;
    // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(124,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := T#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Set#Subset(T#0, U#0);
      free invariant $w$loop#0 ==> p#0 != null ==> _module.Composite.Acyclic#canCall($Heap, p#0, T#0);
      invariant $w$loop#0
         ==> p#0 == null || _module.Composite.Acyclic($LS($LS($LZ)), $Heap, p#0, T#0);
      free invariant $w$loop#0
         ==> (forall c#5: ref ::
          { _module.Composite.Valid($Heap, c#5, S#0) } { S#0[$Box(c#5)] }
          $Is(c#5, Tclass._module.Composite())
             ==>
            S#0[$Box(c#5)]
             ==>
            c#5 != p#0
             ==> _module.Composite.Valid#canCall($Heap, c#5, S#0));
      invariant $w$loop#0
         ==> (forall c#5: ref ::
          { _module.Composite.Valid($Heap, c#5, S#0) } { S#0[$Box(c#5)] }
          $Is(c#5, Tclass._module.Composite())
             ==>
            S#0[$Box(c#5)] && c#5 != p#0
             ==> _module.Composite.Valid($Heap, c#5, S#0));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==>
        p#0 != null
         ==> read($Heap, p#0, _module.Composite.sum) + delta#0
           == read($Heap, p#0, _module.Composite.val)
             + (if read($Heap, p#0, _module.Composite.left) == null
               then 0
               else read($Heap, read($Heap, p#0, _module.Composite.left), _module.Composite.sum))
             + (if read($Heap, p#0, _module.Composite.right) == null
               then 0
               else read($Heap, read($Heap, p#0, _module.Composite.right), _module.Composite.sum));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall c#7: ref ::
          { read(old($Heap), c#7, _module.Composite.val) }
            { read($Heap, c#7, _module.Composite.val) }
            { read(old($Heap), c#7, _module.Composite.parent) }
            { read($Heap, c#7, _module.Composite.parent) }
            { read(old($Heap), c#7, _module.Composite.right) }
            { read($Heap, c#7, _module.Composite.right) }
            { read(old($Heap), c#7, _module.Composite.left) }
            { read($Heap, c#7, _module.Composite.left) }
            { S#0[$Box(c#7)] }
          $Is(c#7, Tclass._module.Composite())
             ==> (S#0[$Box(c#7)]
                 ==> read($Heap, c#7, _module.Composite.left)
                   == read(old($Heap), c#7, _module.Composite.left))
               && (S#0[$Box(c#7)]
                 ==> read($Heap, c#7, _module.Composite.right)
                   == read(old($Heap), c#7, _module.Composite.right))
               && (S#0[$Box(c#7)]
                 ==> read($Heap, c#7, _module.Composite.parent)
                   == read(old($Heap), c#7, _module.Composite.parent))
               && (S#0[$Box(c#7)]
                 ==> read($Heap, c#7, _module.Composite.val)
                   == read(old($Heap), c#7, _module.Composite.val)));
      free invariant (forall $o: ref ::
        { $Heap[$o] }
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || U#0[$Box($o)]);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || (U#0[$Box($o)] && $f == _module.Composite.sum));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Set#Subset(T#0, $decr_init$loop#00)
         && (Set#Equal(T#0, $decr_init$loop#00) ==> true);
    {
        if (!$w$loop#0)
        {
            assume true;
            assume Set#Subset(T#0, U#0);
            newtype$check#5 := null;
            if (p#0 != null)
            {
                assert {:subsumption 0} p#0 != null;
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(p#0, Tclass._module.Composite?(), $Heap);
                ##S#3 := T#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##S#3, TSet(Tclass._module.Composite()), $Heap);
                assume _module.Composite.Acyclic#canCall($Heap, p#0, T#0);
            }

            assume p#0 != null ==> _module.Composite.Acyclic#canCall($Heap, p#0, T#0);
            assume p#0 == null || _module.Composite.Acyclic($LS($LZ), $Heap, p#0, T#0);
            // Begin Comprehension WF check
            havoc c#4;
            if ($Is(c#4, Tclass._module.Composite())
               && $IsAlloc(c#4, Tclass._module.Composite(), $Heap))
            {
                if (S#0[$Box(c#4)])
                {
                }

                if (S#0[$Box(c#4)] && c#4 != p#0)
                {
                    assert {:subsumption 0} c#4 != null;
                    // assume allocatedness for receiver argument to function
                    assume $IsAlloc(c#4, Tclass._module.Composite?(), $Heap);
                    ##S#4 := S#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##S#4, TSet(Tclass._module.Composite()), $Heap);
                    assume _module.Composite.Valid#canCall($Heap, c#4, S#0);
                }
            }

            // End Comprehension WF check
            assume (forall c#5: ref ::
              { _module.Composite.Valid($Heap, c#5, S#0) } { S#0[$Box(c#5)] }
              $Is(c#5, Tclass._module.Composite())
                 ==>
                S#0[$Box(c#5)]
                 ==>
                c#5 != p#0
                 ==> _module.Composite.Valid#canCall($Heap, c#5, S#0));
            assume (forall c#5: ref ::
              { _module.Composite.Valid($Heap, c#5, S#0) } { S#0[$Box(c#5)] }
              $Is(c#5, Tclass._module.Composite())
                 ==>
                S#0[$Box(c#5)] && c#5 != p#0
                 ==> _module.Composite.Valid($Heap, c#5, S#0));
            newtype$check#6 := null;
            if (p#0 != null)
            {
                assert {:subsumption 0} p#0 != null;
                assert {:subsumption 0} p#0 != null;
                assert {:subsumption 0} p#0 != null;
                newtype$check#7 := null;
                if (read($Heap, p#0, _module.Composite.left) == null)
                {
                }
                else
                {
                    assert {:subsumption 0} p#0 != null;
                    assert {:subsumption 0} read($Heap, p#0, _module.Composite.left) != null;
                }

                assert {:subsumption 0} p#0 != null;
                newtype$check#8 := null;
                if (read($Heap, p#0, _module.Composite.right) == null)
                {
                }
                else
                {
                    assert {:subsumption 0} p#0 != null;
                    assert {:subsumption 0} read($Heap, p#0, _module.Composite.right) != null;
                }
            }

            assume true;
            assume p#0 != null
               ==> read($Heap, p#0, _module.Composite.sum) + delta#0
                 == read($Heap, p#0, _module.Composite.val)
                   + (if read($Heap, p#0, _module.Composite.left) == null
                     then 0
                     else read($Heap, read($Heap, p#0, _module.Composite.left), _module.Composite.sum))
                   + (if read($Heap, p#0, _module.Composite.right) == null
                     then 0
                     else read($Heap, read($Heap, p#0, _module.Composite.right), _module.Composite.sum));
            // Begin Comprehension WF check
            havoc c#6;
            if ($Is(c#6, Tclass._module.Composite())
               && $IsAlloc(c#6, Tclass._module.Composite(), $Heap))
            {
                if (S#0[$Box(c#6)])
                {
                    assert {:subsumption 0} c#6 != null;
                    assert {:subsumption 0} c#6 != null;
                    assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
                    if (read($Heap, c#6, _module.Composite.left)
                       == read(old($Heap), c#6, _module.Composite.left))
                    {
                        assert {:subsumption 0} c#6 != null;
                        assert {:subsumption 0} c#6 != null;
                        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
                    }

                    if (read($Heap, c#6, _module.Composite.left)
                         == read(old($Heap), c#6, _module.Composite.left)
                       && read($Heap, c#6, _module.Composite.right)
                         == read(old($Heap), c#6, _module.Composite.right))
                    {
                        assert {:subsumption 0} c#6 != null;
                        assert {:subsumption 0} c#6 != null;
                        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
                    }

                    if (read($Heap, c#6, _module.Composite.left)
                         == read(old($Heap), c#6, _module.Composite.left)
                       && read($Heap, c#6, _module.Composite.right)
                         == read(old($Heap), c#6, _module.Composite.right)
                       && read($Heap, c#6, _module.Composite.parent)
                         == read(old($Heap), c#6, _module.Composite.parent))
                    {
                        assert {:subsumption 0} c#6 != null;
                        assert {:subsumption 0} c#6 != null;
                        assert $IsAlloc(c#6, Tclass._module.Composite(), old($Heap));
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall c#7: ref ::
              { read(old($Heap), c#7, _module.Composite.val) }
                { read($Heap, c#7, _module.Composite.val) }
                { read(old($Heap), c#7, _module.Composite.parent) }
                { read($Heap, c#7, _module.Composite.parent) }
                { read(old($Heap), c#7, _module.Composite.right) }
                { read($Heap, c#7, _module.Composite.right) }
                { read(old($Heap), c#7, _module.Composite.left) }
                { read($Heap, c#7, _module.Composite.left) }
                { S#0[$Box(c#7)] }
              $Is(c#7, Tclass._module.Composite())
                 ==> (S#0[$Box(c#7)]
                     ==> read($Heap, c#7, _module.Composite.left)
                       == read(old($Heap), c#7, _module.Composite.left))
                   && (S#0[$Box(c#7)]
                     ==> read($Heap, c#7, _module.Composite.right)
                       == read(old($Heap), c#7, _module.Composite.right))
                   && (S#0[$Box(c#7)]
                     ==> read($Heap, c#7, _module.Composite.parent)
                       == read(old($Heap), c#7, _module.Composite.parent))
                   && (S#0[$Box(c#7)]
                     ==> read($Heap, c#7, _module.Composite.val)
                       == read(old($Heap), c#7, _module.Composite.val)));
            assume true;
            assume false;
        }

        newtype$check#9 := null;
        assume true;
        if (p#0 == null)
        {
            break;
        }

        $decr$loop#00 := T#0;
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(132,13)
        assert p#0 != null;
        assume true;
        assert $_Frame[p#0, _module.Composite.sum];
        assert p#0 != null;
        assume true;
        $rhs#0_0 := read($Heap, p#0, _module.Composite.sum) + delta#0;
        $Heap := update($Heap, p#0, _module.Composite.sum, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(133,9)
        assume true;
        assume true;
        T#0 := Set#Difference(T#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0)));
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(134,9)
        assume true;
        assert p#0 != null;
        assume true;
        p#0 := read($Heap, p#0, _module.Composite.parent);
        // ----- loop termination check ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(124,5)
        assert Set#Subset(T#0, $decr$loop#00) && !Set#Subset($decr$loop#00, T#0);
        assume Set#Subset(T#0, U#0)
           ==> (p#0 != null ==> _module.Composite.Acyclic#canCall($Heap, p#0, T#0))
             && (p#0 == null || _module.Composite.Acyclic($LS($LZ), $Heap, p#0, T#0)
               ==> (forall c#5: ref ::
                { _module.Composite.Valid($Heap, c#5, S#0) } { S#0[$Box(c#5)] }
                $Is(c#5, Tclass._module.Composite())
                   ==>
                  S#0[$Box(c#5)]
                   ==>
                  c#5 != p#0
                   ==> _module.Composite.Valid#canCall($Heap, c#5, S#0)));
    }
}



// _module.Composite: non-null type $Is
axiom (forall c#0: ref ::
  { $Is(c#0, Tclass._module.Composite()) }
  $Is(c#0, Tclass._module.Composite())
     <==> $Is(c#0, Tclass._module.Composite?()) && c#0 != null);

// _module.Composite: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap ::
  { $IsAlloc(c#0, Tclass._module.Composite(), $h) }
  $IsAlloc(c#0, Tclass._module.Composite(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Composite?(), $h));

const unique class._module.__default: ClassName;

function Tclass._module.__default() : Ty;

const unique Tagclass._module.__default: TyTag;

// Tclass._module.__default Tag
axiom Tag(Tclass._module.__default()) == Tagclass._module.__default
   && TagFamily(Tclass._module.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass._module.__default
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.__default()) }
  $IsBox(bx, Tclass._module.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.__default()));

// _default: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.__default()) }
  $Is($o, Tclass._module.__default())
     <==> $o == null || dtype($o) == Tclass._module.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.__default(), $h) }
  $IsAlloc($o, Tclass._module.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure {:verboseName "Main (well-formedness)"} CheckWellFormed$$_module.__default.Main();
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Main (call)"} Call$$_module.__default.Main();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Main (correctness)"} Impl$$_module.__default.Main() returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Main (correctness)"} Impl$$_module.__default.Main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#c0#0: bool;
  var c0#0: ref
     where defass#c0#0
       ==> $Is(c0#0, Tclass._module.Composite())
         && $IsAlloc(c0#0, Tclass._module.Composite(), $Heap);
  var $nw: ref;
  var x##0: int;
  var defass#c1#0: bool;
  var c1#0: ref
     where defass#c1#0
       ==> $Is(c1#0, Tclass._module.Composite())
         && $IsAlloc(c1#0, Tclass._module.Composite(), $Heap);
  var x##1: int;
  var S##0: Set Box;
  var child##0: ref;
  var U##0: Set Box;
  var defass#c2#0: bool;
  var c2#0: ref
     where defass#c2#0
       ==> $Is(c2#0, Tclass._module.Composite())
         && $IsAlloc(c2#0, Tclass._module.Composite(), $Heap);
  var x##2: int;
  var defass#c3#0: bool;
  var c3#0: ref
     where defass#c3#0
       ==> $Is(c3#0, Tclass._module.Composite())
         && $IsAlloc(c3#0, Tclass._module.Composite(), $Heap);
  var x##3: int;
  var S##1: Set Box;
  var child##1: ref;
  var U##1: Set Box;
  var S##2: Set Box;
  var child##2: ref;
  var U##2: Set Box;
  var S#0: Set Box
     where $Is(S#0, TSet(Tclass._module.Composite()))
       && $IsAlloc(S#0, TSet(Tclass._module.Composite()), $Heap);
  var x##4: int;
  var S##3: Set Box;
  var x##5: int;
  var S##4: Set Box;
  var S##5: Set Box;
  var x##6: int;
  var S##6: Set Box;
  var x##7: int;
  var S##7: Set Box;

    // AddMethodImpl: Main, Impl$$_module.__default.Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(141,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(141,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(57);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##0);
    // TrCallStmt: After ProcessCallStmt
    c0#0 := $nw;
    defass#c0#0 := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(143,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(143,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(12);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##1);
    // TrCallStmt: After ProcessCallStmt
    c1#0 := $nw;
    defass#c1#0 := true;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(144,9)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c0#0;
    assume true;
    assert c0#0 != null;
    assert defass#c0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##0 := Set#UnionOne(Set#Empty(): Set Box, $Box(c0#0));
    assert defass#c1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    child##0 := c1#0;
    assert defass#c1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##0 := Set#UnionOne(Set#Empty(): Set Box, $Box(c1#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && (S##0[$Box($o)] || $o == child##0)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Add(c0#0, S##0, child##0, U##0);
    // TrCallStmt: After ProcessCallStmt
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(146,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(146,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##2 := LitInt(48);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##2);
    // TrCallStmt: After ProcessCallStmt
    c2#0 := $nw;
    defass#c2#0 := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(148,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(148,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##3 := LitInt(48);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##3);
    // TrCallStmt: After ProcessCallStmt
    c3#0 := $nw;
    defass#c3#0 := true;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(149,9)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c2#0;
    assume true;
    assert c2#0 != null;
    assert defass#c2#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##1 := Set#UnionOne(Set#Empty(): Set Box, $Box(c2#0));
    assert defass#c3#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    child##1 := c3#0;
    assert defass#c3#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##1 := Set#UnionOne(Set#Empty(): Set Box, $Box(c3#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && (S##1[$Box($o)] || $o == child##1)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Add(c2#0, S##1, child##1, U##1);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(150,9)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c0#0;
    assume true;
    assert c0#0 != null;
    assert defass#c0#0;
    assert defass#c1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##2 := Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c0#0)), $Box(c1#0));
    assert defass#c2#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    child##2 := c2#0;
    assert defass#c2#0;
    assert defass#c3#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##2 := Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c2#0)), $Box(c3#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && (S##2[$Box($o)] || $o == child##2)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Add(c0#0, S##2, child##2, U##2);
    // TrCallStmt: After ProcessCallStmt
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(152,15)
    assume true;
    assert defass#c0#0;
    assert defass#c1#0;
    assert defass#c2#0;
    assert defass#c3#0;
    assume true;
    S#0 := Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c0#0)), $Box(c1#0)),
        $Box(c2#0)),
      $Box(c3#0));
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(153,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c1#0;
    assume true;
    assert c1#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##4 := LitInt(100);
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##3 := S#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##3[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Update(c1#0, x##4, S##3);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(154,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c2#0;
    assume true;
    assert c2#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##5 := LitInt(102);
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##4 := S#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##4[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Update(c2#0, x##5, S##4);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(156,14)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c2#0;
    assume true;
    assert c2#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##5 := S#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##5[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Dislodge(c2#0, S##5);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(157,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c2#0;
    assume true;
    assert c2#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##6 := LitInt(496);
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##6 := S#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##6[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Update(c2#0, x##6, S##6);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(158,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#c0#0;
    assume true;
    assert c0#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##7 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##7 := S#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##7[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Update(c0#0, x##7, S##7);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "Harness (well-formedness)"} CheckWellFormed$$_module.__default.Harness();
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Harness (call)"} Call$$_module.__default.Harness();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Harness (correctness)"} Impl$$_module.__default.Harness() returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Harness (correctness)"} Impl$$_module.__default.Harness() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#a#0: bool;
  var a#0: ref
     where defass#a#0
       ==> $Is(a#0, Tclass._module.Composite())
         && $IsAlloc(a#0, Tclass._module.Composite(), $Heap);
  var $nw: ref;
  var x##0: int;
  var defass#b#0: bool;
  var b#0: ref
     where defass#b#0
       ==> $Is(b#0, Tclass._module.Composite())
         && $IsAlloc(b#0, Tclass._module.Composite(), $Heap);
  var x##1: int;
  var S##0: Set Box;
  var child##0: ref;
  var U##0: Set Box;
  var x##2: int;
  var S##1: Set Box;
  var defass#c#0: bool;
  var c#0: ref
     where defass#c#0
       ==> $Is(c#0, Tclass._module.Composite())
         && $IsAlloc(c#0, Tclass._module.Composite(), $Heap);
  var x##3: int;
  var S##2: Set Box;
  var child##1: ref;
  var U##1: Set Box;
  var S##3: Set Box;

    // AddMethodImpl: Harness, Impl$$_module.__default.Harness
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(162,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(162,26)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(5);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##0);
    // TrCallStmt: After ProcessCallStmt
    a#0 := $nw;
    defass#a#0 := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(163,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(163,26)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(7);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##1);
    // TrCallStmt: After ProcessCallStmt
    b#0 := $nw;
    defass#b#0 := true;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(164,8)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#a#0;
    assume true;
    assert a#0 != null;
    assert defass#a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##0 := Set#UnionOne(Set#Empty(): Set Box, $Box(a#0));
    assert defass#b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    child##0 := b#0;
    assert defass#b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##0 := Set#UnionOne(Set#Empty(): Set Box, $Box(b#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && (S##0[$Box($o)] || $o == child##0)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Add(a#0, S##0, child##0, U##0);
    // TrCallStmt: After ProcessCallStmt
    // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(165,3)
    assert defass#a#0;
    assert {:subsumption 0} a#0 != null;
    assume true;
    assert read($Heap, a#0, _module.Composite.sum) == LitInt(12);
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(167,11)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b#0;
    assume true;
    assert b#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##2 := LitInt(17);
    assert defass#a#0;
    assert defass#b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##1 := Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(a#0)), $Box(b#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##1[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Update(b#0, x##2, S##1);
    // TrCallStmt: After ProcessCallStmt
    // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(168,3)
    assert defass#a#0;
    assert {:subsumption 0} a#0 != null;
    assume true;
    assert read($Heap, a#0, _module.Composite.sum) == LitInt(22);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(170,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Composite?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(170,26)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##3 := LitInt(10);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Init($nw, x##3);
    // TrCallStmt: After ProcessCallStmt
    c#0 := $nw;
    defass#c#0 := true;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(171,8)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b#0;
    assume true;
    assert b#0 != null;
    assert defass#a#0;
    assert defass#b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##2 := Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(a#0)), $Box(b#0));
    assert defass#c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    child##1 := c#0;
    assert defass#c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    U##1 := Set#UnionOne(Set#Empty(): Set Box, $Box(c#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && (S##2[$Box($o)] || $o == child##1)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Add(b#0, S##2, child##1, U##1);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(172,13)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b#0;
    assume true;
    assert b#0 != null;
    assert defass#a#0;
    assert defass#b#0;
    assert defass#c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##3 := Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(a#0)), $Box(b#0)),
      $Box(c#0));
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##3[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Composite.Dislodge(b#0, S##3);
    // TrCallStmt: After ProcessCallStmt
    // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\Composite.dfy(173,3)
    assert defass#b#0;
    assert {:subsumption 0} b#0 != null;
    assume true;
    assert read($Heap, b#0, _module.Composite.sum) == LitInt(27);
}



const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Composite: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$left: NameFamily;

const unique field$right: NameFamily;

const unique field$parent: NameFamily;

const unique field$val: NameFamily;

const unique field$sum: NameFamily;
