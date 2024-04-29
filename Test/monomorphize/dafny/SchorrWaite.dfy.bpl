// Dafny 3.7.3.40719
// Command Line Options: /compile:0 /print:SchorrWaite.dfy.bpl
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

function Tclass._System.___hFunc3(Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc3: TyTag;

// Tclass._System.___hFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tag(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       == Tagclass._System.___hFunc3
     && TagFamily(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       == tytagFamily$_#Func3);

function Tclass._System.___hFunc3_0(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_0(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hFunc3_1(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_1(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hFunc3_2(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_2(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hFunc3_3(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_3(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)));

function Handle3([Heap,Box,Box,Box]Box, [Heap,Box,Box,Box]bool, [Heap,Box,Box,Box]Set Box)
   : HandleType;

function Apply3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Box;

function Requires3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : bool;

function Reads3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) }
  Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)
     == h[heap, bx0, bx1, bx2]);

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) }
  r[heap, bx0, bx1, bx2]
     ==> Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2));

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx: Box ::
  { Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx] }
  Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx]
     == rd[heap, bx0, bx1, bx2][bx]);

function {:inline} Requires3#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box)
   : bool
{
  true
}

function {:inline} Reads3#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box)
   : bool
{
  true
}

// frame axiom for Reads3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Reads3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// empty-reads property for Reads3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) }
    { Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     ==> (Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
       <==> Set#Equal(Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2), Set#Empty(): Set Box)));

// empty-reads property for Requires3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) }
    { Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
     ==> Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty ::
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)) }
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box ::
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
      $IsGoodHeap(h)
           &&
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, u0: Ty, u1: Ty, u2: Ty, u3: Ty ::
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)), $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)) }
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall bx: Box ::
        { $IsBox(bx, u0) } { $IsBox(bx, t0) }
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box ::
        { $IsBox(bx, u1) } { $IsBox(bx, t1) }
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box ::
        { $IsBox(bx, u2) } { $IsBox(bx, t2) }
        $IsBox(bx, u2) ==> $IsBox(bx, t2))
       && (forall bx: Box ::
        { $IsBox(bx, t3) } { $IsBox(bx, u3) }
        $IsBox(bx, t3) ==> $IsBox(bx, u3))
     ==> $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box ::
        { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
          { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             &&
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             &&
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
           ==> (forall r: ref ::
            { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)] }
            r != null && Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box ::
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsAllocBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3, h)));

function Tclass._System.___hPartialFunc3(Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc3: TyTag;

// Tclass._System.___hPartialFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tag(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       == Tagclass._System.___hPartialFunc3
     && TagFamily(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       == tytagFamily$_#PartialFunc3);

function Tclass._System.___hPartialFunc3_0(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_0(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc3_1(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_1(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc3_2(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_2(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc3_3(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_3(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#PartialFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box ::
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Set#Equal(Reads3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0),
            Set#Empty(): Set Box)));

// _System._#PartialFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R), $h));

function Tclass._System.___hTotalFunc3(Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc3: TyTag;

// Tclass._System.___hTotalFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tag(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
       == Tagclass._System.___hTotalFunc3
     && TagFamily(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
       == tytagFamily$_#TotalFunc3);

function Tclass._System.___hTotalFunc3_0(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_0(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc3_1(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_1(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc3_2(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_2(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc3_3(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_3(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#TotalFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box ::
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Requires3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0)));

// _System._#TotalFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h));

function Tclass._System.___hFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc4: TyTag;

// Tclass._System.___hFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tag(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hFunc4
     && TagFamily(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#Func4);

function Tclass._System.___hFunc4_0(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hFunc4_0(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hFunc4_1(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hFunc4_1(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hFunc4_2(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hFunc4_2(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hFunc4_3(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hFunc4_3(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hFunc4_4(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hFunc4_4(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

function Handle4([Heap,Box,Box,Box,Box]Box,
    [Heap,Box,Box,Box,Box]bool,
    [Heap,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : Box;

function Requires4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : bool;

function Reads4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { Apply4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3) }
  Apply4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)
     == h[heap, bx0, bx1, bx2, bx3]);

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { Requires4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3) }
  r[heap, bx0, bx1, bx2, bx3]
     ==> Requires4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3));

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx: Box ::
  { Reads4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)[bx] }
  Reads4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)[bx]
     == rd[heap, bx0, bx1, bx2, bx3][bx]);

function {:inline} Requires4#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box)
   : bool
{
  true
}

function {:inline} Reads4#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box)
   : bool
{
  true
}

// frame axiom for Reads4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { $HeapSucc(h0, h1), Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Reads4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { $HeapSucc(h0, h1), Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Requires4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { $HeapSucc(h0, h1), Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Requires4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { $HeapSucc(h0, h1), Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Apply4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { $HeapSucc(h0, h1), Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Apply4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { $HeapSucc(h0, h1), Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// empty-reads property for Reads4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), $IsGoodHeap(heap) }
    { Reads4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
     ==> (Set#Equal(Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3),
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3), Set#Empty(): Set Box)));

// empty-reads property for Requires4
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box ::
  { Requires4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), $IsGoodHeap(heap) }
    { Requires4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && Set#Equal(Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3),
        Set#Empty(): Set Box)
     ==> Requires4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty ::
  { $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4)) }
  $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box, bx3: Box ::
      { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) }
      $IsGoodHeap(h)
           &&
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
         ==> $IsBox(Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3), t4)));

axiom (forall f: HandleType,
    t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    u0: Ty,
    u1: Ty,
    u2: Ty,
    u3: Ty,
    u4: Ty ::
  { $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4)), $Is(f, Tclass._System.___hFunc4(u0, u1, u2, u3, u4)) }
  $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall bx: Box ::
        { $IsBox(bx, u0) } { $IsBox(bx, t0) }
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box ::
        { $IsBox(bx, u1) } { $IsBox(bx, t1) }
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box ::
        { $IsBox(bx, u2) } { $IsBox(bx, t2) }
        $IsBox(bx, u2) ==> $IsBox(bx, t2))
       && (forall bx: Box ::
        { $IsBox(bx, u3) } { $IsBox(bx, t3) }
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box ::
        { $IsBox(bx, t4) } { $IsBox(bx, u4) }
        $IsBox(bx, t4) ==> $IsBox(bx, u4))
     ==> $Is(f, Tclass._System.___hFunc4(u0, u1, u2, u3, u4)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box ::
        { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) }
          { Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) }
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             &&
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             &&
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             &&
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
           ==> (forall r: ref ::
            { Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)[$Box(r)] }
            r != null && Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box ::
      { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) }
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
         ==> $IsAllocBox(Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3), t4, h)));

function Tclass._System.___hPartialFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc4: TyTag;

// Tclass._System.___hPartialFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tag(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hPartialFunc4
     && TagFamily(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#PartialFunc4);

function Tclass._System.___hPartialFunc4_0(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hPartialFunc4_0(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc4_1(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hPartialFunc4_1(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc4_2(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hPartialFunc4_2(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc4_3(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hPartialFunc4_3(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc4_4(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hPartialFunc4_4(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType,
        Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

// _System._#PartialFunc4: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box ::
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
           ==> Set#Equal(Reads4(#$T0, #$T1, #$T2, #$T3, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0),
            Set#Empty(): Set Box)));

// _System._#PartialFunc4: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h));

function Tclass._System.___hTotalFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc4: TyTag;

// Tclass._System.___hTotalFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tag(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hTotalFunc4
     && TagFamily(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#TotalFunc4);

function Tclass._System.___hTotalFunc4_0(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hTotalFunc4_0(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc4_1(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hTotalFunc4_1(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc4_2(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hTotalFunc4_2(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc4_3(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hTotalFunc4_3(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc4_4(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) }
  Tclass._System.___hTotalFunc4_4(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType,
        Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

// _System._#TotalFunc4: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box ::
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
           ==> Requires4(#$T0, #$T1, #$T2, #$T3, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0)));

// _System._#TotalFunc4: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h));

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

const unique class._module.Node?: ClassName;

function Tclass._module.Node?() : Ty;

const unique Tagclass._module.Node?: TyTag;

// Tclass._module.Node? Tag
axiom Tag(Tclass._module.Node?()) == Tagclass._module.Node?
   && TagFamily(Tclass._module.Node?()) == tytagFamily$Node;

// Box/unbox axiom for Tclass._module.Node?
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Node?()) }
  $IsBox(bx, Tclass._module.Node?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node?()));

// Node: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.Node?()) }
  $Is($o, Tclass._module.Node?())
     <==> $o == null || dtype($o) == Tclass._module.Node?());

// Node: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Node?(), $h) }
  $IsAlloc($o, Tclass._module.Node?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Node.children) == 0
   && FieldOfDecl(class._module.Node?, field$children) == _module.Node.children
   && !$IsGhostField(_module.Node.children);

const _module.Node.children: Field (Seq Box);

// Node.children: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.children) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.children), TSeq(Tclass._module.Node?())));

// Node.children: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.children) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.children), TSeq(Tclass._module.Node?()), $h));

axiom FDim(_module.Node.marked) == 0
   && FieldOfDecl(class._module.Node?, field$marked) == _module.Node.marked
   && !$IsGhostField(_module.Node.marked);

const _module.Node.marked: Field bool;

// Node.marked: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.marked) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.marked), TBool));

// Node.marked: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.marked) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.marked), TBool, $h));

axiom FDim(_module.Node.childrenVisited) == 0
   && FieldOfDecl(class._module.Node?, field$childrenVisited)
     == _module.Node.childrenVisited
   && !$IsGhostField(_module.Node.childrenVisited);

const _module.Node.childrenVisited: Field int;

// Node.childrenVisited: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.childrenVisited) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.childrenVisited), Tclass._System.nat()));

// Node.childrenVisited: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.childrenVisited) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.childrenVisited), Tclass._System.nat(), $h));

axiom FDim(_module.Node.pathFromRoot) == 0
   && FieldOfDecl(class._module.Node?, field$pathFromRoot)
     == _module.Node.pathFromRoot
   && $IsGhostField(_module.Node.pathFromRoot);

const _module.Node.pathFromRoot: Field DatatypeType;

function Tclass._module.Path() : Ty;

const unique Tagclass._module.Path: TyTag;

// Tclass._module.Path Tag
axiom Tag(Tclass._module.Path()) == Tagclass._module.Path
   && TagFamily(Tclass._module.Path()) == tytagFamily$Path;

// Box/unbox axiom for Tclass._module.Path
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Path()) }
  $IsBox(bx, Tclass._module.Path())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Path()));

// Node.pathFromRoot: Type axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.pathFromRoot) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.pathFromRoot), Tclass._module.Path()));

// Node.pathFromRoot: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.pathFromRoot) }
  $IsGoodHeap($h)
       &&
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.pathFromRoot), Tclass._module.Path(), $h));

function Tclass._module.Node() : Ty;

const unique Tagclass._module.Node: TyTag;

// Tclass._module.Node Tag
axiom Tag(Tclass._module.Node()) == Tagclass._module.Node
   && TagFamily(Tclass._module.Node()) == tytagFamily$Node;

// Box/unbox axiom for Tclass._module.Node
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Node()) }
  $IsBox(bx, Tclass._module.Node())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node()));

// _module.Node: non-null type $Is
axiom (forall c#0: ref ::
  { $Is(c#0, Tclass._module.Node()) }
  $Is(c#0, Tclass._module.Node())
     <==> $Is(c#0, Tclass._module.Node?()) && c#0 != null);

// _module.Node: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap ::
  { $IsAlloc(c#0, Tclass._module.Node(), $h) }
  $IsAlloc(c#0, Tclass._module.Node(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Node?(), $h));

// Constructor function declaration
function #_module.Path.Empty() : DatatypeType;

// Constructor identifier
axiom DatatypeCtorId(#_module.Path.Empty()) == ##_module.Path.Empty;

const unique ##_module.Path.Empty: DtCtorId;

function _module.Path.Empty_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Path.Empty_q(d) }
  _module.Path.Empty_q(d) <==> DatatypeCtorId(d) == ##_module.Path.Empty);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Path.Empty_q(d) }
  _module.Path.Empty_q(d) ==> d == #_module.Path.Empty());

// Constructor $Is
axiom $Is(#_module.Path.Empty(), Tclass._module.Path());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Path.Empty(), Tclass._module.Path(), $h) }
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Path.Empty(), Tclass._module.Path(), $h));

// Constructor literal
axiom #_module.Path.Empty() == Lit(#_module.Path.Empty());

// Constructor function declaration
function #_module.Path.Extend(DatatypeType, ref) : DatatypeType;

// Constructor identifier
axiom (forall a#16#0#0: DatatypeType, a#16#1#0: ref ::
  { #_module.Path.Extend(a#16#0#0, a#16#1#0) }
  DatatypeCtorId(#_module.Path.Extend(a#16#0#0, a#16#1#0))
     == ##_module.Path.Extend);

const unique ##_module.Path.Extend: DtCtorId;

function _module.Path.Extend_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Path.Extend_q(d) }
  _module.Path.Extend_q(d) <==> DatatypeCtorId(d) == ##_module.Path.Extend);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Path.Extend_q(d) }
  _module.Path.Extend_q(d)
     ==> (exists a#17#0#0: DatatypeType, a#17#1#0: ref ::
      d == #_module.Path.Extend(a#17#0#0, a#17#1#0)));

// Constructor $Is
axiom (forall a#18#0#0: DatatypeType, a#18#1#0: ref ::
  { $Is(#_module.Path.Extend(a#18#0#0, a#18#1#0), Tclass._module.Path()) }
  $Is(#_module.Path.Extend(a#18#0#0, a#18#1#0), Tclass._module.Path())
     <==> $Is(a#18#0#0, Tclass._module.Path()) && $Is(a#18#1#0, Tclass._module.Node()));

// Constructor $IsAlloc
axiom (forall a#18#0#0: DatatypeType, a#18#1#0: ref, $h: Heap ::
  { $IsAlloc(#_module.Path.Extend(a#18#0#0, a#18#1#0), Tclass._module.Path(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Path.Extend(a#18#0#0, a#18#1#0), Tclass._module.Path(), $h)
       <==> $IsAlloc(a#18#0#0, Tclass._module.Path(), $h)
         && $IsAlloc(a#18#1#0, Tclass._module.Node(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Path._h0(d), Tclass._module.Path(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Path.Extend_q(d)
       && $IsAlloc(d, Tclass._module.Path(), $h)
     ==> $IsAlloc(_module.Path._h0(d), Tclass._module.Path(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Path._h1(d), Tclass._module.Node(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Path.Extend_q(d)
       && $IsAlloc(d, Tclass._module.Path(), $h)
     ==> $IsAlloc(_module.Path._h1(d), Tclass._module.Node(), $h));

// Constructor literal
axiom (forall a#19#0#0: DatatypeType, a#19#1#0: ref ::
  { #_module.Path.Extend(Lit(a#19#0#0), Lit(a#19#1#0)) }
  #_module.Path.Extend(Lit(a#19#0#0), Lit(a#19#1#0))
     == Lit(#_module.Path.Extend(a#19#0#0, a#19#1#0)));

function _module.Path._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#20#0#0: DatatypeType, a#20#1#0: ref ::
  { #_module.Path.Extend(a#20#0#0, a#20#1#0) }
  _module.Path._h0(#_module.Path.Extend(a#20#0#0, a#20#1#0)) == a#20#0#0);

// Inductive rank
axiom (forall a#21#0#0: DatatypeType, a#21#1#0: ref ::
  { #_module.Path.Extend(a#21#0#0, a#21#1#0) }
  DtRank(a#21#0#0) < DtRank(#_module.Path.Extend(a#21#0#0, a#21#1#0)));

function _module.Path._h1(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#22#0#0: DatatypeType, a#22#1#0: ref ::
  { #_module.Path.Extend(a#22#0#0, a#22#1#0) }
  _module.Path._h1(#_module.Path.Extend(a#22#0#0, a#22#1#0)) == a#22#1#0);

// Depth-one case-split function
function $IsA#_module.Path(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Path(d) }
  $IsA#_module.Path(d) ==> _module.Path.Empty_q(d) || _module.Path.Extend_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _module.Path.Extend_q(d), $Is(d, Tclass._module.Path()) }
    { _module.Path.Empty_q(d), $Is(d, Tclass._module.Path()) }
  $Is(d, Tclass._module.Path())
     ==> _module.Path.Empty_q(d) || _module.Path.Extend_q(d));

// Datatype extensional equality declaration
function _module.Path#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Path.Empty
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _module.Path#Equal(a, b), _module.Path.Empty_q(a) }
    { _module.Path#Equal(a, b), _module.Path.Empty_q(b) }
  _module.Path.Empty_q(a) && _module.Path.Empty_q(b)
     ==> (_module.Path#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Path.Extend
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _module.Path#Equal(a, b), _module.Path.Extend_q(a) }
    { _module.Path#Equal(a, b), _module.Path.Extend_q(b) }
  _module.Path.Extend_q(a) && _module.Path.Extend_q(b)
     ==> (_module.Path#Equal(a, b)
       <==> _module.Path#Equal(_module.Path._h0(a), _module.Path._h0(b))
         && _module.Path._h1(a) == _module.Path._h1(b)));

// Datatype extensionality axiom: _module.Path
axiom (forall a: DatatypeType, b: DatatypeType ::
  { _module.Path#Equal(a, b) }
  _module.Path#Equal(a, b) <==> a == b);

const unique class._module.Path: ClassName;

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

procedure {:verboseName "RecursiveMark (well-formedness)"} CheckWellFormed$$_module.__default.RecursiveMark(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "RecursiveMark (well-formedness)"} CheckWellFormed$$_module.__default.RecursiveMark(root#0: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref;
  var ch#0: ref;
  var newtype$check#0: ref;
  var n#2: ref;
  var n#4: ref;
  var ch#3: ref;
  var newtype$check#1: ref;
  var n#6: ref;

    // AddMethodImpl: RecursiveMark, CheckWellFormed$$_module.__default.RecursiveMark
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume S#0[$Box(root#0)];
    havoc n#0;
    assume $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#0)];
        havoc ch#0;
        assume $Is(ch#0, Tclass._module.Node?())
           && $IsAlloc(ch#0, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#0 != null;
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0));
            if (*)
            {
                newtype$check#0 := null;
                assume ch#0 == null;
            }
            else
            {
                assume ch#0 != null;
                assume S#0[$Box(ch#0)];
            }
        }
        else
        {
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0))
               ==> ch#0 == null || S#0[$Box(ch#0)];
        }

        assume (forall ch#1: ref ::
          { S#0[$Box(ch#1)] }
            { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
          $Is(ch#1, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
             ==> ch#1 == null || S#0[$Box(ch#1)]);
    }
    else
    {
        assume S#0[$Box(n#0)]
           ==> (forall ch#1: ref ::
            { S#0[$Box(ch#1)] }
              { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
            $Is(ch#1, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
               ==> ch#1 == null || S#0[$Box(ch#1)]);
    }

    assume (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node())
         ==>
        S#0[$Box(n#1)]
         ==> (forall ch#2: ref ::
          { S#0[$Box(ch#2)] }
            { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
          $Is(ch#2, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
             ==> ch#2 == null || S#0[$Box(ch#2)]));
    havoc n#2;
    assume $Is(n#2, Tclass._module.Node()) && $IsAlloc(n#2, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#2)];
        assert n#2 != null;
        assume !read($Heap, n#2, _module.Node.marked);
        assert n#2 != null;
        assume read($Heap, n#2, _module.Node.childrenVisited) == LitInt(0);
    }
    else
    {
        assume S#0[$Box(n#2)]
           ==> !read($Heap, n#2, _module.Node.marked)
             && read($Heap, n#2, _module.Node.childrenVisited) == LitInt(0);
    }

    assume (forall n#3: ref ::
      { read($Heap, n#3, _module.Node.childrenVisited) }
        { read($Heap, n#3, _module.Node.marked) }
        { S#0[$Box(n#3)] }
      $Is(n#3, Tclass._module.Node())
         ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
           && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assert root#0 != null;
    assume read($Heap, root#0, _module.Node.marked);
    havoc n#4;
    assume $Is(n#4, Tclass._module.Node()) && $IsAlloc(n#4, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#4)];
        assert n#4 != null;
        assume read($Heap, n#4, _module.Node.marked);
        havoc ch#3;
        assume $Is(ch#3, Tclass._module.Node?())
           && $IsAlloc(ch#3, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#4 != null;
            assume Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#3));
            newtype$check#1 := null;
            assume ch#3 != null;
            assert ch#3 != null;
            assume read($Heap, ch#3, _module.Node.marked);
        }
        else
        {
            assume Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#3))
                 && ch#3 != null
               ==> read($Heap, ch#3, _module.Node.marked);
        }

        assume (forall ch#4: ref ::
          { read($Heap, ch#4, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4)) }
          $Is(ch#4, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4))
               && ch#4 != null
             ==> read($Heap, ch#4, _module.Node.marked));
    }
    else
    {
        assume S#0[$Box(n#4)] && read($Heap, n#4, _module.Node.marked)
           ==> (forall ch#4: ref ::
            { read($Heap, ch#4, _module.Node.marked) }
              { Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4)) }
            $Is(ch#4, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4))
                 && ch#4 != null
               ==> read($Heap, ch#4, _module.Node.marked));
    }

    assume (forall n#5: ref ::
      { read($Heap, n#5, _module.Node.children) }
        { read($Heap, n#5, _module.Node.marked) }
        { S#0[$Box(n#5)] }
      $Is(n#5, Tclass._module.Node())
         ==>
        S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
         ==> (forall ch#5: ref ::
          { read($Heap, ch#5, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
          $Is(ch#5, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
               && ch#5 != null
             ==> read($Heap, ch#5, _module.Node.marked)));
    havoc n#6;
    assume $Is(n#6, Tclass._module.Node()) && $IsAlloc(n#6, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#6)];
        assert n#6 != null;
        assert n#6 != null;
        assert $IsAlloc(n#6, Tclass._module.Node(), old($Heap));
        assume read($Heap, n#6, _module.Node.childrenVisited)
           == read(old($Heap), n#6, _module.Node.childrenVisited);
        assert n#6 != null;
        assert n#6 != null;
        assert $IsAlloc(n#6, Tclass._module.Node(), old($Heap));
        assume Seq#Equal(read($Heap, n#6, _module.Node.children),
          read(old($Heap), n#6, _module.Node.children));
    }
    else
    {
        assume S#0[$Box(n#6)]
           ==> read($Heap, n#6, _module.Node.childrenVisited)
               == read(old($Heap), n#6, _module.Node.childrenVisited)
             && Seq#Equal(read($Heap, n#6, _module.Node.children),
              read(old($Heap), n#6, _module.Node.children));
    }

    assume (forall n#7: ref ::
      { read(old($Heap), n#7, _module.Node.children) }
        { read($Heap, n#7, _module.Node.children) }
        { read(old($Heap), n#7, _module.Node.childrenVisited) }
        { read($Heap, n#7, _module.Node.childrenVisited) }
        { S#0[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node())
         ==> (S#0[$Box(n#7)]
             ==> read($Heap, n#7, _module.Node.childrenVisited)
               == read(old($Heap), n#7, _module.Node.childrenVisited))
           && (S#0[$Box(n#7)]
             ==> Seq#Equal(read($Heap, n#7, _module.Node.children),
              read(old($Heap), n#7, _module.Node.children))));
}



procedure {:verboseName "RecursiveMark (call)"} Call$$_module.__default.RecursiveMark(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.childrenVisited) }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.children) }
      { read($Heap, n#5, _module.Node.marked) }
      { S#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
       ==> (forall ch#5: ref ::
        { read($Heap, ch#5, _module.Node.marked) }
          { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
        $Is(ch#5, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
             && ch#5 != null
           ==> read($Heap, ch#5, _module.Node.marked)));
  free ensures true;
  ensures (forall n#7: ref ::
    { read(old($Heap), n#7, _module.Node.children) }
      { read($Heap, n#7, _module.Node.children) }
      { read(old($Heap), n#7, _module.Node.childrenVisited) }
      { read($Heap, n#7, _module.Node.childrenVisited) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==> (S#0[$Box(n#7)]
           ==> read($Heap, n#7, _module.Node.childrenVisited)
             == read(old($Heap), n#7, _module.Node.childrenVisited))
         && (S#0[$Box(n#7)]
           ==> Seq#Equal(read($Heap, n#7, _module.Node.children),
            read(old($Heap), n#7, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "RecursiveMark (correctness)"} Impl$$_module.__default.RecursiveMark(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.childrenVisited) }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.children) }
      { read($Heap, n#5, _module.Node.marked) }
      { S#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
       ==> (forall ch#5: ref ::
        { read($Heap, ch#5, _module.Node.marked) }
          { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
        $Is(ch#5, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
             && ch#5 != null
           ==> read($Heap, ch#5, _module.Node.marked)));
  free ensures true;
  ensures (forall n#7: ref ::
    { read(old($Heap), n#7, _module.Node.children) }
      { read($Heap, n#7, _module.Node.children) }
      { read(old($Heap), n#7, _module.Node.childrenVisited) }
      { read($Heap, n#7, _module.Node.childrenVisited) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==> (S#0[$Box(n#7)]
           ==> read($Heap, n#7, _module.Node.childrenVisited)
             == read(old($Heap), n#7, _module.Node.childrenVisited))
         && (S#0[$Box(n#7)]
           ==> Seq#Equal(read($Heap, n#7, _module.Node.children),
            read(old($Heap), n#7, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "RecursiveMark (correctness)"} Impl$$_module.__default.RecursiveMark(root#0: ref, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var root##0: ref;
  var S##0: Set Box;
  var stackNodes##0: Set Box;

    // AddMethodImpl: RecursiveMark, Impl$$_module.__default.RecursiveMark
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    $_reverifyPost := false;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(34,22)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    root##0 := root#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##0 := S#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    stackNodes##0 := Lit(Set#Empty(): Set Box);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && S##0[$Box($o)] ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.RecursiveMarkWorker(root##0, S##0, stackNodes##0);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "RecursiveMarkWorker (well-formedness)"} CheckWellFormed$$_module.__default.RecursiveMarkWorker(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap),
    stackNodes#0: Set Box
       where $Is(stackNodes#0, TSet(Tclass._module.Node()))
         && $IsAlloc(stackNodes#0, TSet(Tclass._module.Node()), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "RecursiveMarkWorker (well-formedness)"} CheckWellFormed$$_module.__default.RecursiveMarkWorker(root#0: ref, S#0: Set Box, stackNodes#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref;
  var ch#0: ref;
  var newtype$check#0: ref;
  var n#2: ref;
  var ch#3: ref;
  var newtype$check#1: ref;
  var n#4: ref;
  var n#6: ref;
  var ch#6: ref;
  var newtype$check#2: ref;
  var n#8: ref;
  var n#10: ref;

    // AddMethodImpl: RecursiveMarkWorker, CheckWellFormed$$_module.__default.RecursiveMarkWorker
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume S#0[$Box(root#0)];
    havoc n#0;
    assume $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#0)];
        havoc ch#0;
        assume $Is(ch#0, Tclass._module.Node?())
           && $IsAlloc(ch#0, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#0 != null;
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0));
            if (*)
            {
                newtype$check#0 := null;
                assume ch#0 == null;
            }
            else
            {
                assume ch#0 != null;
                assume S#0[$Box(ch#0)];
            }
        }
        else
        {
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0))
               ==> ch#0 == null || S#0[$Box(ch#0)];
        }

        assume (forall ch#1: ref ::
          { S#0[$Box(ch#1)] }
            { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
          $Is(ch#1, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
             ==> ch#1 == null || S#0[$Box(ch#1)]);
    }
    else
    {
        assume S#0[$Box(n#0)]
           ==> (forall ch#1: ref ::
            { S#0[$Box(ch#1)] }
              { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
            $Is(ch#1, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
               ==> ch#1 == null || S#0[$Box(ch#1)]);
    }

    assume (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node())
         ==>
        S#0[$Box(n#1)]
         ==> (forall ch#2: ref ::
          { S#0[$Box(ch#2)] }
            { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
          $Is(ch#2, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
             ==> ch#2 == null || S#0[$Box(ch#2)]));
    havoc n#2;
    assume $Is(n#2, Tclass._module.Node()) && $IsAlloc(n#2, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#2)];
        assert n#2 != null;
        assume read($Heap, n#2, _module.Node.marked);
        if (*)
        {
            assume stackNodes#0[$Box(n#2)];
        }
        else
        {
            assume !stackNodes#0[$Box(n#2)];
            havoc ch#3;
            assume $Is(ch#3, Tclass._module.Node?())
               && $IsAlloc(ch#3, Tclass._module.Node?(), $Heap);
            if (*)
            {
                assert n#2 != null;
                assume Seq#Contains(read($Heap, n#2, _module.Node.children), $Box(ch#3));
                newtype$check#1 := null;
                assume ch#3 != null;
                assert ch#3 != null;
                assume read($Heap, ch#3, _module.Node.marked);
            }
            else
            {
                assume Seq#Contains(read($Heap, n#2, _module.Node.children), $Box(ch#3))
                     && ch#3 != null
                   ==> read($Heap, ch#3, _module.Node.marked);
            }

            assume (forall ch#4: ref ::
              { read($Heap, ch#4, _module.Node.marked) }
                { Seq#Contains(read($Heap, n#2, _module.Node.children), $Box(ch#4)) }
              $Is(ch#4, Tclass._module.Node?())
                 ==>
                Seq#Contains(read($Heap, n#2, _module.Node.children), $Box(ch#4))
                   && ch#4 != null
                 ==> read($Heap, ch#4, _module.Node.marked));
        }
    }
    else
    {
        assume S#0[$Box(n#2)] && read($Heap, n#2, _module.Node.marked)
           ==> stackNodes#0[$Box(n#2)]
             || (forall ch#4: ref ::
              { read($Heap, ch#4, _module.Node.marked) }
                { Seq#Contains(read($Heap, n#2, _module.Node.children), $Box(ch#4)) }
              $Is(ch#4, Tclass._module.Node?())
                 ==>
                Seq#Contains(read($Heap, n#2, _module.Node.children), $Box(ch#4))
                   && ch#4 != null
                 ==> read($Heap, ch#4, _module.Node.marked));
    }

    assume (forall n#3: ref ::
      { read($Heap, n#3, _module.Node.children) }
        { stackNodes#0[$Box(n#3)] }
        { read($Heap, n#3, _module.Node.marked) }
        { S#0[$Box(n#3)] }
      $Is(n#3, Tclass._module.Node())
         ==>
        S#0[$Box(n#3)] && read($Heap, n#3, _module.Node.marked)
         ==> stackNodes#0[$Box(n#3)]
           || (forall ch#5: ref ::
            { read($Heap, ch#5, _module.Node.marked) }
              { Seq#Contains(read($Heap, n#3, _module.Node.children), $Box(ch#5)) }
            $Is(ch#5, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#3, _module.Node.children), $Box(ch#5))
                 && ch#5 != null
               ==> read($Heap, ch#5, _module.Node.marked)));
    havoc n#4;
    assume $Is(n#4, Tclass._module.Node()) && $IsAlloc(n#4, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume stackNodes#0[$Box(n#4)];
        assert n#4 != null;
        assume read($Heap, n#4, _module.Node.marked);
    }
    else
    {
        assume stackNodes#0[$Box(n#4)] ==> read($Heap, n#4, _module.Node.marked);
    }

    assume (forall n#5: ref ::
      { read($Heap, n#5, _module.Node.marked) } { stackNodes#0[$Box(n#5)] }
      $Is(n#5, Tclass._module.Node())
         ==>
        stackNodes#0[$Box(n#5)]
         ==> read($Heap, n#5, _module.Node.marked));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assert root#0 != null;
    assume read($Heap, root#0, _module.Node.marked);
    havoc n#6;
    assume $Is(n#6, Tclass._module.Node()) && $IsAlloc(n#6, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#6)];
        assert n#6 != null;
        assume read($Heap, n#6, _module.Node.marked);
        if (*)
        {
            assume stackNodes#0[$Box(n#6)];
        }
        else
        {
            assume !stackNodes#0[$Box(n#6)];
            havoc ch#6;
            assume $Is(ch#6, Tclass._module.Node?())
               && $IsAlloc(ch#6, Tclass._module.Node?(), $Heap);
            if (*)
            {
                assert n#6 != null;
                assume Seq#Contains(read($Heap, n#6, _module.Node.children), $Box(ch#6));
                newtype$check#2 := null;
                assume ch#6 != null;
                assert ch#6 != null;
                assume read($Heap, ch#6, _module.Node.marked);
            }
            else
            {
                assume Seq#Contains(read($Heap, n#6, _module.Node.children), $Box(ch#6))
                     && ch#6 != null
                   ==> read($Heap, ch#6, _module.Node.marked);
            }

            assume (forall ch#7: ref ::
              { read($Heap, ch#7, _module.Node.marked) }
                { Seq#Contains(read($Heap, n#6, _module.Node.children), $Box(ch#7)) }
              $Is(ch#7, Tclass._module.Node?())
                 ==>
                Seq#Contains(read($Heap, n#6, _module.Node.children), $Box(ch#7))
                   && ch#7 != null
                 ==> read($Heap, ch#7, _module.Node.marked));
        }
    }
    else
    {
        assume S#0[$Box(n#6)] && read($Heap, n#6, _module.Node.marked)
           ==> stackNodes#0[$Box(n#6)]
             || (forall ch#7: ref ::
              { read($Heap, ch#7, _module.Node.marked) }
                { Seq#Contains(read($Heap, n#6, _module.Node.children), $Box(ch#7)) }
              $Is(ch#7, Tclass._module.Node?())
                 ==>
                Seq#Contains(read($Heap, n#6, _module.Node.children), $Box(ch#7))
                   && ch#7 != null
                 ==> read($Heap, ch#7, _module.Node.marked));
    }

    assume (forall n#7: ref ::
      { read($Heap, n#7, _module.Node.children) }
        { stackNodes#0[$Box(n#7)] }
        { read($Heap, n#7, _module.Node.marked) }
        { S#0[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node())
         ==>
        S#0[$Box(n#7)] && read($Heap, n#7, _module.Node.marked)
         ==> stackNodes#0[$Box(n#7)]
           || (forall ch#8: ref ::
            { read($Heap, ch#8, _module.Node.marked) }
              { Seq#Contains(read($Heap, n#7, _module.Node.children), $Box(ch#8)) }
            $Is(ch#8, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#7, _module.Node.children), $Box(ch#8))
                 && ch#8 != null
               ==> read($Heap, ch#8, _module.Node.marked)));
    havoc n#8;
    assume $Is(n#8, Tclass._module.Node()) && $IsAlloc(n#8, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#8)];
        assert n#8 != null;
        assert $IsAlloc(n#8, Tclass._module.Node(), old($Heap));
        assume read(old($Heap), n#8, _module.Node.marked);
        assert n#8 != null;
        assume read($Heap, n#8, _module.Node.marked);
    }
    else
    {
        assume S#0[$Box(n#8)] && read(old($Heap), n#8, _module.Node.marked)
           ==> read($Heap, n#8, _module.Node.marked);
    }

    assume (forall n#9: ref ::
      { read($Heap, n#9, _module.Node.marked) }
        { read(old($Heap), n#9, _module.Node.marked) }
        { S#0[$Box(n#9)] }
      $Is(n#9, Tclass._module.Node())
         ==>
        S#0[$Box(n#9)] && read(old($Heap), n#9, _module.Node.marked)
         ==> read($Heap, n#9, _module.Node.marked));
    havoc n#10;
    assume $Is(n#10, Tclass._module.Node()) && $IsAlloc(n#10, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#10)];
        assert n#10 != null;
        assert n#10 != null;
        assert $IsAlloc(n#10, Tclass._module.Node(), old($Heap));
        assume read($Heap, n#10, _module.Node.childrenVisited)
           == read(old($Heap), n#10, _module.Node.childrenVisited);
        assert n#10 != null;
        assert n#10 != null;
        assert $IsAlloc(n#10, Tclass._module.Node(), old($Heap));
        assume Seq#Equal(read($Heap, n#10, _module.Node.children),
          read(old($Heap), n#10, _module.Node.children));
    }
    else
    {
        assume S#0[$Box(n#10)]
           ==> read($Heap, n#10, _module.Node.childrenVisited)
               == read(old($Heap), n#10, _module.Node.childrenVisited)
             && Seq#Equal(read($Heap, n#10, _module.Node.children),
              read(old($Heap), n#10, _module.Node.children));
    }

    assume (forall n#11: ref ::
      { read(old($Heap), n#11, _module.Node.children) }
        { read($Heap, n#11, _module.Node.children) }
        { read(old($Heap), n#11, _module.Node.childrenVisited) }
        { read($Heap, n#11, _module.Node.childrenVisited) }
        { S#0[$Box(n#11)] }
      $Is(n#11, Tclass._module.Node())
         ==> (S#0[$Box(n#11)]
             ==> read($Heap, n#11, _module.Node.childrenVisited)
               == read(old($Heap), n#11, _module.Node.childrenVisited))
           && (S#0[$Box(n#11)]
             ==> Seq#Equal(read($Heap, n#11, _module.Node.children),
              read(old($Heap), n#11, _module.Node.children))));
}



procedure {:verboseName "RecursiveMarkWorker (call)"} Call$$_module.__default.RecursiveMarkWorker(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap),
    stackNodes#0: Set Box
       where $Is(stackNodes#0, TSet(Tclass._module.Node()))
         && $IsAlloc(stackNodes#0, TSet(Tclass._module.Node()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.children) }
      { stackNodes#0[$Box(n#3)] }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==>
      S#0[$Box(n#3)] && read($Heap, n#3, _module.Node.marked)
       ==> stackNodes#0[$Box(n#3)]
         || (forall ch#5: ref ::
          { read($Heap, ch#5, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#3, _module.Node.children), $Box(ch#5)) }
          $Is(ch#5, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#3, _module.Node.children), $Box(ch#5))
               && ch#5 != null
             ==> read($Heap, ch#5, _module.Node.marked)));
  requires (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.marked) } { stackNodes#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      stackNodes#0[$Box(n#5)]
       ==> read($Heap, n#5, _module.Node.marked));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#7: ref ::
    { read($Heap, n#7, _module.Node.children) }
      { stackNodes#0[$Box(n#7)] }
      { read($Heap, n#7, _module.Node.marked) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==>
      S#0[$Box(n#7)] && read($Heap, n#7, _module.Node.marked)
       ==> stackNodes#0[$Box(n#7)]
         || (forall ch#8: ref ::
          { read($Heap, ch#8, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#7, _module.Node.children), $Box(ch#8)) }
          $Is(ch#8, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#7, _module.Node.children), $Box(ch#8))
               && ch#8 != null
             ==> read($Heap, ch#8, _module.Node.marked)));
  free ensures true;
  ensures (forall n#9: ref ::
    { read($Heap, n#9, _module.Node.marked) }
      { read(old($Heap), n#9, _module.Node.marked) }
      { S#0[$Box(n#9)] }
    $Is(n#9, Tclass._module.Node())
       ==>
      S#0[$Box(n#9)] && read(old($Heap), n#9, _module.Node.marked)
       ==> read($Heap, n#9, _module.Node.marked));
  free ensures true;
  ensures (forall n#11: ref ::
    { read(old($Heap), n#11, _module.Node.children) }
      { read($Heap, n#11, _module.Node.children) }
      { read(old($Heap), n#11, _module.Node.childrenVisited) }
      { read($Heap, n#11, _module.Node.childrenVisited) }
      { S#0[$Box(n#11)] }
    $Is(n#11, Tclass._module.Node())
       ==> (S#0[$Box(n#11)]
           ==> read($Heap, n#11, _module.Node.childrenVisited)
             == read(old($Heap), n#11, _module.Node.childrenVisited))
         && (S#0[$Box(n#11)]
           ==> Seq#Equal(read($Heap, n#11, _module.Node.children),
            read(old($Heap), n#11, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "RecursiveMarkWorker (correctness)"} Impl$$_module.__default.RecursiveMarkWorker(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap),
    stackNodes#0: Set Box
       where $Is(stackNodes#0, TSet(Tclass._module.Node()))
         && $IsAlloc(stackNodes#0, TSet(Tclass._module.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.children) }
      { stackNodes#0[$Box(n#3)] }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==>
      S#0[$Box(n#3)] && read($Heap, n#3, _module.Node.marked)
       ==> stackNodes#0[$Box(n#3)]
         || (forall ch#5: ref ::
          { read($Heap, ch#5, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#3, _module.Node.children), $Box(ch#5)) }
          $Is(ch#5, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#3, _module.Node.children), $Box(ch#5))
               && ch#5 != null
             ==> read($Heap, ch#5, _module.Node.marked)));
  requires (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.marked) } { stackNodes#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      stackNodes#0[$Box(n#5)]
       ==> read($Heap, n#5, _module.Node.marked));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#7: ref ::
    { read($Heap, n#7, _module.Node.children) }
      { stackNodes#0[$Box(n#7)] }
      { read($Heap, n#7, _module.Node.marked) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==>
      S#0[$Box(n#7)] && read($Heap, n#7, _module.Node.marked)
       ==> stackNodes#0[$Box(n#7)]
         || (forall ch#8: ref ::
          { read($Heap, ch#8, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#7, _module.Node.children), $Box(ch#8)) }
          $Is(ch#8, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#7, _module.Node.children), $Box(ch#8))
               && ch#8 != null
             ==> read($Heap, ch#8, _module.Node.marked)));
  free ensures true;
  ensures (forall n#9: ref ::
    { read($Heap, n#9, _module.Node.marked) }
      { read(old($Heap), n#9, _module.Node.marked) }
      { S#0[$Box(n#9)] }
    $Is(n#9, Tclass._module.Node())
       ==>
      S#0[$Box(n#9)] && read(old($Heap), n#9, _module.Node.marked)
       ==> read($Heap, n#9, _module.Node.marked));
  free ensures true;
  ensures (forall n#11: ref ::
    { read(old($Heap), n#11, _module.Node.children) }
      { read($Heap, n#11, _module.Node.children) }
      { read(old($Heap), n#11, _module.Node.childrenVisited) }
      { read($Heap, n#11, _module.Node.childrenVisited) }
      { S#0[$Box(n#11)] }
    $Is(n#11, Tclass._module.Node())
       ==> (S#0[$Box(n#11)]
           ==> read($Heap, n#11, _module.Node.childrenVisited)
             == read(old($Heap), n#11, _module.Node.childrenVisited))
         && (S#0[$Box(n#11)]
           ==> Seq#Equal(read($Heap, n#11, _module.Node.children),
            read(old($Heap), n#11, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "RecursiveMarkWorker (correctness)"} Impl$$_module.__default.RecursiveMarkWorker(root#0: ref, S#0: Set Box, stackNodes#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: bool;
  var i#0_0: int;
  var $PreLoopHeap$loop#0_0: Heap;
  var $decr_init$loop#0_00: int;
  var $w$loop#0_0: bool;
  var n#0_0: ref;
  var ch#0_0: ref;
  var newtype$check#0_0: ref;
  var j#0_0: int;
  var newtype$check#0_1: ref;
  var n#0_2: ref;
  var n#0_4: ref;
  var $decr$loop#0_00: int;
  var c#0_0_0: ref
     where $Is(c#0_0_0, Tclass._module.Node?())
       && $IsAlloc(c#0_0_0, Tclass._module.Node?(), $Heap);
  var newtype$check#0_0_0: ref;
  var root##0_0_0_0: ref;
  var S##0_0_0_0: Set Box;
  var stackNodes##0_0_0_0: Set Box;

    // AddMethodImpl: RecursiveMarkWorker, Impl$$_module.__default.RecursiveMarkWorker
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    $_reverifyPost := false;
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(57,3)
    assert root#0 != null;
    assume true;
    if (!read($Heap, root#0, _module.Node.marked))
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(58,17)
        assert root#0 != null;
        assume true;
        assert $_Frame[root#0, _module.Node.marked];
        assume true;
        $rhs#0_0 := Lit(true);
        $Heap := update($Heap, root#0, _module.Node.marked, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(59,11)
        assume true;
        assume true;
        i#0_0 := LitInt(0);
        // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(60,5)
        // Assume Fuel Constant
        $PreLoopHeap$loop#0_0 := $Heap;
        $decr_init$loop#0_00 := Seq#Length(read($Heap, root#0, _module.Node.children)) - i#0_0;
        havoc $w$loop#0_0;
        while (true)
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0 ==> read($Heap, root#0, _module.Node.marked);
          invariant $w$loop#0_0 ==> i#0_0 <= Seq#Length(read($Heap, root#0, _module.Node.children));
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0
             ==> (forall n#0_1: ref ::
              { read($Heap, n#0_1, _module.Node.children) }
                { stackNodes#0[$Box(n#0_1)] }
                { read($Heap, n#0_1, _module.Node.marked) }
                { S#0[$Box(n#0_1)] }
              $Is(n#0_1, Tclass._module.Node())
                 ==>
                S#0[$Box(n#0_1)] && read($Heap, n#0_1, _module.Node.marked)
                 ==> n#0_1 == root#0
                   || stackNodes#0[$Box(n#0_1)]
                   || (forall ch#0_1: ref ::
                    { read($Heap, ch#0_1, _module.Node.marked) }
                      { Seq#Contains(read($Heap, n#0_1, _module.Node.children), $Box(ch#0_1)) }
                    $Is(ch#0_1, Tclass._module.Node?())
                       ==>
                      Seq#Contains(read($Heap, n#0_1, _module.Node.children), $Box(ch#0_1))
                         && ch#0_1 != null
                       ==> read($Heap, ch#0_1, _module.Node.marked)));
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0
             ==> (forall j#0_1: int ::
              { $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_1)): ref }
              true
                 ==>
                LitInt(0) <= j#0_1 && j#0_1 < i#0_0
                 ==> $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_1)): ref
                     == null
                   || read($Heap,
                    $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_1)): ref,
                    _module.Node.marked));
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0
             ==> (forall n#0_3: ref ::
              { read($Heap, n#0_3, _module.Node.marked) }
                { read(old($Heap), n#0_3, _module.Node.marked) }
                { S#0[$Box(n#0_3)] }
              $Is(n#0_3, Tclass._module.Node())
                 ==>
                S#0[$Box(n#0_3)] && read(old($Heap), n#0_3, _module.Node.marked)
                 ==> read($Heap, n#0_3, _module.Node.marked));
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0
             ==> (forall n#0_5: ref ::
              { read(old($Heap), n#0_5, _module.Node.children) }
                { read($Heap, n#0_5, _module.Node.children) }
                { read(old($Heap), n#0_5, _module.Node.childrenVisited) }
                { read($Heap, n#0_5, _module.Node.childrenVisited) }
                { S#0[$Box(n#0_5)] }
              $Is(n#0_5, Tclass._module.Node())
                 ==> (S#0[$Box(n#0_5)]
                     ==> read($Heap, n#0_5, _module.Node.childrenVisited)
                       == read(old($Heap), n#0_5, _module.Node.childrenVisited))
                   && (S#0[$Box(n#0_5)]
                     ==> Seq#Equal(read($Heap, n#0_5, _module.Node.children),
                      read(old($Heap), n#0_5, _module.Node.children))));
          free invariant (forall $o: ref ::
            { $Heap[$o] }
            $o != null && read(old($Heap), $o, alloc)
               ==> $Heap[$o] == $PreLoopHeap$loop#0_0[$o] || S#0[$Box($o)]);
          free invariant $HeapSucc($PreLoopHeap$loop#0_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null && read($PreLoopHeap$loop#0_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0_0, $o, $f) || $_Frame[$o, $f]);
          free invariant Seq#Length(read($Heap, root#0, _module.Node.children)) - i#0_0
               <= $decr_init$loop#0_00
             && (Seq#Length(read($Heap, root#0, _module.Node.children)) - i#0_0
                 == $decr_init$loop#0_00
               ==> true);
        {
            if (!$w$loop#0_0)
            {
                assert {:subsumption 0} root#0 != null;
                if (read($Heap, root#0, _module.Node.marked))
                {
                    assert {:subsumption 0} root#0 != null;
                }

                assume true;
                assume read($Heap, root#0, _module.Node.marked)
                   && i#0_0 <= Seq#Length(read($Heap, root#0, _module.Node.children));
                // Begin Comprehension WF check
                havoc n#0_0;
                if ($Is(n#0_0, Tclass._module.Node())
                   && $IsAlloc(n#0_0, Tclass._module.Node(), $Heap))
                {
                    if (S#0[$Box(n#0_0)])
                    {
                        assert {:subsumption 0} n#0_0 != null;
                    }

                    if (S#0[$Box(n#0_0)] && read($Heap, n#0_0, _module.Node.marked))
                    {
                        if (n#0_0 != root#0)
                        {
                        }

                        if (!(n#0_0 == root#0 || stackNodes#0[$Box(n#0_0)]))
                        {
                            // Begin Comprehension WF check
                            havoc ch#0_0;
                            if ($Is(ch#0_0, Tclass._module.Node?())
                               && $IsAlloc(ch#0_0, Tclass._module.Node?(), $Heap))
                            {
                                assert {:subsumption 0} n#0_0 != null;
                                if (Seq#Contains(read($Heap, n#0_0, _module.Node.children), $Box(ch#0_0)))
                                {
                                    newtype$check#0_0 := null;
                                }

                                if (Seq#Contains(read($Heap, n#0_0, _module.Node.children), $Box(ch#0_0))
                                   && ch#0_0 != null)
                                {
                                    assert {:subsumption 0} ch#0_0 != null;
                                }
                            }

                            // End Comprehension WF check
                        }
                    }
                }

                // End Comprehension WF check
                assume true;
                assume (forall n#0_1: ref ::
                  { read($Heap, n#0_1, _module.Node.children) }
                    { stackNodes#0[$Box(n#0_1)] }
                    { read($Heap, n#0_1, _module.Node.marked) }
                    { S#0[$Box(n#0_1)] }
                  $Is(n#0_1, Tclass._module.Node())
                     ==>
                    S#0[$Box(n#0_1)] && read($Heap, n#0_1, _module.Node.marked)
                     ==> n#0_1 == root#0
                       || stackNodes#0[$Box(n#0_1)]
                       || (forall ch#0_1: ref ::
                        { read($Heap, ch#0_1, _module.Node.marked) }
                          { Seq#Contains(read($Heap, n#0_1, _module.Node.children), $Box(ch#0_1)) }
                        $Is(ch#0_1, Tclass._module.Node?())
                           ==>
                          Seq#Contains(read($Heap, n#0_1, _module.Node.children), $Box(ch#0_1))
                             && ch#0_1 != null
                           ==> read($Heap, ch#0_1, _module.Node.marked)));
                // Begin Comprehension WF check
                havoc j#0_0;
                if (true)
                {
                    if (LitInt(0) <= j#0_0)
                    {
                    }

                    if (LitInt(0) <= j#0_0 && j#0_0 < i#0_0)
                    {
                        assert {:subsumption 0} root#0 != null;
                        assert {:subsumption 0} 0 <= j#0_0 && j#0_0 < Seq#Length(read($Heap, root#0, _module.Node.children));
                        newtype$check#0_1 := null;
                        if ($Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_0)): ref
                           != null)
                        {
                            assert {:subsumption 0} root#0 != null;
                            assert {:subsumption 0} 0 <= j#0_0 && j#0_0 < Seq#Length(read($Heap, root#0, _module.Node.children));
                            assert {:subsumption 0} $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_0)): ref
                               != null;
                        }
                    }
                }

                // End Comprehension WF check
                assume true;
                assume (forall j#0_1: int ::
                  { $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_1)): ref }
                  true
                     ==>
                    LitInt(0) <= j#0_1 && j#0_1 < i#0_0
                     ==> $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_1)): ref
                         == null
                       || read($Heap,
                        $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), j#0_1)): ref,
                        _module.Node.marked));
                // Begin Comprehension WF check
                havoc n#0_2;
                if ($Is(n#0_2, Tclass._module.Node())
                   && $IsAlloc(n#0_2, Tclass._module.Node(), $Heap))
                {
                    if (S#0[$Box(n#0_2)])
                    {
                        assert {:subsumption 0} n#0_2 != null;
                        assert $IsAlloc(n#0_2, Tclass._module.Node(), old($Heap));
                    }

                    if (S#0[$Box(n#0_2)] && read(old($Heap), n#0_2, _module.Node.marked))
                    {
                        assert {:subsumption 0} n#0_2 != null;
                    }
                }

                // End Comprehension WF check
                assume true;
                assume (forall n#0_3: ref ::
                  { read($Heap, n#0_3, _module.Node.marked) }
                    { read(old($Heap), n#0_3, _module.Node.marked) }
                    { S#0[$Box(n#0_3)] }
                  $Is(n#0_3, Tclass._module.Node())
                     ==>
                    S#0[$Box(n#0_3)] && read(old($Heap), n#0_3, _module.Node.marked)
                     ==> read($Heap, n#0_3, _module.Node.marked));
                // Begin Comprehension WF check
                havoc n#0_4;
                if ($Is(n#0_4, Tclass._module.Node())
                   && $IsAlloc(n#0_4, Tclass._module.Node(), $Heap))
                {
                    if (S#0[$Box(n#0_4)])
                    {
                        assert {:subsumption 0} n#0_4 != null;
                        assert {:subsumption 0} n#0_4 != null;
                        assert $IsAlloc(n#0_4, Tclass._module.Node(), old($Heap));
                        if (read($Heap, n#0_4, _module.Node.childrenVisited)
                           == read(old($Heap), n#0_4, _module.Node.childrenVisited))
                        {
                            assert {:subsumption 0} n#0_4 != null;
                            assert {:subsumption 0} n#0_4 != null;
                            assert $IsAlloc(n#0_4, Tclass._module.Node(), old($Heap));
                        }
                    }
                }

                // End Comprehension WF check
                assume true;
                assume (forall n#0_5: ref ::
                  { read(old($Heap), n#0_5, _module.Node.children) }
                    { read($Heap, n#0_5, _module.Node.children) }
                    { read(old($Heap), n#0_5, _module.Node.childrenVisited) }
                    { read($Heap, n#0_5, _module.Node.childrenVisited) }
                    { S#0[$Box(n#0_5)] }
                  $Is(n#0_5, Tclass._module.Node())
                     ==> (S#0[$Box(n#0_5)]
                         ==> read($Heap, n#0_5, _module.Node.childrenVisited)
                           == read(old($Heap), n#0_5, _module.Node.childrenVisited))
                       && (S#0[$Box(n#0_5)]
                         ==> Seq#Equal(read($Heap, n#0_5, _module.Node.children),
                          read(old($Heap), n#0_5, _module.Node.children))));
                assert root#0 != null;
                assume true;
                assume false;
            }

            assert root#0 != null;
            assume true;
            if (Seq#Length(read($Heap, root#0, _module.Node.children)) <= i#0_0)
            {
                break;
            }

            $decr$loop#0_00 := Seq#Length(read($Heap, root#0, _module.Node.children)) - i#0_0;
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(73,13)
            assume true;
            assert root#0 != null;
            assert 0 <= i#0_0 && i#0_0 < Seq#Length(read($Heap, root#0, _module.Node.children));
            assume true;
            c#0_0_0 := $Unbox(Seq#Index(read($Heap, root#0, _module.Node.children), i#0_0)): ref;
            // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(74,7)
            newtype$check#0_0_0 := null;
            assume true;
            if (c#0_0_0 != null)
            {
                // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(75,28)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(c#0_0_0, Tclass._module.Node());
                root##0_0_0_0 := c#0_0_0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                S##0_0_0_0 := S#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                stackNodes##0_0_0_0 := Set#Union(stackNodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(root#0)));
                assert (forall<alpha> $o: ref, $f: Field alpha ::
                  $o != null && read($Heap, $o, alloc) && S##0_0_0_0[$Box($o)] ==> $_Frame[$o, $f]);
                assert Set#Subset(Set#Difference(S##0_0_0_0, stackNodes##0_0_0_0),
                    Set#Difference(S#0, stackNodes#0))
                   && !Set#Subset(Set#Difference(S#0, stackNodes#0),
                    Set#Difference(S##0_0_0_0, stackNodes##0_0_0_0));
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.RecursiveMarkWorker(root##0_0_0_0, S##0_0_0_0, stackNodes##0_0_0_0);
                // TrCallStmt: After ProcessCallStmt
            }
            else
            {
            }

            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(77,9)
            assume true;
            assume true;
            i#0_0 := i#0_0 + 1;
            // ----- loop termination check ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(60,5)
            assert 0 <= $decr$loop#0_00
               || Seq#Length(read($Heap, root#0, _module.Node.children)) - i#0_0
                 == $decr$loop#0_00;
            assert Seq#Length(read($Heap, root#0, _module.Node.children)) - i#0_0 < $decr$loop#0_00;
            assume true;
        }
    }
    else
    {
    }
}



procedure {:verboseName "IterativeMark (well-formedness)"} CheckWellFormed$$_module.__default.IterativeMark(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "IterativeMark (well-formedness)"} CheckWellFormed$$_module.__default.IterativeMark(root#0: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref;
  var ch#0: ref;
  var newtype$check#0: ref;
  var n#2: ref;
  var n#4: ref;
  var ch#3: ref;
  var newtype$check#1: ref;
  var n#6: ref;

    // AddMethodImpl: IterativeMark, CheckWellFormed$$_module.__default.IterativeMark
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume S#0[$Box(root#0)];
    havoc n#0;
    assume $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#0)];
        havoc ch#0;
        assume $Is(ch#0, Tclass._module.Node?())
           && $IsAlloc(ch#0, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#0 != null;
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0));
            if (*)
            {
                newtype$check#0 := null;
                assume ch#0 == null;
            }
            else
            {
                assume ch#0 != null;
                assume S#0[$Box(ch#0)];
            }
        }
        else
        {
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0))
               ==> ch#0 == null || S#0[$Box(ch#0)];
        }

        assume (forall ch#1: ref ::
          { S#0[$Box(ch#1)] }
            { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
          $Is(ch#1, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
             ==> ch#1 == null || S#0[$Box(ch#1)]);
    }
    else
    {
        assume S#0[$Box(n#0)]
           ==> (forall ch#1: ref ::
            { S#0[$Box(ch#1)] }
              { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
            $Is(ch#1, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
               ==> ch#1 == null || S#0[$Box(ch#1)]);
    }

    assume (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node())
         ==>
        S#0[$Box(n#1)]
         ==> (forall ch#2: ref ::
          { S#0[$Box(ch#2)] }
            { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
          $Is(ch#2, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
             ==> ch#2 == null || S#0[$Box(ch#2)]));
    havoc n#2;
    assume $Is(n#2, Tclass._module.Node()) && $IsAlloc(n#2, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#2)];
        assert n#2 != null;
        assume !read($Heap, n#2, _module.Node.marked);
        assert n#2 != null;
        assume read($Heap, n#2, _module.Node.childrenVisited) == LitInt(0);
    }
    else
    {
        assume S#0[$Box(n#2)]
           ==> !read($Heap, n#2, _module.Node.marked)
             && read($Heap, n#2, _module.Node.childrenVisited) == LitInt(0);
    }

    assume (forall n#3: ref ::
      { read($Heap, n#3, _module.Node.childrenVisited) }
        { read($Heap, n#3, _module.Node.marked) }
        { S#0[$Box(n#3)] }
      $Is(n#3, Tclass._module.Node())
         ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
           && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assert root#0 != null;
    assume read($Heap, root#0, _module.Node.marked);
    havoc n#4;
    assume $Is(n#4, Tclass._module.Node()) && $IsAlloc(n#4, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#4)];
        assert n#4 != null;
        assume read($Heap, n#4, _module.Node.marked);
        havoc ch#3;
        assume $Is(ch#3, Tclass._module.Node?())
           && $IsAlloc(ch#3, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#4 != null;
            assume Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#3));
            newtype$check#1 := null;
            assume ch#3 != null;
            assert ch#3 != null;
            assume read($Heap, ch#3, _module.Node.marked);
        }
        else
        {
            assume Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#3))
                 && ch#3 != null
               ==> read($Heap, ch#3, _module.Node.marked);
        }

        assume (forall ch#4: ref ::
          { read($Heap, ch#4, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4)) }
          $Is(ch#4, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4))
               && ch#4 != null
             ==> read($Heap, ch#4, _module.Node.marked));
    }
    else
    {
        assume S#0[$Box(n#4)] && read($Heap, n#4, _module.Node.marked)
           ==> (forall ch#4: ref ::
            { read($Heap, ch#4, _module.Node.marked) }
              { Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4)) }
            $Is(ch#4, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4))
                 && ch#4 != null
               ==> read($Heap, ch#4, _module.Node.marked));
    }

    assume (forall n#5: ref ::
      { read($Heap, n#5, _module.Node.children) }
        { read($Heap, n#5, _module.Node.marked) }
        { S#0[$Box(n#5)] }
      $Is(n#5, Tclass._module.Node())
         ==>
        S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
         ==> (forall ch#5: ref ::
          { read($Heap, ch#5, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
          $Is(ch#5, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
               && ch#5 != null
             ==> read($Heap, ch#5, _module.Node.marked)));
    havoc n#6;
    assume $Is(n#6, Tclass._module.Node()) && $IsAlloc(n#6, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#6)];
        assert n#6 != null;
        assert n#6 != null;
        assert $IsAlloc(n#6, Tclass._module.Node(), old($Heap));
        assume read($Heap, n#6, _module.Node.childrenVisited)
           == read(old($Heap), n#6, _module.Node.childrenVisited);
        assert n#6 != null;
        assert n#6 != null;
        assert $IsAlloc(n#6, Tclass._module.Node(), old($Heap));
        assume Seq#Equal(read($Heap, n#6, _module.Node.children),
          read(old($Heap), n#6, _module.Node.children));
    }
    else
    {
        assume S#0[$Box(n#6)]
           ==> read($Heap, n#6, _module.Node.childrenVisited)
               == read(old($Heap), n#6, _module.Node.childrenVisited)
             && Seq#Equal(read($Heap, n#6, _module.Node.children),
              read(old($Heap), n#6, _module.Node.children));
    }

    assume (forall n#7: ref ::
      { read(old($Heap), n#7, _module.Node.children) }
        { read($Heap, n#7, _module.Node.children) }
        { read(old($Heap), n#7, _module.Node.childrenVisited) }
        { read($Heap, n#7, _module.Node.childrenVisited) }
        { S#0[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node())
         ==> (S#0[$Box(n#7)]
             ==> read($Heap, n#7, _module.Node.childrenVisited)
               == read(old($Heap), n#7, _module.Node.childrenVisited))
           && (S#0[$Box(n#7)]
             ==> Seq#Equal(read($Heap, n#7, _module.Node.children),
              read(old($Heap), n#7, _module.Node.children))));
}



procedure {:verboseName "IterativeMark (call)"} Call$$_module.__default.IterativeMark(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.childrenVisited) }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.children) }
      { read($Heap, n#5, _module.Node.marked) }
      { S#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
       ==> (forall ch#5: ref ::
        { read($Heap, ch#5, _module.Node.marked) }
          { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
        $Is(ch#5, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
             && ch#5 != null
           ==> read($Heap, ch#5, _module.Node.marked)));
  free ensures true;
  ensures (forall n#7: ref ::
    { read(old($Heap), n#7, _module.Node.children) }
      { read($Heap, n#7, _module.Node.children) }
      { read(old($Heap), n#7, _module.Node.childrenVisited) }
      { read($Heap, n#7, _module.Node.childrenVisited) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==> (S#0[$Box(n#7)]
           ==> read($Heap, n#7, _module.Node.childrenVisited)
             == read(old($Heap), n#7, _module.Node.childrenVisited))
         && (S#0[$Box(n#7)]
           ==> Seq#Equal(read($Heap, n#7, _module.Node.children),
            read(old($Heap), n#7, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "IterativeMark (correctness)"} Impl$$_module.__default.IterativeMark(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.childrenVisited) }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.children) }
      { read($Heap, n#5, _module.Node.marked) }
      { S#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
       ==> (forall ch#5: ref ::
        { read($Heap, ch#5, _module.Node.marked) }
          { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
        $Is(ch#5, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
             && ch#5 != null
           ==> read($Heap, ch#5, _module.Node.marked)));
  free ensures true;
  ensures (forall n#7: ref ::
    { read(old($Heap), n#7, _module.Node.children) }
      { read($Heap, n#7, _module.Node.children) }
      { read(old($Heap), n#7, _module.Node.childrenVisited) }
      { read($Heap, n#7, _module.Node.childrenVisited) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==> (S#0[$Box(n#7)]
           ==> read($Heap, n#7, _module.Node.childrenVisited)
             == read(old($Heap), n#7, _module.Node.childrenVisited))
         && (S#0[$Box(n#7)]
           ==> Seq#Equal(read($Heap, n#7, _module.Node.children),
            read(old($Heap), n#7, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "IterativeMark (correctness)"} Impl$$_module.__default.IterativeMark(root#0: ref, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: ref
     where $Is(t#0, Tclass._module.Node?()) && $IsAlloc(t#0, Tclass._module.Node?(), $Heap);
  var $rhs#0: bool;
  var stackNodes#0: Seq Box
     where $Is(stackNodes#0, TSeq(Tclass._module.Node()))
       && $IsAlloc(stackNodes#0, TSeq(Tclass._module.Node()), $Heap);
  var unmarkedNodes#0: Set Box
     where $Is(unmarkedNodes#0, TSet(Tclass._module.Node?()))
       && $IsAlloc(unmarkedNodes#0, TSet(Tclass._module.Node?()), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $decr_init$loop#01: Seq Box;
  var $decr_init$loop#02: int;
  var $w$loop#0: bool;
  var i#0: int;
  var j#0: int;
  var n#8: ref;
  var n#10: ref;
  var j#2: int;
  var newtype$check#2: ref;
  var n#12: ref;
  var j#4: int;
  var n#14: ref;
  var ch#6: ref;
  var newtype$check#3: ref;
  var n#16: ref;
  var n#18: ref;
  var n#20: ref;
  var $decr$loop#00: Set Box;
  var $decr$loop#01: Seq Box;
  var $decr$loop#02: int;
  var $rhs#0_0_0: int;
  var $rhs#0_0_1: int;
  var newtype$check#0_1_0: ref;
  var $rhs#0_1_0_0: int;
  var $rhs#0_1_1_0: bool;

    // AddMethodImpl: IterativeMark, Impl$$_module.__default.IterativeMark
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(99,9)
    assume true;
    assume true;
    t#0 := root#0;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(100,12)
    assert t#0 != null;
    assume true;
    assert $_Frame[t#0, _module.Node.marked];
    assume true;
    $rhs#0 := Lit(true);
    $Heap := update($Heap, t#0, _module.Node.marked, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(101,29)
    assume true;
    assume true;
    stackNodes#0 := Lit(Seq#Empty(): Seq Box);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(102,27)
    assume true;
    assume true;
    unmarkedNodes#0 := Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(t#0)));
    // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(103,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := unmarkedNodes#0;
    $decr_init$loop#01 := stackNodes#0;
    $decr_init$loop#02 := Seq#Length(read($Heap, t#0, _module.Node.children))
       - read($Heap, t#0, _module.Node.childrenVisited);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, root#0, _module.Node.marked);
      invariant $w$loop#0 ==> S#0[$Box(t#0)];
      invariant $w$loop#0 ==> !Seq#Contains(stackNodes#0, $Box(t#0));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall i#1: int, j#1: int ::
          { $Unbox(Seq#Index(stackNodes#0, j#1)): ref, $Unbox(Seq#Index(stackNodes#0, i#1)): ref }
          true
             ==>
            LitInt(0) <= i#1 && i#1 < j#1 && j#1 < Seq#Length(stackNodes#0)
             ==> $Unbox(Seq#Index(stackNodes#0, i#1)): ref
               != $Unbox(Seq#Index(stackNodes#0, j#1)): ref);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#9: ref ::
          { S#0[$Box(n#9)] } { Seq#Contains(stackNodes#0, $Box(n#9)) }
          $Is(n#9, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#9))
             ==> S#0[$Box(n#9)]);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#11: ref ::
          { read($Heap, n#11, _module.Node.marked) }
            { Seq#Contains(stackNodes#0, $Box(n#11)) }
          $Is(n#11, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
             ==> read($Heap, n#11, _module.Node.marked));
      invariant $w$loop#0
         ==> (forall n#11: ref ::
          { read($Heap, n#11, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#11)) }
          $Is(n#11, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
             ==> LitInt(0) <= read($Heap, n#11, _module.Node.childrenVisited));
      invariant $w$loop#0
         ==> (forall n#11: ref ::
          { read($Heap, n#11, _module.Node.children) }
            { read($Heap, n#11, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#11)) }
          $Is(n#11, Tclass._module.Node())
             ==> (Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
                 ==> read($Heap, n#11, _module.Node.childrenVisited)
                   <= Seq#Length(read($Heap, n#11, _module.Node.children)))
               && (Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
                 ==> (forall j#3: int ::
                  { $Unbox(Seq#Index(read($Heap, n#11, _module.Node.children), j#3)): ref }
                  true
                     ==>
                    LitInt(0) <= j#3 && j#3 < read($Heap, n#11, _module.Node.childrenVisited)
                     ==> $Unbox(Seq#Index(read($Heap, n#11, _module.Node.children), j#3)): ref == null
                       || read($Heap,
                        $Unbox(Seq#Index(read($Heap, n#11, _module.Node.children), j#3)): ref,
                        _module.Node.marked))));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#13: ref ::
          { read($Heap, n#13, _module.Node.children) }
            { read($Heap, n#13, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#13)) }
          $Is(n#13, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#13))
             ==> read($Heap, n#13, _module.Node.childrenVisited)
               < Seq#Length(read($Heap, n#13, _module.Node.children)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall j#5: int, _t#0#0: int ::
          { $Unbox(Seq#Index(stackNodes#0, _t#0#0)): ref, $Unbox(Seq#Index(stackNodes#0, j#5)): ref }
          _t#0#0 == j#5 + 1
             ==>
            LitInt(0) <= j#5 && _t#0#0 < Seq#Length(stackNodes#0)
             ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, j#5)): ref, _module.Node.children),
                  read($Heap, $Unbox(Seq#Index(stackNodes#0, j#5)): ref, _module.Node.childrenVisited))): ref
               == $Unbox(Seq#Index(stackNodes#0, _t#0#0)): ref);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==>
        0 < Seq#Length(stackNodes#0)
         ==> $Unbox(Seq#Index(read($Heap,
                $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                _module.Node.children),
              read($Heap,
                $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                _module.Node.childrenVisited))): ref
           == t#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#15: ref ::
          { read($Heap, n#15, _module.Node.children) }
            { Seq#Contains(stackNodes#0, $Box(n#15)) }
            { read($Heap, n#15, _module.Node.marked) }
            { S#0[$Box(n#15)] }
          $Is(n#15, Tclass._module.Node())
             ==>
            S#0[$Box(n#15)]
               && read($Heap, n#15, _module.Node.marked)
               && !Seq#Contains(stackNodes#0, $Box(n#15))
               && n#15 != t#0
             ==> (forall ch#7: ref ::
              { read($Heap, ch#7, _module.Node.marked) }
                { Seq#Contains(read($Heap, n#15, _module.Node.children), $Box(ch#7)) }
              $Is(ch#7, Tclass._module.Node?())
                 ==>
                Seq#Contains(read($Heap, n#15, _module.Node.children), $Box(ch#7))
                   && ch#7 != null
                 ==> read($Heap, ch#7, _module.Node.marked)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#17: ref ::
          { read(old($Heap), n#17, _module.Node.childrenVisited) }
            { read($Heap, n#17, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#17)) }
            { S#0[$Box(n#17)] }
          $Is(n#17, Tclass._module.Node())
             ==>
            S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17)) && n#17 != t#0
             ==> read($Heap, n#17, _module.Node.childrenVisited)
               == read(old($Heap), n#17, _module.Node.childrenVisited));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#19: ref ::
          { read(old($Heap), n#19, _module.Node.children) }
            { read($Heap, n#19, _module.Node.children) }
            { S#0[$Box(n#19)] }
          $Is(n#19, Tclass._module.Node())
             ==>
            S#0[$Box(n#19)]
             ==> Seq#Equal(read($Heap, n#19, _module.Node.children),
              read(old($Heap), n#19, _module.Node.children)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#21: ref ::
          { unmarkedNodes#0[$Box(n#21)] }
            { read($Heap, n#21, _module.Node.marked) }
            { S#0[$Box(n#21)] }
          $Is(n#21, Tclass._module.Node())
             ==>
            S#0[$Box(n#21)] && !read($Heap, n#21, _module.Node.marked)
             ==> unmarkedNodes#0[$Box(n#21)]);
      free invariant (forall $o: ref ::
        { $Heap[$o] }
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || S#0[$Box($o)]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Set#Subset(unmarkedNodes#0, $decr_init$loop#00)
         && (Set#Equal(unmarkedNodes#0, $decr_init$loop#00)
           ==> Seq#Rank(stackNodes#0) <= Seq#Rank($decr_init$loop#01)
             && (Seq#Rank(stackNodes#0) == Seq#Rank($decr_init$loop#01)
               ==> Seq#Length(read($Heap, t#0, _module.Node.children))
                     - read($Heap, t#0, _module.Node.childrenVisited)
                   <= $decr_init$loop#02
                 && (Seq#Length(read($Heap, t#0, _module.Node.children))
                       - read($Heap, t#0, _module.Node.childrenVisited)
                     == $decr_init$loop#02
                   ==> true)));
    {
        if (!$w$loop#0)
        {
            assert {:subsumption 0} root#0 != null;
            if (read($Heap, root#0, _module.Node.marked))
            {
            }

            if (read($Heap, root#0, _module.Node.marked) && S#0[$Box(t#0)])
            {
            }

            assume true;
            assume read($Heap, root#0, _module.Node.marked)
               && S#0[$Box(t#0)]
               && !Seq#Contains(stackNodes#0, $Box(t#0));
            // Begin Comprehension WF check
            havoc i#0;
            havoc j#0;
            if (true)
            {
                if (LitInt(0) <= i#0)
                {
                }

                if (LitInt(0) <= i#0 && i#0 < j#0)
                {
                }

                if (LitInt(0) <= i#0 && i#0 < j#0 && j#0 < Seq#Length(stackNodes#0))
                {
                    assert {:subsumption 0} 0 <= i#0 && i#0 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} 0 <= j#0 && j#0 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall i#1: int, j#1: int ::
              { $Unbox(Seq#Index(stackNodes#0, j#1)): ref, $Unbox(Seq#Index(stackNodes#0, i#1)): ref }
              true
                 ==>
                LitInt(0) <= i#1 && i#1 < j#1 && j#1 < Seq#Length(stackNodes#0)
                 ==> $Unbox(Seq#Index(stackNodes#0, i#1)): ref
                   != $Unbox(Seq#Index(stackNodes#0, j#1)): ref);
            // Begin Comprehension WF check
            havoc n#8;
            if ($Is(n#8, Tclass._module.Node()) && $IsAlloc(n#8, Tclass._module.Node(), $Heap))
            {
                if (Seq#Contains(stackNodes#0, $Box(n#8)))
                {
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#9: ref ::
              { S#0[$Box(n#9)] } { Seq#Contains(stackNodes#0, $Box(n#9)) }
              $Is(n#9, Tclass._module.Node())
                 ==>
                Seq#Contains(stackNodes#0, $Box(n#9))
                 ==> S#0[$Box(n#9)]);
            // Begin Comprehension WF check
            havoc n#10;
            if ($Is(n#10, Tclass._module.Node()) && $IsAlloc(n#10, Tclass._module.Node(), $Heap))
            {
                if (!Seq#Contains(stackNodes#0, $Box(n#10)))
                {
                }

                if (Seq#Contains(stackNodes#0, $Box(n#10)) || n#10 == t#0)
                {
                    assert {:subsumption 0} n#10 != null;
                    if (read($Heap, n#10, _module.Node.marked))
                    {
                        assert {:subsumption 0} n#10 != null;
                        if (LitInt(0) <= read($Heap, n#10, _module.Node.childrenVisited))
                        {
                            assert {:subsumption 0} n#10 != null;
                            assert {:subsumption 0} n#10 != null;
                        }
                    }

                    if (read($Heap, n#10, _module.Node.marked)
                       &&
                      LitInt(0) <= read($Heap, n#10, _module.Node.childrenVisited)
                       && read($Heap, n#10, _module.Node.childrenVisited)
                         <= Seq#Length(read($Heap, n#10, _module.Node.children)))
                    {
                        // Begin Comprehension WF check
                        havoc j#2;
                        if (true)
                        {
                            if (LitInt(0) <= j#2)
                            {
                                assert {:subsumption 0} n#10 != null;
                            }

                            if (LitInt(0) <= j#2 && j#2 < read($Heap, n#10, _module.Node.childrenVisited))
                            {
                                assert {:subsumption 0} n#10 != null;
                                assert {:subsumption 0} 0 <= j#2 && j#2 < Seq#Length(read($Heap, n#10, _module.Node.children));
                                newtype$check#2 := null;
                                if ($Unbox(Seq#Index(read($Heap, n#10, _module.Node.children), j#2)): ref != null)
                                {
                                    assert {:subsumption 0} n#10 != null;
                                    assert {:subsumption 0} 0 <= j#2 && j#2 < Seq#Length(read($Heap, n#10, _module.Node.children));
                                    assert {:subsumption 0} $Unbox(Seq#Index(read($Heap, n#10, _module.Node.children), j#2)): ref != null;
                                }
                            }
                        }

                        // End Comprehension WF check
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#11: ref ::
                { read($Heap, n#11, _module.Node.marked) }
                  { Seq#Contains(stackNodes#0, $Box(n#11)) }
                $Is(n#11, Tclass._module.Node())
                   ==>
                  Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
                   ==> read($Heap, n#11, _module.Node.marked))
               && (forall n#11: ref ::
                { read($Heap, n#11, _module.Node.childrenVisited) }
                  { Seq#Contains(stackNodes#0, $Box(n#11)) }
                $Is(n#11, Tclass._module.Node())
                   ==>
                  Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
                   ==> LitInt(0) <= read($Heap, n#11, _module.Node.childrenVisited))
               && (forall n#11: ref ::
                { read($Heap, n#11, _module.Node.children) }
                  { read($Heap, n#11, _module.Node.childrenVisited) }
                  { Seq#Contains(stackNodes#0, $Box(n#11)) }
                $Is(n#11, Tclass._module.Node())
                   ==> (Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
                       ==> read($Heap, n#11, _module.Node.childrenVisited)
                         <= Seq#Length(read($Heap, n#11, _module.Node.children)))
                     && (Seq#Contains(stackNodes#0, $Box(n#11)) || n#11 == t#0
                       ==> (forall j#3: int ::
                        { $Unbox(Seq#Index(read($Heap, n#11, _module.Node.children), j#3)): ref }
                        true
                           ==>
                          LitInt(0) <= j#3 && j#3 < read($Heap, n#11, _module.Node.childrenVisited)
                           ==> $Unbox(Seq#Index(read($Heap, n#11, _module.Node.children), j#3)): ref == null
                             || read($Heap,
                              $Unbox(Seq#Index(read($Heap, n#11, _module.Node.children), j#3)): ref,
                              _module.Node.marked))));
            // Begin Comprehension WF check
            havoc n#12;
            if ($Is(n#12, Tclass._module.Node()) && $IsAlloc(n#12, Tclass._module.Node(), $Heap))
            {
                if (Seq#Contains(stackNodes#0, $Box(n#12)))
                {
                    assert {:subsumption 0} n#12 != null;
                    assert {:subsumption 0} n#12 != null;
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#13: ref ::
              { read($Heap, n#13, _module.Node.children) }
                { read($Heap, n#13, _module.Node.childrenVisited) }
                { Seq#Contains(stackNodes#0, $Box(n#13)) }
              $Is(n#13, Tclass._module.Node())
                 ==>
                Seq#Contains(stackNodes#0, $Box(n#13))
                 ==> read($Heap, n#13, _module.Node.childrenVisited)
                   < Seq#Length(read($Heap, n#13, _module.Node.children)));
            // Begin Comprehension WF check
            havoc j#4;
            if (true)
            {
                if (LitInt(0) <= j#4)
                {
                }

                if (LitInt(0) <= j#4 && j#4 + 1 < Seq#Length(stackNodes#0))
                {
                    assert {:subsumption 0} 0 <= j#4 && j#4 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, j#4)): ref != null;
                    assert {:subsumption 0} 0 <= j#4 && j#4 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, j#4)): ref != null;
                    assert {:subsumption 0} 0
                         <= read($Heap, $Unbox(Seq#Index(stackNodes#0, j#4)): ref, _module.Node.childrenVisited)
                       && read($Heap, $Unbox(Seq#Index(stackNodes#0, j#4)): ref, _module.Node.childrenVisited)
                         < Seq#Length(read($Heap, $Unbox(Seq#Index(stackNodes#0, j#4)): ref, _module.Node.children));
                    assert {:subsumption 0} 0 <= j#4 + 1 && j#4 + 1 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall j#5: int, _t#0#0: int ::
              { $Unbox(Seq#Index(stackNodes#0, _t#0#0)): ref, $Unbox(Seq#Index(stackNodes#0, j#5)): ref }
              _t#0#0 == j#5 + 1
                 ==>
                LitInt(0) <= j#5 && _t#0#0 < Seq#Length(stackNodes#0)
                 ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, j#5)): ref, _module.Node.children),
                      read($Heap, $Unbox(Seq#Index(stackNodes#0, j#5)): ref, _module.Node.childrenVisited))): ref
                   == $Unbox(Seq#Index(stackNodes#0, _t#0#0)): ref);
            if (0 < Seq#Length(stackNodes#0))
            {
                assert {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref != null;
                assert {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref != null;
                assert {:subsumption 0} 0
                     <= read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.childrenVisited)
                   && read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.childrenVisited)
                     < Seq#Length(read($Heap,
                        $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                        _module.Node.children));
            }

            assume true;
            assume 0 < Seq#Length(stackNodes#0)
               ==> $Unbox(Seq#Index(read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.children),
                    read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.childrenVisited))): ref
                 == t#0;
            // Begin Comprehension WF check
            havoc n#14;
            if ($Is(n#14, Tclass._module.Node()) && $IsAlloc(n#14, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#14)])
                {
                    assert {:subsumption 0} n#14 != null;
                }

                if (S#0[$Box(n#14)] && read($Heap, n#14, _module.Node.marked))
                {
                }

                if (S#0[$Box(n#14)]
                   && read($Heap, n#14, _module.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#14)))
                {
                }

                if (S#0[$Box(n#14)]
                   && read($Heap, n#14, _module.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#14))
                   && n#14 != t#0)
                {
                    // Begin Comprehension WF check
                    havoc ch#6;
                    if ($Is(ch#6, Tclass._module.Node?())
                       && $IsAlloc(ch#6, Tclass._module.Node?(), $Heap))
                    {
                        assert {:subsumption 0} n#14 != null;
                        if (Seq#Contains(read($Heap, n#14, _module.Node.children), $Box(ch#6)))
                        {
                            newtype$check#3 := null;
                        }

                        if (Seq#Contains(read($Heap, n#14, _module.Node.children), $Box(ch#6))
                           && ch#6 != null)
                        {
                            assert {:subsumption 0} ch#6 != null;
                        }
                    }

                    // End Comprehension WF check
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#15: ref ::
              { read($Heap, n#15, _module.Node.children) }
                { Seq#Contains(stackNodes#0, $Box(n#15)) }
                { read($Heap, n#15, _module.Node.marked) }
                { S#0[$Box(n#15)] }
              $Is(n#15, Tclass._module.Node())
                 ==>
                S#0[$Box(n#15)]
                   && read($Heap, n#15, _module.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#15))
                   && n#15 != t#0
                 ==> (forall ch#7: ref ::
                  { read($Heap, ch#7, _module.Node.marked) }
                    { Seq#Contains(read($Heap, n#15, _module.Node.children), $Box(ch#7)) }
                  $Is(ch#7, Tclass._module.Node?())
                     ==>
                    Seq#Contains(read($Heap, n#15, _module.Node.children), $Box(ch#7))
                       && ch#7 != null
                     ==> read($Heap, ch#7, _module.Node.marked)));
            // Begin Comprehension WF check
            havoc n#16;
            if ($Is(n#16, Tclass._module.Node()) && $IsAlloc(n#16, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#16)])
                {
                }

                if (S#0[$Box(n#16)] && !Seq#Contains(stackNodes#0, $Box(n#16)))
                {
                }

                if (S#0[$Box(n#16)] && !Seq#Contains(stackNodes#0, $Box(n#16)) && n#16 != t#0)
                {
                    assert {:subsumption 0} n#16 != null;
                    assert {:subsumption 0} n#16 != null;
                    assert $IsAlloc(n#16, Tclass._module.Node(), old($Heap));
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#17: ref ::
              { read(old($Heap), n#17, _module.Node.childrenVisited) }
                { read($Heap, n#17, _module.Node.childrenVisited) }
                { Seq#Contains(stackNodes#0, $Box(n#17)) }
                { S#0[$Box(n#17)] }
              $Is(n#17, Tclass._module.Node())
                 ==>
                S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17)) && n#17 != t#0
                 ==> read($Heap, n#17, _module.Node.childrenVisited)
                   == read(old($Heap), n#17, _module.Node.childrenVisited));
            // Begin Comprehension WF check
            havoc n#18;
            if ($Is(n#18, Tclass._module.Node()) && $IsAlloc(n#18, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#18)])
                {
                    assert {:subsumption 0} n#18 != null;
                    assert {:subsumption 0} n#18 != null;
                    assert $IsAlloc(n#18, Tclass._module.Node(), old($Heap));
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#19: ref ::
              { read(old($Heap), n#19, _module.Node.children) }
                { read($Heap, n#19, _module.Node.children) }
                { S#0[$Box(n#19)] }
              $Is(n#19, Tclass._module.Node())
                 ==>
                S#0[$Box(n#19)]
                 ==> Seq#Equal(read($Heap, n#19, _module.Node.children),
                  read(old($Heap), n#19, _module.Node.children)));
            // Begin Comprehension WF check
            havoc n#20;
            if ($Is(n#20, Tclass._module.Node()) && $IsAlloc(n#20, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#20)])
                {
                    assert {:subsumption 0} n#20 != null;
                }

                if (S#0[$Box(n#20)] && !read($Heap, n#20, _module.Node.marked))
                {
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#21: ref ::
              { unmarkedNodes#0[$Box(n#21)] }
                { read($Heap, n#21, _module.Node.marked) }
                { S#0[$Box(n#21)] }
              $Is(n#21, Tclass._module.Node())
                 ==>
                S#0[$Box(n#21)] && !read($Heap, n#21, _module.Node.marked)
                 ==> unmarkedNodes#0[$Box(n#21)]);
            assume true;
            assume true;
            assert t#0 != null;
            assert t#0 != null;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := unmarkedNodes#0;
        $decr$loop#01 := stackNodes#0;
        $decr$loop#02 := Seq#Length(read($Heap, t#0, _module.Node.children))
           - read($Heap, t#0, _module.Node.childrenVisited);
        // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(128,5)
        assert t#0 != null;
        assert t#0 != null;
        assume true;
        if (read($Heap, t#0, _module.Node.childrenVisited)
           == Seq#Length(read($Heap, t#0, _module.Node.children)))
        {
            // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(129,7)
            assume true;
            assert {:focus} Lit(true);
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(131,25)
            assert t#0 != null;
            assume true;
            assert $_Frame[t#0, _module.Node.childrenVisited];
            assume true;
            assert $Is(LitInt(0), Tclass._System.nat());
            $rhs#0_0_0 := LitInt(0);
            $Heap := update($Heap, t#0, _module.Node.childrenVisited, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(132,7)
            assume true;
            if (Seq#Length(stackNodes#0) == LitInt(0))
            {
                // ----- return statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(133,9)
                return;
            }
            else
            {
            }

            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(135,9)
            assume true;
            assert 0 <= Seq#Length(stackNodes#0) - 1
               && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
            assume true;
            t#0 := $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref;
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(136,18)
            assume true;
            assert 0 <= Seq#Length(stackNodes#0) - 1
               && Seq#Length(stackNodes#0) - 1 <= Seq#Length(stackNodes#0);
            assume true;
            stackNodes#0 := Seq#Take(stackNodes#0, Seq#Length(stackNodes#0) - 1);
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(137,25)
            assert t#0 != null;
            assume true;
            assert $_Frame[t#0, _module.Node.childrenVisited];
            assert t#0 != null;
            assume true;
            assert $Is(read($Heap, t#0, _module.Node.childrenVisited) + 1, Tclass._System.nat());
            $rhs#0_0_1 := read($Heap, t#0, _module.Node.childrenVisited) + 1;
            $Heap := update($Heap, t#0, _module.Node.childrenVisited, $rhs#0_0_1);
            assume $IsGoodHeap($Heap);
        }
        else
        {
            // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(138,12)
            assert t#0 != null;
            assert t#0 != null;
            assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
               && read($Heap, t#0, _module.Node.childrenVisited)
                 < Seq#Length(read($Heap, t#0, _module.Node.children));
            newtype$check#0_1_0 := null;
            if ($Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                  read($Heap, t#0, _module.Node.childrenVisited))): ref
               != null)
            {
                assert t#0 != null;
                assert t#0 != null;
                assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
                   && read($Heap, t#0, _module.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, _module.Node.children));
                assert $Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                      read($Heap, t#0, _module.Node.childrenVisited))): ref
                   != null;
            }

            assume true;
            if ($Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                    read($Heap, t#0, _module.Node.childrenVisited))): ref
                 == null
               || read($Heap,
                $Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                    read($Heap, t#0, _module.Node.childrenVisited))): ref,
                _module.Node.marked))
            {
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(140,25)
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, _module.Node.childrenVisited];
                assert t#0 != null;
                assume true;
                assert $Is(read($Heap, t#0, _module.Node.childrenVisited) + 1, Tclass._System.nat());
                $rhs#0_1_0_0 := read($Heap, t#0, _module.Node.childrenVisited) + 1;
                $Heap := update($Heap, t#0, _module.Node.childrenVisited, $rhs#0_1_0_0);
                assume $IsGoodHeap($Heap);
            }
            else
            {
                // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(142,7)
                assume true;
                assert {:focus} Lit(true);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(144,18)
                assume true;
                assume true;
                assert $Is(Seq#Append(stackNodes#0, Seq#Build(Seq#Empty(): Seq Box, $Box(t#0))),
                  TSeq(Tclass._module.Node()));
                stackNodes#0 := Seq#Append(stackNodes#0, Seq#Build(Seq#Empty(): Seq Box, $Box(t#0)));
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(145,9)
                assume true;
                assert t#0 != null;
                assert t#0 != null;
                assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
                   && read($Heap, t#0, _module.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, _module.Node.children));
                assume true;
                t#0 := $Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                    read($Heap, t#0, _module.Node.childrenVisited))): ref;
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(146,16)
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, _module.Node.marked];
                assume true;
                $rhs#0_1_1_0 := Lit(true);
                $Heap := update($Heap, t#0, _module.Node.marked, $rhs#0_1_1_0);
                assume $IsGoodHeap($Heap);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(147,21)
                assume true;
                assume true;
                unmarkedNodes#0 := Set#Difference(unmarkedNodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(t#0)));
            }
        }

        // ----- loop termination check ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(103,3)
        assert 0 <= $decr$loop#02
           || (Set#Subset(unmarkedNodes#0, $decr$loop#00)
             && !Set#Subset($decr$loop#00, unmarkedNodes#0))
           || Seq#Rank(stackNodes#0) < Seq#Rank($decr$loop#01)
           || Seq#Length(read($Heap, t#0, _module.Node.children))
               - read($Heap, t#0, _module.Node.childrenVisited)
             == $decr$loop#02;
        assert (Set#Subset(unmarkedNodes#0, $decr$loop#00)
             && !Set#Subset($decr$loop#00, unmarkedNodes#0))
           || (Set#Equal(unmarkedNodes#0, $decr$loop#00)
             && (Seq#Rank(stackNodes#0) < Seq#Rank($decr$loop#01)
               || (Seq#Rank(stackNodes#0) == Seq#Rank($decr$loop#01)
                 && Seq#Length(read($Heap, t#0, _module.Node.children))
                     - read($Heap, t#0, _module.Node.childrenVisited)
                   < $decr$loop#02)));
        assume true;
    }
}



// function declaration for _module._default.Reachable
function _module.__default.Reachable($heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box) : bool;

function _module.__default.Reachable#canCall($heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box) : bool;

// frame axiom for _module.__default.Reachable
axiom (forall $h0: Heap, $h1: Heap, source#0: ref, sink#0: ref, S#0: Set Box ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Reachable($h1, source#0, sink#0, S#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Reachable#canCall($h0, source#0, sink#0, S#0)
         || (
          $Is(source#0, Tclass._module.Node())
           && $Is(sink#0, Tclass._module.Node())
           && $Is(S#0, TSet(Tclass._module.Node()))))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && S#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Reachable($h0, source#0, sink#0, S#0)
       == _module.__default.Reachable($h1, source#0, sink#0, S#0));

// consequence axiom for _module.__default.Reachable
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box ::
    { _module.__default.Reachable($Heap, source#0, sink#0, S#0) }
    _module.__default.Reachable#canCall($Heap, source#0, sink#0, S#0)
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass._module.Node())
           && $Is(sink#0, Tclass._module.Node())
           && $Is(S#0, TSet(Tclass._module.Node())))
       ==> true);

function _module.__default.Reachable#requires(Heap, ref, ref, Set Box) : bool;

// #requires axiom for _module.__default.Reachable
axiom (forall $Heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box ::
  { _module.__default.Reachable#requires($Heap, source#0, sink#0, S#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       && $Is(source#0, Tclass._module.Node())
       && $Is(sink#0, Tclass._module.Node())
       && $Is(S#0, TSet(Tclass._module.Node()))
     ==> _module.__default.Reachable#requires($Heap, source#0, sink#0, S#0) == true);

// definition axiom for _module.__default.Reachable (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box ::
    { _module.__default.Reachable($Heap, source#0, sink#0, S#0), $IsGoodHeap($Heap) }
    _module.__default.Reachable#canCall($Heap, source#0, sink#0, S#0)
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass._module.Node())
           && $Is(sink#0, Tclass._module.Node())
           && $Is(S#0, TSet(Tclass._module.Node())))
       ==> (forall via#0: DatatypeType ::
          { _module.__default.ReachableVia($LS($LZ), $Heap, source#0, via#0, sink#0, S#0) }
          $Is(via#0, Tclass._module.Path())
             ==> _module.__default.ReachableVia#canCall($Heap, source#0, via#0, sink#0, S#0))
         && _module.__default.Reachable($Heap, source#0, sink#0, S#0)
           == (exists via#0: DatatypeType ::
            { _module.__default.ReachableVia($LS($LZ), $Heap, source#0, via#0, sink#0, S#0) }
            $Is(via#0, Tclass._module.Path())
               && _module.__default.ReachableVia($LS($LZ), $Heap, source#0, via#0, sink#0, S#0)));

procedure {:verboseName "Reachable (well-formedness)"} CheckWellformed$$_module.__default.Reachable(source#0: ref where $Is(source#0, Tclass._module.Node()),
    sink#0: ref where $Is(sink#0, Tclass._module.Node()),
    S#0: Set Box where $Is(S#0, TSet(Tclass._module.Node())));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Reachable (well-formedness)"} CheckWellformed$$_module.__default.Reachable(source#0: ref, sink#0: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var via#1: DatatypeType;
  var ##source#0: ref;
  var ##p#0: DatatypeType;
  var ##sink#0: ref;
  var ##S#0: Set Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Reachable
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
        // Begin Comprehension WF check
        havoc via#1;
        if ($Is(via#1, Tclass._module.Path())
           && $IsAlloc(via#1, Tclass._module.Path(), $Heap))
        {
            ##source#0 := source#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##source#0, Tclass._module.Node(), $Heap);
            ##p#0 := via#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, Tclass._module.Path(), $Heap);
            ##sink#0 := sink#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##sink#0, Tclass._module.Node(), $Heap);
            ##S#0 := S#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##S#0, TSet(Tclass._module.Node()), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null && read($Heap, $o, alloc) && ##S#0[$Box($o)] ==> $_Frame[$o, $f]);
            assume _module.__default.ReachableVia#canCall($Heap, source#0, via#1, sink#0, S#0);
        }

        // End Comprehension WF check
        assume _module.__default.Reachable($Heap, source#0, sink#0, S#0)
           == (exists via#2: DatatypeType ::
            { _module.__default.ReachableVia($LS($LZ), $Heap, source#0, via#2, sink#0, S#0) }
            $Is(via#2, Tclass._module.Path())
               && _module.__default.ReachableVia($LS($LZ), $Heap, source#0, via#2, sink#0, S#0));
        assume (forall via#2: DatatypeType ::
          { _module.__default.ReachableVia($LS($LZ), $Heap, source#0, via#2, sink#0, S#0) }
          $Is(via#2, Tclass._module.Path())
             ==> _module.__default.ReachableVia#canCall($Heap, source#0, via#2, sink#0, S#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Reachable($Heap, source#0, sink#0, S#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ReachableVia
function _module.__default.ReachableVia($ly: LayerType,
    $heap: Heap,
    source#0: ref,
    p#0: DatatypeType,
    sink#0: ref,
    S#0: Set Box)
   : bool;

function _module.__default.ReachableVia#canCall($heap: Heap, source#0: ref, p#0: DatatypeType, sink#0: ref, S#0: Set Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType,
    $Heap: Heap,
    source#0: ref,
    p#0: DatatypeType,
    sink#0: ref,
    S#0: Set Box ::
  { _module.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0) }
  _module.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0)
     == _module.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0));

// fuel synonym axiom
axiom (forall $ly: LayerType,
    $Heap: Heap,
    source#0: ref,
    p#0: DatatypeType,
    sink#0: ref,
    S#0: Set Box ::
  { _module.__default.ReachableVia(AsFuelBottom($ly), $Heap, source#0, p#0, sink#0, S#0) }
  _module.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0)
     == _module.__default.ReachableVia($LZ, $Heap, source#0, p#0, sink#0, S#0));

// frame axiom for _module.__default.ReachableVia
axiom (forall $ly: LayerType,
    $h0: Heap,
    $h1: Heap,
    source#0: ref,
    p#0: DatatypeType,
    sink#0: ref,
    S#0: Set Box ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ReachableVia($ly, $h1, source#0, p#0, sink#0, S#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ReachableVia#canCall($h0, source#0, p#0, sink#0, S#0)
         || (
          $Is(source#0, Tclass._module.Node())
           && $Is(p#0, Tclass._module.Path())
           && $Is(sink#0, Tclass._module.Node())
           && $Is(S#0, TSet(Tclass._module.Node()))))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && S#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ReachableVia($ly, $h0, source#0, p#0, sink#0, S#0)
       == _module.__default.ReachableVia($ly, $h1, source#0, p#0, sink#0, S#0));

// consequence axiom for _module.__default.ReachableVia
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType,
      $Heap: Heap,
      source#0: ref,
      p#0: DatatypeType,
      sink#0: ref,
      S#0: Set Box ::
    { _module.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0) }
    _module.__default.ReachableVia#canCall($Heap, source#0, p#0, sink#0, S#0)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass._module.Node())
           && $Is(p#0, Tclass._module.Path())
           && $Is(sink#0, Tclass._module.Node())
           && $Is(S#0, TSet(Tclass._module.Node())))
       ==> (forall $olderHeap: Heap ::
        { $OlderTag($olderHeap) }
        $IsGoodHeap($olderHeap)
             && $OlderTag($olderHeap)
             &&
            _module.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0)
             &&
            $IsAlloc(source#0, Tclass._module.Node(), $olderHeap)
             && $IsAlloc(sink#0, Tclass._module.Node(), $olderHeap)
             && $IsAlloc(S#0, TSet(Tclass._module.Node()), $olderHeap)
           ==> $IsAlloc(p#0, Tclass._module.Path(), $olderHeap)));

function _module.__default.ReachableVia#requires(LayerType, Heap, ref, DatatypeType, ref, Set Box) : bool;

// #requires axiom for _module.__default.ReachableVia
axiom (forall $ly: LayerType,
    $Heap: Heap,
    source#0: ref,
    p#0: DatatypeType,
    sink#0: ref,
    S#0: Set Box ::
  { _module.__default.ReachableVia#requires($ly, $Heap, source#0, p#0, sink#0, S#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       && $Is(source#0, Tclass._module.Node())
       && $Is(p#0, Tclass._module.Path())
       && $Is(sink#0, Tclass._module.Node())
       && $Is(S#0, TSet(Tclass._module.Node()))
     ==> _module.__default.ReachableVia#requires($ly, $Heap, source#0, p#0, sink#0, S#0)
       == true);

// definition axiom for _module.__default.ReachableVia (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType,
      $Heap: Heap,
      source#0: ref,
      p#0: DatatypeType,
      sink#0: ref,
      S#0: Set Box ::
    { _module.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0), $IsGoodHeap($Heap) }
    _module.__default.ReachableVia#canCall($Heap, source#0, p#0, sink#0, S#0)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass._module.Node())
           && $Is(p#0, Tclass._module.Path())
           && $Is(sink#0, Tclass._module.Node())
           && $Is(S#0, TSet(Tclass._module.Node())))
       ==> (!_module.Path.Empty_q(p#0)
           ==> (var n#1 := _module.Path._h1(p#0);
            (var prefix#1 := _module.Path._h0(p#0);
              S#0[$Box(n#1)]
                 ==>
                Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(sink#0))
                 ==> _module.__default.ReachableVia#canCall($Heap, source#0, prefix#1, n#1, S#0))))
         && _module.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0)
           == (if _module.Path.Empty_q(p#0)
             then source#0 == sink#0
             else (var n#0 := _module.Path._h1(p#0);
              (var prefix#0 := _module.Path._h0(p#0);
                S#0[$Box(n#0)]
                   && Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(sink#0))
                   && _module.__default.ReachableVia($ly, $Heap, source#0, prefix#0, n#0, S#0)))));

procedure {:verboseName "ReachableVia (well-formedness)"} CheckWellformed$$_module.__default.ReachableVia(source#0: ref where $Is(source#0, Tclass._module.Node()),
    p#0: DatatypeType where $Is(p#0, Tclass._module.Path()),
    sink#0: ref where $Is(sink#0, Tclass._module.Node()),
    S#0: Set Box where $Is(S#0, TSet(Tclass._module.Node())));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "ReachableVia (well-formedness)"} CheckWellformed$$_module.__default.ReachableVia(source#0: ref, p#0: DatatypeType, sink#0: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: ref;
  var n#Z#0: ref;
  var let#0#0#0: ref;
  var prefix#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##source#0: ref;
  var ##p#0: DatatypeType;
  var ##sink#0: ref;
  var ##S#0: Set Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ReachableVia
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
        if (p#0 == #_module.Path.Empty())
        {
            assume _module.__default.ReachableVia($LS($LZ), $Heap, source#0, p#0, sink#0, S#0)
               ==
              (source#0
               == sink#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ReachableVia($LS($LZ), $Heap, source#0, p#0, sink#0, S#0),
              TBool);
        }
        else if (p#0 == #_module.Path.Extend(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Path());
            assume $Is(_mcc#1#0, Tclass._module.Node());
            havoc n#Z#0;
            assume $Is(n#Z#0, Tclass._module.Node())
               && $IsAlloc(n#Z#0, Tclass._module.Node(), $Heap);
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Node());
            assume n#Z#0 == let#0#0#0;
            havoc prefix#Z#0;
            assume $Is(prefix#Z#0, Tclass._module.Path())
               && $IsAlloc(prefix#Z#0, Tclass._module.Path(), $Heap);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Path());
            assume prefix#Z#0 == let#1#0#0;
            if (S#0[$Box(n#Z#0)])
            {
                assert n#Z#0 != null;
                b$reqreads#0 := $_Frame[n#Z#0, _module.Node.children];
            }

            if (S#0[$Box(n#Z#0)]
               && Seq#Contains(read($Heap, n#Z#0, _module.Node.children), $Box(sink#0)))
            {
                ##source#0 := source#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##source#0, Tclass._module.Node(), $Heap);
                ##p#0 := prefix#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0, Tclass._module.Path(), $Heap);
                ##sink#0 := n#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##sink#0, Tclass._module.Node(), $Heap);
                ##S#0 := S#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##S#0, TSet(Tclass._module.Node()), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha ::
                  $o != null && read($Heap, $o, alloc) && ##S#0[$Box($o)] ==> $_Frame[$o, $f]);
                assert DtRank(##p#0) < DtRank(p#0);
                assume _module.__default.ReachableVia#canCall($Heap, source#0, prefix#Z#0, n#Z#0, S#0);
            }

            assume _module.__default.ReachableVia($LS($LZ), $Heap, source#0, p#0, sink#0, S#0)
               == (
                S#0[$Box(n#Z#0)]
                 && Seq#Contains(read($Heap, n#Z#0, _module.Node.children), $Box(sink#0))
                 && _module.__default.ReachableVia($LS($LZ), $Heap, source#0, prefix#Z#0, n#Z#0, S#0));
            assume S#0[$Box(n#Z#0)]
               ==>
              Seq#Contains(read($Heap, n#Z#0, _module.Node.children), $Box(sink#0))
               ==> _module.__default.ReachableVia#canCall($Heap, source#0, prefix#Z#0, n#Z#0, S#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ReachableVia($LS($LZ), $Heap, source#0, p#0, sink#0, S#0),
              TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert (forall $olderHeap: Heap ::
          { $OlderTag($olderHeap) }
          $IsGoodHeap($olderHeap)
               && $OlderTag($olderHeap)
               &&
              _module.__default.ReachableVia($LS($LZ), $Heap, source#0, p#0, sink#0, S#0)
               &&
              $IsAlloc(source#0, Tclass._module.Node(), $olderHeap)
               && $IsAlloc(sink#0, Tclass._module.Node(), $olderHeap)
               && $IsAlloc(S#0, TSet(Tclass._module.Node()), $olderHeap)
             ==> $IsAlloc(p#0, Tclass._module.Path(), $olderHeap));
    }
}



procedure {:verboseName "SchorrWaite (well-formedness)"} CheckWellFormed$$_module.__default.SchorrWaite(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "SchorrWaite (well-formedness)"} CheckWellFormed$$_module.__default.SchorrWaite(root#0: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref;
  var ch#0: ref;
  var newtype$check#0: ref;
  var n#2: ref;
  var n#4: ref;
  var ch#3: ref;
  var newtype$check#1: ref;
  var n#6: ref;
  var ##source#0: ref;
  var ##sink#0: ref;
  var ##S#0: Set Box;
  var n#8: ref;

    // AddMethodImpl: SchorrWaite, CheckWellFormed$$_module.__default.SchorrWaite
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume S#0[$Box(root#0)];
    havoc n#0;
    assume $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#0)];
        havoc ch#0;
        assume $Is(ch#0, Tclass._module.Node?())
           && $IsAlloc(ch#0, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#0 != null;
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0));
            if (*)
            {
                newtype$check#0 := null;
                assume ch#0 == null;
            }
            else
            {
                assume ch#0 != null;
                assume S#0[$Box(ch#0)];
            }
        }
        else
        {
            assume Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#0))
               ==> ch#0 == null || S#0[$Box(ch#0)];
        }

        assume (forall ch#1: ref ::
          { S#0[$Box(ch#1)] }
            { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
          $Is(ch#1, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
             ==> ch#1 == null || S#0[$Box(ch#1)]);
    }
    else
    {
        assume S#0[$Box(n#0)]
           ==> (forall ch#1: ref ::
            { S#0[$Box(ch#1)] }
              { Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1)) }
            $Is(ch#1, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#0, _module.Node.children), $Box(ch#1))
               ==> ch#1 == null || S#0[$Box(ch#1)]);
    }

    assume (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node())
         ==>
        S#0[$Box(n#1)]
         ==> (forall ch#2: ref ::
          { S#0[$Box(ch#2)] }
            { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
          $Is(ch#2, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
             ==> ch#2 == null || S#0[$Box(ch#2)]));
    havoc n#2;
    assume $Is(n#2, Tclass._module.Node()) && $IsAlloc(n#2, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#2)];
        assert n#2 != null;
        assume !read($Heap, n#2, _module.Node.marked);
        assert n#2 != null;
        assume read($Heap, n#2, _module.Node.childrenVisited) == LitInt(0);
    }
    else
    {
        assume S#0[$Box(n#2)]
           ==> !read($Heap, n#2, _module.Node.marked)
             && read($Heap, n#2, _module.Node.childrenVisited) == LitInt(0);
    }

    assume (forall n#3: ref ::
      { read($Heap, n#3, _module.Node.childrenVisited) }
        { read($Heap, n#3, _module.Node.marked) }
        { S#0[$Box(n#3)] }
      $Is(n#3, Tclass._module.Node())
         ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
           && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
    havoc $Heap;
    assume (forall $o: ref ::
      { $Heap[$o] }
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assert root#0 != null;
    assume read($Heap, root#0, _module.Node.marked);
    havoc n#4;
    assume $Is(n#4, Tclass._module.Node()) && $IsAlloc(n#4, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#4)];
        assert n#4 != null;
        assume read($Heap, n#4, _module.Node.marked);
        havoc ch#3;
        assume $Is(ch#3, Tclass._module.Node?())
           && $IsAlloc(ch#3, Tclass._module.Node?(), $Heap);
        if (*)
        {
            assert n#4 != null;
            assume Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#3));
            newtype$check#1 := null;
            assume ch#3 != null;
            assert ch#3 != null;
            assume read($Heap, ch#3, _module.Node.marked);
        }
        else
        {
            assume Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#3))
                 && ch#3 != null
               ==> read($Heap, ch#3, _module.Node.marked);
        }

        assume (forall ch#4: ref ::
          { read($Heap, ch#4, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4)) }
          $Is(ch#4, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4))
               && ch#4 != null
             ==> read($Heap, ch#4, _module.Node.marked));
    }
    else
    {
        assume S#0[$Box(n#4)] && read($Heap, n#4, _module.Node.marked)
           ==> (forall ch#4: ref ::
            { read($Heap, ch#4, _module.Node.marked) }
              { Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4)) }
            $Is(ch#4, Tclass._module.Node?())
               ==>
              Seq#Contains(read($Heap, n#4, _module.Node.children), $Box(ch#4))
                 && ch#4 != null
               ==> read($Heap, ch#4, _module.Node.marked));
    }

    assume (forall n#5: ref ::
      { read($Heap, n#5, _module.Node.children) }
        { read($Heap, n#5, _module.Node.marked) }
        { S#0[$Box(n#5)] }
      $Is(n#5, Tclass._module.Node())
         ==>
        S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
         ==> (forall ch#5: ref ::
          { read($Heap, ch#5, _module.Node.marked) }
            { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
          $Is(ch#5, Tclass._module.Node?())
             ==>
            Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
               && ch#5 != null
             ==> read($Heap, ch#5, _module.Node.marked)));
    havoc n#6;
    assume $Is(n#6, Tclass._module.Node()) && $IsAlloc(n#6, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#6)];
        assert n#6 != null;
        assume read($Heap, n#6, _module.Node.marked);
        ##source#0 := root#0;
        ##sink#0 := n#6;
        ##S#0 := S#0;
        assert $IsAlloc(root#0, Tclass._module.Node(), old($Heap));
        assert $IsAlloc(n#6, Tclass._module.Node(), old($Heap));
        assert $IsAlloc(S#0, TSet(Tclass._module.Node()), old($Heap));
        assume _module.__default.Reachable#canCall(old($Heap), root#0, n#6, S#0);
        assume _module.__default.Reachable(old($Heap), root#0, n#6, S#0);
    }
    else
    {
        assume S#0[$Box(n#6)] && read($Heap, n#6, _module.Node.marked)
           ==> _module.__default.Reachable(old($Heap), root#0, n#6, S#0);
    }

    assume (forall n#7: ref ::
      { _module.__default.Reachable(old($Heap), root#0, n#7, S#0) }
        { read($Heap, n#7, _module.Node.marked) }
        { S#0[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node())
         ==>
        S#0[$Box(n#7)] && read($Heap, n#7, _module.Node.marked)
         ==> _module.__default.Reachable(old($Heap), root#0, n#7, S#0));
    havoc n#8;
    assume $Is(n#8, Tclass._module.Node()) && $IsAlloc(n#8, Tclass._module.Node(), $Heap);
    if (*)
    {
        assume S#0[$Box(n#8)];
        assert n#8 != null;
        assert n#8 != null;
        assert $IsAlloc(n#8, Tclass._module.Node(), old($Heap));
        assume read($Heap, n#8, _module.Node.childrenVisited)
           == read(old($Heap), n#8, _module.Node.childrenVisited);
        assert n#8 != null;
        assert n#8 != null;
        assert $IsAlloc(n#8, Tclass._module.Node(), old($Heap));
        assume Seq#Equal(read($Heap, n#8, _module.Node.children),
          read(old($Heap), n#8, _module.Node.children));
    }
    else
    {
        assume S#0[$Box(n#8)]
           ==> read($Heap, n#8, _module.Node.childrenVisited)
               == read(old($Heap), n#8, _module.Node.childrenVisited)
             && Seq#Equal(read($Heap, n#8, _module.Node.children),
              read(old($Heap), n#8, _module.Node.children));
    }

    assume (forall n#9: ref ::
      { read(old($Heap), n#9, _module.Node.children) }
        { read($Heap, n#9, _module.Node.children) }
        { read(old($Heap), n#9, _module.Node.childrenVisited) }
        { read($Heap, n#9, _module.Node.childrenVisited) }
        { S#0[$Box(n#9)] }
      $Is(n#9, Tclass._module.Node())
         ==> (S#0[$Box(n#9)]
             ==> read($Heap, n#9, _module.Node.childrenVisited)
               == read(old($Heap), n#9, _module.Node.childrenVisited))
           && (S#0[$Box(n#9)]
             ==> Seq#Equal(read($Heap, n#9, _module.Node.children),
              read(old($Heap), n#9, _module.Node.children))));
}



procedure {:verboseName "SchorrWaite (call)"} Call$$_module.__default.SchorrWaite(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.childrenVisited) }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.children) }
      { read($Heap, n#5, _module.Node.marked) }
      { S#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
       ==> (forall ch#5: ref ::
        { read($Heap, ch#5, _module.Node.marked) }
          { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
        $Is(ch#5, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
             && ch#5 != null
           ==> read($Heap, ch#5, _module.Node.marked)));
  free ensures (forall n#7: ref ::
    { _module.__default.Reachable(old($Heap), root#0, n#7, S#0) }
      { read($Heap, n#7, _module.Node.marked) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==>
      S#0[$Box(n#7)]
       ==>
      read($Heap, n#7, _module.Node.marked)
       ==> _module.__default.Reachable#canCall(old($Heap), root#0, n#7, S#0));
  ensures (forall n#7: ref ::
    { _module.__default.Reachable(old($Heap), root#0, n#7, S#0) }
      { read($Heap, n#7, _module.Node.marked) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==>
      S#0[$Box(n#7)] && read($Heap, n#7, _module.Node.marked)
       ==> _module.__default.Reachable(old($Heap), root#0, n#7, S#0));
  free ensures true;
  ensures (forall n#9: ref ::
    { read(old($Heap), n#9, _module.Node.children) }
      { read($Heap, n#9, _module.Node.children) }
      { read(old($Heap), n#9, _module.Node.childrenVisited) }
      { read($Heap, n#9, _module.Node.childrenVisited) }
      { S#0[$Box(n#9)] }
    $Is(n#9, Tclass._module.Node())
       ==> (S#0[$Box(n#9)]
           ==> read($Heap, n#9, _module.Node.childrenVisited)
             == read(old($Heap), n#9, _module.Node.childrenVisited))
         && (S#0[$Box(n#9)]
           ==> Seq#Equal(read($Heap, n#9, _module.Node.children),
            read(old($Heap), n#9, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "SchorrWaite (correctness)"} Impl$$_module.__default.SchorrWaite(root#0: ref
       where $Is(root#0, Tclass._module.Node())
         && $IsAlloc(root#0, Tclass._module.Node(), $Heap),
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.children) } { S#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node())
       ==>
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref ::
        { S#0[$Box(ch#2)] }
          { Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2)) }
        $Is(ch#2, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#1, _module.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.childrenVisited) }
      { read($Heap, n#3, _module.Node.marked) }
      { S#0[$Box(n#3)] }
    $Is(n#3, Tclass._module.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, _module.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, _module.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, _module.Node.marked);
  free ensures true;
  ensures (forall n#5: ref ::
    { read($Heap, n#5, _module.Node.children) }
      { read($Heap, n#5, _module.Node.marked) }
      { S#0[$Box(n#5)] }
    $Is(n#5, Tclass._module.Node())
       ==>
      S#0[$Box(n#5)] && read($Heap, n#5, _module.Node.marked)
       ==> (forall ch#5: ref ::
        { read($Heap, ch#5, _module.Node.marked) }
          { Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5)) }
        $Is(ch#5, Tclass._module.Node?())
           ==>
          Seq#Contains(read($Heap, n#5, _module.Node.children), $Box(ch#5))
             && ch#5 != null
           ==> read($Heap, ch#5, _module.Node.marked)));
  free ensures (forall n#7: ref ::
    { _module.__default.Reachable(old($Heap), root#0, n#7, S#0) }
      { read($Heap, n#7, _module.Node.marked) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==>
      S#0[$Box(n#7)]
       ==>
      read($Heap, n#7, _module.Node.marked)
       ==> _module.__default.Reachable#canCall(old($Heap), root#0, n#7, S#0));
  ensures (forall n#7: ref ::
    { _module.__default.Reachable(old($Heap), root#0, n#7, S#0) }
      { read($Heap, n#7, _module.Node.marked) }
      { S#0[$Box(n#7)] }
    $Is(n#7, Tclass._module.Node())
       ==>
      S#0[$Box(n#7)] && read($Heap, n#7, _module.Node.marked)
       ==> _module.__default.Reachable(old($Heap), root#0, n#7, S#0));
  free ensures true;
  ensures (forall n#9: ref ::
    { read(old($Heap), n#9, _module.Node.children) }
      { read($Heap, n#9, _module.Node.children) }
      { read(old($Heap), n#9, _module.Node.childrenVisited) }
      { read($Heap, n#9, _module.Node.childrenVisited) }
      { S#0[$Box(n#9)] }
    $Is(n#9, Tclass._module.Node())
       ==> (S#0[$Box(n#9)]
           ==> read($Heap, n#9, _module.Node.childrenVisited)
             == read(old($Heap), n#9, _module.Node.childrenVisited))
         && (S#0[$Box(n#9)]
           ==> Seq#Equal(read($Heap, n#9, _module.Node.children),
            read(old($Heap), n#9, _module.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref ::
    { $Heap[$o] }
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "SchorrWaite (correctness)"} Impl$$_module.__default.SchorrWaite(root#0: ref, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#t#0: bool;
  var t#0: ref
     where defass#t#0
       ==> $Is(t#0, Tclass._module.Node()) && $IsAlloc(t#0, Tclass._module.Node(), $Heap);
  var p#0: ref
     where $Is(p#0, Tclass._module.Node?()) && $IsAlloc(p#0, Tclass._module.Node?(), $Heap);
  var newtype$check#2: ref;
  var path#0: DatatypeType
     where $Is(path#0, Tclass._module.Path())
       && $IsAlloc(path#0, Tclass._module.Path(), $Heap);
  var $rhs#0: bool;
  var $rhs#1: DatatypeType;
  var stackNodes#0: Seq Box
     where $Is(stackNodes#0, TSeq(Tclass._module.Node()))
       && $IsAlloc(stackNodes#0, TSeq(Tclass._module.Node()), $Heap);
  var unmarkedNodes#0: Set Box
     where $Is(unmarkedNodes#0, TSet(Tclass._module.Node()))
       && $IsAlloc(unmarkedNodes#0, TSet(Tclass._module.Node()), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var preLoop$loop#0$defass#t#0: bool;
  var $decr_init$loop#00: Set Box;
  var $decr_init$loop#01: Seq Box;
  var $decr_init$loop#02: int;
  var $w$loop#0: bool;
  var i#0: int;
  var newtype$check#3: ref;
  var n#10: ref;
  var n#12: ref;
  var n#14: ref;
  var j#0: int;
  var n#16: ref;
  var newtype$check#4: ref;
  var k#0: int;
  var k#2: int;
  var n#18: ref;
  var ch#6: ref;
  var newtype$check#5: ref;
  var n#20: ref;
  var j#2: int;
  var newtype$check#6: ref;
  var ##source#1: ref;
  var ##p#0: DatatypeType;
  var ##sink#1: ref;
  var ##S#1: Set Box;
  var n#24: ref;
  var pth#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##source#2: ref;
  var ##p#1: DatatypeType;
  var ##sink#2: ref;
  var ##S#2: Set Box;
  var n#26: ref;
  var ##source#3: ref;
  var ##sink#3: ref;
  var ##S#3: Set Box;
  var n#28: ref;
  var $decr$loop#00: Set Box;
  var $decr$loop#01: Seq Box;
  var $decr$loop#02: int;
  var $rhs#0_0_0: int;
  var newtype$check#0_0_0: ref;
  var oldP#0_0_0: ref
     where $Is(oldP#0_0_0, Tclass._module.Node?())
       && $IsAlloc(oldP#0_0_0, Tclass._module.Node?(), $Heap);
  var $rhs#0_0_1: Seq Box;
  var $rhs#0_0_2: int;
  var newtype$check#0_1_0: ref;
  var $rhs#0_1_0_0: int;
  var newT#0_1_1_0: ref
     where $Is(newT#0_1_1_0, Tclass._module.Node?())
       && $IsAlloc(newT#0_1_1_0, Tclass._module.Node?(), $Heap);
  var $rhs#0_1_1_0: Seq Box;
  var $rhs#0_1_1_1: bool;
  var $rhs#0_1_1_2: DatatypeType;

    // AddMethodImpl: SchorrWaite, Impl$$_module.__default.SchorrWaite
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(188,9)
    assume true;
    assume true;
    t#0 := root#0;
    defass#t#0 := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(189,16)
    assume true;
    newtype$check#2 := null;
    assume true;
    p#0 := null;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(190,18)
    assume true;
    assume true;
    path#0 := Lit(#_module.Path.Empty());
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(191,12)
    assert defass#t#0;
    assert t#0 != null;
    assume true;
    assert $_Frame[t#0, _module.Node.marked];
    assume true;
    $rhs#0 := Lit(true);
    $Heap := update($Heap, t#0, _module.Node.marked, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(192,18)
    assert defass#t#0;
    assert t#0 != null;
    assume true;
    assert $_Frame[t#0, _module.Node.pathFromRoot];
    assume true;
    $rhs#1 := path#0;
    $Heap := update($Heap, t#0, _module.Node.pathFromRoot, $rhs#1);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(193,35)
    assume true;
    assume true;
    stackNodes#0 := Lit(Seq#Empty(): Seq Box);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(194,27)
    assume true;
    assert defass#t#0;
    assume true;
    unmarkedNodes#0 := Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(t#0)));
    // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(195,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#t#0 := defass#t#0;
    $decr_init$loop#00 := unmarkedNodes#0;
    $decr_init$loop#01 := stackNodes#0;
    $decr_init$loop#02 := Seq#Length(read($Heap, t#0, _module.Node.children))
       - read($Heap, t#0, _module.Node.childrenVisited);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall i#1: int ::
          { $Unbox(Seq#Index(stackNodes#0, i#1)): ref }
          true
             ==>
            LitInt(0) <= i#1 && i#1 < Seq#Length(stackNodes#0)
             ==> S#0[Seq#Index(stackNodes#0, i#1)]);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> S#0[$Box(t#0)];
      invariant $w$loop#0 ==> !Seq#Contains(stackNodes#0, $Box(t#0));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> p#0
           == (if Seq#Length(stackNodes#0) == LitInt(0)
             then null
             else $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#11: ref ::
          { read($Heap, n#11, _module.Node.children) }
            { read($Heap, n#11, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#11)) }
          $Is(n#11, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#11))
             ==> read($Heap, n#11, _module.Node.childrenVisited)
               < Seq#Length(read($Heap, n#11, _module.Node.children)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> read($Heap, t#0, _module.Node.childrenVisited)
           <= Seq#Length(read($Heap, t#0, _module.Node.children));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#13: ref ::
          { read($Heap, n#13, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#13)) }
            { S#0[$Box(n#13)] }
          $Is(n#13, Tclass._module.Node())
             ==>
            S#0[$Box(n#13)] && !Seq#Contains(stackNodes#0, $Box(n#13)) && n#13 != t#0
             ==> read($Heap, n#13, _module.Node.childrenVisited) == LitInt(0));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#15: ref ::
          { read($Heap, n#15, _module.Node.childrenVisited) }
            { read(old($Heap), n#15, _module.Node.children) }
            { read($Heap, n#15, _module.Node.children) }
            { Seq#Contains(stackNodes#0, $Box(n#15)) }
          $Is(n#15, Tclass._module.Node())
             ==> (Seq#Contains(stackNodes#0, $Box(n#15))
                 ==> Seq#Length(read($Heap, n#15, _module.Node.children))
                   == Seq#Length(read(old($Heap), n#15, _module.Node.children)))
               && (Seq#Contains(stackNodes#0, $Box(n#15))
                 ==> (forall j#1: int ::
                  { $Unbox(Seq#Index(read(old($Heap), n#15, _module.Node.children), j#1)): ref }
                    { $Unbox(Seq#Index(read($Heap, n#15, _module.Node.children), j#1)): ref }
                  true
                     ==>
                    LitInt(0) <= j#1 && j#1 < Seq#Length(read($Heap, n#15, _module.Node.children))
                     ==> j#1 == read($Heap, n#15, _module.Node.childrenVisited)
                       || $Unbox(Seq#Index(read($Heap, n#15, _module.Node.children), j#1)): ref
                         == $Unbox(Seq#Index(read(old($Heap), n#15, _module.Node.children), j#1)): ref)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#17: ref ::
          { read(old($Heap), n#17, _module.Node.children) }
            { read($Heap, n#17, _module.Node.children) }
            { Seq#Contains(stackNodes#0, $Box(n#17)) }
            { S#0[$Box(n#17)] }
          $Is(n#17, Tclass._module.Node())
             ==>
            S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17))
             ==> Seq#Equal(read($Heap, n#17, _module.Node.children),
              read(old($Heap), n#17, _module.Node.children)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==>
        0 < Seq#Length(stackNodes#0)
         ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, _module.Node.children),
              read($Heap,
                $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref,
                _module.Node.childrenVisited))): ref
           == null;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall k#1: int ::
          {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.childrenVisited) }
            { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.children) }
          true
             ==>
            0 < k#1 && k#1 < Seq#Length(stackNodes#0)
             ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.children),
                  read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.childrenVisited))): ref
               == $Unbox(Seq#Index(stackNodes#0, k#1 - 1)): ref);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall k#3: int ::
          {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.childrenVisited) }
            { $Unbox(Seq#Index(stackNodes#0, k#3)): ref }
          true
             ==>
            LitInt(0) <= k#3 && k#3 < Seq#Length(stackNodes#0) - 1
             ==> $Unbox(Seq#Index(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.children),
                  read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.childrenVisited))): ref
               == $Unbox(Seq#Index(stackNodes#0, k#3 + 1)): ref);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==>
        0 < Seq#Length(stackNodes#0)
         ==> $Unbox(Seq#Index(read(old($Heap),
                $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                _module.Node.children),
              read($Heap,
                $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                _module.Node.childrenVisited))): ref
           == t#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, root#0, _module.Node.marked);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#19: ref ::
          { read($Heap, n#19, _module.Node.children) }
            { Seq#Contains(stackNodes#0, $Box(n#19)) }
            { read($Heap, n#19, _module.Node.marked) }
            { S#0[$Box(n#19)] }
          $Is(n#19, Tclass._module.Node())
             ==>
            S#0[$Box(n#19)]
               && read($Heap, n#19, _module.Node.marked)
               && !Seq#Contains(stackNodes#0, $Box(n#19))
               && n#19 != t#0
             ==> (forall ch#7: ref ::
              { read($Heap, ch#7, _module.Node.marked) }
                { Seq#Contains(read($Heap, n#19, _module.Node.children), $Box(ch#7)) }
              $Is(ch#7, Tclass._module.Node?())
                 ==>
                Seq#Contains(read($Heap, n#19, _module.Node.children), $Box(ch#7))
                   && ch#7 != null
                 ==> read($Heap, ch#7, _module.Node.marked)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#21: ref ::
          { read($Heap, n#21, _module.Node.marked) }
            { Seq#Contains(stackNodes#0, $Box(n#21)) }
          $Is(n#21, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
             ==> read($Heap, n#21, _module.Node.marked));
      invariant $w$loop#0
         ==> (forall n#21: ref ::
          { read($Heap, n#21, _module.Node.children) }
            { read($Heap, n#21, _module.Node.childrenVisited) }
            { Seq#Contains(stackNodes#0, $Box(n#21)) }
          $Is(n#21, Tclass._module.Node())
             ==>
            Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
             ==> (forall j#3: int ::
              { $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref }
              true
                 ==>
                LitInt(0) <= j#3 && j#3 < read($Heap, n#21, _module.Node.childrenVisited)
                 ==> $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref == null
                   || read($Heap,
                    $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref,
                    _module.Node.marked)));
      free invariant $w$loop#0
         ==>
        $IsAlloc(path#0, Tclass._module.Path(), old($Heap))
         ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
      invariant $w$loop#0 ==> $IsAlloc(path#0, Tclass._module.Path(), old($Heap));
      invariant $w$loop#0
         ==>
        _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0)
         ==> _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0)
           || (_module.Path.Empty_q(path#0) ==> root#0 == t#0);
      invariant $w$loop#0
         ==>
        _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0)
         ==> _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0)
           || (!_module.Path.Empty_q(path#0)
             ==> (var n#22 := _module.Path._h1(path#0);
              (var prefix#0 := _module.Path._h0(path#0); S#0[$Box(n#22)])));
      invariant $w$loop#0
         ==>
        _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0)
         ==> _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0)
           || (!_module.Path.Empty_q(path#0)
             ==> (var n#22 := _module.Path._h1(path#0);
              (var prefix#0 := _module.Path._h0(path#0);
                Seq#Contains(read(old($Heap), n#22, _module.Node.children), $Box(t#0)))));
      invariant $w$loop#0
         ==>
        _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0)
         ==> _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0)
           || (!_module.Path.Empty_q(path#0)
             ==> (var n#22 := _module.Path._h1(path#0);
              (var prefix#0 := _module.Path._h0(path#0);
                _module.__default.ReachableVia($LS($LS($LZ)), old($Heap), root#0, prefix#0, n#22, S#0))));
      free invariant $w$loop#0
         ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0)
           &&
          _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0)
           && (if _module.Path.Empty_q(path#0)
             then root#0 == t#0
             else (var n#23 := _module.Path._h1(path#0);
              (var prefix#1 := _module.Path._h0(path#0);
                S#0[$Box(n#23)]
                   && Seq#Contains(read(old($Heap), n#23, _module.Node.children), $Box(t#0))
                   && _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, prefix#1, n#23, S#0))));
      free invariant $w$loop#0
         ==> (forall n#25: ref ::
          { _module.__default.ReachableVia($LS($LZ),
              old($Heap),
              root#0,
              read(old($Heap), n#25, _module.Node.pathFromRoot),
              n#25,
              S#0) }
            { read($Heap, n#25, _module.Node.pathFromRoot) }
            { read($Heap, n#25, _module.Node.marked) }
            { S#0[$Box(n#25)] }
          $Is(n#25, Tclass._module.Node())
             ==>
            S#0[$Box(n#25)]
             ==>
            read($Heap, n#25, _module.Node.marked)
             ==> (var pth#0 := read($Heap, n#25, _module.Node.pathFromRoot);
              $IsAlloc(pth#0, Tclass._module.Path(), old($Heap))
                 ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, pth#0, n#25, S#0)));
      invariant $w$loop#0
         ==> (forall n#25: ref ::
          { _module.__default.ReachableVia($LS($LZ),
              old($Heap),
              root#0,
              read(old($Heap), n#25, _module.Node.pathFromRoot),
              n#25,
              S#0) }
            { read($Heap, n#25, _module.Node.pathFromRoot) }
            { read($Heap, n#25, _module.Node.marked) }
            { S#0[$Box(n#25)] }
          $Is(n#25, Tclass._module.Node())
             ==>
            S#0[$Box(n#25)] && read($Heap, n#25, _module.Node.marked)
             ==> (var pth#0 := read($Heap, n#25, _module.Node.pathFromRoot);
              $IsAlloc(pth#0, Tclass._module.Path(), old($Heap))
                 && _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, pth#0, n#25, S#0)));
      free invariant $w$loop#0
         ==> (forall n#27: ref ::
          { _module.__default.Reachable(old($Heap), root#0, n#27, S#0) }
            { read($Heap, n#27, _module.Node.marked) }
            { S#0[$Box(n#27)] }
          $Is(n#27, Tclass._module.Node())
             ==>
            S#0[$Box(n#27)]
             ==>
            read($Heap, n#27, _module.Node.marked)
             ==> _module.__default.Reachable#canCall(old($Heap), root#0, n#27, S#0));
      invariant $w$loop#0
         ==> (forall n#27: ref ::
          { _module.__default.Reachable(old($Heap), root#0, n#27, S#0) }
            { read($Heap, n#27, _module.Node.marked) }
            { S#0[$Box(n#27)] }
          $Is(n#27, Tclass._module.Node())
             ==>
            S#0[$Box(n#27)] && read($Heap, n#27, _module.Node.marked)
             ==> _module.__default.Reachable(old($Heap), root#0, n#27, S#0));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall n#29: ref ::
          { unmarkedNodes#0[$Box(n#29)] }
            { read($Heap, n#29, _module.Node.marked) }
            { S#0[$Box(n#29)] }
          $Is(n#29, Tclass._module.Node())
             ==>
            S#0[$Box(n#29)] && !read($Heap, n#29, _module.Node.marked)
             ==> unmarkedNodes#0[$Box(n#29)]);
      free invariant (forall $o: ref ::
        { $Heap[$o] }
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || S#0[$Box($o)]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant preLoop$loop#0$defass#t#0 ==> defass#t#0;
      free invariant Set#Subset(unmarkedNodes#0, $decr_init$loop#00)
         && (Set#Equal(unmarkedNodes#0, $decr_init$loop#00)
           ==> Seq#Rank(stackNodes#0) <= Seq#Rank($decr_init$loop#01)
             && (Seq#Rank(stackNodes#0) == Seq#Rank($decr_init$loop#01)
               ==> Seq#Length(read($Heap, t#0, _module.Node.children))
                     - read($Heap, t#0, _module.Node.childrenVisited)
                   <= $decr_init$loop#02
                 && (Seq#Length(read($Heap, t#0, _module.Node.children))
                       - read($Heap, t#0, _module.Node.childrenVisited)
                     == $decr_init$loop#02
                   ==> true)));
    {
        if (!$w$loop#0)
        {
            // Begin Comprehension WF check
            havoc i#0;
            if (true)
            {
                if (LitInt(0) <= i#0)
                {
                }

                if (LitInt(0) <= i#0 && i#0 < Seq#Length(stackNodes#0))
                {
                    assert {:subsumption 0} 0 <= i#0 && i#0 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall i#1: int ::
              { $Unbox(Seq#Index(stackNodes#0, i#1)): ref }
              true
                 ==>
                LitInt(0) <= i#1 && i#1 < Seq#Length(stackNodes#0)
                 ==> S#0[Seq#Index(stackNodes#0, i#1)]);
            assert defass#t#0;
            if (S#0[$Box(t#0)])
            {
                assert defass#t#0;
            }

            assume true;
            assume S#0[$Box(t#0)] && !Seq#Contains(stackNodes#0, $Box(t#0));
            if (Seq#Length(stackNodes#0) == LitInt(0))
            {
                newtype$check#3 := null;
            }
            else
            {
                assert {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
            }

            assume true;
            assume p#0
               == (if Seq#Length(stackNodes#0) == LitInt(0)
                 then null
                 else $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref);
            // Begin Comprehension WF check
            havoc n#10;
            if ($Is(n#10, Tclass._module.Node()) && $IsAlloc(n#10, Tclass._module.Node(), $Heap))
            {
                if (Seq#Contains(stackNodes#0, $Box(n#10)))
                {
                    assert {:subsumption 0} n#10 != null;
                    assert {:subsumption 0} n#10 != null;
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#11: ref ::
              { read($Heap, n#11, _module.Node.children) }
                { read($Heap, n#11, _module.Node.childrenVisited) }
                { Seq#Contains(stackNodes#0, $Box(n#11)) }
              $Is(n#11, Tclass._module.Node())
                 ==>
                Seq#Contains(stackNodes#0, $Box(n#11))
                 ==> read($Heap, n#11, _module.Node.childrenVisited)
                   < Seq#Length(read($Heap, n#11, _module.Node.children)));
            assert defass#t#0;
            assert {:subsumption 0} t#0 != null;
            assert defass#t#0;
            assert {:subsumption 0} t#0 != null;
            assume true;
            assume read($Heap, t#0, _module.Node.childrenVisited)
               <= Seq#Length(read($Heap, t#0, _module.Node.children));
            // Begin Comprehension WF check
            havoc n#12;
            if ($Is(n#12, Tclass._module.Node()) && $IsAlloc(n#12, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#12)])
                {
                }

                if (S#0[$Box(n#12)] && !Seq#Contains(stackNodes#0, $Box(n#12)))
                {
                    assert defass#t#0;
                }

                if (S#0[$Box(n#12)] && !Seq#Contains(stackNodes#0, $Box(n#12)) && n#12 != t#0)
                {
                    assert {:subsumption 0} n#12 != null;
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#13: ref ::
              { read($Heap, n#13, _module.Node.childrenVisited) }
                { Seq#Contains(stackNodes#0, $Box(n#13)) }
                { S#0[$Box(n#13)] }
              $Is(n#13, Tclass._module.Node())
                 ==>
                S#0[$Box(n#13)] && !Seq#Contains(stackNodes#0, $Box(n#13)) && n#13 != t#0
                 ==> read($Heap, n#13, _module.Node.childrenVisited) == LitInt(0));
            // Begin Comprehension WF check
            havoc n#14;
            if ($Is(n#14, Tclass._module.Node()) && $IsAlloc(n#14, Tclass._module.Node(), $Heap))
            {
                if (Seq#Contains(stackNodes#0, $Box(n#14)))
                {
                    assert {:subsumption 0} n#14 != null;
                    assert {:subsumption 0} n#14 != null;
                    assert $IsAlloc(n#14, Tclass._module.Node(), old($Heap));
                    if (Seq#Length(read($Heap, n#14, _module.Node.children))
                       == Seq#Length(read(old($Heap), n#14, _module.Node.children)))
                    {
                        // Begin Comprehension WF check
                        havoc j#0;
                        if (true)
                        {
                            if (LitInt(0) <= j#0)
                            {
                                assert {:subsumption 0} n#14 != null;
                            }

                            if (LitInt(0) <= j#0 && j#0 < Seq#Length(read($Heap, n#14, _module.Node.children)))
                            {
                                assert {:subsumption 0} n#14 != null;
                                if (j#0 != read($Heap, n#14, _module.Node.childrenVisited))
                                {
                                    assert {:subsumption 0} n#14 != null;
                                    assert {:subsumption 0} 0 <= j#0 && j#0 < Seq#Length(read($Heap, n#14, _module.Node.children));
                                    assert {:subsumption 0} n#14 != null;
                                    assert $IsAlloc(n#14, Tclass._module.Node(), old($Heap));
                                    assert {:subsumption 0} 0 <= j#0 && j#0 < Seq#Length(read(old($Heap), n#14, _module.Node.children));
                                }
                            }
                        }

                        // End Comprehension WF check
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#15: ref ::
              { read($Heap, n#15, _module.Node.childrenVisited) }
                { read(old($Heap), n#15, _module.Node.children) }
                { read($Heap, n#15, _module.Node.children) }
                { Seq#Contains(stackNodes#0, $Box(n#15)) }
              $Is(n#15, Tclass._module.Node())
                 ==> (Seq#Contains(stackNodes#0, $Box(n#15))
                     ==> Seq#Length(read($Heap, n#15, _module.Node.children))
                       == Seq#Length(read(old($Heap), n#15, _module.Node.children)))
                   && (Seq#Contains(stackNodes#0, $Box(n#15))
                     ==> (forall j#1: int ::
                      { $Unbox(Seq#Index(read(old($Heap), n#15, _module.Node.children), j#1)): ref }
                        { $Unbox(Seq#Index(read($Heap, n#15, _module.Node.children), j#1)): ref }
                      true
                         ==>
                        LitInt(0) <= j#1 && j#1 < Seq#Length(read($Heap, n#15, _module.Node.children))
                         ==> j#1 == read($Heap, n#15, _module.Node.childrenVisited)
                           || $Unbox(Seq#Index(read($Heap, n#15, _module.Node.children), j#1)): ref
                             == $Unbox(Seq#Index(read(old($Heap), n#15, _module.Node.children), j#1)): ref)));
            // Begin Comprehension WF check
            havoc n#16;
            if ($Is(n#16, Tclass._module.Node()) && $IsAlloc(n#16, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#16)])
                {
                }

                if (S#0[$Box(n#16)] && !Seq#Contains(stackNodes#0, $Box(n#16)))
                {
                    assert {:subsumption 0} n#16 != null;
                    assert {:subsumption 0} n#16 != null;
                    assert $IsAlloc(n#16, Tclass._module.Node(), old($Heap));
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#17: ref ::
              { read(old($Heap), n#17, _module.Node.children) }
                { read($Heap, n#17, _module.Node.children) }
                { Seq#Contains(stackNodes#0, $Box(n#17)) }
                { S#0[$Box(n#17)] }
              $Is(n#17, Tclass._module.Node())
                 ==>
                S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17))
                 ==> Seq#Equal(read($Heap, n#17, _module.Node.children),
                  read(old($Heap), n#17, _module.Node.children)));
            if (0 < Seq#Length(stackNodes#0))
            {
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref != null;
                // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(231,40)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assume true;
                assert Seq#Contains(stackNodes#0, Seq#Index(stackNodes#0, LitInt(0)));
                // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(231,76)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref != null;
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref != null;
                assume true;
                assert read($Heap,
                    $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref,
                    _module.Node.childrenVisited)
                   < Seq#Length(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, _module.Node.children));
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref != null;
                assert {:subsumption 0} 0
                     <= read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref,
                      _module.Node.childrenVisited)
                   && read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref,
                      _module.Node.childrenVisited)
                     < Seq#Length(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, _module.Node.children));
                newtype$check#4 := null;
            }

            assume true;
            assume 0 < Seq#Length(stackNodes#0)
               ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, _module.Node.children),
                    read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref,
                      _module.Node.childrenVisited))): ref
                 == null;
            // Begin Comprehension WF check
            havoc k#0;
            if (true)
            {
                if (0 < k#0)
                {
                }

                if (0 < k#0 && k#0 < Seq#Length(stackNodes#0))
                {
                    assert {:subsumption 0} 0 <= k#0 && k#0 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#0)): ref != null;
                    assert {:subsumption 0} 0 <= k#0 && k#0 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#0)): ref != null;
                    assert {:subsumption 0} 0
                         <= read($Heap, $Unbox(Seq#Index(stackNodes#0, k#0)): ref, _module.Node.childrenVisited)
                       && read($Heap, $Unbox(Seq#Index(stackNodes#0, k#0)): ref, _module.Node.childrenVisited)
                         < Seq#Length(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#0)): ref, _module.Node.children));
                    assert {:subsumption 0} 0 <= k#0 - 1 && k#0 - 1 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#1: int ::
              {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.childrenVisited) }
                { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.children) }
              true
                 ==>
                0 < k#1 && k#1 < Seq#Length(stackNodes#0)
                 ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.children),
                      read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.childrenVisited))): ref
                   == $Unbox(Seq#Index(stackNodes#0, k#1 - 1)): ref);
            // Begin Comprehension WF check
            havoc k#2;
            if (true)
            {
                if (LitInt(0) <= k#2)
                {
                }

                if (LitInt(0) <= k#2 && k#2 < Seq#Length(stackNodes#0) - 1)
                {
                    assert {:subsumption 0} 0 <= k#2 && k#2 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#2)): ref != null;
                    assert $IsAlloc($Unbox(Seq#Index(stackNodes#0, k#2)): ref, Tclass._module.Node(), old($Heap));
                    assert {:subsumption 0} 0 <= k#2 && k#2 < Seq#Length(stackNodes#0);
                    assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#2)): ref != null;
                    assert {:subsumption 0} 0
                         <= read($Heap, $Unbox(Seq#Index(stackNodes#0, k#2)): ref, _module.Node.childrenVisited)
                       && read($Heap, $Unbox(Seq#Index(stackNodes#0, k#2)): ref, _module.Node.childrenVisited)
                         < Seq#Length(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#2)): ref, _module.Node.children));
                    assert {:subsumption 0} 0 <= k#2 + 1 && k#2 + 1 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#3: int ::
              {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.childrenVisited) }
                { $Unbox(Seq#Index(stackNodes#0, k#3)): ref }
              true
                 ==>
                LitInt(0) <= k#3 && k#3 < Seq#Length(stackNodes#0) - 1
                 ==> $Unbox(Seq#Index(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.children),
                      read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.childrenVisited))): ref
                   == $Unbox(Seq#Index(stackNodes#0, k#3 + 1)): ref);
            if (0 < Seq#Length(stackNodes#0))
            {
                assert {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref != null;
                assert $IsAlloc($Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                  Tclass._module.Node(),
                  old($Heap));
                assert {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
                assert {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref != null;
                assert {:subsumption 0} 0
                     <= read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.childrenVisited)
                   && read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.childrenVisited)
                     < Seq#Length(read(old($Heap),
                        $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                        _module.Node.children));
                assert defass#t#0;
            }

            assume true;
            assume 0 < Seq#Length(stackNodes#0)
               ==> $Unbox(Seq#Index(read(old($Heap),
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.children),
                    read($Heap,
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                      _module.Node.childrenVisited))): ref
                 == t#0;
            assert {:subsumption 0} root#0 != null;
            assume true;
            assume read($Heap, root#0, _module.Node.marked);
            // Begin Comprehension WF check
            havoc n#18;
            if ($Is(n#18, Tclass._module.Node()) && $IsAlloc(n#18, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#18)])
                {
                    assert {:subsumption 0} n#18 != null;
                }

                if (S#0[$Box(n#18)] && read($Heap, n#18, _module.Node.marked))
                {
                }

                if (S#0[$Box(n#18)]
                   && read($Heap, n#18, _module.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#18)))
                {
                    assert defass#t#0;
                }

                if (S#0[$Box(n#18)]
                   && read($Heap, n#18, _module.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#18))
                   && n#18 != t#0)
                {
                    // Begin Comprehension WF check
                    havoc ch#6;
                    if ($Is(ch#6, Tclass._module.Node?())
                       && $IsAlloc(ch#6, Tclass._module.Node?(), $Heap))
                    {
                        assert {:subsumption 0} n#18 != null;
                        if (Seq#Contains(read($Heap, n#18, _module.Node.children), $Box(ch#6)))
                        {
                            newtype$check#5 := null;
                        }

                        if (Seq#Contains(read($Heap, n#18, _module.Node.children), $Box(ch#6))
                           && ch#6 != null)
                        {
                            assert {:subsumption 0} ch#6 != null;
                        }
                    }

                    // End Comprehension WF check
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#19: ref ::
              { read($Heap, n#19, _module.Node.children) }
                { Seq#Contains(stackNodes#0, $Box(n#19)) }
                { read($Heap, n#19, _module.Node.marked) }
                { S#0[$Box(n#19)] }
              $Is(n#19, Tclass._module.Node())
                 ==>
                S#0[$Box(n#19)]
                   && read($Heap, n#19, _module.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#19))
                   && n#19 != t#0
                 ==> (forall ch#7: ref ::
                  { read($Heap, ch#7, _module.Node.marked) }
                    { Seq#Contains(read($Heap, n#19, _module.Node.children), $Box(ch#7)) }
                  $Is(ch#7, Tclass._module.Node?())
                     ==>
                    Seq#Contains(read($Heap, n#19, _module.Node.children), $Box(ch#7))
                       && ch#7 != null
                     ==> read($Heap, ch#7, _module.Node.marked)));
            // Begin Comprehension WF check
            havoc n#20;
            if ($Is(n#20, Tclass._module.Node()) && $IsAlloc(n#20, Tclass._module.Node(), $Heap))
            {
                if (!Seq#Contains(stackNodes#0, $Box(n#20)))
                {
                    assert defass#t#0;
                }

                if (Seq#Contains(stackNodes#0, $Box(n#20)) || n#20 == t#0)
                {
                    assert {:subsumption 0} n#20 != null;
                    if (read($Heap, n#20, _module.Node.marked))
                    {
                        // Begin Comprehension WF check
                        havoc j#2;
                        if (true)
                        {
                            if (LitInt(0) <= j#2)
                            {
                                assert {:subsumption 0} n#20 != null;
                            }

                            if (LitInt(0) <= j#2 && j#2 < read($Heap, n#20, _module.Node.childrenVisited))
                            {
                                assert {:subsumption 0} n#20 != null;
                                assert {:subsumption 0} 0 <= j#2 && j#2 < Seq#Length(read($Heap, n#20, _module.Node.children));
                                newtype$check#6 := null;
                                if ($Unbox(Seq#Index(read($Heap, n#20, _module.Node.children), j#2)): ref != null)
                                {
                                    assert {:subsumption 0} n#20 != null;
                                    assert {:subsumption 0} 0 <= j#2 && j#2 < Seq#Length(read($Heap, n#20, _module.Node.children));
                                    assert {:subsumption 0} $Unbox(Seq#Index(read($Heap, n#20, _module.Node.children), j#2)): ref != null;
                                }
                            }
                        }

                        // End Comprehension WF check
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#21: ref ::
                { read($Heap, n#21, _module.Node.marked) }
                  { Seq#Contains(stackNodes#0, $Box(n#21)) }
                $Is(n#21, Tclass._module.Node())
                   ==>
                  Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
                   ==> read($Heap, n#21, _module.Node.marked))
               && (forall n#21: ref ::
                { read($Heap, n#21, _module.Node.children) }
                  { read($Heap, n#21, _module.Node.childrenVisited) }
                  { Seq#Contains(stackNodes#0, $Box(n#21)) }
                $Is(n#21, Tclass._module.Node())
                   ==>
                  Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
                   ==> (forall j#3: int ::
                    { $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref }
                    true
                       ==>
                      LitInt(0) <= j#3 && j#3 < read($Heap, n#21, _module.Node.childrenVisited)
                       ==> $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref == null
                         || read($Heap,
                          $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref,
                          _module.Node.marked)));
            if ($IsAlloc(path#0, Tclass._module.Path(), old($Heap)))
            {
                assert defass#t#0;
                ##source#1 := root#0;
                ##p#0 := path#0;
                ##sink#1 := t#0;
                ##S#1 := S#0;
                assert $IsAlloc(root#0, Tclass._module.Node(), old($Heap));
                assert $IsAlloc(path#0, Tclass._module.Path(), old($Heap));
                assert $IsAlloc(t#0, Tclass._module.Node(), old($Heap));
                assert $IsAlloc(S#0, TSet(Tclass._module.Node()), old($Heap));
                assume _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
            }

            assume $IsAlloc(path#0, Tclass._module.Path(), old($Heap))
               ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
            assume $IsAlloc(path#0, Tclass._module.Path(), old($Heap))
               && _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0);
            // Begin Comprehension WF check
            havoc n#24;
            if ($Is(n#24, Tclass._module.Node()) && $IsAlloc(n#24, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#24)])
                {
                    assert {:subsumption 0} n#24 != null;
                }

                if (S#0[$Box(n#24)] && read($Heap, n#24, _module.Node.marked))
                {
                    havoc pth#Z#0;
                    assume $Is(pth#Z#0, Tclass._module.Path())
                       && $IsAlloc(pth#Z#0, Tclass._module.Path(), $Heap);
                    assert {:subsumption 0} n#24 != null;
                    assume let#0#0#0 == read($Heap, n#24, _module.Node.pathFromRoot);
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(let#0#0#0, Tclass._module.Path());
                    assume pth#Z#0 == let#0#0#0;
                    if ($IsAlloc(pth#Z#0, Tclass._module.Path(), old($Heap)))
                    {
                        ##source#2 := root#0;
                        ##p#1 := pth#Z#0;
                        ##sink#2 := n#24;
                        ##S#2 := S#0;
                        assert $IsAlloc(root#0, Tclass._module.Node(), old($Heap));
                        assert $IsAlloc(pth#Z#0, Tclass._module.Path(), old($Heap));
                        assert $IsAlloc(n#24, Tclass._module.Node(), old($Heap));
                        assert $IsAlloc(S#0, TSet(Tclass._module.Node()), old($Heap));
                        assume _module.__default.ReachableVia#canCall(old($Heap), root#0, pth#Z#0, n#24, S#0);
                    }
                }
            }

            // End Comprehension WF check
            assume (forall n#25: ref ::
              { _module.__default.ReachableVia($LS($LZ),
                  old($Heap),
                  root#0,
                  read(old($Heap), n#25, _module.Node.pathFromRoot),
                  n#25,
                  S#0) }
                { read($Heap, n#25, _module.Node.pathFromRoot) }
                { read($Heap, n#25, _module.Node.marked) }
                { S#0[$Box(n#25)] }
              $Is(n#25, Tclass._module.Node())
                 ==>
                S#0[$Box(n#25)]
                 ==>
                read($Heap, n#25, _module.Node.marked)
                 ==> (var pth#0 := read($Heap, n#25, _module.Node.pathFromRoot);
                  $IsAlloc(pth#0, Tclass._module.Path(), old($Heap))
                     ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, pth#0, n#25, S#0)));
            assume (forall n#25: ref ::
              { _module.__default.ReachableVia($LS($LZ),
                  old($Heap),
                  root#0,
                  read(old($Heap), n#25, _module.Node.pathFromRoot),
                  n#25,
                  S#0) }
                { read($Heap, n#25, _module.Node.pathFromRoot) }
                { read($Heap, n#25, _module.Node.marked) }
                { S#0[$Box(n#25)] }
              $Is(n#25, Tclass._module.Node())
                 ==>
                S#0[$Box(n#25)] && read($Heap, n#25, _module.Node.marked)
                 ==> (var pth#0 := read($Heap, n#25, _module.Node.pathFromRoot);
                  $IsAlloc(pth#0, Tclass._module.Path(), old($Heap))
                     && _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, pth#0, n#25, S#0)));
            // Begin Comprehension WF check
            havoc n#26;
            if ($Is(n#26, Tclass._module.Node()) && $IsAlloc(n#26, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#26)])
                {
                    assert {:subsumption 0} n#26 != null;
                }

                if (S#0[$Box(n#26)] && read($Heap, n#26, _module.Node.marked))
                {
                    ##source#3 := root#0;
                    ##sink#3 := n#26;
                    ##S#3 := S#0;
                    assert $IsAlloc(root#0, Tclass._module.Node(), old($Heap));
                    assert $IsAlloc(n#26, Tclass._module.Node(), old($Heap));
                    assert $IsAlloc(S#0, TSet(Tclass._module.Node()), old($Heap));
                    assume _module.__default.Reachable#canCall(old($Heap), root#0, n#26, S#0);
                }
            }

            // End Comprehension WF check
            assume (forall n#27: ref ::
              { _module.__default.Reachable(old($Heap), root#0, n#27, S#0) }
                { read($Heap, n#27, _module.Node.marked) }
                { S#0[$Box(n#27)] }
              $Is(n#27, Tclass._module.Node())
                 ==>
                S#0[$Box(n#27)]
                 ==>
                read($Heap, n#27, _module.Node.marked)
                 ==> _module.__default.Reachable#canCall(old($Heap), root#0, n#27, S#0));
            assume (forall n#27: ref ::
              { _module.__default.Reachable(old($Heap), root#0, n#27, S#0) }
                { read($Heap, n#27, _module.Node.marked) }
                { S#0[$Box(n#27)] }
              $Is(n#27, Tclass._module.Node())
                 ==>
                S#0[$Box(n#27)] && read($Heap, n#27, _module.Node.marked)
                 ==> _module.__default.Reachable(old($Heap), root#0, n#27, S#0));
            // Begin Comprehension WF check
            havoc n#28;
            if ($Is(n#28, Tclass._module.Node()) && $IsAlloc(n#28, Tclass._module.Node(), $Heap))
            {
                if (S#0[$Box(n#28)])
                {
                    assert {:subsumption 0} n#28 != null;
                }

                if (S#0[$Box(n#28)] && !read($Heap, n#28, _module.Node.marked))
                {
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#29: ref ::
              { unmarkedNodes#0[$Box(n#29)] }
                { read($Heap, n#29, _module.Node.marked) }
                { S#0[$Box(n#29)] }
              $Is(n#29, Tclass._module.Node())
                 ==>
                S#0[$Box(n#29)] && !read($Heap, n#29, _module.Node.marked)
                 ==> unmarkedNodes#0[$Box(n#29)]);
            assume true;
            assume true;
            assert defass#t#0;
            assert t#0 != null;
            assert defass#t#0;
            assert t#0 != null;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := unmarkedNodes#0;
        $decr$loop#01 := stackNodes#0;
        $decr$loop#02 := Seq#Length(read($Heap, t#0, _module.Node.children))
           - read($Heap, t#0, _module.Node.childrenVisited);
        // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(258,5)
        assert defass#t#0;
        assert t#0 != null;
        assert defass#t#0;
        assert t#0 != null;
        assume true;
        if (read($Heap, t#0, _module.Node.childrenVisited)
           == Seq#Length(read($Heap, t#0, _module.Node.children)))
        {
            // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(259,7)
            assume true;
            assert {:focus} Lit(true);
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(261,25)
            assert defass#t#0;
            assert t#0 != null;
            assume true;
            assert $_Frame[t#0, _module.Node.childrenVisited];
            assume true;
            assert $Is(LitInt(0), Tclass._System.nat());
            $rhs#0_0_0 := LitInt(0);
            $Heap := update($Heap, t#0, _module.Node.childrenVisited, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(262,7)
            newtype$check#0_0_0 := null;
            assume true;
            if (p#0 == null)
            {
                // ----- return statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(263,9)
                return;
            }
            else
            {
            }

            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(265,16)
            assume true;
            assert p#0 != null;
            assert p#0 != null;
            assert 0 <= read($Heap, p#0, _module.Node.childrenVisited)
               && read($Heap, p#0, _module.Node.childrenVisited)
                 < Seq#Length(read($Heap, p#0, _module.Node.children));
            assume true;
            oldP#0_0_0 := $Unbox(Seq#Index(read($Heap, p#0, _module.Node.children),
                read($Heap, p#0, _module.Node.childrenVisited))): ref;
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(266,18)
            assert p#0 != null;
            assume true;
            assert $_Frame[p#0, _module.Node.children];
            assert p#0 != null;
            assert p#0 != null;
            assert 0 <= read($Heap, p#0, _module.Node.childrenVisited)
               && read($Heap, p#0, _module.Node.childrenVisited)
                 < Seq#Length(read($Heap, p#0, _module.Node.children));
            assert defass#t#0;
            assume true;
            $rhs#0_0_1 := Seq#Update(read($Heap, p#0, _module.Node.children),
              read($Heap, p#0, _module.Node.childrenVisited),
              $Box(t#0));
            $Heap := update($Heap, p#0, _module.Node.children, $rhs#0_0_1);
            assume $IsGoodHeap($Heap);
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(267,9)
            assume true;
            assume true;
            assert $Is(p#0, Tclass._module.Node());
            t#0 := p#0;
            defass#t#0 := true;
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(268,9)
            assume true;
            assume true;
            p#0 := oldP#0_0_0;
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(269,18)
            assume true;
            assert 0 <= Seq#Length(stackNodes#0) - 1
               && Seq#Length(stackNodes#0) - 1 <= Seq#Length(stackNodes#0);
            assume true;
            stackNodes#0 := Seq#Take(stackNodes#0, Seq#Length(stackNodes#0) - 1);
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(270,25)
            assert defass#t#0;
            assert t#0 != null;
            assume true;
            assert $_Frame[t#0, _module.Node.childrenVisited];
            assert defass#t#0;
            assert t#0 != null;
            assume true;
            assert $Is(read($Heap, t#0, _module.Node.childrenVisited) + 1, Tclass._System.nat());
            $rhs#0_0_2 := read($Heap, t#0, _module.Node.childrenVisited) + 1;
            $Heap := update($Heap, t#0, _module.Node.childrenVisited, $rhs#0_0_2);
            assume $IsGoodHeap($Heap);
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(271,12)
            assume true;
            assert defass#t#0;
            assert t#0 != null;
            assume true;
            path#0 := read($Heap, t#0, _module.Node.pathFromRoot);
        }
        else
        {
            // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(273,12)
            assert defass#t#0;
            assert t#0 != null;
            assert defass#t#0;
            assert t#0 != null;
            assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
               && read($Heap, t#0, _module.Node.childrenVisited)
                 < Seq#Length(read($Heap, t#0, _module.Node.children));
            newtype$check#0_1_0 := null;
            if ($Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                  read($Heap, t#0, _module.Node.childrenVisited))): ref
               != null)
            {
                assert defass#t#0;
                assert t#0 != null;
                assert defass#t#0;
                assert t#0 != null;
                assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
                   && read($Heap, t#0, _module.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, _module.Node.children));
                assert $Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                      read($Heap, t#0, _module.Node.childrenVisited))): ref
                   != null;
            }

            assume true;
            if ($Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                    read($Heap, t#0, _module.Node.childrenVisited))): ref
                 == null
               || read($Heap,
                $Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                    read($Heap, t#0, _module.Node.childrenVisited))): ref,
                _module.Node.marked))
            {
                // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(274,7)
                assume true;
                assert {:focus} Lit(true);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(276,25)
                assert defass#t#0;
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, _module.Node.childrenVisited];
                assert defass#t#0;
                assert t#0 != null;
                assume true;
                assert $Is(read($Heap, t#0, _module.Node.childrenVisited) + 1, Tclass._System.nat());
                $rhs#0_1_0_0 := read($Heap, t#0, _module.Node.childrenVisited) + 1;
                $Heap := update($Heap, t#0, _module.Node.childrenVisited, $rhs#0_1_0_0);
                assume $IsGoodHeap($Heap);
            }
            else
            {
                // ----- assert statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(279,7)
                assume true;
                assert {:focus} Lit(true);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(282,16)
                assume true;
                assert defass#t#0;
                assert t#0 != null;
                assert defass#t#0;
                assert t#0 != null;
                assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
                   && read($Heap, t#0, _module.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, _module.Node.children));
                assume true;
                newT#0_1_1_0 := $Unbox(Seq#Index(read($Heap, t#0, _module.Node.children),
                    read($Heap, t#0, _module.Node.childrenVisited))): ref;
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(283,18)
                assert defass#t#0;
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, _module.Node.children];
                assert defass#t#0;
                assert t#0 != null;
                assert defass#t#0;
                assert t#0 != null;
                assert 0 <= read($Heap, t#0, _module.Node.childrenVisited)
                   && read($Heap, t#0, _module.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, _module.Node.children));
                assume true;
                $rhs#0_1_1_0 := Seq#Update(read($Heap, t#0, _module.Node.children),
                  read($Heap, t#0, _module.Node.childrenVisited),
                  $Box(p#0));
                $Heap := update($Heap, t#0, _module.Node.children, $rhs#0_1_1_0);
                assume $IsGoodHeap($Heap);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(284,9)
                assume true;
                assert defass#t#0;
                assume true;
                p#0 := t#0;
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(285,18)
                assume true;
                assert defass#t#0;
                assume true;
                stackNodes#0 := Seq#Append(stackNodes#0, Seq#Build(Seq#Empty(): Seq Box, $Box(t#0)));
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(286,12)
                assume true;
                assert defass#t#0;
                assume true;
                path#0 := #_module.Path.Extend(path#0, t#0);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(287,9)
                assume true;
                assume true;
                assert $Is(newT#0_1_1_0, Tclass._module.Node());
                t#0 := newT#0_1_1_0;
                defass#t#0 := true;
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(288,16)
                assert defass#t#0;
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, _module.Node.marked];
                assume true;
                $rhs#0_1_1_1 := Lit(true);
                $Heap := update($Heap, t#0, _module.Node.marked, $rhs#0_1_1_1);
                assume $IsGoodHeap($Heap);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(289,22)
                assert defass#t#0;
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, _module.Node.pathFromRoot];
                assume true;
                $rhs#0_1_1_2 := path#0;
                $Heap := update($Heap, t#0, _module.Node.pathFromRoot, $rhs#0_1_1_2);
                assume $IsGoodHeap($Heap);
                // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(290,21)
                assume true;
                assert defass#t#0;
                assume true;
                unmarkedNodes#0 := Set#Difference(unmarkedNodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(t#0)));
            }
        }

        // ----- loop termination check ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\SchorrWaite.dfy(195,3)
        assert 0 <= $decr$loop#02
           || (Set#Subset(unmarkedNodes#0, $decr$loop#00)
             && !Set#Subset($decr$loop#00, unmarkedNodes#0))
           || Seq#Rank(stackNodes#0) < Seq#Rank($decr$loop#01)
           || Seq#Length(read($Heap, t#0, _module.Node.children))
               - read($Heap, t#0, _module.Node.childrenVisited)
             == $decr$loop#02;
        assert (Set#Subset(unmarkedNodes#0, $decr$loop#00)
             && !Set#Subset($decr$loop#00, unmarkedNodes#0))
           || (Set#Equal(unmarkedNodes#0, $decr$loop#00)
             && (Seq#Rank(stackNodes#0) < Seq#Rank($decr$loop#01)
               || (Seq#Rank(stackNodes#0) == Seq#Rank($decr$loop#01)
                 && Seq#Length(read($Heap, t#0, _module.Node.children))
                     - read($Heap, t#0, _module.Node.childrenVisited)
                   < $decr$loop#02)));
        assume (forall i#1: int ::
            { $Unbox(Seq#Index(stackNodes#0, i#1)): ref }
            true
               ==>
              LitInt(0) <= i#1 && i#1 < Seq#Length(stackNodes#0)
               ==> S#0[Seq#Index(stackNodes#0, i#1)])
           ==>
          S#0[$Box(t#0)]
           ==>
          !Seq#Contains(stackNodes#0, $Box(t#0))
           ==>
          p#0
             == (if Seq#Length(stackNodes#0) == LitInt(0)
               then null
               else $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref)
           ==>
          (forall n#11: ref ::
            { read($Heap, n#11, _module.Node.children) }
              { read($Heap, n#11, _module.Node.childrenVisited) }
              { Seq#Contains(stackNodes#0, $Box(n#11)) }
            $Is(n#11, Tclass._module.Node())
               ==>
              Seq#Contains(stackNodes#0, $Box(n#11))
               ==> read($Heap, n#11, _module.Node.childrenVisited)
                 < Seq#Length(read($Heap, n#11, _module.Node.children)))
           ==>
          read($Heap, t#0, _module.Node.childrenVisited)
             <= Seq#Length(read($Heap, t#0, _module.Node.children))
           ==>
          (forall n#13: ref ::
            { read($Heap, n#13, _module.Node.childrenVisited) }
              { Seq#Contains(stackNodes#0, $Box(n#13)) }
              { S#0[$Box(n#13)] }
            $Is(n#13, Tclass._module.Node())
               ==>
              S#0[$Box(n#13)] && !Seq#Contains(stackNodes#0, $Box(n#13)) && n#13 != t#0
               ==> read($Heap, n#13, _module.Node.childrenVisited) == LitInt(0))
           ==>
          (forall n#15: ref ::
            { read($Heap, n#15, _module.Node.childrenVisited) }
              { read(old($Heap), n#15, _module.Node.children) }
              { read($Heap, n#15, _module.Node.children) }
              { Seq#Contains(stackNodes#0, $Box(n#15)) }
            $Is(n#15, Tclass._module.Node())
               ==> (Seq#Contains(stackNodes#0, $Box(n#15))
                   ==> Seq#Length(read($Heap, n#15, _module.Node.children))
                     == Seq#Length(read(old($Heap), n#15, _module.Node.children)))
                 && (Seq#Contains(stackNodes#0, $Box(n#15))
                   ==> (forall j#1: int ::
                    { $Unbox(Seq#Index(read(old($Heap), n#15, _module.Node.children), j#1)): ref }
                      { $Unbox(Seq#Index(read($Heap, n#15, _module.Node.children), j#1)): ref }
                    true
                       ==>
                      LitInt(0) <= j#1 && j#1 < Seq#Length(read($Heap, n#15, _module.Node.children))
                       ==> j#1 == read($Heap, n#15, _module.Node.childrenVisited)
                         || $Unbox(Seq#Index(read($Heap, n#15, _module.Node.children), j#1)): ref
                           == $Unbox(Seq#Index(read(old($Heap), n#15, _module.Node.children), j#1)): ref)))
           ==>
          (forall n#17: ref ::
            { read(old($Heap), n#17, _module.Node.children) }
              { read($Heap, n#17, _module.Node.children) }
              { Seq#Contains(stackNodes#0, $Box(n#17)) }
              { S#0[$Box(n#17)] }
            $Is(n#17, Tclass._module.Node())
               ==>
              S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17))
               ==> Seq#Equal(read($Heap, n#17, _module.Node.children),
                read(old($Heap), n#17, _module.Node.children)))
           ==>
          (0 < Seq#Length(stackNodes#0)
           ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, _module.Node.children),
                read($Heap,
                  $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref,
                  _module.Node.childrenVisited))): ref
             == null)
           ==>
          (forall k#1: int ::
            {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.childrenVisited) }
              { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.children) }
            true
               ==>
              0 < k#1 && k#1 < Seq#Length(stackNodes#0)
               ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.children),
                    read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, _module.Node.childrenVisited))): ref
                 == $Unbox(Seq#Index(stackNodes#0, k#1 - 1)): ref)
           ==>
          (forall k#3: int ::
            {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.childrenVisited) }
              { $Unbox(Seq#Index(stackNodes#0, k#3)): ref }
            true
               ==>
              LitInt(0) <= k#3 && k#3 < Seq#Length(stackNodes#0) - 1
               ==> $Unbox(Seq#Index(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.children),
                    read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, _module.Node.childrenVisited))): ref
                 == $Unbox(Seq#Index(stackNodes#0, k#3 + 1)): ref)
           ==>
          (0 < Seq#Length(stackNodes#0)
           ==> $Unbox(Seq#Index(read(old($Heap),
                  $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                  _module.Node.children),
                read($Heap,
                  $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref,
                  _module.Node.childrenVisited))): ref
             == t#0)
           ==>
          read($Heap, root#0, _module.Node.marked)
           ==>
          (forall n#19: ref ::
            { read($Heap, n#19, _module.Node.children) }
              { Seq#Contains(stackNodes#0, $Box(n#19)) }
              { read($Heap, n#19, _module.Node.marked) }
              { S#0[$Box(n#19)] }
            $Is(n#19, Tclass._module.Node())
               ==>
              S#0[$Box(n#19)]
                 && read($Heap, n#19, _module.Node.marked)
                 && !Seq#Contains(stackNodes#0, $Box(n#19))
                 && n#19 != t#0
               ==> (forall ch#7: ref ::
                { read($Heap, ch#7, _module.Node.marked) }
                  { Seq#Contains(read($Heap, n#19, _module.Node.children), $Box(ch#7)) }
                $Is(ch#7, Tclass._module.Node?())
                   ==>
                  Seq#Contains(read($Heap, n#19, _module.Node.children), $Box(ch#7))
                     && ch#7 != null
                   ==> read($Heap, ch#7, _module.Node.marked)))
           ==>
          (forall n#21: ref ::
              { read($Heap, n#21, _module.Node.marked) }
                { Seq#Contains(stackNodes#0, $Box(n#21)) }
              $Is(n#21, Tclass._module.Node())
                 ==>
                Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
                 ==> read($Heap, n#21, _module.Node.marked))
             && (forall n#21: ref ::
              { read($Heap, n#21, _module.Node.children) }
                { read($Heap, n#21, _module.Node.childrenVisited) }
                { Seq#Contains(stackNodes#0, $Box(n#21)) }
              $Is(n#21, Tclass._module.Node())
                 ==>
                Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
                 ==> (forall j#3: int ::
                  { $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref }
                  true
                     ==>
                    LitInt(0) <= j#3 && j#3 < read($Heap, n#21, _module.Node.childrenVisited)
                     ==> $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref == null
                       || read($Heap,
                        $Unbox(Seq#Index(read($Heap, n#21, _module.Node.children), j#3)): ref,
                        _module.Node.marked)))
           ==>
          $IsAlloc(path#0, Tclass._module.Path(), old($Heap))
           ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0)
             && (_module.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0)
               ==> (forall n#25: ref ::
                  { _module.__default.ReachableVia($LS($LZ),
                      old($Heap),
                      root#0,
                      read(old($Heap), n#25, _module.Node.pathFromRoot),
                      n#25,
                      S#0) }
                    { read($Heap, n#25, _module.Node.pathFromRoot) }
                    { read($Heap, n#25, _module.Node.marked) }
                    { S#0[$Box(n#25)] }
                  $Is(n#25, Tclass._module.Node())
                     ==>
                    S#0[$Box(n#25)]
                     ==>
                    read($Heap, n#25, _module.Node.marked)
                     ==> (var pth#0 := read($Heap, n#25, _module.Node.pathFromRoot);
                      $IsAlloc(pth#0, Tclass._module.Path(), old($Heap))
                         ==> _module.__default.ReachableVia#canCall(old($Heap), root#0, pth#0, n#25, S#0)))
                 && ((forall n#25: ref ::
                    { _module.__default.ReachableVia($LS($LZ),
                        old($Heap),
                        root#0,
                        read(old($Heap), n#25, _module.Node.pathFromRoot),
                        n#25,
                        S#0) }
                      { read($Heap, n#25, _module.Node.pathFromRoot) }
                      { read($Heap, n#25, _module.Node.marked) }
                      { S#0[$Box(n#25)] }
                    $Is(n#25, Tclass._module.Node())
                       ==>
                      S#0[$Box(n#25)] && read($Heap, n#25, _module.Node.marked)
                       ==> (var pth#0 := read($Heap, n#25, _module.Node.pathFromRoot);
                        $IsAlloc(pth#0, Tclass._module.Path(), old($Heap))
                           && _module.__default.ReachableVia($LS($LZ), old($Heap), root#0, pth#0, n#25, S#0)))
                   ==> (forall n#27: ref ::
                    { _module.__default.Reachable(old($Heap), root#0, n#27, S#0) }
                      { read($Heap, n#27, _module.Node.marked) }
                      { S#0[$Box(n#27)] }
                    $Is(n#27, Tclass._module.Node())
                       ==>
                      S#0[$Box(n#27)]
                       ==>
                      read($Heap, n#27, _module.Node.marked)
                       ==> _module.__default.Reachable#canCall(old($Heap), root#0, n#27, S#0))));
    }
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

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$Path: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$children: NameFamily;

const unique field$marked: NameFamily;

const unique field$childrenVisited: NameFamily;

const unique field$pathFromRoot: NameFamily;
