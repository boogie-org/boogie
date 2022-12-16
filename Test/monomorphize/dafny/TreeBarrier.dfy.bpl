// Dafny 3.7.3.40719
// Command Line Options: /compile:0 /print:TreeBarrier.dfy.bpl

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

axiom FDim(_module.Node.left) == 0
   && FieldOfDecl(class._module.Node?, field$left) == _module.Node.left
   && !$IsGhostField(_module.Node.left);

const _module.Node.left: Field ref;

// Node.left: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.left) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.left), Tclass._module.Node?()));

// Node.left: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.left) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.left), Tclass._module.Node?(), $h));

axiom FDim(_module.Node.right) == 0
   && FieldOfDecl(class._module.Node?, field$right) == _module.Node.right
   && !$IsGhostField(_module.Node.right);

const _module.Node.right: Field ref;

// Node.right: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.right) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.right), Tclass._module.Node?()));

// Node.right: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.right) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.right), Tclass._module.Node?(), $h));

axiom FDim(_module.Node.parent) == 0
   && FieldOfDecl(class._module.Node?, field$parent) == _module.Node.parent
   && !$IsGhostField(_module.Node.parent);

const _module.Node.parent: Field ref;

// Node.parent: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.parent) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.parent), Tclass._module.Node?()));

// Node.parent: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.parent) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.parent), Tclass._module.Node?(), $h));

axiom FDim(_module.Node.anc) == 0
   && FieldOfDecl(class._module.Node?, field$anc) == _module.Node.anc
   && !$IsGhostField(_module.Node.anc);

const _module.Node.anc: Field (Set Box);

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

// Node.anc: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.anc) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.anc), TSet(Tclass._module.Node())));

// Node.anc: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.anc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.anc), TSet(Tclass._module.Node()), $h));

axiom FDim(_module.Node.desc) == 0
   && FieldOfDecl(class._module.Node?, field$desc) == _module.Node.desc
   && !$IsGhostField(_module.Node.desc);

const _module.Node.desc: Field (Set Box);

// Node.desc: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.desc) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.desc), TSet(Tclass._module.Node())));

// Node.desc: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.desc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.desc), TSet(Tclass._module.Node()), $h));

axiom FDim(_module.Node.sense) == 0
   && FieldOfDecl(class._module.Node?, field$sense) == _module.Node.sense
   && !$IsGhostField(_module.Node.sense);

const _module.Node.sense: Field bool;

// Node.sense: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.sense) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.sense), TBool));

// Node.sense: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.sense) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.sense), TBool, $h));

axiom FDim(_module.Node.pc) == 0
   && FieldOfDecl(class._module.Node?, field$pc) == _module.Node.pc
   && !$IsGhostField(_module.Node.pc);

const _module.Node.pc: Field int;

// Node.pc: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.pc) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.pc), TInt));

// Node.pc: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.pc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.pc), TInt, $h));

// function declaration for _module.Node.validDown
function _module.Node.validDown($ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.Node.validDown#canCall($heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.validDown($LS($ly), $Heap, this) } 
  _module.Node.validDown($LS($ly), $Heap, this)
     == _module.Node.validDown($ly, $Heap, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.validDown(AsFuelBottom($ly), $Heap, this) } 
  _module.Node.validDown($ly, $Heap, this)
     == _module.Node.validDown($LZ, $Heap, this));

// frame axiom for _module.Node.validDown
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.validDown($ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.Node.desc)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.validDown($ly, $h0, this) == _module.Node.validDown($ly, $h1, this));

// consequence axiom for _module.Node.validDown
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.validDown($ly, $Heap, this) } 
    _module.Node.validDown#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.validDown#requires(LayerType, Heap, ref) : bool;

// #requires axiom for _module.Node.validDown
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.validDown#requires($ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.validDown#requires($ly, $Heap, this) == true);

// definition axiom for _module.Node.validDown (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.validDown($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.validDown#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> (!read($Heap, this, _module.Node.desc)[$Box(this)]
           ==> 
          read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           ==> 
          (read($Heap, this, _module.Node.right) != null
           ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
             && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
           ==> (read($Heap, this, _module.Node.left) != null
               ==> 
              read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
               ==> 
              (read($Heap, this, _module.Node.right) != null
               ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                      $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               ==> 
              (read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
               ==> _module.Node.validDown#canCall($Heap, read($Heap, this, _module.Node.left)))
             && (
              (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                 && (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                          $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
                 && _module.Node.validDown($ly, $Heap, read($Heap, this, _module.Node.left)))
               ==> 
              (read($Heap, this, _module.Node.left) == null
               ==> (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
               ==> (read($Heap, this, _module.Node.right) != null
                   ==> _module.Node.validDown#canCall($Heap, read($Heap, this, _module.Node.right)))
                 && (
                  (read($Heap, this, _module.Node.right) != null
                   ==> _module.Node.validDown($ly, $Heap, read($Heap, this, _module.Node.right)))
                   ==> _module.Node.blocked#canCall($Heap, this)
                     && (_module.Node.blocked($Heap, this)
                       ==> (forall m#0: ref :: 
                        { _module.Node.blocked($Heap, m#0) } 
                          { read($Heap, this, _module.Node.desc)[$Box(m#0)] } 
                        $Is(m#0, Tclass._module.Node())
                           ==> 
                          read($Heap, this, _module.Node.desc)[$Box(m#0)]
                           ==> _module.Node.blocked#canCall($Heap, m#0)))
                     && (
                      (_module.Node.blocked($Heap, this)
                       ==> (forall m#0: ref :: 
                        { _module.Node.blocked($Heap, m#0) } 
                          { read($Heap, this, _module.Node.desc)[$Box(m#0)] } 
                        $Is(m#0, Tclass._module.Node())
                           ==> 
                          read($Heap, this, _module.Node.desc)[$Box(m#0)]
                           ==> _module.Node.blocked($Heap, m#0)))
                       ==> _module.Node.after#canCall($Heap, this)
                         && (_module.Node.after($Heap, this)
                           ==> (forall m#1: ref :: 
                            { _module.Node.after($Heap, m#1) } 
                              { _module.Node.blocked($Heap, m#1) } 
                              { read($Heap, this, _module.Node.desc)[$Box(m#1)] } 
                            $Is(m#1, Tclass._module.Node())
                               ==> 
                              read($Heap, this, _module.Node.desc)[$Box(m#1)]
                               ==> _module.Node.blocked#canCall($Heap, m#1)
                                 && (!_module.Node.blocked($Heap, m#1) ==> _module.Node.after#canCall($Heap, m#1))))))))
         && _module.Node.validDown($LS($ly), $Heap, this)
           == (
            !read($Heap, this, _module.Node.desc)[$Box(this)]
             && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
             && (read($Heap, this, _module.Node.right) != null
               ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
                 && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
             && (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                 && (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                          $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
                 && _module.Node.validDown($ly, $Heap, read($Heap, this, _module.Node.left)))
             && (read($Heap, this, _module.Node.left) == null
               ==> (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
             && (read($Heap, this, _module.Node.right) != null
               ==> _module.Node.validDown($ly, $Heap, read($Heap, this, _module.Node.right)))
             && (_module.Node.blocked($Heap, this)
               ==> (forall m#0: ref :: 
                { _module.Node.blocked($Heap, m#0) } 
                  { read($Heap, this, _module.Node.desc)[$Box(m#0)] } 
                $Is(m#0, Tclass._module.Node())
                   ==> 
                  read($Heap, this, _module.Node.desc)[$Box(m#0)]
                   ==> _module.Node.blocked($Heap, m#0)))
             && (_module.Node.after($Heap, this)
               ==> (forall m#1: ref :: 
                { _module.Node.after($Heap, m#1) } 
                  { _module.Node.blocked($Heap, m#1) } 
                  { read($Heap, this, _module.Node.desc)[$Box(m#1)] } 
                $Is(m#1, Tclass._module.Node())
                   ==> 
                  read($Heap, this, _module.Node.desc)[$Box(m#1)]
                   ==> _module.Node.blocked($Heap, m#1) || _module.Node.after($Heap, m#1)))));

procedure {:verboseName "Node.validDown (well-formedness)"} CheckWellformed$$_module.Node.validDown(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Node.validDown (well-formedness)"} CheckWellformed$$_module.Node.validDown(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var newtype$check#0: ref;
  var newtype$check#1: ref;
  var newtype$check#2: ref;
  var newtype$check#3: ref;
  var newtype$check#4: ref;
  var newtype$check#5: ref;
  var newtype$check#6: ref;
  var newtype$check#7: ref;
  var m#2: ref;
  var m#3: ref;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
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
  var b$reqreads#29: bool;
  var b$reqreads#30: bool;
  var b$reqreads#31: bool;
  var b$reqreads#32: bool;
  var b$reqreads#33: bool;
  var b$reqreads#34: bool;
  var b$reqreads#35: bool;
  var b$reqreads#36: bool;
  var b$reqreads#37: bool;
  var b$reqreads#38: bool;
  var b$reqreads#39: bool;
  var b$reqreads#40: bool;
  var b$reqreads#41: bool;
  var b$reqreads#42: bool;
  var b$reqreads#43: bool;
  var b$reqreads#44: bool;
  var b$reqreads#45: bool;

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
    b$reqreads#29 := true;
    b$reqreads#30 := true;
    b$reqreads#31 := true;
    b$reqreads#32 := true;
    b$reqreads#33 := true;
    b$reqreads#34 := true;
    b$reqreads#35 := true;
    b$reqreads#36 := true;
    b$reqreads#37 := true;
    b$reqreads#38 := true;
    b$reqreads#39 := true;
    b$reqreads#40 := true;
    b$reqreads#41 := true;
    b$reqreads#42 := true;
    b$reqreads#43 := true;
    b$reqreads#44 := true;
    b$reqreads#45 := true;

    // AddWellformednessCheck for function validDown
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Node.desc)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Node.desc];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Node.desc)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Node.desc];
        if (!read($Heap, this, _module.Node.desc)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Node.left];
            b$reqreads#3 := $_Frame[this, _module.Node.right];
        }

        if (!read($Heap, this, _module.Node.desc)[$Box(this)]
           && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right))
        {
            b$reqreads#4 := $_Frame[this, _module.Node.right];
            newtype$check#0 := null;
            if (read($Heap, this, _module.Node.right) != null)
            {
                b$reqreads#5 := $_Frame[this, _module.Node.right];
                b$reqreads#6 := $_Frame[this, _module.Node.desc];
                if (read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))])
                {
                    b$reqreads#7 := $_Frame[this, _module.Node.left];
                    b$reqreads#8 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    b$reqreads#9 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.desc];
                }
            }
        }

        if (!read($Heap, this, _module.Node.desc)[$Box(this)]
           && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]))
        {
            b$reqreads#10 := $_Frame[this, _module.Node.left];
            newtype$check#1 := null;
            if (read($Heap, this, _module.Node.left) != null)
            {
                b$reqreads#11 := $_Frame[this, _module.Node.left];
                b$reqreads#12 := $_Frame[this, _module.Node.desc];
                if (read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
                {
                    b$reqreads#13 := $_Frame[this, _module.Node.right];
                    newtype$check#2 := null;
                    if (read($Heap, this, _module.Node.right) != null)
                    {
                        b$reqreads#14 := $_Frame[this, _module.Node.desc];
                        b$reqreads#15 := $_Frame[this, _module.Node.left];
                        b$reqreads#16 := $_Frame[this, _module.Node.right];
                        b$reqreads#17 := $_Frame[this, _module.Node.left];
                        assert read($Heap, this, _module.Node.left) != null;
                        b$reqreads#18 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.desc];
                        b$reqreads#19 := $_Frame[this, _module.Node.right];
                        assert read($Heap, this, _module.Node.right) != null;
                        b$reqreads#20 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.desc];
                    }
                }

                if (read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                   && (read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                            $Box(read($Heap, this, _module.Node.right))), 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))))
                {
                    b$reqreads#21 := $_Frame[this, _module.Node.right];
                    newtype$check#3 := null;
                    if (read($Heap, this, _module.Node.right) == null)
                    {
                        b$reqreads#22 := $_Frame[this, _module.Node.desc];
                        b$reqreads#23 := $_Frame[this, _module.Node.left];
                        b$reqreads#24 := $_Frame[this, _module.Node.left];
                        assert read($Heap, this, _module.Node.left) != null;
                        b$reqreads#25 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.desc];
                    }
                }

                if (read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                   && (read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                            $Box(read($Heap, this, _module.Node.right))), 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                   && (read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)))))
                {
                    b$reqreads#26 := $_Frame[this, _module.Node.left];
                    assert read($Heap, this, _module.Node.left) != null;
                    // assume allocatedness for receiver argument to function
                    assume $IsAlloc(read($Heap, this, _module.Node.left), Tclass._module.Node?(), $Heap);
                    b$reqreads#27 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.Node.left)
                             || read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left)))), 
                        Set#Union(read($Heap, this, _module.Node.desc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.Node.desc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left)))));
                    assume _module.Node.validDown#canCall($Heap, read($Heap, this, _module.Node.left));
                }
            }
        }

        if (!read($Heap, this, _module.Node.desc)[$Box(this)]
           && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
               && (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
               && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left))))
        {
            b$reqreads#28 := $_Frame[this, _module.Node.left];
            newtype$check#4 := null;
            if (read($Heap, this, _module.Node.left) == null)
            {
                b$reqreads#29 := $_Frame[this, _module.Node.right];
                newtype$check#5 := null;
                if (read($Heap, this, _module.Node.right) != null)
                {
                    b$reqreads#30 := $_Frame[this, _module.Node.desc];
                    b$reqreads#31 := $_Frame[this, _module.Node.right];
                    b$reqreads#32 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    b$reqreads#33 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.desc];
                }

                if (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                {
                    b$reqreads#34 := $_Frame[this, _module.Node.right];
                    newtype$check#6 := null;
                    if (read($Heap, this, _module.Node.right) == null)
                    {
                        b$reqreads#35 := $_Frame[this, _module.Node.desc];
                    }
                }
            }
        }

        if (!read($Heap, this, _module.Node.desc)[$Box(this)]
           && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
               && (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
               && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
           && (read($Heap, this, _module.Node.left) == null
             ==> (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box))))
        {
            b$reqreads#36 := $_Frame[this, _module.Node.right];
            newtype$check#7 := null;
            if (read($Heap, this, _module.Node.right) != null)
            {
                b$reqreads#37 := $_Frame[this, _module.Node.right];
                assert read($Heap, this, _module.Node.right) != null;
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(read($Heap, this, _module.Node.right), Tclass._module.Node?(), $Heap);
                b$reqreads#38 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && ($o == read($Heap, this, _module.Node.right)
                         || read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box($o)])
                     ==> $_Frame[$o, $f]);
                assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right)))), 
                    Set#Union(read($Heap, this, _module.Node.desc), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                   && !Set#Subset(Set#Union(read($Heap, this, _module.Node.desc), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                    Set#Union(read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right)))));
                assume _module.Node.validDown#canCall($Heap, read($Heap, this, _module.Node.right));
            }
        }

        if (!read($Heap, this, _module.Node.desc)[$Box(this)]
           && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
               && (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
               && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
           && (read($Heap, this, _module.Node.left) == null
             ==> (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
           && (read($Heap, this, _module.Node.right) != null
             ==> _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.right))))
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
            b$reqreads#39 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
            assume _module.Node.blocked#canCall($Heap, this);
            if (_module.Node.blocked($Heap, this))
            {
                // Begin Comprehension WF check
                havoc m#2;
                if ($Is(m#2, Tclass._module.Node()) && $IsAlloc(m#2, Tclass._module.Node(), $Heap))
                {
                    b$reqreads#40 := $_Frame[this, _module.Node.desc];
                    if (read($Heap, this, _module.Node.desc)[$Box(m#2)])
                    {
                        assert m#2 != null;
                        // assume allocatedness for receiver argument to function
                        assume $IsAlloc(m#2, Tclass._module.Node?(), $Heap);
                        b$reqreads#41 := (forall<alpha> $o: ref, $f: Field alpha :: 
                          $o != null && read($Heap, $o, alloc) && $o == m#2 ==> $_Frame[$o, $f]);
                        assume _module.Node.blocked#canCall($Heap, m#2);
                    }
                }

                // End Comprehension WF check
            }
        }

        if (!read($Heap, this, _module.Node.desc)[$Box(this)]
           && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
               && (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
               && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
           && (read($Heap, this, _module.Node.left) == null
             ==> (read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               && (read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
           && (read($Heap, this, _module.Node.right) != null
             ==> _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.right)))
           && (_module.Node.blocked($Heap, this)
             ==> (forall m#4: ref :: 
              { _module.Node.blocked($Heap, m#4) } 
                { read($Heap, this, _module.Node.desc)[$Box(m#4)] } 
              $Is(m#4, Tclass._module.Node())
                 ==> 
                read($Heap, this, _module.Node.desc)[$Box(m#4)]
                 ==> _module.Node.blocked($Heap, m#4))))
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
            b$reqreads#42 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
            assume _module.Node.after#canCall($Heap, this);
            if (_module.Node.after($Heap, this))
            {
                // Begin Comprehension WF check
                havoc m#3;
                if ($Is(m#3, Tclass._module.Node()) && $IsAlloc(m#3, Tclass._module.Node(), $Heap))
                {
                    b$reqreads#43 := $_Frame[this, _module.Node.desc];
                    if (read($Heap, this, _module.Node.desc)[$Box(m#3)])
                    {
                        assert m#3 != null;
                        // assume allocatedness for receiver argument to function
                        assume $IsAlloc(m#3, Tclass._module.Node?(), $Heap);
                        b$reqreads#44 := (forall<alpha> $o: ref, $f: Field alpha :: 
                          $o != null && read($Heap, $o, alloc) && $o == m#3 ==> $_Frame[$o, $f]);
                        assume _module.Node.blocked#canCall($Heap, m#3);
                        if (!_module.Node.blocked($Heap, m#3))
                        {
                            assert m#3 != null;
                            // assume allocatedness for receiver argument to function
                            assume $IsAlloc(m#3, Tclass._module.Node?(), $Heap);
                            b$reqreads#45 := (forall<alpha> $o: ref, $f: Field alpha :: 
                              $o != null && read($Heap, $o, alloc) && $o == m#3 ==> $_Frame[$o, $f]);
                            assume _module.Node.after#canCall($Heap, m#3);
                        }
                    }
                }

                // End Comprehension WF check
            }
        }

        assume _module.Node.validDown($LS($LZ), $Heap, this)
           == (
            !read($Heap, this, _module.Node.desc)[$Box(this)]
             && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
             && (read($Heap, this, _module.Node.right) != null
               ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
                 && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
             && (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                 && (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                          $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
                 && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
             && (read($Heap, this, _module.Node.left) == null
               ==> (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
             && (read($Heap, this, _module.Node.right) != null
               ==> _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.right)))
             && (_module.Node.blocked($Heap, this)
               ==> (forall m#4: ref :: 
                { _module.Node.blocked($Heap, m#4) } 
                  { read($Heap, this, _module.Node.desc)[$Box(m#4)] } 
                $Is(m#4, Tclass._module.Node())
                   ==> 
                  read($Heap, this, _module.Node.desc)[$Box(m#4)]
                   ==> _module.Node.blocked($Heap, m#4)))
             && (_module.Node.after($Heap, this)
               ==> (forall m#5: ref :: 
                { _module.Node.after($Heap, m#5) } 
                  { _module.Node.blocked($Heap, m#5) } 
                  { read($Heap, this, _module.Node.desc)[$Box(m#5)] } 
                $Is(m#5, Tclass._module.Node())
                   ==> 
                  read($Heap, this, _module.Node.desc)[$Box(m#5)]
                   ==> _module.Node.blocked($Heap, m#5) || _module.Node.after($Heap, m#5))));
        assume !read($Heap, this, _module.Node.desc)[$Box(this)]
           ==> 
          read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
           ==> 
          (read($Heap, this, _module.Node.right) != null
           ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
             && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
           ==> (read($Heap, this, _module.Node.left) != null
               ==> 
              read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
               ==> 
              (read($Heap, this, _module.Node.right) != null
               ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                      $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
               ==> 
              (read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
               ==> _module.Node.validDown#canCall($Heap, read($Heap, this, _module.Node.left)))
             && (
              (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                 && (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                          $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
                 && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
               ==> 
              (read($Heap, this, _module.Node.left) == null
               ==> (read($Heap, this, _module.Node.right) != null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                 && (read($Heap, this, _module.Node.right) == null
                   ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
               ==> (read($Heap, this, _module.Node.right) != null
                   ==> _module.Node.validDown#canCall($Heap, read($Heap, this, _module.Node.right)))
                 && (
                  (read($Heap, this, _module.Node.right) != null
                   ==> _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.right)))
                   ==> _module.Node.blocked#canCall($Heap, this)
                     && (_module.Node.blocked($Heap, this)
                       ==> (forall m#4: ref :: 
                        { _module.Node.blocked($Heap, m#4) } 
                          { read($Heap, this, _module.Node.desc)[$Box(m#4)] } 
                        $Is(m#4, Tclass._module.Node())
                           ==> 
                          read($Heap, this, _module.Node.desc)[$Box(m#4)]
                           ==> _module.Node.blocked#canCall($Heap, m#4)))
                     && (
                      (_module.Node.blocked($Heap, this)
                       ==> (forall m#4: ref :: 
                        { _module.Node.blocked($Heap, m#4) } 
                          { read($Heap, this, _module.Node.desc)[$Box(m#4)] } 
                        $Is(m#4, Tclass._module.Node())
                           ==> 
                          read($Heap, this, _module.Node.desc)[$Box(m#4)]
                           ==> _module.Node.blocked($Heap, m#4)))
                       ==> _module.Node.after#canCall($Heap, this)
                         && (_module.Node.after($Heap, this)
                           ==> (forall m#5: ref :: 
                            { _module.Node.after($Heap, m#5) } 
                              { _module.Node.blocked($Heap, m#5) } 
                              { read($Heap, this, _module.Node.desc)[$Box(m#5)] } 
                            $Is(m#5, Tclass._module.Node())
                               ==> 
                              read($Heap, this, _module.Node.desc)[$Box(m#5)]
                               ==> _module.Node.blocked#canCall($Heap, m#5)
                                 && (!_module.Node.blocked($Heap, m#5) ==> _module.Node.after#canCall($Heap, m#5)))))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.validDown($LS($LZ), $Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
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
        assert b$reqreads#29;
        assert b$reqreads#30;
        assert b$reqreads#31;
        assert b$reqreads#32;
        assert b$reqreads#33;
        assert b$reqreads#34;
        assert b$reqreads#35;
        assert b$reqreads#36;
        assert b$reqreads#37;
        assert b$reqreads#38;
        assert b$reqreads#39;
        assert b$reqreads#40;
        assert b$reqreads#41;
        assert b$reqreads#42;
        assert b$reqreads#43;
        assert b$reqreads#44;
        assert b$reqreads#45;
    }
}



// function declaration for _module.Node.validUp
function _module.Node.validUp($ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.Node.validUp#canCall($heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.validUp($LS($ly), $Heap, this) } 
  _module.Node.validUp($LS($ly), $Heap, this)
     == _module.Node.validUp($ly, $Heap, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.validUp(AsFuelBottom($ly), $Heap, this) } 
  _module.Node.validUp($ly, $Heap, this) == _module.Node.validUp($LZ, $Heap, this));

// frame axiom for _module.Node.validUp
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.validUp($ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.Node.anc)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.validUp($ly, $h0, this) == _module.Node.validUp($ly, $h1, this));

// consequence axiom for _module.Node.validUp
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.validUp($ly, $Heap, this) } 
    _module.Node.validUp#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.validUp#requires(LayerType, Heap, ref) : bool;

// #requires axiom for _module.Node.validUp
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.validUp#requires($ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.validUp#requires($ly, $Heap, this) == true);

// definition axiom for _module.Node.validUp (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.validUp($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.validUp#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> (!read($Heap, this, _module.Node.anc)[$Box(this)]
           ==> (read($Heap, this, _module.Node.parent) != null
               ==> 
              read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
               ==> 
              Set#Equal(read($Heap, this, _module.Node.anc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                  read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
               ==> _module.Node.validUp#canCall($Heap, read($Heap, this, _module.Node.parent)))
             && (
              (read($Heap, this, _module.Node.parent) != null
               ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
                 && Set#Equal(read($Heap, this, _module.Node.anc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                    read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
                 && _module.Node.validUp($ly, $Heap, read($Heap, this, _module.Node.parent)))
               ==> 
              (read($Heap, this, _module.Node.parent) == null
               ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box))
               ==> _module.Node.after#canCall($Heap, this)
                 && (_module.Node.after($Heap, this)
                   ==> (forall m#0: ref :: 
                    { _module.Node.after($Heap, m#0) } 
                      { read($Heap, this, _module.Node.anc)[$Box(m#0)] } 
                    $Is(m#0, Tclass._module.Node())
                       ==> 
                      read($Heap, this, _module.Node.anc)[$Box(m#0)]
                       ==> _module.Node.after#canCall($Heap, m#0)))))
         && _module.Node.validUp($LS($ly), $Heap, this)
           == (
            !read($Heap, this, _module.Node.anc)[$Box(this)]
             && (read($Heap, this, _module.Node.parent) != null
               ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
                 && Set#Equal(read($Heap, this, _module.Node.anc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                    read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
                 && _module.Node.validUp($ly, $Heap, read($Heap, this, _module.Node.parent)))
             && (read($Heap, this, _module.Node.parent) == null
               ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box))
             && (_module.Node.after($Heap, this)
               ==> (forall m#0: ref :: 
                { _module.Node.after($Heap, m#0) } 
                  { read($Heap, this, _module.Node.anc)[$Box(m#0)] } 
                $Is(m#0, Tclass._module.Node())
                   ==> 
                  read($Heap, this, _module.Node.anc)[$Box(m#0)]
                   ==> _module.Node.after($Heap, m#0)))));

procedure {:verboseName "Node.validUp (well-formedness)"} CheckWellformed$$_module.Node.validUp(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Node.validUp (well-formedness)"} CheckWellformed$$_module.Node.validUp(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var newtype$check#0: ref;
  var newtype$check#1: ref;
  var m#1: ref;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
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

    // AddWellformednessCheck for function validUp
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Node.anc)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Node.anc];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Node.anc)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Node.anc];
        if (!read($Heap, this, _module.Node.anc)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Node.parent];
            newtype$check#0 := null;
            if (read($Heap, this, _module.Node.parent) != null)
            {
                b$reqreads#3 := $_Frame[this, _module.Node.parent];
                b$reqreads#4 := $_Frame[this, _module.Node.anc];
                if (read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))])
                {
                    b$reqreads#5 := $_Frame[this, _module.Node.anc];
                    b$reqreads#6 := $_Frame[this, _module.Node.parent];
                    b$reqreads#7 := $_Frame[this, _module.Node.parent];
                    assert read($Heap, this, _module.Node.parent) != null;
                    b$reqreads#8 := $_Frame[read($Heap, this, _module.Node.parent), _module.Node.anc];
                }

                if (read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
                   && Set#Equal(read($Heap, this, _module.Node.anc), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                      read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc))))
                {
                    b$reqreads#9 := $_Frame[this, _module.Node.parent];
                    assert read($Heap, this, _module.Node.parent) != null;
                    // assume allocatedness for receiver argument to function
                    assume $IsAlloc(read($Heap, this, _module.Node.parent), Tclass._module.Node?(), $Heap);
                    b$reqreads#10 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.Node.parent)
                             || read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent)))), 
                        Set#Union(read($Heap, this, _module.Node.anc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.Node.anc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent)))));
                    assume _module.Node.validUp#canCall($Heap, read($Heap, this, _module.Node.parent));
                }
            }
        }

        if (!read($Heap, this, _module.Node.anc)[$Box(this)]
           && (read($Heap, this, _module.Node.parent) != null
             ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
               && Set#Equal(read($Heap, this, _module.Node.anc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                  read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
               && _module.Node.validUp($LS($LZ), $Heap, read($Heap, this, _module.Node.parent))))
        {
            b$reqreads#11 := $_Frame[this, _module.Node.parent];
            newtype$check#1 := null;
            if (read($Heap, this, _module.Node.parent) == null)
            {
                b$reqreads#12 := $_Frame[this, _module.Node.anc];
            }
        }

        if (!read($Heap, this, _module.Node.anc)[$Box(this)]
           && (read($Heap, this, _module.Node.parent) != null
             ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
               && Set#Equal(read($Heap, this, _module.Node.anc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                  read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
               && _module.Node.validUp($LS($LZ), $Heap, read($Heap, this, _module.Node.parent)))
           && (read($Heap, this, _module.Node.parent) == null
             ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box)))
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
            b$reqreads#13 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
            assume _module.Node.after#canCall($Heap, this);
            if (_module.Node.after($Heap, this))
            {
                // Begin Comprehension WF check
                havoc m#1;
                if ($Is(m#1, Tclass._module.Node()) && $IsAlloc(m#1, Tclass._module.Node(), $Heap))
                {
                    b$reqreads#14 := $_Frame[this, _module.Node.anc];
                    if (read($Heap, this, _module.Node.anc)[$Box(m#1)])
                    {
                        assert m#1 != null;
                        // assume allocatedness for receiver argument to function
                        assume $IsAlloc(m#1, Tclass._module.Node?(), $Heap);
                        b$reqreads#15 := (forall<alpha> $o: ref, $f: Field alpha :: 
                          $o != null && read($Heap, $o, alloc) && $o == m#1 ==> $_Frame[$o, $f]);
                        assume _module.Node.after#canCall($Heap, m#1);
                    }
                }

                // End Comprehension WF check
            }
        }

        assume _module.Node.validUp($LS($LZ), $Heap, this)
           == (
            !read($Heap, this, _module.Node.anc)[$Box(this)]
             && (read($Heap, this, _module.Node.parent) != null
               ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
                 && Set#Equal(read($Heap, this, _module.Node.anc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                    read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
                 && _module.Node.validUp($LS($LZ), $Heap, read($Heap, this, _module.Node.parent)))
             && (read($Heap, this, _module.Node.parent) == null
               ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box))
             && (_module.Node.after($Heap, this)
               ==> (forall m#2: ref :: 
                { _module.Node.after($Heap, m#2) } 
                  { read($Heap, this, _module.Node.anc)[$Box(m#2)] } 
                $Is(m#2, Tclass._module.Node())
                   ==> 
                  read($Heap, this, _module.Node.anc)[$Box(m#2)]
                   ==> _module.Node.after($Heap, m#2))));
        assume !read($Heap, this, _module.Node.anc)[$Box(this)]
           ==> (read($Heap, this, _module.Node.parent) != null
               ==> 
              read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
               ==> 
              Set#Equal(read($Heap, this, _module.Node.anc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                  read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
               ==> _module.Node.validUp#canCall($Heap, read($Heap, this, _module.Node.parent)))
             && (
              (read($Heap, this, _module.Node.parent) != null
               ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
                 && Set#Equal(read($Heap, this, _module.Node.anc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                    read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
                 && _module.Node.validUp($LS($LZ), $Heap, read($Heap, this, _module.Node.parent)))
               ==> 
              (read($Heap, this, _module.Node.parent) == null
               ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box))
               ==> _module.Node.after#canCall($Heap, this)
                 && (_module.Node.after($Heap, this)
                   ==> (forall m#2: ref :: 
                    { _module.Node.after($Heap, m#2) } 
                      { read($Heap, this, _module.Node.anc)[$Box(m#2)] } 
                    $Is(m#2, Tclass._module.Node())
                       ==> 
                      read($Heap, this, _module.Node.anc)[$Box(m#2)]
                       ==> _module.Node.after#canCall($Heap, m#2))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.validUp($LS($LZ), $Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
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
    }
}



// function declaration for _module.Node.valid
function _module.Node.valid($heap: Heap, this: ref) : bool;

function _module.Node.valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Node.valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || read($h0, this, _module.Node.desc)[$Box($o)]
             || read($h0, this, _module.Node.anc)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.valid($h0, this) == _module.Node.valid($h1, this));

// consequence axiom for _module.Node.valid
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.valid($Heap, this) } 
    _module.Node.valid#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Node.valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Node.valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.valid#requires($Heap, this) == true);

// definition axiom for _module.Node.valid (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.valid($Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.valid#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> _module.Node.validUp#canCall($Heap, this)
         && (_module.Node.validUp($LS($LZ), $Heap, this)
           ==> _module.Node.validDown#canCall($Heap, this))
         && _module.Node.valid($Heap, this)
           == (
            _module.Node.validUp($LS($LZ), $Heap, this)
             && _module.Node.validDown($LS($LZ), $Heap, this)
             && Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc))));

procedure {:verboseName "Node.valid (well-formedness)"} CheckWellformed$$_module.Node.valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Node.valid (well-formedness)"} CheckWellformed$$_module.Node.valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;

    // AddWellformednessCheck for function valid
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || read($Heap, this, _module.Node.desc)[$Box($o)]
           || read($Heap, this, _module.Node.anc)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Node.desc];
    b$reqreads#1 := $_Frame[this, _module.Node.anc];
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this
               || read($Heap, this, _module.Node.desc)[$Box($o)]
               || read($Heap, this, _module.Node.anc)[$Box($o)]);
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && ($o == this || read($Heap, this, _module.Node.anc)[$Box($o)])
             ==> $_Frame[$o, $f]);
        assume _module.Node.validUp#canCall($Heap, this);
        if (_module.Node.validUp($LS($LZ), $Heap, this))
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == this || read($Heap, this, _module.Node.desc)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.Node.validDown#canCall($Heap, this);
        }

        if (_module.Node.validUp($LS($LZ), $Heap, this)
           && _module.Node.validDown($LS($LZ), $Heap, this))
        {
            b$reqreads#4 := $_Frame[this, _module.Node.desc];
            b$reqreads#5 := $_Frame[this, _module.Node.anc];
        }

        assume _module.Node.valid($Heap, this)
           == (
            _module.Node.validUp($LS($LZ), $Heap, this)
             && _module.Node.validDown($LS($LZ), $Heap, this)
             && Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc)));
        assume _module.Node.validUp#canCall($Heap, this)
           && (_module.Node.validUp($LS($LZ), $Heap, this)
             ==> _module.Node.validDown#canCall($Heap, this));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.valid($Heap, this), TBool);
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
    }
}



// function declaration for _module.Node.before
function _module.Node.before($heap: Heap, this: ref) : bool;

function _module.Node.before#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Node.before
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.before($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.before($h0, this) == _module.Node.before($h1, this));

// consequence axiom for _module.Node.before
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.before($Heap, this) } 
    _module.Node.before#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.before#requires(Heap, ref) : bool;

// #requires axiom for _module.Node.before
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Node.before#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.before#requires($Heap, this) == true);

// definition axiom for _module.Node.before (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.before($Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.before#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> _module.Node.before($Heap, this)
         == (!read($Heap, this, _module.Node.sense)
           && read($Heap, this, _module.Node.pc) <= LitInt(2)));

procedure {:verboseName "Node.before (well-formedness)"} CheckWellformed$$_module.Node.before(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Node.before (well-formedness)"} CheckWellformed$$_module.Node.before(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function before
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.Node.sense];
        if (!read($Heap, this, _module.Node.sense))
        {
            b$reqreads#1 := $_Frame[this, _module.Node.pc];
        }

        assume _module.Node.before($Heap, this)
           == (!read($Heap, this, _module.Node.sense)
             && read($Heap, this, _module.Node.pc) <= LitInt(2));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.before($Heap, this), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module.Node.blocked
function _module.Node.blocked($heap: Heap, this: ref) : bool;

function _module.Node.blocked#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Node.blocked
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.blocked($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.blocked($h0, this) == _module.Node.blocked($h1, this));

// consequence axiom for _module.Node.blocked
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.blocked($Heap, this) } 
    _module.Node.blocked#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.blocked#requires(Heap, ref) : bool;

// #requires axiom for _module.Node.blocked
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Node.blocked#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.blocked#requires($Heap, this) == true);

// definition axiom for _module.Node.blocked (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.blocked($Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.blocked#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> _module.Node.blocked($Heap, this) == read($Heap, this, _module.Node.sense));

procedure {:verboseName "Node.blocked (well-formedness)"} CheckWellformed$$_module.Node.blocked(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Node.blocked (well-formedness)"} CheckWellformed$$_module.Node.blocked(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function blocked
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.Node.sense];
        assume _module.Node.blocked($Heap, this) == read($Heap, this, _module.Node.sense);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.blocked($Heap, this), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module.Node.after
function _module.Node.after($heap: Heap, this: ref) : bool;

function _module.Node.after#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Node.after
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.after($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.after($h0, this) == _module.Node.after($h1, this));

// consequence axiom for _module.Node.after
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.after($Heap, this) } 
    _module.Node.after#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.after#requires(Heap, ref) : bool;

// #requires axiom for _module.Node.after
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Node.after#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.after#requires($Heap, this) == true);

// definition axiom for _module.Node.after (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Node.after($Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.after#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> _module.Node.after($Heap, this)
         == (!read($Heap, this, _module.Node.sense)
           && LitInt(3) <= read($Heap, this, _module.Node.pc)));

procedure {:verboseName "Node.after (well-formedness)"} CheckWellformed$$_module.Node.after(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Node.after (well-formedness)"} CheckWellformed$$_module.Node.after(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function after
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.Node.sense];
        if (!read($Heap, this, _module.Node.sense))
        {
            b$reqreads#1 := $_Frame[this, _module.Node.pc];
        }

        assume _module.Node.after($Heap, this)
           == (!read($Heap, this, _module.Node.sense)
             && LitInt(3) <= read($Heap, this, _module.Node.pc));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.after($Heap, this), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:verboseName "Node.barrier (well-formedness)"} CheckWellFormed$$_module.Node.barrier(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Node.barrier (call)"} Call$$_module.Node.barrier(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || !read($Heap, this, _module.Node.anc)[$Box(this)]);
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) != null
             ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) != null
             ==> Set#Equal(read($Heap, this, _module.Node.anc), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) != null
             ==> _module.Node.validUp($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.parent))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) == null
             ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box)));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (_module.Node.after($Heap, this)
             ==> (forall m#0: ref :: 
              { _module.Node.after($Heap, m#0) } 
                { read($Heap, this, _module.Node.anc)[$Box(m#0)] } 
              $Is(m#0, Tclass._module.Node())
                 ==> 
                read($Heap, this, _module.Node.anc)[$Box(m#0)]
                 ==> _module.Node.after($Heap, m#0))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || !read($Heap, this, _module.Node.desc)[$Box(this)]);
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.right) != null
             ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.left) != null
             ==> 
            read($Heap, this, _module.Node.right) != null
             ==> Set#Equal(read($Heap, this, _module.Node.desc), 
              Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    $Box(read($Heap, this, _module.Node.right))), 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.left) != null
             ==> 
            read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.desc), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.left) != null
             ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.left) == null
             ==> 
            read($Heap, this, _module.Node.right) != null
             ==> Set#Equal(read($Heap, this, _module.Node.desc), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.left) == null
             ==> 
            read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.right) != null
             ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (_module.Node.blocked($Heap, this)
             ==> (forall m#1: ref :: 
              { _module.Node.blocked($Heap, m#1) } 
                { read($Heap, this, _module.Node.desc)[$Box(m#1)] } 
              $Is(m#1, Tclass._module.Node())
                 ==> 
                read($Heap, this, _module.Node.desc)[$Box(m#1)]
                 ==> _module.Node.blocked($Heap, m#1))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || (_module.Node.validDown#canCall($Heap, this)
         ==> _module.Node.validDown($LS($LZ), $Heap, this)
           || (_module.Node.after($Heap, this)
             ==> (forall m#2: ref :: 
              { _module.Node.after($Heap, m#2) } 
                { _module.Node.blocked($Heap, m#2) } 
                { read($Heap, this, _module.Node.desc)[$Box(m#2)] } 
              $Is(m#2, Tclass._module.Node())
                 ==> 
                read($Heap, this, _module.Node.desc)[$Box(m#2)]
                 ==> _module.Node.blocked($Heap, m#2) || _module.Node.after($Heap, m#2))));
  requires _module.Node.valid#canCall($Heap, this)
     ==> _module.Node.valid($Heap, this)
       || Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
  requires _module.Node.before#canCall($Heap, this)
     ==> _module.Node.before($Heap, this) || !read($Heap, this, _module.Node.sense);
  requires _module.Node.before#canCall($Heap, this)
     ==> _module.Node.before($Heap, this)
       || read($Heap, this, _module.Node.pc) <= LitInt(2);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || $o == read(old($Heap), this, _module.Node.left)
         || $o == read(old($Heap), this, _module.Node.right));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Node.barrier (correctness)"} Impl$$_module.Node.barrier(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Node.valid#canCall($Heap, this)
     && 
    _module.Node.valid($Heap, this)
     && 
    _module.Node.validUp($LS($LZ), $Heap, this)
     && _module.Node.validDown($LS($LZ), $Heap, this)
     && Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
  free requires _module.Node.before#canCall($Heap, this)
     && 
    _module.Node.before($Heap, this)
     && 
    !read($Heap, this, _module.Node.sense)
     && read($Heap, this, _module.Node.pc) <= LitInt(2);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || $o == read(old($Heap), this, _module.Node.left)
         || $o == read(old($Heap), this, _module.Node.right));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Node.barrier (correctness)"} Impl$$_module.Node.barrier(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var newtype$check#0: ref;
  var $PreLoopHeap$loop#0_0: Heap;
  var $Frame$loop#0_0: <beta>[ref,Field beta]bool;
  var $w$loop#0_0: bool;
  var $rhs#0_0_0: bool;
  var m#0_0_0: ref;
  var newtype$check#1: ref;
  var $PreLoopHeap$loop#1_0: Heap;
  var $Frame$loop#1_0: <beta>[ref,Field beta]bool;
  var $w$loop#1_0: bool;
  var $rhs#1_0_0: bool;
  var m#1_0_0: ref;
  var $rhs#1: int;
  var newtype$check#2: ref;
  var $rhs#2_0: bool;
  var $rhs#2: int;
  var $PreLoopHeap$loop#0: Heap;
  var $Frame$loop#0: <beta>[ref,Field beta]bool;
  var $w$loop#0: bool;
  var newtype$check#3: ref;
  var $rhs#3_0: bool;
  var $rhs#3: int;
  var newtype$check#4: ref;
  var $rhs#4_0: bool;
  var $rhs#4: int;
  var newtype$check#5: ref;
  var $rhs#5_0: bool;
  var $rhs#5: int;

    // AddMethodImpl: barrier, Impl$$_module.Node.barrier
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || $o == read($Heap, this, _module.Node.left)
           || $o == read($Heap, this, _module.Node.right));
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(74,8)
    assume true;
    assert $_Frame[this, _module.Node.pc];
    assume true;
    $rhs#0 := LitInt(1);
    $Heap := update($Heap, this, _module.Node.pc, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(75,5)
    newtype$check#0 := null;
    assume true;
    if (read($Heap, this, _module.Node.left) != null)
    {
        // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(76,7)
        // Assume Fuel Constant
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && $o == read($Heap, this, _module.Node.left)
             ==> $_Frame[$o, $f]);
        $Frame$loop#0_0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == read($Heap, this, _module.Node.left));
        $PreLoopHeap$loop#0_0 := $Heap;
        havoc $w$loop#0_0;
        while (true)
          free invariant $w$loop#0_0 ==> _module.Node.validDown#canCall($Heap, this);
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || !read($Heap, this, _module.Node.desc)[$Box(this)];
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right);
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]);
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]);
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]);
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> 
                read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> 
                read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left)));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) == null
                 ==> 
                read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) == null
                 ==> 
                read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right)));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (_module.Node.blocked($Heap, this)
                 ==> (forall m#0_0: ref :: 
                  { _module.Node.blocked($Heap, m#0_0) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#0_0)] } 
                  $Is(m#0_0, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#0_0)]
                     ==> _module.Node.blocked($Heap, m#0_0)));
          invariant $w$loop#0_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (_module.Node.after($Heap, this)
                 ==> (forall m#0_1: ref :: 
                  { _module.Node.after($Heap, m#0_1) } 
                    { _module.Node.blocked($Heap, m#0_1) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#0_1)] } 
                  $Is(m#0_1, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#0_1)]
                     ==> _module.Node.blocked($Heap, m#0_1) || _module.Node.after($Heap, m#0_1)));
          free invariant $w$loop#0_0
             ==> _module.Node.validDown#canCall($Heap, this)
               && 
              _module.Node.validDown($LS($LZ), $Heap, this)
               && 
              !read($Heap, this, _module.Node.desc)[$Box(this)]
               && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
               && (read($Heap, this, _module.Node.right) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
                   && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
               && (read($Heap, this, _module.Node.left) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                   && (read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                            $Box(read($Heap, this, _module.Node.right))), 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                   && (read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
                   && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
               && (read($Heap, this, _module.Node.left) == null
                 ==> (read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                   && (read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
               && (read($Heap, this, _module.Node.right) != null
                 ==> _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.right)))
               && (_module.Node.blocked($Heap, this)
                 ==> (forall m#0_0: ref :: 
                  { _module.Node.blocked($Heap, m#0_0) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#0_0)] } 
                  $Is(m#0_0, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#0_0)]
                     ==> _module.Node.blocked($Heap, m#0_0)))
               && (_module.Node.after($Heap, this)
                 ==> (forall m#0_1: ref :: 
                  { _module.Node.after($Heap, m#0_1) } 
                    { _module.Node.blocked($Heap, m#0_1) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#0_1)] } 
                  $Is(m#0_1, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#0_1)]
                     ==> _module.Node.blocked($Heap, m#0_1) || _module.Node.after($Heap, m#0_1)));
          free invariant $w$loop#0_0 ==> _module.Node.valid#canCall($Heap, this);
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || !read($Heap, this, _module.Node.anc)[$Box(this)]);
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) != null
                     ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.anc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                        read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) != null
                     ==> _module.Node.validUp($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.parent))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box)));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (_module.Node.after($Heap, this)
                     ==> (forall m#0_2: ref :: 
                      { _module.Node.after($Heap, m#0_2) } 
                        { read($Heap, this, _module.Node.anc)[$Box(m#0_2)] } 
                      $Is(m#0_2, Tclass._module.Node())
                         ==> 
                        read($Heap, this, _module.Node.anc)[$Box(m#0_2)]
                         ==> _module.Node.after($Heap, m#0_2))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || !read($Heap, this, _module.Node.desc)[$Box(this)]);
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.right) != null
                     ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.right) != null
                     ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> 
                    read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                            $Box(read($Heap, this, _module.Node.right))), 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> 
                    read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) == null
                     ==> 
                    read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) == null
                     ==> 
                    read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.right) != null
                     ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (_module.Node.blocked($Heap, this)
                     ==> (forall m#0_3: ref :: 
                      { _module.Node.blocked($Heap, m#0_3) } 
                        { read($Heap, this, _module.Node.desc)[$Box(m#0_3)] } 
                      $Is(m#0_3, Tclass._module.Node())
                         ==> 
                        read($Heap, this, _module.Node.desc)[$Box(m#0_3)]
                         ==> _module.Node.blocked($Heap, m#0_3))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (_module.Node.after($Heap, this)
                     ==> (forall m#0_4: ref :: 
                      { _module.Node.after($Heap, m#0_4) } 
                        { _module.Node.blocked($Heap, m#0_4) } 
                        { read($Heap, this, _module.Node.desc)[$Box(m#0_4)] } 
                      $Is(m#0_4, Tclass._module.Node())
                         ==> 
                        read($Heap, this, _module.Node.desc)[$Box(m#0_4)]
                         ==> _module.Node.blocked($Heap, m#0_4) || _module.Node.after($Heap, m#0_4))));
          invariant $w$loop#0_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
          free invariant $w$loop#0_0
             ==> _module.Node.valid#canCall($Heap, this)
               && 
              _module.Node.valid($Heap, this)
               && 
              _module.Node.validUp($LS($LZ), $Heap, this)
               && _module.Node.validDown($LS($LZ), $Heap, this)
               && Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
          free invariant (forall $o: ref :: 
            { $Heap[$o] } 
            $o != null && read(old($Heap), $o, alloc)
               ==> $Heap[$o] == $PreLoopHeap$loop#0_0[$o]
                 || 
                $o == this
                 || $o == read(old($Heap), this, _module.Node.left)
                 || $o == read(old($Heap), this, _module.Node.right));
          free invariant $HeapSucc($PreLoopHeap$loop#0_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
            { read($Heap, $o, $f) } 
            $o != null && read($PreLoopHeap$loop#0_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0_0, $o, $f)
                 || $Frame$loop#0_0[$o, $f]);
        {
            if (!$w$loop#0_0)
            {
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
                assume _module.Node.validDown#canCall($Heap, this);
                assume _module.Node.validDown#canCall($Heap, this);
                assume _module.Node.validDown($LS($LZ), $Heap, this);
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
                assume _module.Node.valid#canCall($Heap, this);
                assume _module.Node.valid#canCall($Heap, this);
                assume _module.Node.valid($Heap, this);
                assume true;
                assume false;
            }

            assert read($Heap, this, _module.Node.left) != null;
            assume true;
            if (read($Heap, read($Heap, this, _module.Node.left), _module.Node.sense))
            {
                break;
            }

            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(90,20)
            assert read($Heap, this, _module.Node.left) != null;
            assume true;
            assert $Frame$loop#0_0[read($Heap, this, _module.Node.left), _module.Node.sense];
            havoc $rhs#0_0_0;
            $Heap := update($Heap, read($Heap, this, _module.Node.left), _module.Node.sense, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            // ----- assume statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(91,9)
            assert {:subsumption 0} read($Heap, this, _module.Node.left) != null;
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(read($Heap, this, _module.Node.left), Tclass._module.Node?(), $Heap);
            assume _module.Node.blocked#canCall($Heap, read($Heap, this, _module.Node.left));
            if (_module.Node.blocked($Heap, read($Heap, this, _module.Node.left)))
            {
                // Begin Comprehension WF check
                havoc m#0_0_0;
                if ($Is(m#0_0_0, Tclass._module.Node())
                   && $IsAlloc(m#0_0_0, Tclass._module.Node(), $Heap))
                {
                    assert {:subsumption 0} read($Heap, this, _module.Node.left) != null;
                    if (read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)[$Box(m#0_0_0)])
                    {
                        assert {:subsumption 0} m#0_0_0 != null;
                        // assume allocatedness for receiver argument to function
                        assume $IsAlloc(m#0_0_0, Tclass._module.Node?(), $Heap);
                        assume _module.Node.blocked#canCall($Heap, m#0_0_0);
                    }
                }

                // End Comprehension WF check
            }

            assume _module.Node.blocked#canCall($Heap, read($Heap, this, _module.Node.left))
               && (_module.Node.blocked($Heap, read($Heap, this, _module.Node.left))
                 ==> (forall m#0_0_1: ref :: 
                  { _module.Node.blocked($Heap, m#0_0_1) } 
                    { read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)[$Box(m#0_0_1)] } 
                  $Is(m#0_0_1, Tclass._module.Node())
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)[$Box(m#0_0_1)]
                     ==> _module.Node.blocked#canCall($Heap, m#0_0_1)));
            assume _module.Node.blocked($Heap, read($Heap, this, _module.Node.left))
               ==> (forall m#0_0_1: ref :: 
                { _module.Node.blocked($Heap, m#0_0_1) } 
                  { read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)[$Box(m#0_0_1)] } 
                $Is(m#0_0_1, Tclass._module.Node())
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)[$Box(m#0_0_1)]
                   ==> _module.Node.blocked($Heap, m#0_0_1));
            assume _module.Node.validDown#canCall($Heap, this)
               && (_module.Node.validDown($LS($LZ), $Heap, this)
                 ==> _module.Node.valid#canCall($Heap, this));
        }
    }
    else
    {
    }

    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(94,5)
    newtype$check#1 := null;
    assume true;
    if (read($Heap, this, _module.Node.right) != null)
    {
        // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(95,7)
        // Assume Fuel Constant
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && $o == read($Heap, this, _module.Node.right)
             ==> $_Frame[$o, $f]);
        $Frame$loop#1_0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == read($Heap, this, _module.Node.right));
        $PreLoopHeap$loop#1_0 := $Heap;
        havoc $w$loop#1_0;
        while (true)
          free invariant $w$loop#1_0 ==> _module.Node.validDown#canCall($Heap, this);
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || !read($Heap, this, _module.Node.desc)[$Box(this)];
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right);
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]);
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]);
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]);
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> 
                read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> 
                read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left)));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) == null
                 ==> 
                read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) == null
                 ==> 
                read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right)));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (_module.Node.blocked($Heap, this)
                 ==> (forall m#1_0: ref :: 
                  { _module.Node.blocked($Heap, m#1_0) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#1_0)] } 
                  $Is(m#1_0, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#1_0)]
                     ==> _module.Node.blocked($Heap, m#1_0)));
          invariant $w$loop#1_0
             ==> 
            _module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (_module.Node.after($Heap, this)
                 ==> (forall m#1_1: ref :: 
                  { _module.Node.after($Heap, m#1_1) } 
                    { _module.Node.blocked($Heap, m#1_1) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#1_1)] } 
                  $Is(m#1_1, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#1_1)]
                     ==> _module.Node.blocked($Heap, m#1_1) || _module.Node.after($Heap, m#1_1)));
          free invariant $w$loop#1_0
             ==> _module.Node.validDown#canCall($Heap, this)
               && 
              _module.Node.validDown($LS($LZ), $Heap, this)
               && 
              !read($Heap, this, _module.Node.desc)[$Box(this)]
               && read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right)
               && (read($Heap, this, _module.Node.right) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]
                   && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))])
               && (read($Heap, this, _module.Node.left) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]
                   && (read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                            $Box(read($Heap, this, _module.Node.right))), 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                   && (read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc))))
                   && _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
               && (read($Heap, this, _module.Node.left) == null
                 ==> (read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc))))
                   && (read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)))
               && (read($Heap, this, _module.Node.right) != null
                 ==> _module.Node.validDown($LS($LZ), $Heap, read($Heap, this, _module.Node.right)))
               && (_module.Node.blocked($Heap, this)
                 ==> (forall m#1_0: ref :: 
                  { _module.Node.blocked($Heap, m#1_0) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#1_0)] } 
                  $Is(m#1_0, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#1_0)]
                     ==> _module.Node.blocked($Heap, m#1_0)))
               && (_module.Node.after($Heap, this)
                 ==> (forall m#1_1: ref :: 
                  { _module.Node.after($Heap, m#1_1) } 
                    { _module.Node.blocked($Heap, m#1_1) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#1_1)] } 
                  $Is(m#1_1, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#1_1)]
                     ==> _module.Node.blocked($Heap, m#1_1) || _module.Node.after($Heap, m#1_1)));
          free invariant $w$loop#1_0 ==> _module.Node.valid#canCall($Heap, this);
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || !read($Heap, this, _module.Node.anc)[$Box(this)]);
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) != null
                     ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.anc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                        read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) != null
                     ==> _module.Node.validUp($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.parent))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.parent) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box)));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validUp#canCall($Heap, this)
                 ==> _module.Node.validUp($LS($LZ), $Heap, this)
                   || (_module.Node.after($Heap, this)
                     ==> (forall m#1_2: ref :: 
                      { _module.Node.after($Heap, m#1_2) } 
                        { read($Heap, this, _module.Node.anc)[$Box(m#1_2)] } 
                      $Is(m#1_2, Tclass._module.Node())
                         ==> 
                        read($Heap, this, _module.Node.anc)[$Box(m#1_2)]
                         ==> _module.Node.after($Heap, m#1_2))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || !read($Heap, this, _module.Node.desc)[$Box(this)]);
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.right) != null
                     ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.right) != null
                     ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> 
                    read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                            $Box(read($Heap, this, _module.Node.right))), 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> 
                    read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) != null
                     ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) == null
                     ==> 
                    read($Heap, this, _module.Node.right) != null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.left) == null
                     ==> 
                    read($Heap, this, _module.Node.right) == null
                     ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (read($Heap, this, _module.Node.right) != null
                     ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (_module.Node.blocked($Heap, this)
                     ==> (forall m#1_3: ref :: 
                      { _module.Node.blocked($Heap, m#1_3) } 
                        { read($Heap, this, _module.Node.desc)[$Box(m#1_3)] } 
                      $Is(m#1_3, Tclass._module.Node())
                         ==> 
                        read($Heap, this, _module.Node.desc)[$Box(m#1_3)]
                         ==> _module.Node.blocked($Heap, m#1_3))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || (_module.Node.validDown#canCall($Heap, this)
                 ==> _module.Node.validDown($LS($LZ), $Heap, this)
                   || (_module.Node.after($Heap, this)
                     ==> (forall m#1_4: ref :: 
                      { _module.Node.after($Heap, m#1_4) } 
                        { _module.Node.blocked($Heap, m#1_4) } 
                        { read($Heap, this, _module.Node.desc)[$Box(m#1_4)] } 
                      $Is(m#1_4, Tclass._module.Node())
                         ==> 
                        read($Heap, this, _module.Node.desc)[$Box(m#1_4)]
                         ==> _module.Node.blocked($Heap, m#1_4) || _module.Node.after($Heap, m#1_4))));
          invariant $w$loop#1_0
             ==> 
            _module.Node.valid#canCall($Heap, this)
             ==> _module.Node.valid($Heap, this)
               || Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
          free invariant $w$loop#1_0
             ==> _module.Node.valid#canCall($Heap, this)
               && 
              _module.Node.valid($Heap, this)
               && 
              _module.Node.validUp($LS($LZ), $Heap, this)
               && _module.Node.validDown($LS($LZ), $Heap, this)
               && Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
          free invariant (forall $o: ref :: 
            { $Heap[$o] } 
            $o != null && read(old($Heap), $o, alloc)
               ==> $Heap[$o] == $PreLoopHeap$loop#1_0[$o]
                 || 
                $o == this
                 || $o == read(old($Heap), this, _module.Node.left)
                 || $o == read(old($Heap), this, _module.Node.right));
          free invariant $HeapSucc($PreLoopHeap$loop#1_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
            { read($Heap, $o, $f) } 
            $o != null && read($PreLoopHeap$loop#1_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1_0, $o, $f)
                 || $Frame$loop#1_0[$o, $f]);
        {
            if (!$w$loop#1_0)
            {
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
                assume _module.Node.validDown#canCall($Heap, this);
                assume _module.Node.validDown#canCall($Heap, this);
                assume _module.Node.validDown($LS($LZ), $Heap, this);
                // assume allocatedness for receiver argument to function
                assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
                assume _module.Node.valid#canCall($Heap, this);
                assume _module.Node.valid#canCall($Heap, this);
                assume _module.Node.valid($Heap, this);
                assume true;
                assume false;
            }

            assert read($Heap, this, _module.Node.right) != null;
            assume true;
            if (read($Heap, read($Heap, this, _module.Node.right), _module.Node.sense))
            {
                break;
            }

            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(102,21)
            assert read($Heap, this, _module.Node.right) != null;
            assume true;
            assert $Frame$loop#1_0[read($Heap, this, _module.Node.right), _module.Node.sense];
            havoc $rhs#1_0_0;
            $Heap := update($Heap, read($Heap, this, _module.Node.right), _module.Node.sense, $rhs#1_0_0);
            assume $IsGoodHeap($Heap);
            // ----- assume statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(103,9)
            assert {:subsumption 0} read($Heap, this, _module.Node.right) != null;
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(read($Heap, this, _module.Node.right), Tclass._module.Node?(), $Heap);
            assume _module.Node.blocked#canCall($Heap, read($Heap, this, _module.Node.right));
            if (_module.Node.blocked($Heap, read($Heap, this, _module.Node.right)))
            {
                // Begin Comprehension WF check
                havoc m#1_0_0;
                if ($Is(m#1_0_0, Tclass._module.Node())
                   && $IsAlloc(m#1_0_0, Tclass._module.Node(), $Heap))
                {
                    assert {:subsumption 0} read($Heap, this, _module.Node.right) != null;
                    if (read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(m#1_0_0)])
                    {
                        assert {:subsumption 0} m#1_0_0 != null;
                        // assume allocatedness for receiver argument to function
                        assume $IsAlloc(m#1_0_0, Tclass._module.Node?(), $Heap);
                        assume _module.Node.blocked#canCall($Heap, m#1_0_0);
                    }
                }

                // End Comprehension WF check
            }

            assume _module.Node.blocked#canCall($Heap, read($Heap, this, _module.Node.right))
               && (_module.Node.blocked($Heap, read($Heap, this, _module.Node.right))
                 ==> (forall m#1_0_1: ref :: 
                  { _module.Node.blocked($Heap, m#1_0_1) } 
                    { read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(m#1_0_1)] } 
                  $Is(m#1_0_1, Tclass._module.Node())
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(m#1_0_1)]
                     ==> _module.Node.blocked#canCall($Heap, m#1_0_1)));
            assume _module.Node.blocked($Heap, read($Heap, this, _module.Node.right))
               ==> (forall m#1_0_1: ref :: 
                { _module.Node.blocked($Heap, m#1_0_1) } 
                  { read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(m#1_0_1)] } 
                $Is(m#1_0_1, Tclass._module.Node())
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(m#1_0_1)]
                   ==> _module.Node.blocked($Heap, m#1_0_1));
            assume _module.Node.validDown#canCall($Heap, this)
               && (_module.Node.validDown($LS($LZ), $Heap, this)
                 ==> _module.Node.valid#canCall($Heap, this));
        }
    }
    else
    {
    }

    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(108,8)
    assume true;
    assert $_Frame[this, _module.Node.pc];
    assume true;
    $rhs#1 := LitInt(2);
    $Heap := update($Heap, this, _module.Node.pc, $rhs#1);
    assume $IsGoodHeap($Heap);
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(109,5)
    newtype$check#2 := null;
    assume true;
    if (read($Heap, this, _module.Node.parent) != null)
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(110,13)
        assume true;
        assert $_Frame[this, _module.Node.sense];
        assume true;
        $rhs#2_0 := Lit(true);
        $Heap := update($Heap, this, _module.Node.sense, $rhs#2_0);
        assume $IsGoodHeap($Heap);
    }
    else
    {
    }

    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(113,8)
    assume true;
    assert $_Frame[this, _module.Node.pc];
    assume true;
    $rhs#2 := LitInt(3);
    $Heap := update($Heap, this, _module.Node.pc, $rhs#2);
    assume $IsGoodHeap($Heap);
    // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(114,5)
    // Assume Fuel Constant
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
    $Frame$loop#0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.Node.validUp#canCall($Heap, this);
      invariant $w$loop#0
         ==> 
        _module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || !read($Heap, this, _module.Node.anc)[$Box(this)];
      invariant $w$loop#0
         ==> 
        _module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) != null
             ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]);
      invariant $w$loop#0
         ==> 
        _module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) != null
             ==> Set#Equal(read($Heap, this, _module.Node.anc), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc))));
      invariant $w$loop#0
         ==> 
        _module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) != null
             ==> _module.Node.validUp($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.parent)));
      invariant $w$loop#0
         ==> 
        _module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (read($Heap, this, _module.Node.parent) == null
             ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box));
      invariant $w$loop#0
         ==> 
        _module.Node.validUp#canCall($Heap, this)
         ==> _module.Node.validUp($LS($LZ), $Heap, this)
           || (_module.Node.after($Heap, this)
             ==> (forall m#6: ref :: 
              { _module.Node.after($Heap, m#6) } 
                { read($Heap, this, _module.Node.anc)[$Box(m#6)] } 
              $Is(m#6, Tclass._module.Node())
                 ==> 
                read($Heap, this, _module.Node.anc)[$Box(m#6)]
                 ==> _module.Node.after($Heap, m#6)));
      free invariant $w$loop#0
         ==> _module.Node.validUp#canCall($Heap, this)
           && 
          _module.Node.validUp($LS($LZ), $Heap, this)
           && 
          !read($Heap, this, _module.Node.anc)[$Box(this)]
           && (read($Heap, this, _module.Node.parent) != null
             ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]
               && Set#Equal(read($Heap, this, _module.Node.anc), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                  read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))
               && _module.Node.validUp($LS($LZ), $Heap, read($Heap, this, _module.Node.parent)))
           && (read($Heap, this, _module.Node.parent) == null
             ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box))
           && (_module.Node.after($Heap, this)
             ==> (forall m#6: ref :: 
              { _module.Node.after($Heap, m#6) } 
                { read($Heap, this, _module.Node.anc)[$Box(m#6)] } 
              $Is(m#6, Tclass._module.Node())
                 ==> 
                read($Heap, this, _module.Node.anc)[$Box(m#6)]
                 ==> _module.Node.after($Heap, m#6)));
      free invariant $w$loop#0 ==> _module.Node.valid#canCall($Heap, this);
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validUp#canCall($Heap, this)
             ==> _module.Node.validUp($LS($LZ), $Heap, this)
               || !read($Heap, this, _module.Node.anc)[$Box(this)]);
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validUp#canCall($Heap, this)
             ==> _module.Node.validUp($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.parent) != null
                 ==> read($Heap, this, _module.Node.anc)[$Box(read($Heap, this, _module.Node.parent))]));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validUp#canCall($Heap, this)
             ==> _module.Node.validUp($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.parent) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.anc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.parent))), 
                    read($Heap, read($Heap, this, _module.Node.parent), _module.Node.anc)))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validUp#canCall($Heap, this)
             ==> _module.Node.validUp($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.parent) != null
                 ==> _module.Node.validUp($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.parent))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validUp#canCall($Heap, this)
             ==> _module.Node.validUp($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.parent) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.anc), Set#Empty(): Set Box)));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validUp#canCall($Heap, this)
             ==> _module.Node.validUp($LS($LZ), $Heap, this)
               || (_module.Node.after($Heap, this)
                 ==> (forall m#7: ref :: 
                  { _module.Node.after($Heap, m#7) } 
                    { read($Heap, this, _module.Node.anc)[$Box(m#7)] } 
                  $Is(m#7, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.anc)[$Box(m#7)]
                     ==> _module.Node.after($Heap, m#7))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || !read($Heap, this, _module.Node.desc)[$Box(this)]);
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || read($Heap, this, _module.Node.left) != read($Heap, this, _module.Node.right));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.right))]));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> read($Heap, this, _module.Node.desc)[$Box(read($Heap, this, _module.Node.left))]));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> 
                read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#Union(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                        $Box(read($Heap, this, _module.Node.right))), 
                      read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> 
                read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left))), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.desc)))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) != null
                 ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) == null
                 ==> 
                read($Heap, this, _module.Node.right) != null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), 
                  Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.desc)))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.left) == null
                 ==> 
                read($Heap, this, _module.Node.right) == null
                 ==> Set#Equal(read($Heap, this, _module.Node.desc), Set#Empty(): Set Box)));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (read($Heap, this, _module.Node.right) != null
                 ==> _module.Node.validDown($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (_module.Node.blocked($Heap, this)
                 ==> (forall m#8: ref :: 
                  { _module.Node.blocked($Heap, m#8) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#8)] } 
                  $Is(m#8, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#8)]
                     ==> _module.Node.blocked($Heap, m#8))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || (_module.Node.validDown#canCall($Heap, this)
             ==> _module.Node.validDown($LS($LZ), $Heap, this)
               || (_module.Node.after($Heap, this)
                 ==> (forall m#9: ref :: 
                  { _module.Node.after($Heap, m#9) } 
                    { _module.Node.blocked($Heap, m#9) } 
                    { read($Heap, this, _module.Node.desc)[$Box(m#9)] } 
                  $Is(m#9, Tclass._module.Node())
                     ==> 
                    read($Heap, this, _module.Node.desc)[$Box(m#9)]
                     ==> _module.Node.blocked($Heap, m#9) || _module.Node.after($Heap, m#9))));
      invariant $w$loop#0
         ==> 
        _module.Node.valid#canCall($Heap, this)
         ==> _module.Node.valid($Heap, this)
           || Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
      free invariant $w$loop#0
         ==> _module.Node.valid#canCall($Heap, this)
           && 
          _module.Node.valid($Heap, this)
           && 
          _module.Node.validUp($LS($LZ), $Heap, this)
           && _module.Node.validDown($LS($LZ), $Heap, this)
           && Set#Disjoint(read($Heap, this, _module.Node.desc), read($Heap, this, _module.Node.anc));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> read($Heap, this, _module.Node.left)
           == read(old($Heap), this, _module.Node.left);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> read($Heap, this, _module.Node.right)
           == read(old($Heap), this, _module.Node.right);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> 
        read($Heap, this, _module.Node.sense)
         ==> read($Heap, this, _module.Node.parent) != null;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]
             || 
            $o == this
             || $o == read(old($Heap), this, _module.Node.left)
             || $o == read(old($Heap), this, _module.Node.right));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || $Frame$loop#0[$o, $f]);
    {
        if (!$w$loop#0)
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
            assume _module.Node.validUp#canCall($Heap, this);
            assume _module.Node.validUp#canCall($Heap, this);
            assume _module.Node.validUp($LS($LZ), $Heap, this);
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Node?(), $Heap);
            assume _module.Node.valid#canCall($Heap, this);
            assume _module.Node.valid#canCall($Heap, this);
            assume _module.Node.valid($Heap, this);
            assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
            assume true;
            assume read($Heap, this, _module.Node.left)
               == read(old($Heap), this, _module.Node.left);
            assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
            assume true;
            assume read($Heap, this, _module.Node.right)
               == read(old($Heap), this, _module.Node.right);
            if (read($Heap, this, _module.Node.sense))
            {
                newtype$check#3 := null;
            }

            assume true;
            assume read($Heap, this, _module.Node.sense)
               ==> read($Heap, this, _module.Node.parent) != null;
            assume true;
            assume false;
        }

        assume true;
        if (!read($Heap, this, _module.Node.sense))
        {
            break;
        }

        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(128,13)
        assume true;
        assert $Frame$loop#0[this, _module.Node.sense];
        havoc $rhs#3_0;
        $Heap := update($Heap, this, _module.Node.sense, $rhs#3_0);
        assume $IsGoodHeap($Heap);
        // ----- assume statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(129,7)
        if (!read($Heap, this, _module.Node.sense))
        {
            assert {:subsumption 0} read($Heap, this, _module.Node.parent) != null;
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(read($Heap, this, _module.Node.parent), Tclass._module.Node?(), $Heap);
            assume _module.Node.after#canCall($Heap, read($Heap, this, _module.Node.parent));
        }

        assume !read($Heap, this, _module.Node.sense)
           ==> _module.Node.after#canCall($Heap, read($Heap, this, _module.Node.parent));
        assume !read($Heap, this, _module.Node.sense)
           ==> _module.Node.after($Heap, read($Heap, this, _module.Node.parent));
        assume _module.Node.validUp#canCall($Heap, this)
           && (_module.Node.validUp($LS($LZ), $Heap, this)
             ==> _module.Node.valid#canCall($Heap, this));
    }

    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(132,8)
    assume true;
    assert $_Frame[this, _module.Node.pc];
    assume true;
    $rhs#3 := LitInt(4);
    $Heap := update($Heap, this, _module.Node.pc, $rhs#3);
    assume $IsGoodHeap($Heap);
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(133,5)
    newtype$check#4 := null;
    assume true;
    if (read($Heap, this, _module.Node.left) != null)
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(134,18)
        assert read($Heap, this, _module.Node.left) != null;
        assume true;
        assert $_Frame[read($Heap, this, _module.Node.left), _module.Node.sense];
        assume true;
        $rhs#4_0 := Lit(false);
        $Heap := update($Heap, read($Heap, this, _module.Node.left), _module.Node.sense, $rhs#4_0);
        assume $IsGoodHeap($Heap);
    }
    else
    {
    }

    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(137,8)
    assume true;
    assert $_Frame[this, _module.Node.pc];
    assume true;
    $rhs#4 := LitInt(5);
    $Heap := update($Heap, this, _module.Node.pc, $rhs#4);
    assume $IsGoodHeap($Heap);
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(138,5)
    newtype$check#5 := null;
    assume true;
    if (read($Heap, this, _module.Node.right) != null)
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(139,19)
        assert read($Heap, this, _module.Node.right) != null;
        assume true;
        assert $_Frame[read($Heap, this, _module.Node.right), _module.Node.sense];
        assume true;
        $rhs#5_0 := Lit(false);
        $Heap := update($Heap, read($Heap, this, _module.Node.right), _module.Node.sense, $rhs#5_0);
        assume $IsGoodHeap($Heap);
    }
    else
    {
    }

    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\TreeBarrier.dfy(142,8)
    assume true;
    assert $_Frame[this, _module.Node.pc];
    assume true;
    $rhs#5 := LitInt(6);
    $Heap := update($Heap, this, _module.Node.pc, $rhs#5);
    assume $IsGoodHeap($Heap);
}



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

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$left: NameFamily;

const unique field$right: NameFamily;

const unique field$parent: NameFamily;

const unique field$anc: NameFamily;

const unique field$desc: NameFamily;

const unique field$sense: NameFamily;

const unique field$pc: NameFamily;
