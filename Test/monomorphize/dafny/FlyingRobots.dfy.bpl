// Dafny 3.7.3.40719
// Command Line Options: /compile:0 /print:FlyingRobots.dfy.bpl

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

// Constructor function declaration
function #_System._tuple#3._#Make3(Box, Box, Box) : DatatypeType;

// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box, a#0#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#0#0#0, a#0#1#0, a#0#2#0) } 
  DatatypeCtorId(#_System._tuple#3._#Make3(a#0#0#0, a#0#1#0, a#0#2#0))
     == ##_System._tuple#3._#Make3);

const unique ##_System._tuple#3._#Make3: DtCtorId;

function _System.Tuple3.___hMake3_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple3.___hMake3_q(d) } 
  _System.Tuple3.___hMake3_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#3._#Make3);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple3.___hMake3_q(d) } 
  _System.Tuple3.___hMake3_q(d)
     ==> (exists a#1#0#0: Box, a#1#1#0: Box, a#1#2#0: Box :: 
      d == #_System._tuple#3._#Make3(a#1#0#0, a#1#1#0, a#1#2#0)));

function Tclass._System.Tuple3(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.Tuple3: TyTag;

// Tclass._System.Tuple3 Tag
axiom (forall _System._tuple#3$T0: Ty, _System._tuple#3$T1: Ty, _System._tuple#3$T2: Ty :: 
  { Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2) } 
  Tag(Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
       == Tagclass._System.Tuple3
     && TagFamily(Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
       == tytagFamily$_tuple#3);

function Tclass._System.Tuple3_0(Ty) : Ty;

// Tclass._System.Tuple3 injectivity 0
axiom (forall _System._tuple#3$T0: Ty, _System._tuple#3$T1: Ty, _System._tuple#3$T2: Ty :: 
  { Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2) } 
  Tclass._System.Tuple3_0(Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
     == _System._tuple#3$T0);

function Tclass._System.Tuple3_1(Ty) : Ty;

// Tclass._System.Tuple3 injectivity 1
axiom (forall _System._tuple#3$T0: Ty, _System._tuple#3$T1: Ty, _System._tuple#3$T2: Ty :: 
  { Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2) } 
  Tclass._System.Tuple3_1(Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
     == _System._tuple#3$T1);

function Tclass._System.Tuple3_2(Ty) : Ty;

// Tclass._System.Tuple3 injectivity 2
axiom (forall _System._tuple#3$T0: Ty, _System._tuple#3$T1: Ty, _System._tuple#3$T2: Ty :: 
  { Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2) } 
  Tclass._System.Tuple3_2(Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
     == _System._tuple#3$T2);

// Box/unbox axiom for Tclass._System.Tuple3
axiom (forall _System._tuple#3$T0: Ty, 
    _System._tuple#3$T1: Ty, 
    _System._tuple#3$T2: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2)) } 
  $IsBox(bx, 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2)));

// Constructor $Is
axiom (forall _System._tuple#3$T0: Ty, 
    _System._tuple#3$T1: Ty, 
    _System._tuple#3$T2: Ty, 
    a#2#0#0: Box, 
    a#2#1#0: Box, 
    a#2#2#0: Box :: 
  { $Is(#_System._tuple#3._#Make3(a#2#0#0, a#2#1#0, a#2#2#0), 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2)) } 
  $Is(#_System._tuple#3._#Make3(a#2#0#0, a#2#1#0, a#2#2#0), 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
     <==> $IsBox(a#2#0#0, _System._tuple#3$T0)
       && $IsBox(a#2#1#0, _System._tuple#3$T1)
       && $IsBox(a#2#2#0, _System._tuple#3$T2));

// Constructor $IsAlloc
axiom (forall _System._tuple#3$T0: Ty, 
    _System._tuple#3$T1: Ty, 
    _System._tuple#3$T2: Ty, 
    a#2#0#0: Box, 
    a#2#1#0: Box, 
    a#2#2#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#3._#Make3(a#2#0#0, a#2#1#0, a#2#2#0), 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#3._#Make3(a#2#0#0, a#2#1#0, a#2#2#0), 
        Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
        $h)
       <==> $IsAllocBox(a#2#0#0, _System._tuple#3$T0, $h)
         && $IsAllocBox(a#2#1#0, _System._tuple#3$T1, $h)
         && $IsAllocBox(a#2#2#0, _System._tuple#3$T2, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#3$T0: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple3._0(d), _System._tuple#3$T0, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple3.___hMake3_q(d)
       && (exists _System._tuple#3$T1: Ty, _System._tuple#3$T2: Ty :: 
        { $IsAlloc(d, 
            Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
            $h) } 
        $IsAlloc(d, 
          Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
          $h))
     ==> $IsAllocBox(_System.Tuple3._0(d), _System._tuple#3$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#3$T1: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple3._1(d), _System._tuple#3$T1, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple3.___hMake3_q(d)
       && (exists _System._tuple#3$T0: Ty, _System._tuple#3$T2: Ty :: 
        { $IsAlloc(d, 
            Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
            $h) } 
        $IsAlloc(d, 
          Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
          $h))
     ==> $IsAllocBox(_System.Tuple3._1(d), _System._tuple#3$T1, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#3$T2: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple3._2(d), _System._tuple#3$T2, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple3.___hMake3_q(d)
       && (exists _System._tuple#3$T0: Ty, _System._tuple#3$T1: Ty :: 
        { $IsAlloc(d, 
            Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
            $h) } 
        $IsAlloc(d, 
          Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2), 
          $h))
     ==> $IsAllocBox(_System.Tuple3._2(d), _System._tuple#3$T2, $h));

// Constructor literal
axiom (forall a#3#0#0: Box, a#3#1#0: Box, a#3#2#0: Box :: 
  { #_System._tuple#3._#Make3(Lit(a#3#0#0), Lit(a#3#1#0), Lit(a#3#2#0)) } 
  #_System._tuple#3._#Make3(Lit(a#3#0#0), Lit(a#3#1#0), Lit(a#3#2#0))
     == Lit(#_System._tuple#3._#Make3(a#3#0#0, a#3#1#0, a#3#2#0)));

function _System.Tuple3._0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#4#0#0: Box, a#4#1#0: Box, a#4#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#4#0#0, a#4#1#0, a#4#2#0) } 
  _System.Tuple3._0(#_System._tuple#3._#Make3(a#4#0#0, a#4#1#0, a#4#2#0))
     == a#4#0#0);

// Inductive rank
axiom (forall a#5#0#0: Box, a#5#1#0: Box, a#5#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#5#0#0, a#5#1#0, a#5#2#0) } 
  BoxRank(a#5#0#0) < DtRank(#_System._tuple#3._#Make3(a#5#0#0, a#5#1#0, a#5#2#0)));

function _System.Tuple3._1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#6#0#0: Box, a#6#1#0: Box, a#6#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#6#0#0, a#6#1#0, a#6#2#0) } 
  _System.Tuple3._1(#_System._tuple#3._#Make3(a#6#0#0, a#6#1#0, a#6#2#0))
     == a#6#1#0);

// Inductive rank
axiom (forall a#7#0#0: Box, a#7#1#0: Box, a#7#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#7#0#0, a#7#1#0, a#7#2#0) } 
  BoxRank(a#7#1#0) < DtRank(#_System._tuple#3._#Make3(a#7#0#0, a#7#1#0, a#7#2#0)));

function _System.Tuple3._2(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#8#0#0: Box, a#8#1#0: Box, a#8#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#8#0#0, a#8#1#0, a#8#2#0) } 
  _System.Tuple3._2(#_System._tuple#3._#Make3(a#8#0#0, a#8#1#0, a#8#2#0))
     == a#8#2#0);

// Inductive rank
axiom (forall a#9#0#0: Box, a#9#1#0: Box, a#9#2#0: Box :: 
  { #_System._tuple#3._#Make3(a#9#0#0, a#9#1#0, a#9#2#0) } 
  BoxRank(a#9#2#0) < DtRank(#_System._tuple#3._#Make3(a#9#0#0, a#9#1#0, a#9#2#0)));

// Depth-one case-split function
function $IsA#_System.Tuple3(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple3(d) } 
  $IsA#_System.Tuple3(d) ==> _System.Tuple3.___hMake3_q(d));

// Questionmark data type disjunctivity
axiom (forall _System._tuple#3$T0: Ty, 
    _System._tuple#3$T1: Ty, 
    _System._tuple#3$T2: Ty, 
    d: DatatypeType :: 
  { _System.Tuple3.___hMake3_q(d), $Is(d, 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2)) } 
  $Is(d, 
      Tclass._System.Tuple3(_System._tuple#3$T0, _System._tuple#3$T1, _System._tuple#3$T2))
     ==> _System.Tuple3.___hMake3_q(d));

// Datatype extensional equality declaration
function _System.Tuple3#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#3._#Make3
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple3#Equal(a, b) } 
  true
     ==> (_System.Tuple3#Equal(a, b)
       <==> _System.Tuple3._0(a) == _System.Tuple3._0(b)
         && _System.Tuple3._1(a) == _System.Tuple3._1(b)
         && _System.Tuple3._2(a) == _System.Tuple3._2(b)));

// Datatype extensionality axiom: _System._tuple#3
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple3#Equal(a, b) } 
  _System.Tuple3#Equal(a, b) <==> a == b);

const unique class._System.Tuple3: ClassName;

// Constructor identifier
axiom (forall a#10#0#0: Box, a#10#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#10#0#0, a#10#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#10#0#0, a#10#1#0))
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
     ==> (exists a#11#0#0: Box, a#11#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#11#0#0, a#11#1#0)));

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
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#12#0#0: Box, a#12#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#12#0#0, _System._tuple#2$T0) && $IsBox(a#12#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty, 
    _System._tuple#2$T1: Ty, 
    a#12#0#0: Box, 
    a#12#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#12#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#12#1#0, _System._tuple#2$T1, $h)));

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
axiom (forall a#13#0#0: Box, a#13#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#13#0#0), Lit(a#13#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#13#0#0), Lit(a#13#1#0))
     == Lit(#_System._tuple#2._#Make2(a#13#0#0, a#13#1#0)));

// Constructor injectivity
axiom (forall a#14#0#0: Box, a#14#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#14#0#0, a#14#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#14#0#0, a#14#1#0)) == a#14#0#0);

// Inductive rank
axiom (forall a#15#0#0: Box, a#15#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#15#0#0, a#15#1#0) } 
  BoxRank(a#15#0#0) < DtRank(#_System._tuple#2._#Make2(a#15#0#0, a#15#1#0)));

// Constructor injectivity
axiom (forall a#16#0#0: Box, a#16#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#16#0#0, a#16#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#16#0#0, a#16#1#0)) == a#16#1#0);

// Inductive rank
axiom (forall a#17#0#0: Box, a#17#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#17#0#0, a#17#1#0) } 
  BoxRank(a#17#1#0) < DtRank(#_System._tuple#2._#Make2(a#17#0#0, a#17#1#0)));

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

const BaseFuel__module.Bot.Valid: LayerType;

const StartFuel__module.Bot.Valid: LayerType;

const StartFuelAssert__module.Bot.Valid: LayerType;

const unique class._module.Cell?: ClassName;

function Tclass._module.Cell?() : Ty;

const unique Tagclass._module.Cell?: TyTag;

// Tclass._module.Cell? Tag
axiom Tag(Tclass._module.Cell?()) == Tagclass._module.Cell?
   && TagFamily(Tclass._module.Cell?()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass._module.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cell?()) } 
  $IsBox(bx, Tclass._module.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cell?()));

// Cell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Cell?()) } 
  $Is($o, Tclass._module.Cell?())
     <==> $o == null || dtype($o) == Tclass._module.Cell?());

// Cell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Cell?(), $h) } 
  $IsAlloc($o, Tclass._module.Cell?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Cell.val) == 0
   && FieldOfDecl(class._module.Cell?, field$val) == _module.Cell.val
   && !$IsGhostField(_module.Cell.val);

const _module.Cell.val: Field int;

// Cell.val: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cell.val) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Cell?()
     ==> $Is(read($h, $o, _module.Cell.val), TInt));

// Cell.val: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cell.val) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Cell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Cell.val), TInt, $h));

function Tclass._module.Cell() : Ty;

const unique Tagclass._module.Cell: TyTag;

// Tclass._module.Cell Tag
axiom Tag(Tclass._module.Cell()) == Tagclass._module.Cell
   && TagFamily(Tclass._module.Cell()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass._module.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cell()) } 
  $IsBox(bx, Tclass._module.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cell()));

procedure {:verboseName "Cell._ctor (well-formedness)"} CheckWellFormed$$_module.Cell.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && $IsAlloc(this, Tclass._module.Cell(), $Heap), 
    v#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Cell._ctor (call)"} Call$$_module.Cell.__ctor(v#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && $IsAlloc(this, Tclass._module.Cell(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Cell.val) == v#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Cell._ctor (correctness)"} Impl$$_module.Cell.__ctor(v#0: int)
   returns (this: ref where this != null && $Is(this, Tclass._module.Cell()), 
    $_reverifyPost: bool);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Cell.val) == v#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Cell._ctor (correctness)"} Impl$$_module.Cell.__ctor(v#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.val: int;

    // AddMethodImpl: _ctor, Impl$$_module.Cell.__ctor
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- divided block before new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(11,3)
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(12,9)
    assume true;
    assume true;
    this.val := v#0;
    // ----- new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(11,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Cell.val) == this.val;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(11,3)
}



// _module.Cell: non-null type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Cell()) } 
  $Is(c#0, Tclass._module.Cell())
     <==> $Is(c#0, Tclass._module.Cell?()) && c#0 != null);

// _module.Cell: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Cell(), $h) } 
  $IsAlloc(c#0, Tclass._module.Cell(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Cell?(), $h));

const unique class._module.Point?: ClassName;

function Tclass._module.Point?() : Ty;

const unique Tagclass._module.Point?: TyTag;

// Tclass._module.Point? Tag
axiom Tag(Tclass._module.Point?()) == Tagclass._module.Point?
   && TagFamily(Tclass._module.Point?()) == tytagFamily$Point;

// Box/unbox axiom for Tclass._module.Point?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Point?()) } 
  $IsBox(bx, Tclass._module.Point?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Point?()));

// Point: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Point?()) } 
  $Is($o, Tclass._module.Point?())
     <==> $o == null || dtype($o) == Tclass._module.Point?());

// Point: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Point?(), $h) } 
  $IsAlloc($o, Tclass._module.Point?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Point.Value) == 0
   && FieldOfDecl(class._module.Point?, field$Value) == _module.Point.Value
   && $IsGhostField(_module.Point.Value);

const _module.Point.Value: Field DatatypeType;

// Point.Value: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.Value) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Point?()
     ==> $Is(read($h, $o, _module.Point.Value), Tclass._System.Tuple3(TInt, TInt, TInt)));

// Point.Value: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.Value) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Point?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Point.Value), Tclass._System.Tuple3(TInt, TInt, TInt), $h));

axiom FDim(_module.Point.Repr) == 0
   && FieldOfDecl(class._module.Point?, field$Repr) == _module.Point.Repr
   && $IsGhostField(_module.Point.Repr);

const _module.Point.Repr: Field (Set Box);

// Point.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Point?()
     ==> $Is(read($h, $o, _module.Point.Repr), TSet(Tclass._System.object())));

// Point.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Point?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Point.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.Point.Valid
function _module.Point.Valid($heap: Heap, this: ref) : bool;

function _module.Point.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass._module.Point() : Ty;

const unique Tagclass._module.Point: TyTag;

// Tclass._module.Point Tag
axiom Tag(Tclass._module.Point()) == Tagclass._module.Point
   && TagFamily(Tclass._module.Point()) == tytagFamily$Point;

// Box/unbox axiom for Tclass._module.Point
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Point()) } 
  $IsBox(bx, Tclass._module.Point())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Point()));

// frame axiom for _module.Point.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Point.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Point())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.Point.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Point.Valid($h0, this) == _module.Point.Valid($h1, this));

// consequence axiom for _module.Point.Valid
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Point.Valid($Heap, this) } 
    _module.Point.Valid#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Point())
           && $IsAlloc(this, Tclass._module.Point(), $Heap))
       ==> 
      _module.Point.Valid($Heap, this)
       ==> read($Heap, this, _module.Point.Repr)[$Box(this)]);

function _module.Point.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Point.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Point.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Point())
       && $IsAlloc(this, Tclass._module.Point(), $Heap)
     ==> _module.Point.Valid#requires($Heap, this) == true);

axiom FDim(_module.Point.x) == 0
   && FieldOfDecl(class._module.Point?, field$x) == _module.Point.x
   && !$IsGhostField(_module.Point.x);

axiom FDim(_module.Point.y) == 0
   && FieldOfDecl(class._module.Point?, field$y) == _module.Point.y
   && !$IsGhostField(_module.Point.y);

axiom FDim(_module.Point.z) == 0
   && FieldOfDecl(class._module.Point?, field$z) == _module.Point.z
   && !$IsGhostField(_module.Point.z);

// definition axiom for _module.Point.Valid (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Point.Valid($Heap, this), $IsGoodHeap($Heap) } 
    _module.Point.Valid#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Point())
           && $IsAlloc(this, Tclass._module.Point(), $Heap))
       ==> (read($Heap, this, _module.Point.Repr)[$Box(this)]
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                $Box(read($Heap, this, _module.Point.y))), 
              $Box(read($Heap, this, _module.Point.z))), 
            read($Heap, this, _module.Point.Repr))
           ==> 
          read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
           ==> 
          read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
           ==> 
          read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
           ==> $IsA#_System.Tuple3(read($Heap, this, _module.Point.Value)))
         && _module.Point.Valid($Heap, this)
           == (
            read($Heap, this, _module.Point.Repr)[$Box(this)]
             && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                  $Box(read($Heap, this, _module.Point.y))), 
                $Box(read($Heap, this, _module.Point.z))), 
              read($Heap, this, _module.Point.Repr))
             && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
             && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
             && read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
             && _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
              #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
                $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
                $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))))));

procedure {:verboseName "Point.Valid (well-formedness)"} CheckWellformed$$_module.Point.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Point())
         && $IsAlloc(this, Tclass._module.Point(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Point.Valid($Heap, this)
     ==> read($Heap, this, _module.Point.Repr)[$Box(this)];



implementation {:verboseName "Point.Valid (well-formedness)"} CheckWellformed$$_module.Point.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
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

    // AddWellformednessCheck for function Valid
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Point.Repr)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    b$reqreads#0 := $_Frame[this, _module.Point.Repr];
    assert b$reqreads#0;
    if (*)
    {
        if (*)
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Point?(), $Heap);
            assert this == this
               || (Set#Subset(Set#Union(read($Heap, this, _module.Point.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Point.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.Point.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Point.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
            assume this == this || _module.Point.Valid#canCall($Heap, this);
            assume _module.Point.Valid($Heap, this);
            assume read($Heap, this, _module.Point.Repr)[$Box(this)];
        }
        else
        {
            assume _module.Point.Valid($Heap, this)
               ==> read($Heap, this, _module.Point.Repr)[$Box(this)];
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Point.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Point.Repr];
        if (read($Heap, this, _module.Point.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Point.x];
            b$reqreads#3 := $_Frame[this, _module.Point.y];
            b$reqreads#4 := $_Frame[this, _module.Point.z];
            b$reqreads#5 := $_Frame[this, _module.Point.Repr];
        }

        if (read($Heap, this, _module.Point.Repr)[$Box(this)]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                $Box(read($Heap, this, _module.Point.y))), 
              $Box(read($Heap, this, _module.Point.z))), 
            read($Heap, this, _module.Point.Repr)))
        {
            b$reqreads#6 := $_Frame[this, _module.Point.x];
            b$reqreads#7 := $_Frame[this, _module.Point.y];
        }

        if (read($Heap, this, _module.Point.Repr)[$Box(this)]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                $Box(read($Heap, this, _module.Point.y))), 
              $Box(read($Heap, this, _module.Point.z))), 
            read($Heap, this, _module.Point.Repr))
           && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y))
        {
            b$reqreads#8 := $_Frame[this, _module.Point.y];
            b$reqreads#9 := $_Frame[this, _module.Point.z];
        }

        if (read($Heap, this, _module.Point.Repr)[$Box(this)]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                $Box(read($Heap, this, _module.Point.y))), 
              $Box(read($Heap, this, _module.Point.z))), 
            read($Heap, this, _module.Point.Repr))
           && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
           && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z))
        {
            b$reqreads#10 := $_Frame[this, _module.Point.z];
            b$reqreads#11 := $_Frame[this, _module.Point.x];
        }

        if (read($Heap, this, _module.Point.Repr)[$Box(this)]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                $Box(read($Heap, this, _module.Point.y))), 
              $Box(read($Heap, this, _module.Point.z))), 
            read($Heap, this, _module.Point.Repr))
           && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
           && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
           && read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x))
        {
            b$reqreads#12 := $_Frame[this, _module.Point.Value];
            b$reqreads#13 := $_Frame[this, _module.Point.x];
            assert read($Heap, this, _module.Point.x) != null;
            b$reqreads#14 := $_Frame[read($Heap, this, _module.Point.x), _module.Cell.val];
            b$reqreads#15 := $_Frame[this, _module.Point.y];
            assert read($Heap, this, _module.Point.y) != null;
            b$reqreads#16 := $_Frame[read($Heap, this, _module.Point.y), _module.Cell.val];
            b$reqreads#17 := $_Frame[this, _module.Point.z];
            assert read($Heap, this, _module.Point.z) != null;
            b$reqreads#18 := $_Frame[read($Heap, this, _module.Point.z), _module.Cell.val];
        }

        assume _module.Point.Valid($Heap, this)
           == (
            read($Heap, this, _module.Point.Repr)[$Box(this)]
             && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                  $Box(read($Heap, this, _module.Point.y))), 
                $Box(read($Heap, this, _module.Point.z))), 
              read($Heap, this, _module.Point.Repr))
             && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
             && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
             && read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
             && _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
              #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
                $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
                $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val)))));
        assume read($Heap, this, _module.Point.Repr)[$Box(this)]
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
                $Box(read($Heap, this, _module.Point.y))), 
              $Box(read($Heap, this, _module.Point.z))), 
            read($Heap, this, _module.Point.Repr))
           ==> 
          read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
           ==> 
          read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
           ==> 
          read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
           ==> $IsA#_System.Tuple3(read($Heap, this, _module.Point.Value));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Point.Valid($Heap, this), TBool);
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
    }
}



const _module.Point.x: Field ref;

// Point.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Point?()
     ==> $Is(read($h, $o, _module.Point.x), Tclass._module.Cell()));

// Point.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Point?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Point.x), Tclass._module.Cell(), $h));

const _module.Point.y: Field ref;

// Point.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Point?()
     ==> $Is(read($h, $o, _module.Point.y), Tclass._module.Cell()));

// Point.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Point?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Point.y), Tclass._module.Cell(), $h));

const _module.Point.z: Field ref;

// Point.z: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.z) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Point?()
     ==> $Is(read($h, $o, _module.Point.z), Tclass._module.Cell()));

// Point.z: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Point.z) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Point?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Point.z), Tclass._module.Cell(), $h));

procedure {:verboseName "Point._ctor (well-formedness)"} CheckWellFormed$$_module.Point.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Point())
         && $IsAlloc(this, Tclass._module.Point(), $Heap), 
    a#0: int, 
    b#0: int, 
    c#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Point._ctor (call)"} Call$$_module.Point.__ctor(a#0: int, b#0: int, c#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Point())
         && $IsAlloc(this, Tclass._module.Point(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Point.Valid#canCall($Heap, this);
  free ensures _module.Point.Valid#canCall($Heap, this)
     && 
    _module.Point.Valid($Heap, this)
     && 
    read($Heap, this, _module.Point.Repr)[$Box(this)]
     && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
          $Box(read($Heap, this, _module.Point.y))), 
        $Box(read($Heap, this, _module.Point.z))), 
      read($Heap, this, _module.Point.Repr))
     && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
     && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
     && read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
     && _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
      #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Point.Repr)[$Box($o)] } 
    read($Heap, this, _module.Point.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple3(read($Heap, this, _module.Point.Value));
  ensures _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
    #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0)));
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Point._ctor (correctness)"} Impl$$_module.Point.__ctor(a#0: int, b#0: int, c#0: int)
   returns (this: ref where this != null && $Is(this, Tclass._module.Point()), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Point.Valid#canCall($Heap, this);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.Repr)[$Box(this)];
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
            $Box(read($Heap, this, _module.Point.y))), 
          $Box(read($Heap, this, _module.Point.z))), 
        read($Heap, this, _module.Point.Repr));
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
        #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Point.Repr)[$Box($o)] } 
    read($Heap, this, _module.Point.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple3(read($Heap, this, _module.Point.Value));
  ensures _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
    #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Point._ctor (correctness)"} Impl$$_module.Point.__ctor(a#0: int, b#0: int, c#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Value: DatatypeType;
  var this.Repr: Set Box;
  var this.x: ref;
  var this.y: ref;
  var this.z: ref;
  var defass#this.x: bool;
  var defass#this.y: bool;
  var defass#this.z: bool;
  var $nw: ref;
  var v##0: int;
  var v##1: int;
  var v##2: int;

    // AddMethodImpl: _ctor, Impl$$_module.Point.__ctor
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- divided block before new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(35,3)
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(36,7)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(36,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##0 := a#0;
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Cell.__ctor(v##0);
    // TrCallStmt: After ProcessCallStmt
    this.x := $nw;
    defass#this.x := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(37,7)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(37,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##1 := b#0;
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Cell.__ctor(v##1);
    // TrCallStmt: After ProcessCallStmt
    this.y := $nw;
    defass#this.y := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(38,7)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(38,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##2 := c#0;
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Cell.__ctor(v##2);
    // TrCallStmt: After ProcessCallStmt
    this.z := $nw;
    defass#this.z := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(39,10)
    assume true;
    assert defass#this.x;
    assert defass#this.y;
    assert defass#this.z;
    assume true;
    this.Repr := Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), $Box(this.x)), 
        $Box(this.y)), 
      $Box(this.z));
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(40,11)
    assume true;
    assume true;
    this.Value := #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0));
    // ----- new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(35,3)
    assert defass#this.x;
    assert defass#this.y;
    assert defass#this.z;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Point.Value) == this.Value;
    assume read($Heap, this, _module.Point.Repr) == this.Repr;
    assume read($Heap, this, _module.Point.x) == this.x;
    assume read($Heap, this, _module.Point.y) == this.y;
    assume read($Heap, this, _module.Point.z) == this.z;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(35,3)
}



procedure {:verboseName "Point.Mutate (well-formedness)"} CheckWellFormed$$_module.Point.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Point())
         && $IsAlloc(this, Tclass._module.Point(), $Heap), 
    a#0: int, 
    b#0: int, 
    c#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Point.Mutate (well-formedness)"} CheckWellFormed$$_module.Point.Mutate(this: ref, a#0: int, b#0: int, c#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Mutate, CheckWellFormed$$_module.Point.Mutate
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Point.Repr)[$Box($o)]);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Point?(), $Heap);
    assume _module.Point.Valid#canCall($Heap, this);
    assume _module.Point.Valid($Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.Point.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Point?(), $Heap);
    assume _module.Point.Valid#canCall($Heap, this);
    assume _module.Point.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.Point(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.Point.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Point.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assume _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
      #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0)));
}



procedure {:verboseName "Point.Mutate (call)"} Call$$_module.Point.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Point())
         && $IsAlloc(this, Tclass._module.Point(), $Heap), 
    a#0: int, 
    b#0: int, 
    c#0: int);
  // user-defined preconditions
  requires _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.Repr)[$Box(this)];
  requires _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
            $Box(read($Heap, this, _module.Point.y))), 
          $Box(read($Heap, this, _module.Point.z))), 
        read($Heap, this, _module.Point.Repr));
  requires _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y);
  requires _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z);
  requires _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x);
  requires _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
        #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Point.Valid#canCall($Heap, this);
  free ensures _module.Point.Valid#canCall($Heap, this)
     && 
    _module.Point.Valid($Heap, this)
     && 
    read($Heap, this, _module.Point.Repr)[$Box(this)]
     && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
          $Box(read($Heap, this, _module.Point.y))), 
        $Box(read($Heap, this, _module.Point.z))), 
      read($Heap, this, _module.Point.Repr))
     && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
     && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
     && read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
     && _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
      #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Point.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Point.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple3(read($Heap, this, _module.Point.Value));
  ensures _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
    #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Point.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Point.Mutate (correctness)"} Impl$$_module.Point.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Point())
         && $IsAlloc(this, Tclass._module.Point(), $Heap), 
    a#0: int, 
    b#0: int, 
    c#0: int)
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Point.Valid#canCall($Heap, this)
     && 
    _module.Point.Valid($Heap, this)
     && 
    read($Heap, this, _module.Point.Repr)[$Box(this)]
     && Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
          $Box(read($Heap, this, _module.Point.y))), 
        $Box(read($Heap, this, _module.Point.z))), 
      read($Heap, this, _module.Point.Repr))
     && read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y)
     && read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z)
     && read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
     && _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
      #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Point.Valid#canCall($Heap, this);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.Repr)[$Box(this)];
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || Set#Subset(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Point.x))), 
            $Box(read($Heap, this, _module.Point.y))), 
          $Box(read($Heap, this, _module.Point.z))), 
        read($Heap, this, _module.Point.Repr));
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.x) != read($Heap, this, _module.Point.y);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.z);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x);
  ensures _module.Point.Valid#canCall($Heap, this)
     ==> _module.Point.Valid($Heap, this)
       || _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
        #_System._tuple#3._#Make3($Box(read($Heap, read($Heap, this, _module.Point.x), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Point.y), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Point.z), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Point.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Point.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple3(read($Heap, this, _module.Point.Value));
  ensures _System.Tuple3#Equal(read($Heap, this, _module.Point.Value), 
    #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Point.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Point.Mutate (correctness)"} Impl$$_module.Point.Mutate(this: ref, a#0: int, b#0: int, c#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $obj2: ref;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: DatatypeType;

    // AddMethodImpl: Mutate, Impl$$_module.Point.Mutate
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Point.Repr)[$Box($o)]);
    $_reverifyPost := false;
    // ----- update statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(49,25)
    assert read($Heap, this, _module.Point.x) != null;
    assume true;
    $obj0 := read($Heap, this, _module.Point.x);
    assert $_Frame[$obj0, _module.Cell.val];
    assert read($Heap, this, _module.Point.y) != null;
    assume true;
    $obj1 := read($Heap, this, _module.Point.y);
    assert $_Frame[$obj1, _module.Cell.val];
    assert read($Heap, this, _module.Point.z) != null;
    assume true;
    $obj2 := read($Heap, this, _module.Point.z);
    assert $_Frame[$obj2, _module.Cell.val];
    assume true;
    $rhs#0 := a#0;
    assume true;
    $rhs#1 := b#0;
    assume true;
    $rhs#2 := c#0;
    assert read($Heap, this, _module.Point.y) != read($Heap, this, _module.Point.x)
       || $rhs#1 == $rhs#0;
    assert read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.x)
       || $rhs#2 == $rhs#0;
    assert read($Heap, this, _module.Point.z) != read($Heap, this, _module.Point.y)
       || $rhs#2 == $rhs#1;
    $Heap := update($Heap, $obj0, _module.Cell.val, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Cell.val, $rhs#1);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj2, _module.Cell.val, $rhs#2);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(50,11)
    assume true;
    assert $_Frame[this, _module.Point.Value];
    assume true;
    $rhs#3 := #_System._tuple#3._#Make3($Box(a#0), $Box(b#0), $Box(c#0));
    $Heap := update($Heap, this, _module.Point.Value, $rhs#3);
    assume $IsGoodHeap($Heap);
}



// _module.Point: non-null type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Point()) } 
  $Is(c#0, Tclass._module.Point())
     <==> $Is(c#0, Tclass._module.Point?()) && c#0 != null);

// _module.Point: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Point(), $h) } 
  $IsAlloc(c#0, Tclass._module.Point(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Point?(), $h));

const unique class._module.Arm?: ClassName;

function Tclass._module.Arm?() : Ty;

const unique Tagclass._module.Arm?: TyTag;

// Tclass._module.Arm? Tag
axiom Tag(Tclass._module.Arm?()) == Tagclass._module.Arm?
   && TagFamily(Tclass._module.Arm?()) == tytagFamily$Arm;

// Box/unbox axiom for Tclass._module.Arm?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Arm?()) } 
  $IsBox(bx, Tclass._module.Arm?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Arm?()));

// Arm: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Arm?()) } 
  $Is($o, Tclass._module.Arm?())
     <==> $o == null || dtype($o) == Tclass._module.Arm?());

// Arm: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Arm?(), $h) } 
  $IsAlloc($o, Tclass._module.Arm?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Arm.Value) == 0
   && FieldOfDecl(class._module.Arm?, field$Value) == _module.Arm.Value
   && $IsGhostField(_module.Arm.Value);

const _module.Arm.Value: Field DatatypeType;

// Arm.Value: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.Value) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Arm?()
     ==> $Is(read($h, $o, _module.Arm.Value), Tclass._System.Tuple2(TInt, TInt)));

// Arm.Value: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.Value) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Arm?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Arm.Value), Tclass._System.Tuple2(TInt, TInt), $h));

axiom FDim(_module.Arm.Repr) == 0
   && FieldOfDecl(class._module.Arm?, field$Repr) == _module.Arm.Repr
   && $IsGhostField(_module.Arm.Repr);

const _module.Arm.Repr: Field (Set Box);

// Arm.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Arm?()
     ==> $Is(read($h, $o, _module.Arm.Repr), TSet(Tclass._System.object())));

// Arm.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Arm?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Arm.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.Arm.Valid
function _module.Arm.Valid($heap: Heap, this: ref) : bool;

function _module.Arm.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass._module.Arm() : Ty;

const unique Tagclass._module.Arm: TyTag;

// Tclass._module.Arm Tag
axiom Tag(Tclass._module.Arm()) == Tagclass._module.Arm
   && TagFamily(Tclass._module.Arm()) == tytagFamily$Arm;

// Box/unbox axiom for Tclass._module.Arm
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Arm()) } 
  $IsBox(bx, Tclass._module.Arm())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Arm()));

// frame axiom for _module.Arm.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Arm.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Arm())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.Arm.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Arm.Valid($h0, this) == _module.Arm.Valid($h1, this));

// consequence axiom for _module.Arm.Valid
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Arm.Valid($Heap, this) } 
    _module.Arm.Valid#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Arm())
           && $IsAlloc(this, Tclass._module.Arm(), $Heap))
       ==> 
      _module.Arm.Valid($Heap, this)
       ==> read($Heap, this, _module.Arm.Repr)[$Box(this)]);

function _module.Arm.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Arm.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Arm.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Arm())
       && $IsAlloc(this, Tclass._module.Arm(), $Heap)
     ==> _module.Arm.Valid#requires($Heap, this) == true);

axiom FDim(_module.Arm.polar) == 0
   && FieldOfDecl(class._module.Arm?, field$polar) == _module.Arm.polar
   && !$IsGhostField(_module.Arm.polar);

axiom FDim(_module.Arm.azim) == 0
   && FieldOfDecl(class._module.Arm?, field$azim) == _module.Arm.azim
   && !$IsGhostField(_module.Arm.azim);

// definition axiom for _module.Arm.Valid (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Arm.Valid($Heap, this), $IsGoodHeap($Heap) } 
    _module.Arm.Valid#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Arm())
           && $IsAlloc(this, Tclass._module.Arm(), $Heap))
       ==> (read($Heap, this, _module.Arm.Repr)[$Box(this)]
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
              $Box(read($Heap, this, _module.Arm.azim))), 
            read($Heap, this, _module.Arm.Repr))
           ==> 
          read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
           ==> $IsA#_System.Tuple2(read($Heap, this, _module.Arm.Value)))
         && _module.Arm.Valid($Heap, this)
           == (
            read($Heap, this, _module.Arm.Repr)[$Box(this)]
             && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
                $Box(read($Heap, this, _module.Arm.azim))), 
              read($Heap, this, _module.Arm.Repr))
             && read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
             && _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
              #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
                $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))))));

procedure {:verboseName "Arm.Valid (well-formedness)"} CheckWellformed$$_module.Arm.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Arm())
         && $IsAlloc(this, Tclass._module.Arm(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Arm.Valid($Heap, this)
     ==> read($Heap, this, _module.Arm.Repr)[$Box(this)];



implementation {:verboseName "Arm.Valid (well-formedness)"} CheckWellformed$$_module.Arm.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
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

    // AddWellformednessCheck for function Valid
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Arm.Repr)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    b$reqreads#0 := $_Frame[this, _module.Arm.Repr];
    assert b$reqreads#0;
    if (*)
    {
        if (*)
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Arm?(), $Heap);
            assert this == this
               || (Set#Subset(Set#Union(read($Heap, this, _module.Arm.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Arm.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.Arm.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Arm.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
            assume this == this || _module.Arm.Valid#canCall($Heap, this);
            assume _module.Arm.Valid($Heap, this);
            assume read($Heap, this, _module.Arm.Repr)[$Box(this)];
        }
        else
        {
            assume _module.Arm.Valid($Heap, this)
               ==> read($Heap, this, _module.Arm.Repr)[$Box(this)];
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Arm.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Arm.Repr];
        if (read($Heap, this, _module.Arm.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Arm.polar];
            b$reqreads#3 := $_Frame[this, _module.Arm.azim];
            b$reqreads#4 := $_Frame[this, _module.Arm.Repr];
        }

        if (read($Heap, this, _module.Arm.Repr)[$Box(this)]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
              $Box(read($Heap, this, _module.Arm.azim))), 
            read($Heap, this, _module.Arm.Repr)))
        {
            b$reqreads#5 := $_Frame[this, _module.Arm.polar];
            b$reqreads#6 := $_Frame[this, _module.Arm.azim];
        }

        if (read($Heap, this, _module.Arm.Repr)[$Box(this)]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
              $Box(read($Heap, this, _module.Arm.azim))), 
            read($Heap, this, _module.Arm.Repr))
           && read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim))
        {
            b$reqreads#7 := $_Frame[this, _module.Arm.Value];
            b$reqreads#8 := $_Frame[this, _module.Arm.polar];
            assert read($Heap, this, _module.Arm.polar) != null;
            b$reqreads#9 := $_Frame[read($Heap, this, _module.Arm.polar), _module.Cell.val];
            b$reqreads#10 := $_Frame[this, _module.Arm.azim];
            assert read($Heap, this, _module.Arm.azim) != null;
            b$reqreads#11 := $_Frame[read($Heap, this, _module.Arm.azim), _module.Cell.val];
        }

        assume _module.Arm.Valid($Heap, this)
           == (
            read($Heap, this, _module.Arm.Repr)[$Box(this)]
             && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
                $Box(read($Heap, this, _module.Arm.azim))), 
              read($Heap, this, _module.Arm.Repr))
             && read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
             && _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
              #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
                $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val)))));
        assume read($Heap, this, _module.Arm.Repr)[$Box(this)]
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
              $Box(read($Heap, this, _module.Arm.azim))), 
            read($Heap, this, _module.Arm.Repr))
           ==> 
          read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
           ==> $IsA#_System.Tuple2(read($Heap, this, _module.Arm.Value));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Arm.Valid($Heap, this), TBool);
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
    }
}



const _module.Arm.polar: Field ref;

// Arm.polar: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.polar) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Arm?()
     ==> $Is(read($h, $o, _module.Arm.polar), Tclass._module.Cell()));

// Arm.polar: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.polar) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Arm?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Arm.polar), Tclass._module.Cell(), $h));

const _module.Arm.azim: Field ref;

// Arm.azim: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.azim) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Arm?()
     ==> $Is(read($h, $o, _module.Arm.azim), Tclass._module.Cell()));

// Arm.azim: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Arm.azim) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Arm?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Arm.azim), Tclass._module.Cell(), $h));

procedure {:verboseName "Arm._ctor (well-formedness)"} CheckWellFormed$$_module.Arm.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Arm())
         && $IsAlloc(this, Tclass._module.Arm(), $Heap), 
    polar_in#0: int, 
    azim_in#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Arm._ctor (call)"} Call$$_module.Arm.__ctor(polar_in#0: int, azim_in#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Arm())
         && $IsAlloc(this, Tclass._module.Arm(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Arm.Valid#canCall($Heap, this);
  free ensures _module.Arm.Valid#canCall($Heap, this)
     && 
    _module.Arm.Valid($Heap, this)
     && 
    read($Heap, this, _module.Arm.Repr)[$Box(this)]
     && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
        $Box(read($Heap, this, _module.Arm.azim))), 
      read($Heap, this, _module.Arm.Repr))
     && read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
     && _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
      #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Arm.Repr)[$Box($o)] } 
    read($Heap, this, _module.Arm.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple2(read($Heap, this, _module.Arm.Value));
  ensures _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
    #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0)));
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Arm._ctor (correctness)"} Impl$$_module.Arm.__ctor(polar_in#0: int, azim_in#0: int)
   returns (this: ref where this != null && $Is(this, Tclass._module.Arm()), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Arm.Valid#canCall($Heap, this);
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || read($Heap, this, _module.Arm.Repr)[$Box(this)];
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
          $Box(read($Heap, this, _module.Arm.azim))), 
        read($Heap, this, _module.Arm.Repr));
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim);
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
        #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Arm.Repr)[$Box($o)] } 
    read($Heap, this, _module.Arm.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple2(read($Heap, this, _module.Arm.Value));
  ensures _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
    #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Arm._ctor (correctness)"} Impl$$_module.Arm.__ctor(polar_in#0: int, azim_in#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Value: DatatypeType;
  var this.Repr: Set Box;
  var this.polar: ref;
  var this.azim: ref;
  var defass#this.polar: bool;
  var defass#this.azim: bool;
  var $nw: ref;
  var v##0: int;
  var v##1: int;

    // AddMethodImpl: _ctor, Impl$$_module.Arm.__ctor
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- divided block before new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(74,3)
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(75,11)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(75,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##0 := polar_in#0;
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Cell.__ctor(v##0);
    // TrCallStmt: After ProcessCallStmt
    this.polar := $nw;
    defass#this.polar := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(76,10)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(76,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##1 := azim_in#0;
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Cell.__ctor(v##1);
    // TrCallStmt: After ProcessCallStmt
    this.azim := $nw;
    defass#this.azim := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(77,10)
    assume true;
    assert defass#this.polar;
    assert defass#this.azim;
    assume true;
    this.Repr := Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), $Box(this.polar)), 
      $Box(this.azim));
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(78,11)
    assume true;
    assume true;
    this.Value := #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0));
    // ----- new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(74,3)
    assert defass#this.polar;
    assert defass#this.azim;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Arm.Value) == this.Value;
    assume read($Heap, this, _module.Arm.Repr) == this.Repr;
    assume read($Heap, this, _module.Arm.polar) == this.polar;
    assume read($Heap, this, _module.Arm.azim) == this.azim;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(74,3)
}



procedure {:verboseName "Arm.Mutate (well-formedness)"} CheckWellFormed$$_module.Arm.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Arm())
         && $IsAlloc(this, Tclass._module.Arm(), $Heap), 
    polar_in#0: int, 
    azim_in#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Arm.Mutate (well-formedness)"} CheckWellFormed$$_module.Arm.Mutate(this: ref, polar_in#0: int, azim_in#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Mutate, CheckWellFormed$$_module.Arm.Mutate
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Arm.Repr)[$Box($o)]);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Arm?(), $Heap);
    assume _module.Arm.Valid#canCall($Heap, this);
    assume _module.Arm.Valid($Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.Arm.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Arm?(), $Heap);
    assume _module.Arm.Valid#canCall($Heap, this);
    assume _module.Arm.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.Arm(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.Arm.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Arm.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assume _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
      #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0)));
}



procedure {:verboseName "Arm.Mutate (call)"} Call$$_module.Arm.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Arm())
         && $IsAlloc(this, Tclass._module.Arm(), $Heap), 
    polar_in#0: int, 
    azim_in#0: int);
  // user-defined preconditions
  requires _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || read($Heap, this, _module.Arm.Repr)[$Box(this)];
  requires _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
          $Box(read($Heap, this, _module.Arm.azim))), 
        read($Heap, this, _module.Arm.Repr));
  requires _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim);
  requires _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
        #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Arm.Valid#canCall($Heap, this);
  free ensures _module.Arm.Valid#canCall($Heap, this)
     && 
    _module.Arm.Valid($Heap, this)
     && 
    read($Heap, this, _module.Arm.Repr)[$Box(this)]
     && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
        $Box(read($Heap, this, _module.Arm.azim))), 
      read($Heap, this, _module.Arm.Repr))
     && read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
     && _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
      #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Arm.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Arm.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple2(read($Heap, this, _module.Arm.Value));
  ensures _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
    #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Arm.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Arm.Mutate (correctness)"} Impl$$_module.Arm.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Arm())
         && $IsAlloc(this, Tclass._module.Arm(), $Heap), 
    polar_in#0: int, 
    azim_in#0: int)
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Arm.Valid#canCall($Heap, this)
     && 
    _module.Arm.Valid($Heap, this)
     && 
    read($Heap, this, _module.Arm.Repr)[$Box(this)]
     && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
        $Box(read($Heap, this, _module.Arm.azim))), 
      read($Heap, this, _module.Arm.Repr))
     && read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim)
     && _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
      #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
        $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Arm.Valid#canCall($Heap, this);
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || read($Heap, this, _module.Arm.Repr)[$Box(this)];
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Arm.polar))), 
          $Box(read($Heap, this, _module.Arm.azim))), 
        read($Heap, this, _module.Arm.Repr));
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || read($Heap, this, _module.Arm.polar) != read($Heap, this, _module.Arm.azim);
  ensures _module.Arm.Valid#canCall($Heap, this)
     ==> _module.Arm.Valid($Heap, this)
       || _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
        #_System._tuple#2._#Make2($Box(read($Heap, read($Heap, this, _module.Arm.polar), _module.Cell.val)), 
          $Box(read($Heap, read($Heap, this, _module.Arm.azim), _module.Cell.val))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Arm.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Arm.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures $IsA#_System.Tuple2(read($Heap, this, _module.Arm.Value));
  ensures _System.Tuple2#Equal(read($Heap, this, _module.Arm.Value), 
    #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Arm.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Arm.Mutate (correctness)"} Impl$$_module.Arm.Mutate(this: ref, polar_in#0: int, azim_in#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: DatatypeType;

    // AddMethodImpl: Mutate, Impl$$_module.Arm.Mutate
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Arm.Repr)[$Box($o)]);
    $_reverifyPost := false;
    // ----- update statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(87,25)
    assert read($Heap, this, _module.Arm.polar) != null;
    assume true;
    $obj0 := read($Heap, this, _module.Arm.polar);
    assert $_Frame[$obj0, _module.Cell.val];
    assert read($Heap, this, _module.Arm.azim) != null;
    assume true;
    $obj1 := read($Heap, this, _module.Arm.azim);
    assert $_Frame[$obj1, _module.Cell.val];
    assume true;
    $rhs#0 := polar_in#0;
    assume true;
    $rhs#1 := azim_in#0;
    assert read($Heap, this, _module.Arm.azim) != read($Heap, this, _module.Arm.polar)
       || $rhs#1 == $rhs#0;
    $Heap := update($Heap, $obj0, _module.Cell.val, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Cell.val, $rhs#1);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(88,11)
    assume true;
    assert $_Frame[this, _module.Arm.Value];
    assume true;
    $rhs#2 := #_System._tuple#2._#Make2($Box(polar_in#0), $Box(azim_in#0));
    $Heap := update($Heap, this, _module.Arm.Value, $rhs#2);
    assume $IsGoodHeap($Heap);
}



// _module.Arm: non-null type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Arm()) } 
  $Is(c#0, Tclass._module.Arm())
     <==> $Is(c#0, Tclass._module.Arm?()) && c#0 != null);

// _module.Arm: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Arm(), $h) } 
  $IsAlloc(c#0, Tclass._module.Arm(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Arm?(), $h));

const unique class._module.Bot?: ClassName;

function Tclass._module.Bot?() : Ty;

const unique Tagclass._module.Bot?: TyTag;

// Tclass._module.Bot? Tag
axiom Tag(Tclass._module.Bot?()) == Tagclass._module.Bot?
   && TagFamily(Tclass._module.Bot?()) == tytagFamily$Bot;

// Box/unbox axiom for Tclass._module.Bot?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Bot?()) } 
  $IsBox(bx, Tclass._module.Bot?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Bot?()));

// Bot: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Bot?()) } 
  $Is($o, Tclass._module.Bot?())
     <==> $o == null || dtype($o) == Tclass._module.Bot?());

// Bot: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Bot?(), $h) } 
  $IsAlloc($o, Tclass._module.Bot?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Bot.Repr) == 0
   && FieldOfDecl(class._module.Bot?, field$Repr) == _module.Bot.Repr
   && $IsGhostField(_module.Bot.Repr);

const _module.Bot.Repr: Field (Set Box);

// Bot.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Bot?()
     ==> $Is(read($h, $o, _module.Bot.Repr), TSet(Tclass._System.object())));

// Bot.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Bot?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Bot.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.Bot.Valid
function _module.Bot.Valid($ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.Bot.Valid#canCall($heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Bot.Valid($LS($ly), $Heap, this) } 
  _module.Bot.Valid($LS($ly), $Heap, this) == _module.Bot.Valid($ly, $Heap, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Bot.Valid(AsFuelBottom($ly), $Heap, this) } 
  _module.Bot.Valid($ly, $Heap, this) == _module.Bot.Valid($LZ, $Heap, this));

function Tclass._module.Bot() : Ty;

const unique Tagclass._module.Bot: TyTag;

// Tclass._module.Bot Tag
axiom Tag(Tclass._module.Bot()) == Tagclass._module.Bot
   && TagFamily(Tclass._module.Bot()) == tytagFamily$Bot;

// Box/unbox axiom for Tclass._module.Bot
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Bot()) } 
  $IsBox(bx, Tclass._module.Bot())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Bot()));

// frame axiom for _module.Bot.Valid
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Bot.Valid($ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Bot())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.Bot.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Bot.Valid($ly, $h0, this) == _module.Bot.Valid($ly, $h1, this));

// consequence axiom for _module.Bot.Valid
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Bot.Valid($ly, $Heap, this) } 
    _module.Bot.Valid#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap))
       ==> 
      _module.Bot.Valid($ly, $Heap, this)
       ==> read($Heap, this, _module.Bot.Repr)[$Box(this)]);

function _module.Bot.Valid#requires(LayerType, Heap, ref) : bool;

// #requires axiom for _module.Bot.Valid
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Bot.Valid#requires($ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Bot())
       && $IsAlloc(this, Tclass._module.Bot(), $Heap)
     ==> _module.Bot.Valid#requires($ly, $Heap, this) == true);

axiom FDim(_module.Bot.pos) == 0
   && FieldOfDecl(class._module.Bot?, field$pos) == _module.Bot.pos
   && !$IsGhostField(_module.Bot.pos);

axiom FDim(_module.Bot.left) == 0
   && FieldOfDecl(class._module.Bot?, field$left) == _module.Bot.left
   && !$IsGhostField(_module.Bot.left);

axiom FDim(_module.Bot.right) == 0
   && FieldOfDecl(class._module.Bot?, field$right) == _module.Bot.right
   && !$IsGhostField(_module.Bot.right);

// definition axiom for _module.Bot.Valid (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Bot.Valid($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.Bot.Valid#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap))
       ==> (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           ==> 
          read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           ==> 
          Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           ==> 
          Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
            read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr))
           ==> _module.Point.Valid#canCall($Heap, read($Heap, this, _module.Bot.pos))
             && (_module.Point.Valid($Heap, read($Heap, this, _module.Bot.pos))
               ==> _module.Arm.Valid#canCall($Heap, read($Heap, this, _module.Bot.left))
                 && (_module.Arm.Valid($Heap, read($Heap, this, _module.Bot.left))
                   ==> _module.Arm.Valid#canCall($Heap, read($Heap, this, _module.Bot.right)))))
         && _module.Bot.Valid($LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.Bot.Repr)[$Box(this)]
             && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
             && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
                $Box(read($Heap, this, _module.Bot.right))), 
              read($Heap, this, _module.Bot.Repr))
             && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
             && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, this, _module.Bot.Repr))
             && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
              read($Heap, this, _module.Bot.Repr))
             && Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
              read($Heap, this, _module.Bot.Repr))
             && 
            Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
             && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
             && Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
                read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr))
             && _module.Point.Valid($Heap, read($Heap, this, _module.Bot.pos))
             && _module.Arm.Valid($Heap, read($Heap, this, _module.Bot.left))
             && _module.Arm.Valid($Heap, read($Heap, this, _module.Bot.right))));

procedure {:verboseName "Bot.Valid (well-formedness)"} {:opaque} CheckWellformed$$_module.Bot.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this)
     ==> read($Heap, this, _module.Bot.Repr)[$Box(this)];



implementation {:verboseName "Bot.Valid (well-formedness)"} {:opaque} CheckWellformed$$_module.Bot.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
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

    // AddWellformednessCheck for function Valid
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Bot.Repr)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    b$reqreads#0 := $_Frame[this, _module.Bot.Repr];
    assert b$reqreads#0;
    if (*)
    {
        if (*)
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
            assert this == this
               || (Set#Subset(Set#Union(read($Heap, this, _module.Bot.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Bot.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.Bot.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Bot.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
            assume this == this || _module.Bot.Valid#canCall($Heap, this);
            assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
            assume read($Heap, this, _module.Bot.Repr)[$Box(this)];
        }
        else
        {
            assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this)
               ==> read($Heap, this, _module.Bot.Repr)[$Box(this)];
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Bot.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Bot.Repr];
        if (read($Heap, this, _module.Bot.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Bot.pos];
            b$reqreads#3 := $_Frame[this, _module.Bot.Repr];
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))])
        {
            b$reqreads#4 := $_Frame[this, _module.Bot.left];
            b$reqreads#5 := $_Frame[this, _module.Bot.right];
            b$reqreads#6 := $_Frame[this, _module.Bot.Repr];
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr)))
        {
            b$reqreads#7 := $_Frame[this, _module.Bot.left];
            b$reqreads#8 := $_Frame[this, _module.Bot.right];
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right))
        {
            b$reqreads#9 := $_Frame[this, _module.Bot.pos];
            assert read($Heap, this, _module.Bot.pos) != null;
            b$reqreads#10 := $_Frame[read($Heap, this, _module.Bot.pos), _module.Point.Repr];
            b$reqreads#11 := $_Frame[this, _module.Bot.Repr];
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr)))
        {
            b$reqreads#12 := $_Frame[this, _module.Bot.left];
            assert read($Heap, this, _module.Bot.left) != null;
            b$reqreads#13 := $_Frame[read($Heap, this, _module.Bot.left), _module.Arm.Repr];
            b$reqreads#14 := $_Frame[this, _module.Bot.Repr];
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr)))
        {
            b$reqreads#15 := $_Frame[this, _module.Bot.right];
            assert read($Heap, this, _module.Bot.right) != null;
            b$reqreads#16 := $_Frame[read($Heap, this, _module.Bot.right), _module.Arm.Repr];
            b$reqreads#17 := $_Frame[this, _module.Bot.Repr];
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr)))
        {
            b$reqreads#18 := $_Frame[this, _module.Bot.pos];
            assert read($Heap, this, _module.Bot.pos) != null;
            b$reqreads#19 := $_Frame[read($Heap, this, _module.Bot.pos), _module.Point.Repr];
            b$reqreads#20 := $_Frame[this, _module.Bot.left];
            assert read($Heap, this, _module.Bot.left) != null;
            b$reqreads#21 := $_Frame[read($Heap, this, _module.Bot.left), _module.Arm.Repr];
            if (Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)))
            {
                b$reqreads#22 := $_Frame[this, _module.Bot.pos];
                assert read($Heap, this, _module.Bot.pos) != null;
                b$reqreads#23 := $_Frame[read($Heap, this, _module.Bot.pos), _module.Point.Repr];
                b$reqreads#24 := $_Frame[this, _module.Bot.left];
                assert read($Heap, this, _module.Bot.left) != null;
                b$reqreads#25 := $_Frame[read($Heap, this, _module.Bot.left), _module.Arm.Repr];
            }

            if (Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
                read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
               && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
                read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)))
            {
                b$reqreads#26 := $_Frame[this, _module.Bot.pos];
                assert read($Heap, this, _module.Bot.pos) != null;
                b$reqreads#27 := $_Frame[read($Heap, this, _module.Bot.pos), _module.Point.Repr];
                b$reqreads#28 := $_Frame[this, _module.Bot.left];
                assert read($Heap, this, _module.Bot.left) != null;
                b$reqreads#29 := $_Frame[read($Heap, this, _module.Bot.left), _module.Arm.Repr];
                b$reqreads#30 := $_Frame[this, _module.Bot.right];
                assert read($Heap, this, _module.Bot.right) != null;
                b$reqreads#31 := $_Frame[read($Heap, this, _module.Bot.right), _module.Arm.Repr];
            }
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && 
          Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           && Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
            read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr)))
        {
            b$reqreads#32 := $_Frame[this, _module.Bot.pos];
            assert read($Heap, this, _module.Bot.pos) != null;
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(read($Heap, this, _module.Bot.pos), Tclass._module.Point?(), $Heap);
            b$reqreads#33 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.Bot.pos)
                     || read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.Point.Valid#canCall($Heap, read($Heap, this, _module.Bot.pos));
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && 
          Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           && Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
            read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr))
           && _module.Point.Valid($Heap, read($Heap, this, _module.Bot.pos)))
        {
            b$reqreads#34 := $_Frame[this, _module.Bot.left];
            assert read($Heap, this, _module.Bot.left) != null;
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(read($Heap, this, _module.Bot.left), Tclass._module.Arm?(), $Heap);
            b$reqreads#35 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.Bot.left)
                     || read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.Arm.Valid#canCall($Heap, read($Heap, this, _module.Bot.left));
        }

        if (read($Heap, this, _module.Bot.Repr)[$Box(this)]
           && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           && 
          Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
           && Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
            read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr))
           && _module.Point.Valid($Heap, read($Heap, this, _module.Bot.pos))
           && _module.Arm.Valid($Heap, read($Heap, this, _module.Bot.left)))
        {
            b$reqreads#36 := $_Frame[this, _module.Bot.right];
            assert read($Heap, this, _module.Bot.right) != null;
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(read($Heap, this, _module.Bot.right), Tclass._module.Arm?(), $Heap);
            b$reqreads#37 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.Bot.right)
                     || read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.Arm.Valid#canCall($Heap, read($Heap, this, _module.Bot.right));
        }

        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this)
           == (
            read($Heap, this, _module.Bot.Repr)[$Box(this)]
             && read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
             && Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
                $Box(read($Heap, this, _module.Bot.right))), 
              read($Heap, this, _module.Bot.Repr))
             && read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
             && Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, this, _module.Bot.Repr))
             && Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
              read($Heap, this, _module.Bot.Repr))
             && Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
              read($Heap, this, _module.Bot.Repr))
             && 
            Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
             && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
             && Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
                read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr))
             && _module.Point.Valid($Heap, read($Heap, this, _module.Bot.pos))
             && _module.Arm.Valid($Heap, read($Heap, this, _module.Bot.left))
             && _module.Arm.Valid($Heap, read($Heap, this, _module.Bot.right)));
        assume read($Heap, this, _module.Bot.Repr)[$Box(this)]
           ==> 
          read($Heap, this, _module.Bot.Repr)[$Box(read($Heap, this, _module.Bot.pos))]
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Bot.left))), 
              $Box(read($Heap, this, _module.Bot.right))), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          read($Heap, this, _module.Bot.left) != read($Heap, this, _module.Bot.right)
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr), 
            read($Heap, this, _module.Bot.Repr))
           ==> 
          Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
             && Set#Disjoint(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr))
             && Set#Disjoint(Set#Union(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr), 
                read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr))
           ==> _module.Point.Valid#canCall($Heap, read($Heap, this, _module.Bot.pos))
             && (_module.Point.Valid($Heap, read($Heap, this, _module.Bot.pos))
               ==> _module.Arm.Valid#canCall($Heap, read($Heap, this, _module.Bot.left))
                 && (_module.Arm.Valid($Heap, read($Heap, this, _module.Bot.left))
                   ==> _module.Arm.Valid#canCall($Heap, read($Heap, this, _module.Bot.right))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this), TBool);
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
    }
}



const _module.Bot.pos: Field ref;

// Bot.pos: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.pos) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Bot?()
     ==> $Is(read($h, $o, _module.Bot.pos), Tclass._module.Point()));

// Bot.pos: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.pos) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Bot?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Bot.pos), Tclass._module.Point(), $h));

const _module.Bot.left: Field ref;

// Bot.left: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.left) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Bot?()
     ==> $Is(read($h, $o, _module.Bot.left), Tclass._module.Arm()));

// Bot.left: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.left) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Bot?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Bot.left), Tclass._module.Arm(), $h));

const _module.Bot.right: Field ref;

// Bot.right: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.right) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Bot?()
     ==> $Is(read($h, $o, _module.Bot.right), Tclass._module.Arm()));

// Bot.right: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Bot.right) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Bot?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Bot.right), Tclass._module.Arm(), $h));

procedure {:verboseName "Bot._ctor (well-formedness)"} CheckWellFormed$$_module.Bot.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verboseName "Bot._ctor (call)"} Call$$_module.Bot.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, this);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Bot.Repr)[$Box($o)] } 
    read($Heap, this, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Bot._ctor (correctness)"} Impl$$_module.Bot.__ctor()
   returns (this: ref where this != null && $Is(this, Tclass._module.Bot()), 
    $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, this);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Bot.Repr)[$Box($o)] } 
    read($Heap, this, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Bot._ctor (correctness)"} Impl$$_module.Bot.__ctor() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Repr: Set Box;
  var this.pos: ref;
  var this.left: ref;
  var this.right: ref;
  var defass#this.pos: bool;
  var defass#this.left: bool;
  var defass#this.right: bool;
  var $nw: ref;
  var a##0: int;
  var b##0: int;
  var c##0: int;
  var polar_in##0: int;
  var azim_in##0: int;
  var polar_in##1: int;
  var azim_in##1: int;
  var $rhs#0: Set Box;

    // AddMethodImpl: _ctor, Impl$$_module.Bot.__ctor
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- divided block before new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(112,3)
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(113,9)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(113,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := LitInt(0);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Point.__ctor(a##0, b##0, c##0);
    // TrCallStmt: After ProcessCallStmt
    this.pos := $nw;
    defass#this.pos := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(114,10)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(114,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    polar_in##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    azim_in##0 := LitInt(0);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Arm.__ctor(polar_in##0, azim_in##0);
    // TrCallStmt: After ProcessCallStmt
    this.left := $nw;
    defass#this.left := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(115,11)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(115,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    polar_in##1 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    azim_in##1 := LitInt(0);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Arm.__ctor(polar_in##1, azim_in##1);
    // TrCallStmt: After ProcessCallStmt
    this.right := $nw;
    defass#this.right := true;
    // ----- new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(112,3)
    assert defass#this.pos;
    assert defass#this.left;
    assert defass#this.right;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Bot.Repr) == this.Repr;
    assume read($Heap, this, _module.Bot.pos) == this.pos;
    assume read($Heap, this, _module.Bot.left) == this.left;
    assume read($Heap, this, _module.Bot.right) == this.right;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(112,3)
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(117,10)
    assume true;
    assert $_Frame[this, _module.Bot.Repr];
    assert read($Heap, this, _module.Bot.pos) != null;
    assert read($Heap, this, _module.Bot.left) != null;
    assert read($Heap, this, _module.Bot.right) != null;
    assume true;
    $rhs#0 := Set#Union(Set#Union(Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
          read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Repr)), 
        read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Repr)), 
      read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.Repr));
    $Heap := update($Heap, this, _module.Bot.Repr, $rhs#0);
    assume $IsGoodHeap($Heap);
    // ----- reveal statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(118,5)
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(118,17)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.reveal__Valid(this);
    // TrCallStmt: After ProcessCallStmt
}



// function declaration for _module.Bot.flying
function _module.Bot.flying($heap: Heap, this: ref) : bool;

function _module.Bot.flying#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Bot.flying
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Bot.flying($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Bot())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($h0, this, _module.Bot.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Bot.flying($h0, this) == _module.Bot.flying($h1, this));

// consequence axiom for _module.Bot.flying
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Bot.flying($Heap, this) } 
    _module.Bot.flying#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap)
           && _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this))
       ==> true);

function _module.Bot.flying#requires(Heap, ref) : bool;

// #requires axiom for _module.Bot.flying
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Bot.flying#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Bot())
       && $IsAlloc(this, Tclass._module.Bot(), $Heap)
     ==> _module.Bot.flying#requires($Heap, this)
       == _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this));

// definition axiom for _module.Bot.flying (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Bot.flying($Heap, this), $IsGoodHeap($Heap) } 
    _module.Bot.flying#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap)
           && _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this))
       ==> _module.Bot.flying($Heap, this)
         == (read($Heap, 
            read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), 
            _module.Cell.val)
           > 0));

procedure {:verboseName "Bot.flying (well-formedness)"} CheckWellformed$$_module.Bot.flying(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Bot.flying (well-formedness)"} CheckWellformed$$_module.Bot.flying(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    // AddWellformednessCheck for function flying
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    // ----- reveal statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(122,15)
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(122,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.reveal__Valid(this);
    // TrCallStmt: After ProcessCallStmt
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.Bot.Valid#canCall($Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.Bot.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.Bot.pos];
        assert read($Heap, this, _module.Bot.pos) != null;
        b$reqreads#3 := $_Frame[read($Heap, this, _module.Bot.pos), _module.Point.z];
        assert read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z) != null;
        b$reqreads#4 := $_Frame[read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), _module.Cell.val];
        assume _module.Bot.flying($Heap, this)
           == (read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), 
              _module.Cell.val)
             > 0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Bot.flying($Heap, this), TBool);
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
    }
}



// function declaration for _module.Bot.arms_up
function _module.Bot.arms__up($heap: Heap, this: ref) : bool;

function _module.Bot.arms__up#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Bot.arms__up
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Bot.arms__up($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Bot())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($h0, this, _module.Bot.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Bot.arms__up($h0, this) == _module.Bot.arms__up($h1, this));

// consequence axiom for _module.Bot.arms__up
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Bot.arms__up($Heap, this) } 
    _module.Bot.arms__up#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap)
           && _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this))
       ==> true);

function _module.Bot.arms__up#requires(Heap, ref) : bool;

// #requires axiom for _module.Bot.arms__up
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Bot.arms__up#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Bot())
       && $IsAlloc(this, Tclass._module.Bot(), $Heap)
     ==> _module.Bot.arms__up#requires($Heap, this)
       == _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this));

// definition axiom for _module.Bot.arms__up (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Bot.arms__up($Heap, this), $IsGoodHeap($Heap) } 
    _module.Bot.arms__up#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap)
           && _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this))
       ==> _module.Bot.arms__up($Heap, this)
         == (read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar), 
              _module.Cell.val)
             == read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val)
           && read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val)
             == LitInt(0)));

procedure {:verboseName "Bot.arms_up (well-formedness)"} CheckWellformed$$_module.Bot.arms__up(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Bot.arms_up (well-formedness)"} CheckWellformed$$_module.Bot.arms__up(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
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

    // AddWellformednessCheck for function arms_up
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    // ----- reveal statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(129,15)
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(129,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.reveal__Valid(this);
    // TrCallStmt: After ProcessCallStmt
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.Bot.Valid#canCall($Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.Bot.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.Bot.left];
        assert read($Heap, this, _module.Bot.left) != null;
        b$reqreads#3 := $_Frame[read($Heap, this, _module.Bot.left), _module.Arm.polar];
        assert read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar) != null;
        b$reqreads#4 := $_Frame[read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar), _module.Cell.val];
        b$reqreads#5 := $_Frame[this, _module.Bot.right];
        assert read($Heap, this, _module.Bot.right) != null;
        b$reqreads#6 := $_Frame[read($Heap, this, _module.Bot.right), _module.Arm.polar];
        assert read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar) != null;
        b$reqreads#7 := $_Frame[read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), _module.Cell.val];
        if (read($Heap, 
            read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar), 
            _module.Cell.val)
           == read($Heap, 
            read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
            _module.Cell.val))
        {
            b$reqreads#8 := $_Frame[this, _module.Bot.right];
            assert read($Heap, this, _module.Bot.right) != null;
            b$reqreads#9 := $_Frame[read($Heap, this, _module.Bot.right), _module.Arm.polar];
            assert read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar) != null;
            b$reqreads#10 := $_Frame[read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), _module.Cell.val];
        }

        assume _module.Bot.arms__up($Heap, this)
           == (read($Heap, 
                read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar), 
                _module.Cell.val)
               == read($Heap, 
                read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
                _module.Cell.val)
             && read($Heap, 
                read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
                _module.Cell.val)
               == LitInt(0));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Bot.arms__up($Heap, this), TBool);
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
        assert b$reqreads#10;
    }
}



// function declaration for _module.Bot.robot_inv
function _module.Bot.robot__inv($heap: Heap, this: ref) : bool;

function _module.Bot.robot__inv#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Bot.robot__inv
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Bot.robot__inv($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Bot())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($h0, this, _module.Bot.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Bot.robot__inv($h0, this) == _module.Bot.robot__inv($h1, this));

// consequence axiom for _module.Bot.robot__inv
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Bot.robot__inv($Heap, this) } 
    _module.Bot.robot__inv#canCall($Heap, this)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap)
           && _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this))
       ==> true);

function _module.Bot.robot__inv#requires(Heap, ref) : bool;

// #requires axiom for _module.Bot.robot__inv
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Bot.robot__inv#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Bot())
       && $IsAlloc(this, Tclass._module.Bot(), $Heap)
     ==> _module.Bot.robot__inv#requires($Heap, this)
       == _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this));

// definition axiom for _module.Bot.robot__inv (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Bot.robot__inv($Heap, this), $IsGoodHeap($Heap) } 
    _module.Bot.robot__inv#canCall($Heap, this)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Bot())
           && $IsAlloc(this, Tclass._module.Bot(), $Heap)
           && _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this))
       ==> _module.Bot.flying#canCall($Heap, this)
         && (_module.Bot.flying($Heap, this) ==> _module.Bot.arms__up#canCall($Heap, this))
         && _module.Bot.robot__inv($Heap, this)
           == (_module.Bot.flying($Heap, this) ==> _module.Bot.arms__up($Heap, this)));

procedure {:verboseName "Bot.robot_inv (well-formedness)"} CheckWellformed$$_module.Bot.robot__inv(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Bot.robot_inv (well-formedness)"} CheckWellformed$$_module.Bot.robot__inv(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function robot_inv
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    // ----- reveal statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(136,15)
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(136,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.reveal__Valid(this);
    // TrCallStmt: After ProcessCallStmt
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.Bot.Valid#canCall($Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.Bot.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, this, _module.Bot.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.Bot.flying#canCall($Heap, this);
        if (_module.Bot.flying($Heap, this))
        {
            // assume allocatedness for receiver argument to function
            assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
            assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
            assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && read($Heap, this, _module.Bot.Repr)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume _module.Bot.arms__up#canCall($Heap, this);
        }

        assume _module.Bot.robot__inv($Heap, this)
           == (_module.Bot.flying($Heap, this) ==> _module.Bot.arms__up($Heap, this));
        assume _module.Bot.flying#canCall($Heap, this)
           && (_module.Bot.flying($Heap, this) ==> _module.Bot.arms__up#canCall($Heap, this));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Bot.robot__inv($Heap, this), TBool);
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure {:verboseName "Bot.Fly (well-formedness)"} CheckWellFormed$$_module.Bot.Fly(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "Bot.Fly (well-formedness)"} CheckWellFormed$$_module.Bot.Fly(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fly, CheckWellFormed$$_module.Bot.Fly
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.Bot.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    assert $IsAlloc(this, Tclass._module.Bot(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.Bot.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Bot.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    assume _module.Bot.robot__inv#canCall($Heap, this);
    assume _module.Bot.robot__inv($Heap, this);
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(this, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, this);
    assume _module.Bot.flying#canCall($Heap, this);
    assume _module.Bot.flying($Heap, this);
}



procedure {:verboseName "Bot.Fly (call)"} Call$$_module.Bot.Fly(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  // user-defined preconditions
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, this);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures _module.Bot.robot__inv#canCall($Heap, this)
     && (_module.Bot.robot__inv($Heap, this)
       ==> _module.Bot.flying#canCall($Heap, this));
  free ensures _module.Bot.robot__inv#canCall($Heap, this)
     && 
    _module.Bot.robot__inv($Heap, this)
     && (_module.Bot.flying($Heap, this) ==> _module.Bot.arms__up($Heap, this));
  free ensures _module.Bot.flying#canCall($Heap, this)
     && 
    _module.Bot.flying($Heap, this)
     && read($Heap, 
        read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), 
        _module.Cell.val)
       > 0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Bot.Fly (correctness)"} Impl$$_module.Bot.Fly(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, this);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, this);
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures _module.Bot.robot__inv#canCall($Heap, this)
     && (_module.Bot.robot__inv($Heap, this)
       ==> _module.Bot.flying#canCall($Heap, this));
  ensures _module.Bot.robot__inv#canCall($Heap, this)
     ==> _module.Bot.robot__inv($Heap, this)
       || (_module.Bot.flying($Heap, this)
         ==> 
        _module.Bot.arms__up#canCall($Heap, this)
         ==> _module.Bot.arms__up($Heap, this)
           || read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar), 
              _module.Cell.val)
             == read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val));
  ensures _module.Bot.robot__inv#canCall($Heap, this)
     ==> _module.Bot.robot__inv($Heap, this)
       || (_module.Bot.flying($Heap, this)
         ==> 
        _module.Bot.arms__up#canCall($Heap, this)
         ==> _module.Bot.arms__up($Heap, this)
           || read($Heap, 
              read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val)
             == LitInt(0));
  ensures _module.Bot.flying#canCall($Heap, this)
     ==> _module.Bot.flying($Heap, this)
       || read($Heap, 
          read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), 
          _module.Cell.val)
         > 0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "Bot.Fly (correctness)"} Impl$$_module.Bot.Fly(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: DatatypeType;
  var $rhs#5: DatatypeType;
  var $rhs#6: DatatypeType;

    // AddMethodImpl: Fly, Impl$$_module.Bot.Fly
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Bot.Repr)[$Box($o)]);
    $_reverifyPost := false;
    // ----- reveal statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(148,5)
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(148,17)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.reveal__Valid(this);
    // TrCallStmt: After ProcessCallStmt
    // ----- update statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(149,37)
    assert read($Heap, this, _module.Bot.left) != null;
    assert read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar) != null;
    assume true;
    $obj0 := read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar);
    assert $_Frame[$obj0, _module.Cell.val];
    assert read($Heap, this, _module.Bot.right) != null;
    assert read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar) != null;
    assume true;
    $obj1 := read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar);
    assert $_Frame[$obj1, _module.Cell.val];
    assume true;
    $rhs#0 := LitInt(0);
    assume true;
    $rhs#1 := LitInt(0);
    assert read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.polar)
         != read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.polar)
       || $rhs#1 == $rhs#0;
    $Heap := update($Heap, $obj0, _module.Cell.val, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Cell.val, $rhs#1);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(150,15)
    assert read($Heap, this, _module.Bot.pos) != null;
    assert read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z) != null;
    assume true;
    assert $_Frame[read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), _module.Cell.val];
    assume true;
    $rhs#2 := LitInt(100);
    $Heap := update($Heap, 
      read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.z), 
      _module.Cell.val, 
      $rhs#2);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(151,20)
    assert read($Heap, this, _module.Bot.right) != null;
    assert read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.azim) != null;
    assume true;
    assert $_Frame[read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.azim), _module.Cell.val];
    assume true;
    $rhs#3 := LitInt(17);
    $Heap := update($Heap, 
      read($Heap, read($Heap, this, _module.Bot.right), _module.Arm.azim), 
      _module.Cell.val, 
      $rhs#3);
    assume $IsGoodHeap($Heap);
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(152,15)
    assert read($Heap, this, _module.Bot.pos) != null;
    assume true;
    assert $_Frame[read($Heap, this, _module.Bot.pos), _module.Point.Value];
    assert read($Heap, this, _module.Bot.pos) != null;
    assume _System.Tuple3.___hMake3_q(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value));
    assert read($Heap, this, _module.Bot.pos) != null;
    assume _System.Tuple3.___hMake3_q(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value));
    assume _System.Tuple3.___hMake3_q(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value))
       && _System.Tuple3.___hMake3_q(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value));
    $rhs#4 := #_System._tuple#3._#Make3(_System.Tuple3._0(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value)), 
      _System.Tuple3._1(read($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value)), 
      $Box(LitInt(100)));
    $Heap := update($Heap, read($Heap, this, _module.Bot.pos), _module.Point.Value, $rhs#4);
    assume $IsGoodHeap($Heap);
    // ----- update statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(153,29)
    assert read($Heap, this, _module.Bot.left) != null;
    assume true;
    $obj0 := read($Heap, this, _module.Bot.left);
    assert $_Frame[$obj0, _module.Arm.Value];
    assert read($Heap, this, _module.Bot.right) != null;
    assume true;
    $obj1 := read($Heap, this, _module.Bot.right);
    assert $_Frame[$obj1, _module.Arm.Value];
    assert read($Heap, this, _module.Bot.left) != null;
    assume _System.Tuple2.___hMake2_q(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Value));
    assume _System.Tuple2.___hMake2_q(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Value));
    $rhs#5 := #_System._tuple#2._#Make2($Box(LitInt(0)), 
      _System.Tuple2._1(read($Heap, read($Heap, this, _module.Bot.left), _module.Arm.Value)));
    assume true;
    $rhs#6 := Lit(#_System._tuple#2._#Make2($Box(LitInt(0)), $Box(LitInt(17))));
    assert read($Heap, this, _module.Bot.right) != read($Heap, this, _module.Bot.left)
       || $rhs#6 == $rhs#5;
    $Heap := update($Heap, $obj0, _module.Arm.Value, $rhs#5);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Arm.Value, $rhs#6);
    assume $IsGoodHeap($Heap);
    // ----- reveal statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(154,5)
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(154,17)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.reveal__Valid(this);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "Bot.reveal_Valid (well-formedness)"} {:auto_generated} {:opaque_reveal} {:verify false} CheckWellFormed$$_module.Bot.reveal__Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel__module.Bot.Valid0: LayerType;

procedure {:verboseName "Bot.reveal_Valid (call)"} {:auto_generated} {:opaque_reveal} {:verify false} Call$$_module.Bot.reveal__Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bot())
         && $IsAlloc(this, Tclass._module.Bot(), $Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel__module.Bot.Valid == $LS(MoreFuel__module.Bot.Valid0);
  free ensures StartFuelAssert__module.Bot.Valid == $LS($LS(MoreFuel__module.Bot.Valid0));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel__module.Bot.Valid0) == MoreFuel__module.Bot.Valid0;



// _module.Bot: non-null type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Bot()) } 
  $Is(c#0, Tclass._module.Bot())
     <==> $Is(c#0, Tclass._module.Bot?()) && c#0 != null);

// _module.Bot: non-null type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Bot(), $h) } 
  $IsAlloc(c#0, Tclass._module.Bot(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Bot?(), $h));

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

procedure {:verboseName "FlyRobots (well-formedness)"} CheckWellFormed$$_module.__default.FlyRobots(b0#0: ref
       where $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap), 
    b1#0: ref
       where $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "FlyRobots (well-formedness)"} CheckWellFormed$$_module.__default.FlyRobots(b0#0: ref, b1#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: FlyRobots, CheckWellFormed$$_module.__default.FlyRobots
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]);
    assert b0#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b0#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b0#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0);
    assert b1#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b1#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b1#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0);
    if (*)
    {
        assume b0#0 != b1#0;
        assert b0#0 != null;
        assert b1#0 != null;
        assume Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
    }
    else
    {
        assume b0#0 != b1#0
           ==> Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
    }

    assert b0#0 != null;
    assert b1#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
           || read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assert b0#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b0#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b0#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0);
    assert b0#0 != null;
    assert b0#0 != null;
    assert $IsAlloc(b0#0, Tclass._module.Bot(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           && !read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert b1#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b1#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b1#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0);
    assert b1#0 != null;
    assert b1#0 != null;
    assert $IsAlloc(b1#0, Tclass._module.Bot(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
           && !read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    if (*)
    {
        assume b0#0 != b1#0;
        assert b0#0 != null;
        assert b1#0 != null;
        assume Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
    }
    else
    {
        assume b0#0 != b1#0
           ==> Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
    }

    assert b0#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b0#0, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0);
    assume _module.Bot.robot__inv#canCall($Heap, b0#0);
    assume _module.Bot.robot__inv($Heap, b0#0);
    assert b1#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b1#0, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0);
    assume _module.Bot.robot__inv#canCall($Heap, b1#0);
    assume _module.Bot.robot__inv($Heap, b1#0);
    assert b0#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b0#0, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0);
    assume _module.Bot.flying#canCall($Heap, b0#0);
    assume _module.Bot.flying($Heap, b0#0);
    assert b1#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b1#0, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0);
    assume _module.Bot.flying#canCall($Heap, b1#0);
    assume _module.Bot.flying($Heap, b1#0);
}



procedure {:verboseName "FlyRobots (call)"} Call$$_module.__default.FlyRobots(b0#0: ref
       where $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap), 
    b1#0: ref
       where $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap));
  // user-defined preconditions
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  requires b0#0 != b1#0
     ==> Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, b0#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures _module.Bot.Valid#canCall($Heap, b1#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures b0#0 != b1#0
     ==> Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  free ensures _module.Bot.robot__inv#canCall($Heap, b0#0)
     && (_module.Bot.robot__inv($Heap, b0#0)
       ==> _module.Bot.robot__inv#canCall($Heap, b1#0));
  free ensures _module.Bot.robot__inv#canCall($Heap, b0#0)
     && 
    _module.Bot.robot__inv($Heap, b0#0)
     && (_module.Bot.flying($Heap, b0#0) ==> _module.Bot.arms__up($Heap, b0#0));
  free ensures _module.Bot.robot__inv#canCall($Heap, b1#0)
     && 
    _module.Bot.robot__inv($Heap, b1#0)
     && (_module.Bot.flying($Heap, b1#0) ==> _module.Bot.arms__up($Heap, b1#0));
  free ensures _module.Bot.flying#canCall($Heap, b0#0)
     && (_module.Bot.flying($Heap, b0#0) ==> _module.Bot.flying#canCall($Heap, b1#0));
  free ensures _module.Bot.flying#canCall($Heap, b0#0)
     && 
    _module.Bot.flying($Heap, b0#0)
     && read($Heap, 
        read($Heap, read($Heap, b0#0, _module.Bot.pos), _module.Point.z), 
        _module.Cell.val)
       > 0;
  free ensures _module.Bot.flying#canCall($Heap, b1#0)
     && 
    _module.Bot.flying($Heap, b1#0)
     && read($Heap, 
        read($Heap, read($Heap, b1#0, _module.Bot.pos), _module.Point.z), 
        _module.Cell.val)
       > 0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
         || read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "FlyRobots (correctness)"} Impl$$_module.__default.FlyRobots(b0#0: ref
       where $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap), 
    b1#0: ref
       where $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  requires b0#0 != b1#0
     ==> Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, b0#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures _module.Bot.Valid#canCall($Heap, b1#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures b0#0 != b1#0
     ==> Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  free ensures _module.Bot.robot__inv#canCall($Heap, b0#0)
     && (_module.Bot.robot__inv($Heap, b0#0)
       ==> _module.Bot.robot__inv#canCall($Heap, b1#0));
  ensures _module.Bot.robot__inv#canCall($Heap, b0#0)
     ==> _module.Bot.robot__inv($Heap, b0#0)
       || (_module.Bot.flying($Heap, b0#0)
         ==> 
        _module.Bot.arms__up#canCall($Heap, b0#0)
         ==> _module.Bot.arms__up($Heap, b0#0)
           || read($Heap, 
              read($Heap, read($Heap, b0#0, _module.Bot.left), _module.Arm.polar), 
              _module.Cell.val)
             == read($Heap, 
              read($Heap, read($Heap, b0#0, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val));
  ensures _module.Bot.robot__inv#canCall($Heap, b0#0)
     ==> _module.Bot.robot__inv($Heap, b0#0)
       || (_module.Bot.flying($Heap, b0#0)
         ==> 
        _module.Bot.arms__up#canCall($Heap, b0#0)
         ==> _module.Bot.arms__up($Heap, b0#0)
           || read($Heap, 
              read($Heap, read($Heap, b0#0, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val)
             == LitInt(0));
  ensures _module.Bot.robot__inv#canCall($Heap, b1#0)
     ==> _module.Bot.robot__inv($Heap, b1#0)
       || (_module.Bot.flying($Heap, b1#0)
         ==> 
        _module.Bot.arms__up#canCall($Heap, b1#0)
         ==> _module.Bot.arms__up($Heap, b1#0)
           || read($Heap, 
              read($Heap, read($Heap, b1#0, _module.Bot.left), _module.Arm.polar), 
              _module.Cell.val)
             == read($Heap, 
              read($Heap, read($Heap, b1#0, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val));
  ensures _module.Bot.robot__inv#canCall($Heap, b1#0)
     ==> _module.Bot.robot__inv($Heap, b1#0)
       || (_module.Bot.flying($Heap, b1#0)
         ==> 
        _module.Bot.arms__up#canCall($Heap, b1#0)
         ==> _module.Bot.arms__up($Heap, b1#0)
           || read($Heap, 
              read($Heap, read($Heap, b1#0, _module.Bot.right), _module.Arm.polar), 
              _module.Cell.val)
             == LitInt(0));
  free ensures _module.Bot.flying#canCall($Heap, b0#0)
     && (_module.Bot.flying($Heap, b0#0) ==> _module.Bot.flying#canCall($Heap, b1#0));
  ensures _module.Bot.flying#canCall($Heap, b0#0)
     ==> _module.Bot.flying($Heap, b0#0)
       || read($Heap, 
          read($Heap, read($Heap, b0#0, _module.Bot.pos), _module.Point.z), 
          _module.Cell.val)
         > 0;
  ensures _module.Bot.flying#canCall($Heap, b1#0)
     ==> _module.Bot.flying($Heap, b1#0)
       || read($Heap, 
          read($Heap, read($Heap, b1#0, _module.Bot.pos), _module.Point.z), 
          _module.Cell.val)
         > 0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
         || read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "FlyRobots (correctness)"} Impl$$_module.__default.FlyRobots(b0#0: ref, b1#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: FlyRobots, Impl$$_module.__default.FlyRobots
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]);
    $_reverifyPost := false;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(170,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert b0#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.Fly(b0#0);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(171,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert b1#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.Fly(b1#0);
    // TrCallStmt: After ProcessCallStmt
}



// function declaration for _module._default.ArmyRepr
function _module.__default.ArmyRepr($heap: Heap, bots#0: Seq Box) : Set Box;

function _module.__default.ArmyRepr#canCall($heap: Heap, bots#0: Seq Box) : bool;

// frame axiom for _module.__default.ArmyRepr
axiom (forall $h0: Heap, $h1: Heap, bots#0: Seq Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ArmyRepr($h1, bots#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ArmyRepr#canCall($h0, bots#0)
         || $Is(bots#0, TSeq(Tclass._module.Bot())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $Is($o, Tclass._module.Bot()) && Seq#Contains(bots#0, $Box($o))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ArmyRepr($h0, bots#0)
       == _module.__default.ArmyRepr($h1, bots#0));

// consequence axiom for _module.__default.ArmyRepr
axiom 1 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, bots#0: Seq Box :: 
    { _module.__default.ArmyRepr($Heap, bots#0) } 
    _module.__default.ArmyRepr#canCall($Heap, bots#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(bots#0, TSeq(Tclass._module.Bot())))
       ==> $Is(_module.__default.ArmyRepr($Heap, bots#0), TSet(Tclass._System.object())));

function _module.__default.ArmyRepr#requires(Heap, Seq Box) : bool;

// #requires axiom for _module.__default.ArmyRepr
axiom (forall $Heap: Heap, bots#0: Seq Box :: 
  { _module.__default.ArmyRepr#requires($Heap, bots#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(bots#0, TSeq(Tclass._module.Bot()))
     ==> _module.__default.ArmyRepr#requires($Heap, bots#0) == true);

// definition axiom for _module.__default.ArmyRepr (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, bots#0: Seq Box :: 
    { _module.__default.ArmyRepr($Heap, bots#0), $IsGoodHeap($Heap) } 
    _module.__default.ArmyRepr#canCall($Heap, bots#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(bots#0, TSeq(Tclass._module.Bot())))
       ==> _module.__default.ArmyRepr($Heap, bots#0)
         == (lambda $y#0: Box :: 
          (exists b#0: ref, o#0: ref :: 
            { read($Heap, b#0, _module.Bot.Repr)[$Box(o#0)] } 
            $Is(b#0, Tclass._module.Bot())
               && $Is(o#0, Tclass._System.object())
               && 
              Seq#Contains(bots#0, $Box(b#0))
               && read($Heap, b#0, _module.Bot.Repr)[$Box(o#0)]
               && $y#0 == $Box(o#0))));

procedure {:verboseName "ArmyRepr (well-formedness)"} CheckWellformed$$_module.__default.ArmyRepr(bots#0: Seq Box where $Is(bots#0, TSeq(Tclass._module.Bot())));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "ArmyRepr (well-formedness)"} CheckWellformed$$_module.__default.ArmyRepr(bots#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#1: ref;
  var b#2: ref;
  var b#3: ref;
  var o#1: ref;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ArmyRepr
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $Is($o, Tclass._module.Bot()) && Seq#Contains(bots#0, $Box($o)));
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    // Begin Comprehension WF check
    havoc b#1;
    if ($Is(b#1, Tclass._module.Bot()) && $IsAlloc(b#1, Tclass._module.Bot(), $Heap))
    {
        if (Seq#Contains(bots#0, $Box(b#1)))
        {
        }
    }

    // End Comprehension WF check
    // Begin Comprehension WF check
    havoc b#2;
    if ($Is(b#2, Tclass._module.Bot()) && $IsAlloc(b#2, Tclass._module.Bot(), $Heap))
    {
        if (Seq#Contains(bots#0, $Box(b#2)))
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume $Is(_module.__default.ArmyRepr($Heap, bots#0), TSet(Tclass._System.object()));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $Is($o, Tclass._module.Bot()) && Seq#Contains(bots#0, $Box($o)));
        // Begin Comprehension WF check
        havoc b#3;
        havoc o#1;
        if ($Is(b#3, Tclass._module.Bot())
           && $IsAlloc(b#3, Tclass._module.Bot(), $Heap)
           && 
          $Is(o#1, Tclass._System.object())
           && $IsAlloc(o#1, Tclass._System.object(), $Heap))
        {
            if (Seq#Contains(bots#0, $Box(b#3)))
            {
                assert b#3 != null;
                b$reqreads#0 := $_Frame[b#3, _module.Bot.Repr];
            }

            if (Seq#Contains(bots#0, $Box(b#3)) && read($Heap, b#3, _module.Bot.Repr)[$Box(o#1)])
            {
            }
        }

        // End Comprehension WF check
        assume _module.__default.ArmyRepr($Heap, bots#0)
           == (lambda $y#1: Box :: 
            (exists b#4: ref, o#2: ref :: 
              { read($Heap, b#4, _module.Bot.Repr)[$Box(o#2)] } 
              $Is(b#4, Tclass._module.Bot())
                 && $Is(o#2, Tclass._System.object())
                 && 
                Seq#Contains(bots#0, $Box(b#4))
                 && read($Heap, b#4, _module.Bot.Repr)[$Box(o#2)]
                 && $y#1 == $Box(o#2)));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ArmyRepr($Heap, bots#0), TSet(Tclass._System.object()));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ValidArmy
function _module.__default.ValidArmy($heap: Heap, bots#0: Seq Box) : bool;

function _module.__default.ValidArmy#canCall($heap: Heap, bots#0: Seq Box) : bool;

// frame axiom for _module.__default.ValidArmy
axiom (forall $h0: Heap, $h1: Heap, bots#0: Seq Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ValidArmy($h1, bots#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ValidArmy#canCall($h0, bots#0)
         || $Is(bots#0, TSeq(Tclass._module.Bot())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (($Is($o, Tclass._module.Bot()) && Seq#Contains(bots#0, $Box($o)))
             || _module.__default.ArmyRepr($h0, bots#0)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ValidArmy($h0, bots#0)
       == _module.__default.ValidArmy($h1, bots#0));

// consequence axiom for _module.__default.ValidArmy
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, bots#0: Seq Box :: 
    { _module.__default.ValidArmy($Heap, bots#0) } 
    _module.__default.ValidArmy#canCall($Heap, bots#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(bots#0, TSeq(Tclass._module.Bot())))
       ==> true);

function _module.__default.ValidArmy#requires(Heap, Seq Box) : bool;

// #requires axiom for _module.__default.ValidArmy
axiom (forall $Heap: Heap, bots#0: Seq Box :: 
  { _module.__default.ValidArmy#requires($Heap, bots#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(bots#0, TSeq(Tclass._module.Bot()))
     ==> _module.__default.ValidArmy#requires($Heap, bots#0) == true);

// definition axiom for _module.__default.ValidArmy (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, bots#0: Seq Box :: 
    { _module.__default.ValidArmy($Heap, bots#0), $IsGoodHeap($Heap) } 
    _module.__default.ValidArmy#canCall($Heap, bots#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(bots#0, TSeq(Tclass._module.Bot())))
       ==> (forall i#0: int :: 
          { $Unbox(Seq#Index(bots#0, i#0)): ref } 
          LitInt(0) <= i#0
             ==> 
            i#0 < Seq#Length(bots#0)
             ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, i#0)): ref))
         && _module.__default.ValidArmy($Heap, bots#0)
           == ((forall i#0: int :: 
              { $Unbox(Seq#Index(bots#0, i#0)): ref } 
              true
                 ==> 
                LitInt(0) <= i#0 && i#0 < Seq#Length(bots#0)
                 ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#0)): ref))
             && (forall i#1: int, j#0: int :: 
              { $Unbox(Seq#Index(bots#0, j#0)): ref, $Unbox(Seq#Index(bots#0, i#1)): ref } 
              true
                 ==> 
                LitInt(0) <= i#1 && i#1 < j#0 && j#0 < Seq#Length(bots#0)
                 ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr), 
                  read($Heap, $Unbox(Seq#Index(bots#0, j#0)): ref, _module.Bot.Repr)))));

procedure {:verboseName "ValidArmy (well-formedness)"} CheckWellformed$$_module.__default.ValidArmy(bots#0: Seq Box where $Is(bots#0, TSeq(Tclass._module.Bot())));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "ValidArmy (well-formedness)"} CheckWellformed$$_module.__default.ValidArmy(bots#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#0: ref;
  var ##bots#0: Seq Box;
  var b$reqreads#0: bool;
  var b#1: ref;
  var ##bots#1: Seq Box;
  var i#2: int;
  var i#3: int;
  var j#1: int;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function ValidArmy
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> ($Is($o, Tclass._module.Bot()) && Seq#Contains(bots#0, $Box($o)))
           || _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    // Begin Comprehension WF check
    havoc b#0;
    if ($Is(b#0, Tclass._module.Bot()) && $IsAlloc(b#0, Tclass._module.Bot(), $Heap))
    {
        if (Seq#Contains(bots#0, $Box(b#0)))
        {
        }
    }

    // End Comprehension WF check
    ##bots#0 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#0, TSeq(Tclass._module.Bot()), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && 
          $Is($o, Tclass._module.Bot())
           && Seq#Contains(##bots#0, $Box($o))
         ==> $_Frame[$o, $f]);
    assume _module.__default.ArmyRepr#canCall($Heap, bots#0);
    assert b$reqreads#0;
    // Begin Comprehension WF check
    havoc b#1;
    if ($Is(b#1, Tclass._module.Bot()) && $IsAlloc(b#1, Tclass._module.Bot(), $Heap))
    {
        if (Seq#Contains(bots#0, $Box(b#1)))
        {
        }
    }

    // End Comprehension WF check
    ##bots#1 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#1, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ArmyRepr#canCall($Heap, bots#0);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> ($Is($o, Tclass._module.Bot()) && Seq#Contains(bots#0, $Box($o)))
               || _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]);
        // Begin Comprehension WF check
        havoc i#2;
        if (true)
        {
            if (LitInt(0) <= i#2)
            {
            }

            if (LitInt(0) <= i#2 && i#2 < Seq#Length(bots#0))
            {
                assert 0 <= i#2 && i#2 < Seq#Length(bots#0);
                assert $Unbox(Seq#Index(bots#0, i#2)): ref != null;
                // assume allocatedness for receiver argument to function
                assume $IsAlloc($Unbox(Seq#Index(bots#0, i#2)): ref, Tclass._module.Bot?(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && ($o == $Unbox(Seq#Index(bots#0, i#2)): ref
                         || read($Heap, $Unbox(Seq#Index(bots#0, i#2)): ref, _module.Bot.Repr)[$Box($o)])
                     ==> $_Frame[$o, $f]);
                assume _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, i#2)): ref);
            }
        }

        // End Comprehension WF check
        if ((forall i#4: int :: 
          { $Unbox(Seq#Index(bots#0, i#4)): ref } 
          true
             ==> 
            LitInt(0) <= i#4 && i#4 < Seq#Length(bots#0)
             ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#4)): ref)))
        {
            // Begin Comprehension WF check
            havoc i#3;
            havoc j#1;
            if (true)
            {
                if (LitInt(0) <= i#3)
                {
                }

                if (LitInt(0) <= i#3 && i#3 < j#1)
                {
                }

                if (LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(bots#0))
                {
                    assert 0 <= i#3 && i#3 < Seq#Length(bots#0);
                    assert $Unbox(Seq#Index(bots#0, i#3)): ref != null;
                    b$reqreads#2 := $_Frame[$Unbox(Seq#Index(bots#0, i#3)): ref, _module.Bot.Repr];
                    assert 0 <= j#1 && j#1 < Seq#Length(bots#0);
                    assert $Unbox(Seq#Index(bots#0, j#1)): ref != null;
                    b$reqreads#3 := $_Frame[$Unbox(Seq#Index(bots#0, j#1)): ref, _module.Bot.Repr];
                }
            }

            // End Comprehension WF check
        }

        assume _module.__default.ValidArmy($Heap, bots#0)
           == ((forall i#4: int :: 
              { $Unbox(Seq#Index(bots#0, i#4)): ref } 
              true
                 ==> 
                LitInt(0) <= i#4 && i#4 < Seq#Length(bots#0)
                 ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#4)): ref))
             && (forall i#5: int, j#2: int :: 
              { $Unbox(Seq#Index(bots#0, j#2)): ref, $Unbox(Seq#Index(bots#0, i#5)): ref } 
              true
                 ==> 
                LitInt(0) <= i#5 && i#5 < j#2 && j#2 < Seq#Length(bots#0)
                 ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#5)): ref, _module.Bot.Repr), 
                  read($Heap, $Unbox(Seq#Index(bots#0, j#2)): ref, _module.Bot.Repr))));
        assume (forall i#4: int :: 
          { $Unbox(Seq#Index(bots#0, i#4)): ref } 
          LitInt(0) <= i#4 && i#4 < Seq#Length(bots#0)
             ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, i#4)): ref));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ValidArmy($Heap, bots#0), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure {:verboseName "FlyRobotArmy (well-formedness)"} CheckWellFormed$$_module.__default.FlyRobotArmy(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "FlyRobotArmy (well-formedness)"} CheckWellFormed$$_module.__default.FlyRobotArmy(bots#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##bots#0: Seq Box;
  var ##bots#1: Seq Box;
  var ##bots#2: Seq Box;
  var ##bots#3: Seq Box;
  var ##bots#4: Seq Box;
  var b#0: ref;

    // AddMethodImpl: FlyRobotArmy, CheckWellFormed$$_module.__default.FlyRobotArmy
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]);
    ##bots#0 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#0, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ValidArmy#canCall($Heap, bots#0);
    assume _module.__default.ValidArmy($Heap, bots#0);
    ##bots#1 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#1, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ArmyRepr#canCall($Heap, bots#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    ##bots#2 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#2, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ValidArmy#canCall($Heap, bots#0);
    assume _module.__default.ValidArmy($Heap, bots#0);
    ##bots#3 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#3, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ArmyRepr#canCall($Heap, bots#0);
    ##bots#4 := bots#0;
    assert $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), old($Heap));
    assume _module.__default.ArmyRepr#canCall(old($Heap), bots#0);
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]
           && !_module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    havoc b#0;
    assume $Is(b#0, Tclass._module.Bot()) && $IsAlloc(b#0, Tclass._module.Bot(), $Heap);
    if (*)
    {
        assume Seq#Contains(bots#0, $Box(b#0));
        assert b#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(b#0, Tclass._module.Bot?(), $Heap);
        assume _module.Bot.Valid#canCall($Heap, b#0);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#0);
        assert b#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(b#0, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.robot__inv#canCall($Heap, b#0);
        assume _module.Bot.robot__inv($Heap, b#0);
        assert b#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(b#0, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.flying#canCall($Heap, b#0);
        assume _module.Bot.flying($Heap, b#0);
    }
    else
    {
        assume Seq#Contains(bots#0, $Box(b#0))
           ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#0)
             && _module.Bot.robot__inv($Heap, b#0)
             && _module.Bot.flying($Heap, b#0);
    }

    assume (forall b#1: ref :: 
      { _module.Bot.flying($Heap, b#1) } 
        { _module.Bot.robot__inv($Heap, b#1) } 
        { _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1) } 
        { Seq#Contains(bots#0, $Box(b#1)) } 
      $Is(b#1, Tclass._module.Bot())
         ==> (Seq#Contains(bots#0, $Box(b#1))
             ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1))
           && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv($Heap, b#1))
           && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.flying($Heap, b#1)));
}



procedure {:verboseName "FlyRobotArmy (call)"} Call$$_module.__default.FlyRobotArmy(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap));
  // user-defined preconditions
  requires _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(bots#0, i#0)): ref } 
        true
           ==> 
          LitInt(0) <= i#0 && i#0 < Seq#Length(bots#0)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#0)): ref));
  requires _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#1: int, j#0: int :: 
        { $Unbox(Seq#Index(bots#0, j#0)): ref, $Unbox(Seq#Index(bots#0, i#1)): ref } 
        true
           ==> 
          LitInt(0) <= i#1 && i#1 < j#0 && j#0 < Seq#Length(bots#0)
           ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr), 
            read($Heap, $Unbox(Seq#Index(bots#0, j#0)): ref, _module.Bot.Repr)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     && (_module.__default.ValidArmy($Heap, bots#0)
       ==> _module.__default.ArmyRepr#canCall($Heap, bots#0)
         && _module.__default.ArmyRepr#canCall(old($Heap), bots#0));
  free ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     && 
    _module.__default.ValidArmy($Heap, bots#0)
     && 
    (forall i#2: int :: 
      { $Unbox(Seq#Index(bots#0, i#2)): ref } 
      true
         ==> 
        LitInt(0) <= i#2 && i#2 < Seq#Length(bots#0)
         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#2)): ref))
     && (forall i#3: int, j#1: int :: 
      { $Unbox(Seq#Index(bots#0, j#1)): ref, $Unbox(Seq#Index(bots#0, i#3)): ref } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(bots#0)
         ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#3)): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(bots#0, j#1)): ref, _module.Bot.Repr)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]
         && !_module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.Valid#canCall($Heap, b#1))
         && (
          (Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1))
           ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv#canCall($Heap, b#1))
             && (
              (Seq#Contains(bots#0, $Box(b#1))
               ==> _module.Bot.robot__inv($Heap, b#1))
               ==> 
              Seq#Contains(bots#0, $Box(b#1))
               ==> _module.Bot.flying#canCall($Heap, b#1))));
  free ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1))
         && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv($Heap, b#1))
         && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.flying($Heap, b#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "FlyRobotArmy (correctness)"} Impl$$_module.__default.FlyRobotArmy(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.ValidArmy#canCall($Heap, bots#0)
     && 
    _module.__default.ValidArmy($Heap, bots#0)
     && 
    (forall i#4: int :: 
      { $Unbox(Seq#Index(bots#0, i#4)): ref } 
      true
         ==> 
        LitInt(0) <= i#4 && i#4 < Seq#Length(bots#0)
         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#4)): ref))
     && (forall i#5: int, j#2: int :: 
      { $Unbox(Seq#Index(bots#0, j#2)): ref, $Unbox(Seq#Index(bots#0, i#5)): ref } 
      true
         ==> 
        LitInt(0) <= i#5 && i#5 < j#2 && j#2 < Seq#Length(bots#0)
         ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#5)): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(bots#0, j#2)): ref, _module.Bot.Repr)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     && (_module.__default.ValidArmy($Heap, bots#0)
       ==> _module.__default.ArmyRepr#canCall($Heap, bots#0)
         && _module.__default.ArmyRepr#canCall(old($Heap), bots#0));
  ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#6: int :: 
        { $Unbox(Seq#Index(bots#0, i#6)): ref } 
        true
           ==> 
          LitInt(0) <= i#6 && i#6 < Seq#Length(bots#0)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#6)): ref));
  ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#7: int, j#3: int :: 
        { $Unbox(Seq#Index(bots#0, j#3)): ref, $Unbox(Seq#Index(bots#0, i#7)): ref } 
        true
           ==> 
          LitInt(0) <= i#7 && i#7 < j#3 && j#3 < Seq#Length(bots#0)
           ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#7)): ref, _module.Bot.Repr), 
            read($Heap, $Unbox(Seq#Index(bots#0, j#3)): ref, _module.Bot.Repr)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]
         && !_module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.Valid#canCall($Heap, b#1))
         && (
          (Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#1))
           ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv#canCall($Heap, b#1))
             && (
              (Seq#Contains(bots#0, $Box(b#1))
               ==> _module.Bot.robot__inv($Heap, b#1))
               ==> 
              Seq#Contains(bots#0, $Box(b#1))
               ==> _module.Bot.flying#canCall($Heap, b#1))));
  ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b#1))
         && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv($Heap, b#1))
         && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.flying($Heap, b#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "FlyRobotArmy (correctness)"} Impl$$_module.__default.FlyRobotArmy(bots#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var bots##0_0: Seq Box;
  var n#1_0: int;
  var $PreLoopHeap$loop#1_0: Heap;
  var $decr_init$loop#1_00: int;
  var $w$loop#1_0: bool;
  var ##bots#1_0: Seq Box;
  var j#1_1: int;
  var i#1_2: int;
  var $decr$loop#1_00: int;
  var bots##1_0_0: Seq Box;
  var n##1_0_0: int;

    // AddMethodImpl: FlyRobotArmy, Impl$$_module.__default.FlyRobotArmy
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]);
    $_reverifyPost := false;
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(198,3)
    if (*)
    {
        // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(200,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        bots##0_0 := bots#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && _module.__default.ArmyRepr($Heap, bots##0_0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.FlyRobotArmy__Recursively(bots##0_0);
        // TrCallStmt: After ProcessCallStmt
    }
    else
    {
        // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(203,11)
        assume true;
        assume true;
        n#1_0 := LitInt(0);
        // ----- while statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(204,5)
        // Assume Fuel Constant
        $PreLoopHeap$loop#1_0 := $Heap;
        $decr_init$loop#1_00 := Seq#Length(bots#0) - n#1_0;
        havoc $w$loop#1_0;
        while (true)
          free invariant $w$loop#1_0 ==> true;
          invariant $w$loop#1_0 ==> LitInt(0) <= n#1_0;
          invariant $w$loop#1_0 ==> n#1_0 <= Seq#Length(bots#0);
          free invariant $w$loop#1_0 ==> _module.__default.ValidArmy#canCall($Heap, bots#0);
          invariant $w$loop#1_0
             ==> 
            _module.__default.ValidArmy#canCall($Heap, bots#0)
             ==> _module.__default.ValidArmy($Heap, bots#0)
               || (forall i#1_0: int :: 
                { $Unbox(Seq#Index(bots#0, i#1_0)): ref } 
                true
                   ==> 
                  LitInt(0) <= i#1_0 && i#1_0 < Seq#Length(bots#0)
                   ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#1_0)): ref));
          invariant $w$loop#1_0
             ==> 
            _module.__default.ValidArmy#canCall($Heap, bots#0)
             ==> _module.__default.ValidArmy($Heap, bots#0)
               || (forall i#1_1: int, j#1_0: int :: 
                { $Unbox(Seq#Index(bots#0, j#1_0)): ref, $Unbox(Seq#Index(bots#0, i#1_1)): ref } 
                true
                   ==> 
                  LitInt(0) <= i#1_1 && i#1_1 < j#1_0 && j#1_0 < Seq#Length(bots#0)
                   ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1_1)): ref, _module.Bot.Repr), 
                    read($Heap, $Unbox(Seq#Index(bots#0, j#1_0)): ref, _module.Bot.Repr)));
          free invariant $w$loop#1_0
             ==> _module.__default.ValidArmy#canCall($Heap, bots#0)
               && 
              _module.__default.ValidArmy($Heap, bots#0)
               && 
              (forall i#1_0: int :: 
                { $Unbox(Seq#Index(bots#0, i#1_0)): ref } 
                true
                   ==> 
                  LitInt(0) <= i#1_0 && i#1_0 < Seq#Length(bots#0)
                   ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#1_0)): ref))
               && (forall i#1_1: int, j#1_0: int :: 
                { $Unbox(Seq#Index(bots#0, j#1_0)): ref, $Unbox(Seq#Index(bots#0, i#1_1)): ref } 
                true
                   ==> 
                  LitInt(0) <= i#1_1 && i#1_1 < j#1_0 && j#1_0 < Seq#Length(bots#0)
                   ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1_1)): ref, _module.Bot.Repr), 
                    read($Heap, $Unbox(Seq#Index(bots#0, j#1_0)): ref, _module.Bot.Repr)));
          free invariant $w$loop#1_0
             ==> (forall j#1_2: int :: 
              { $Unbox(Seq#Index(bots#0, j#1_2)): ref } 
              (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                   ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                 && (
                  (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                   ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                   ==> (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                       ==> _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                     && (
                      (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                       ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                       ==> 
                      LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                       ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))));
          invariant $w$loop#1_0
             ==> (forall j#1_2: int :: 
              { $Unbox(Seq#Index(bots#0, j#1_2)): ref } 
              true
                 ==> (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                     ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                   && (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                     ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                   && (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                     ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref)));
          free invariant $w$loop#1_0
             ==> (forall j#1_2: int :: 
              { $Unbox(Seq#Index(bots#0, j#1_2)): ref } 
              true
                 ==> (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                     ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                   && (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                     ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                   && (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                     ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref)));
          free invariant $w$loop#1_0 ==> true;
          invariant $w$loop#1_0
             ==> (forall i#1_3: int :: 
              { $Unbox(Seq#Index(bots#0, i#1_3)): ref } 
                { $Unbox(Seq#Index(bots#0, i#1_3)): ref } 
              true
                 ==> 
                LitInt(0) <= i#1_3 && i#1_3 < Seq#Length(bots#0)
                 ==> (forall $o: ref :: 
                  { read(old($Heap), $o, alloc) } 
                  read($Heap, $Unbox(Seq#Index(bots#0, i#1_3)): ref, _module.Bot.Repr)[$Box($o)]
                       && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#1_3)): ref, _module.Bot.Repr)[$Box($o)]
                     ==> $o != null && !read(old($Heap), $o, alloc)));
          free invariant (forall $o: ref :: 
            { $Heap[$o] } 
            $o != null && read(old($Heap), $o, alloc)
               ==> $Heap[$o] == $PreLoopHeap$loop#1_0[$o]
                 || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
          free invariant $HeapSucc($PreLoopHeap$loop#1_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
            { read($Heap, $o, $f) } 
            $o != null && read($PreLoopHeap$loop#1_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1_0, $o, $f) || $_Frame[$o, $f]);
          free invariant Seq#Length(bots#0) - n#1_0 <= $decr_init$loop#1_00
             && (Seq#Length(bots#0) - n#1_0 == $decr_init$loop#1_00 ==> true);
        {
            if (!$w$loop#1_0)
            {
                if (LitInt(0) <= n#1_0)
                {
                }

                assume true;
                assume LitInt(0) <= n#1_0 && n#1_0 <= Seq#Length(bots#0);
                ##bots#1_0 := bots#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##bots#1_0, TSeq(Tclass._module.Bot()), $Heap);
                assume _module.__default.ValidArmy#canCall($Heap, bots#0);
                assume _module.__default.ValidArmy#canCall($Heap, bots#0);
                assume _module.__default.ValidArmy($Heap, bots#0);
                // Begin Comprehension WF check
                havoc j#1_1;
                if (true)
                {
                    if (LitInt(0) <= j#1_1)
                    {
                    }

                    if (LitInt(0) <= j#1_1 && j#1_1 < n#1_0)
                    {
                        assert {:subsumption 0} 0 <= j#1_1 && j#1_1 < Seq#Length(bots#0);
                        assert {:subsumption 0} $Unbox(Seq#Index(bots#0, j#1_1)): ref != null;
                        // assume allocatedness for receiver argument to function
                        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#1_1)): ref, Tclass._module.Bot?(), $Heap);
                        assume _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref);
                        if (_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref))
                        {
                            assert {:subsumption 0} 0 <= j#1_1 && j#1_1 < Seq#Length(bots#0);
                            assert {:subsumption 0} $Unbox(Seq#Index(bots#0, j#1_1)): ref != null;
                            // assume allocatedness for receiver argument to function
                            assume $IsAlloc($Unbox(Seq#Index(bots#0, j#1_1)): ref, Tclass._module.Bot?(), $Heap);
                            assert {:subsumption 0} Lit(true)
                               ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref);
                            assume _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref);
                        }

                        if (_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref)
                           && _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref))
                        {
                            assert {:subsumption 0} 0 <= j#1_1 && j#1_1 < Seq#Length(bots#0);
                            assert {:subsumption 0} $Unbox(Seq#Index(bots#0, j#1_1)): ref != null;
                            // assume allocatedness for receiver argument to function
                            assume $IsAlloc($Unbox(Seq#Index(bots#0, j#1_1)): ref, Tclass._module.Bot?(), $Heap);
                            assert {:subsumption 0} Lit(true)
                               ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref);
                            assume _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_1)): ref);
                        }
                    }
                }

                // End Comprehension WF check
                assume (forall j#1_2: int :: 
                  { $Unbox(Seq#Index(bots#0, j#1_2)): ref } 
                  (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                       ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                     && (
                      (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                       ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                       ==> (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                           ==> _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                         && (
                          (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                           ==> 
                          LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                           ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))));
                assume (forall j#1_2: int :: 
                  { $Unbox(Seq#Index(bots#0, j#1_2)): ref } 
                  true
                     ==> (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                       && (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                         ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                       && (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                         ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref)));
                // Begin Comprehension WF check
                havoc i#1_2;
                if (true)
                {
                    if (LitInt(0) <= i#1_2)
                    {
                    }

                    if (LitInt(0) <= i#1_2 && i#1_2 < Seq#Length(bots#0))
                    {
                        assert {:subsumption 0} 0 <= i#1_2 && i#1_2 < Seq#Length(bots#0);
                        assert {:subsumption 0} $Unbox(Seq#Index(bots#0, i#1_2)): ref != null;
                        assert {:subsumption 0} 0 <= i#1_2 && i#1_2 < Seq#Length(bots#0);
                        assert {:subsumption 0} $Unbox(Seq#Index(bots#0, i#1_2)): ref != null;
                        assert $IsAlloc($Unbox(Seq#Index(bots#0, i#1_2)): ref, Tclass._module.Bot(), old($Heap));
                    }
                }

                // End Comprehension WF check
                assume true;
                assume (forall i#1_3: int :: 
                  { $Unbox(Seq#Index(bots#0, i#1_3)): ref } 
                    { $Unbox(Seq#Index(bots#0, i#1_3)): ref } 
                  true
                     ==> 
                    LitInt(0) <= i#1_3 && i#1_3 < Seq#Length(bots#0)
                     ==> (forall $o: ref :: 
                      { read(old($Heap), $o, alloc) } 
                      read($Heap, $Unbox(Seq#Index(bots#0, i#1_3)): ref, _module.Bot.Repr)[$Box($o)]
                           && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#1_3)): ref, _module.Bot.Repr)[$Box($o)]
                         ==> $o != null && !read(old($Heap), $o, alloc)));
                assume true;
                assume false;
            }

            assume true;
            if (Seq#Length(bots#0) <= n#1_0)
            {
                break;
            }

            $decr$loop#1_00 := Seq#Length(bots#0) - n#1_0;
            // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(210,13)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            bots##1_0_0 := bots#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            n##1_0_0 := n#1_0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && read($Heap, $Unbox(Seq#Index(bots##1_0_0, n##1_0_0)): ref, _module.Bot.Repr)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.FlyOne(bots##1_0_0, n##1_0_0);
            // TrCallStmt: After ProcessCallStmt
            // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(211,9)
            assume true;
            assume true;
            n#1_0 := n#1_0 + 1;
            // ----- loop termination check ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(204,5)
            assert 0 <= $decr$loop#1_00 || Seq#Length(bots#0) - n#1_0 == $decr$loop#1_00;
            assert Seq#Length(bots#0) - n#1_0 < $decr$loop#1_00;
            assume LitInt(0) <= n#1_0 && n#1_0 <= Seq#Length(bots#0)
               ==> _module.__default.ValidArmy#canCall($Heap, bots#0)
                 && (_module.__default.ValidArmy($Heap, bots#0)
                   ==> (forall j#1_2: int :: 
                    { $Unbox(Seq#Index(bots#0, j#1_2)): ref } 
                    (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                         ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                       && (
                        (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                         ==> (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                             ==> _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                           && (
                            (LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                             ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref))
                             ==> 
                            LitInt(0) <= j#1_2 && j#1_2 < n#1_0
                             ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#1_2)): ref)))));
        }
    }
}



procedure {:verboseName "FlyRobotArmy_Recursively (well-formedness)"} CheckWellFormed$$_module.__default.FlyRobotArmy__Recursively(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "FlyRobotArmy_Recursively (well-formedness)"} CheckWellFormed$$_module.__default.FlyRobotArmy__Recursively(bots#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##bots#0: Seq Box;
  var ##bots#1: Seq Box;
  var ##bots#2: Seq Box;
  var i#0: int;
  var b#0: ref;

    // AddMethodImpl: FlyRobotArmy_Recursively, CheckWellFormed$$_module.__default.FlyRobotArmy__Recursively
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]);
    ##bots#0 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#0, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ValidArmy#canCall($Heap, bots#0);
    assume _module.__default.ValidArmy($Heap, bots#0);
    ##bots#1 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#1, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ArmyRepr#canCall($Heap, bots#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    ##bots#2 := bots#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#2, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ValidArmy#canCall($Heap, bots#0);
    assume _module.__default.ValidArmy($Heap, bots#0);
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assume i#0 < Seq#Length(bots#0);
        assert 0 <= i#0 && i#0 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, i#0)): ref != null;
        assert 0 <= i#0 && i#0 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, i#0)): ref != null;
        assert $IsAlloc($Unbox(Seq#Index(bots#0, i#0)): ref, Tclass._module.Bot(), old($Heap));
        assume (forall $o: ref :: 
          { read(old($Heap), $o, alloc) } 
          read($Heap, $Unbox(Seq#Index(bots#0, i#0)): ref, _module.Bot.Repr)[$Box($o)]
               && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#0)): ref, _module.Bot.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < Seq#Length(bots#0)
           ==> (forall $o: ref :: 
            { read(old($Heap), $o, alloc) } 
            read($Heap, $Unbox(Seq#Index(bots#0, i#0)): ref, _module.Bot.Repr)[$Box($o)]
                 && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#0)): ref, _module.Bot.Repr)[$Box($o)]
               ==> $o != null && !read(old($Heap), $o, alloc));
    }

    assume (forall i#1: int :: 
      { $Unbox(Seq#Index(bots#0, i#1)): ref } { $Unbox(Seq#Index(bots#0, i#1)): ref } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < Seq#Length(bots#0)
         ==> (forall $o: ref :: 
          { read(old($Heap), $o, alloc) } 
          read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr)[$Box($o)]
               && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc)));
    havoc b#0;
    assume $Is(b#0, Tclass._module.Bot()) && $IsAlloc(b#0, Tclass._module.Bot(), $Heap);
    if (*)
    {
        assume Seq#Contains(bots#0, $Box(b#0));
        assert b#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(b#0, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.robot__inv#canCall($Heap, b#0);
        assume _module.Bot.robot__inv($Heap, b#0);
        assert b#0 != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc(b#0, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true) ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b#0);
        assume _module.Bot.flying#canCall($Heap, b#0);
        assume _module.Bot.flying($Heap, b#0);
    }
    else
    {
        assume Seq#Contains(bots#0, $Box(b#0))
           ==> _module.Bot.robot__inv($Heap, b#0) && _module.Bot.flying($Heap, b#0);
    }

    assume (forall b#1: ref :: 
      { _module.Bot.flying($Heap, b#1) } 
        { _module.Bot.robot__inv($Heap, b#1) } 
        { Seq#Contains(bots#0, $Box(b#1)) } 
      $Is(b#1, Tclass._module.Bot())
         ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv($Heap, b#1))
           && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.flying($Heap, b#1)));
}



procedure {:verboseName "FlyRobotArmy_Recursively (call)"} Call$$_module.__default.FlyRobotArmy__Recursively(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap));
  // user-defined preconditions
  requires _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#2: int :: 
        { $Unbox(Seq#Index(bots#0, i#2)): ref } 
        true
           ==> 
          LitInt(0) <= i#2 && i#2 < Seq#Length(bots#0)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#2)): ref));
  requires _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#3: int, j#0: int :: 
        { $Unbox(Seq#Index(bots#0, j#0)): ref, $Unbox(Seq#Index(bots#0, i#3)): ref } 
        true
           ==> 
          LitInt(0) <= i#3 && i#3 < j#0 && j#0 < Seq#Length(bots#0)
           ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#3)): ref, _module.Bot.Repr), 
            read($Heap, $Unbox(Seq#Index(bots#0, j#0)): ref, _module.Bot.Repr)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValidArmy#canCall($Heap, bots#0);
  free ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     && 
    _module.__default.ValidArmy($Heap, bots#0)
     && 
    (forall i#4: int :: 
      { $Unbox(Seq#Index(bots#0, i#4)): ref } 
      true
         ==> 
        LitInt(0) <= i#4 && i#4 < Seq#Length(bots#0)
         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#4)): ref))
     && (forall i#5: int, j#1: int :: 
      { $Unbox(Seq#Index(bots#0, j#1)): ref, $Unbox(Seq#Index(bots#0, i#5)): ref } 
      true
         ==> 
        LitInt(0) <= i#5 && i#5 < j#1 && j#1 < Seq#Length(bots#0)
         ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#5)): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(bots#0, j#1)): ref, _module.Bot.Repr)));
  free ensures true;
  ensures (forall i#1: int :: 
    { $Unbox(Seq#Index(bots#0, i#1)): ref } { $Unbox(Seq#Index(bots#0, i#1)): ref } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < Seq#Length(bots#0)
       ==> (forall $o: ref :: 
        { read(old($Heap), $o, alloc) } 
        read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr)[$Box($o)]
             && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc)));
  free ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv#canCall($Heap, b#1))
         && (
          (Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.robot__inv($Heap, b#1))
           ==> 
          Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.flying#canCall($Heap, b#1)));
  ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv($Heap, b#1))
         && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.flying($Heap, b#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "FlyRobotArmy_Recursively (correctness)"} Impl$$_module.__default.FlyRobotArmy__Recursively(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.ValidArmy#canCall($Heap, bots#0)
     && 
    _module.__default.ValidArmy($Heap, bots#0)
     && 
    (forall i#6: int :: 
      { $Unbox(Seq#Index(bots#0, i#6)): ref } 
      true
         ==> 
        LitInt(0) <= i#6 && i#6 < Seq#Length(bots#0)
         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#6)): ref))
     && (forall i#7: int, j#2: int :: 
      { $Unbox(Seq#Index(bots#0, j#2)): ref, $Unbox(Seq#Index(bots#0, i#7)): ref } 
      true
         ==> 
        LitInt(0) <= i#7 && i#7 < j#2 && j#2 < Seq#Length(bots#0)
         ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#7)): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(bots#0, j#2)): ref, _module.Bot.Repr)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValidArmy#canCall($Heap, bots#0);
  ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#8: int :: 
        { $Unbox(Seq#Index(bots#0, i#8)): ref } 
        true
           ==> 
          LitInt(0) <= i#8 && i#8 < Seq#Length(bots#0)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, i#8)): ref));
  ensures _module.__default.ValidArmy#canCall($Heap, bots#0)
     ==> _module.__default.ValidArmy($Heap, bots#0)
       || (forall i#9: int, j#3: int :: 
        { $Unbox(Seq#Index(bots#0, j#3)): ref, $Unbox(Seq#Index(bots#0, i#9)): ref } 
        true
           ==> 
          LitInt(0) <= i#9 && i#9 < j#3 && j#3 < Seq#Length(bots#0)
           ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#9)): ref, _module.Bot.Repr), 
            read($Heap, $Unbox(Seq#Index(bots#0, j#3)): ref, _module.Bot.Repr)));
  free ensures true;
  ensures (forall i#1: int :: 
    { $Unbox(Seq#Index(bots#0, i#1)): ref } { $Unbox(Seq#Index(bots#0, i#1)): ref } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < Seq#Length(bots#0)
       ==> (forall $o: ref :: 
        { read(old($Heap), $o, alloc) } 
        read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr)[$Box($o)]
             && !read(old($Heap), $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc)));
  free ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv#canCall($Heap, b#1))
         && (
          (Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.robot__inv($Heap, b#1))
           ==> 
          Seq#Contains(bots#0, $Box(b#1))
           ==> _module.Bot.flying#canCall($Heap, b#1)));
  ensures (forall b#1: ref :: 
    { _module.Bot.flying($Heap, b#1) } 
      { _module.Bot.robot__inv($Heap, b#1) } 
      { Seq#Contains(bots#0, $Box(b#1)) } 
    $Is(b#1, Tclass._module.Bot())
       ==> (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.robot__inv($Heap, b#1))
         && (Seq#Contains(bots#0, $Box(b#1)) ==> _module.Bot.flying($Heap, b#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || _module.__default.ArmyRepr(old($Heap), bots#0)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "FlyRobotArmy_Recursively (correctness)"} Impl$$_module.__default.FlyRobotArmy__Recursively(bots#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var bots##0_0: Seq Box;
  var n##0_0: int;
  var bots##0_1: Seq Box;

    // AddMethodImpl: FlyRobotArmy_Recursively, Impl$$_module.__default.FlyRobotArmy__Recursively
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> _module.__default.ArmyRepr($Heap, bots#0)[$Box($o)]);
    $_reverifyPost := false;
    // ----- if statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(223,3)
    assume true;
    if (!Seq#Equal(bots#0, Seq#Empty(): Seq Box))
    {
        // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(224,11)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        bots##0_0 := bots#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0_0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, $Unbox(Seq#Index(bots##0_0, n##0_0)): ref, _module.Bot.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.FlyOne(bots##0_0, n##0_0);
        // TrCallStmt: After ProcessCallStmt
        // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(225,29)
        // TrCallStmt: Before ProcessCallStmt
        assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(bots#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        bots##0_1 := Seq#Drop(bots#0, LitInt(1));
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && _module.__default.ArmyRepr($Heap, bots##0_1)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Seq#Rank(bots##0_1) < Seq#Rank(bots#0);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.FlyRobotArmy__Recursively(bots##0_1);
        // TrCallStmt: After ProcessCallStmt
    }
    else
    {
    }
}



procedure {:verboseName "FlyOne (well-formedness)"} CheckWellFormed$$_module.__default.FlyOne(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap), 
    n#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "FlyOne (well-formedness)"} CheckWellFormed$$_module.__default.FlyOne(bots#0: Seq Box, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#0: int;
  var i#0: int;
  var j#2: int;
  var j#4: int;
  var j#6: int;
  var j#8: int;
  var j#10: int;

    // AddMethodImpl: FlyOne, CheckWellFormed$$_module.__default.FlyOne
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]);
    if (LitInt(0) <= n#0)
    {
    }

    assume LitInt(0) <= n#0 && n#0 < Seq#Length(bots#0);
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= j#0;
        assume j#0 < Seq#Length(bots#0);
        assert 0 <= j#0 && j#0 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#0)): ref != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#0)): ref, Tclass._module.Bot?(), $Heap);
        assume _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#0)): ref);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#0)): ref);
    }
    else
    {
        assume LitInt(0) <= j#0 && j#0 < Seq#Length(bots#0)
           ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#0)): ref);
    }

    assume (forall j#1: int :: 
      { $Unbox(Seq#Index(bots#0, j#1)): ref } 
      true
         ==> 
        LitInt(0) <= j#1 && j#1 < Seq#Length(bots#0)
         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1)): ref));
    havoc i#0;
    havoc j#2;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assume i#0 < j#2;
        assume j#2 < Seq#Length(bots#0);
        assert 0 <= i#0 && i#0 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, i#0)): ref != null;
        assert 0 <= j#2 && j#2 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#2)): ref != null;
        assume Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#0)): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(bots#0, j#2)): ref, _module.Bot.Repr));
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < j#2 && j#2 < Seq#Length(bots#0)
           ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#0)): ref, _module.Bot.Repr), 
            read($Heap, $Unbox(Seq#Index(bots#0, j#2)): ref, _module.Bot.Repr));
    }

    assume (forall i#1: int, j#3: int :: 
      { $Unbox(Seq#Index(bots#0, j#3)): ref, $Unbox(Seq#Index(bots#0, i#1)): ref } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < j#3 && j#3 < Seq#Length(bots#0)
         ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(bots#0, j#3)): ref, _module.Bot.Repr)));
    havoc j#4;
    assume true;
    if (*)
    {
        assume LitInt(0) <= j#4;
        assume j#4 < n#0;
        assert 0 <= j#4 && j#4 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#4)): ref != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#4)): ref, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assume _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assume _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assert 0 <= j#4 && j#4 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#4)): ref != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#4)): ref, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assume _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
        assume _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
    }
    else
    {
        assume LitInt(0) <= j#4 && j#4 < n#0
           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#4)): ref)
             && _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#4)): ref);
    }

    assume (forall j#5: int :: 
      { $Unbox(Seq#Index(bots#0, j#5)): ref } 
      true
         ==> (LitInt(0) <= j#5 && j#5 < n#0
             ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#5)): ref))
           && (LitInt(0) <= j#5 && j#5 < n#0
             ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#5)): ref)));
    assert 0 <= n#0 && n#0 < Seq#Length(bots#0);
    assert $Unbox(Seq#Index(bots#0, n#0)): ref != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc j#6;
    assume true;
    if (*)
    {
        assume LitInt(0) <= j#6;
        assume j#6 < Seq#Length(bots#0);
        assert 0 <= j#6 && j#6 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#6)): ref != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#6)): ref, Tclass._module.Bot?(), $Heap);
        assume _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#6)): ref);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#6)): ref);
    }
    else
    {
        assume LitInt(0) <= j#6 && j#6 < Seq#Length(bots#0)
           ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#6)): ref);
    }

    assume (forall j#7: int :: 
      { $Unbox(Seq#Index(bots#0, j#7)): ref } 
      true
         ==> 
        LitInt(0) <= j#7 && j#7 < Seq#Length(bots#0)
         ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#7)): ref));
    assert 0 <= n#0 && n#0 < Seq#Length(bots#0);
    assert $Unbox(Seq#Index(bots#0, n#0)): ref != null;
    assert 0 <= n#0 && n#0 < Seq#Length(bots#0);
    assert $Unbox(Seq#Index(bots#0, n#0)): ref != null;
    assert $IsAlloc($Unbox(Seq#Index(bots#0, n#0)): ref, Tclass._module.Bot(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
           && !read(old($Heap), $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert 0 <= n#0 && n#0 < Seq#Length(bots#0);
    assert $Unbox(Seq#Index(bots#0, n#0)): ref != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc($Unbox(Seq#Index(bots#0, n#0)): ref, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true)
       ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assume _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assume _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assert 0 <= n#0 && n#0 < Seq#Length(bots#0);
    assert $Unbox(Seq#Index(bots#0, n#0)): ref != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc($Unbox(Seq#Index(bots#0, n#0)): ref, Tclass._module.Bot?(), $Heap);
    assert {:subsumption 0} Lit(true)
       ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assume _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    assume _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref);
    havoc j#8;
    assume true;
    if (*)
    {
        assume LitInt(0) <= j#8;
        assume j#8 < Seq#Length(bots#0);
        assume j#8 != n#0;
        assert 0 <= j#8 && j#8 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#8)): ref != null;
        assert 0 <= j#8 && j#8 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#8)): ref != null;
        assert $IsAlloc($Unbox(Seq#Index(bots#0, j#8)): ref, Tclass._module.Bot(), old($Heap));
        assume Set#Equal(read($Heap, $Unbox(Seq#Index(bots#0, j#8)): ref, _module.Bot.Repr), 
          read(old($Heap), $Unbox(Seq#Index(bots#0, j#8)): ref, _module.Bot.Repr));
    }
    else
    {
        assume LitInt(0) <= j#8 && j#8 < Seq#Length(bots#0) && j#8 != n#0
           ==> Set#Equal(read($Heap, $Unbox(Seq#Index(bots#0, j#8)): ref, _module.Bot.Repr), 
            read(old($Heap), $Unbox(Seq#Index(bots#0, j#8)): ref, _module.Bot.Repr));
    }

    assume (forall j#9: int :: 
      { $Unbox(Seq#Index(bots#0, j#9)): ref } { $Unbox(Seq#Index(bots#0, j#9)): ref } 
      true
         ==> 
        LitInt(0) <= j#9 && j#9 < Seq#Length(bots#0) && j#9 != n#0
         ==> Set#Equal(read($Heap, $Unbox(Seq#Index(bots#0, j#9)): ref, _module.Bot.Repr), 
          read(old($Heap), $Unbox(Seq#Index(bots#0, j#9)): ref, _module.Bot.Repr)));
    havoc j#10;
    assume true;
    if (*)
    {
        assume LitInt(0) <= j#10;
        assume j#10 < n#0;
        assert 0 <= j#10 && j#10 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#10)): ref != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#10)): ref, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assume _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assume _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assert 0 <= j#10 && j#10 < Seq#Length(bots#0);
        assert $Unbox(Seq#Index(bots#0, j#10)): ref != null;
        // assume allocatedness for receiver argument to function
        assume $IsAlloc($Unbox(Seq#Index(bots#0, j#10)): ref, Tclass._module.Bot?(), $Heap);
        assert {:subsumption 0} Lit(true)
           ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assume _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
        assume _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
    }
    else
    {
        assume LitInt(0) <= j#10 && j#10 < n#0
           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#10)): ref)
             && _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#10)): ref);
    }

    assume (forall j#11: int :: 
      { $Unbox(Seq#Index(bots#0, j#11)): ref } 
      true
         ==> (LitInt(0) <= j#11 && j#11 < n#0
             ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
           && (LitInt(0) <= j#11 && j#11 < n#0
             ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref)));
}



procedure {:verboseName "FlyOne (call)"} Call$$_module.__default.FlyOne(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap), 
    n#0: int);
  // user-defined preconditions
  requires LitInt(0) <= n#0;
  requires n#0 < Seq#Length(bots#0);
  requires (forall j#1: int :: 
    { $Unbox(Seq#Index(bots#0, j#1)): ref } 
    true
       ==> 
      LitInt(0) <= j#1 && j#1 < Seq#Length(bots#0)
       ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1)): ref));
  requires (forall i#1: int, j#3: int :: 
    { $Unbox(Seq#Index(bots#0, j#3)): ref, $Unbox(Seq#Index(bots#0, i#1)): ref } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < j#3 && j#3 < Seq#Length(bots#0)
       ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr), 
        read($Heap, $Unbox(Seq#Index(bots#0, j#3)): ref, _module.Bot.Repr)));
  requires (forall j#5: int :: 
    { $Unbox(Seq#Index(bots#0, j#5)): ref } 
    true
       ==> (LitInt(0) <= j#5 && j#5 < n#0
           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#5)): ref))
         && (LitInt(0) <= j#5 && j#5 < n#0
           ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#5)): ref)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall j#7: int :: 
    { $Unbox(Seq#Index(bots#0, j#7)): ref } 
    LitInt(0) <= j#7 && j#7 < Seq#Length(bots#0)
       ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#7)): ref));
  free ensures (forall j#7: int :: 
    { $Unbox(Seq#Index(bots#0, j#7)): ref } 
    true
       ==> 
      LitInt(0) <= j#7 && j#7 < Seq#Length(bots#0)
       ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#7)): ref));
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     && (_module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
       ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref));
  free ensures _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     && 
    _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     && (_module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
       ==> _module.Bot.arms__up($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref));
  free ensures _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     && 
    _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     && read($Heap, 
        read($Heap, 
          read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.pos), 
          _module.Point.z), 
        _module.Cell.val)
       > 0;
  free ensures true;
  ensures (forall j#9: int :: 
    { $Unbox(Seq#Index(bots#0, j#9)): ref } { $Unbox(Seq#Index(bots#0, j#9)): ref } 
    true
       ==> 
      LitInt(0) <= j#9 && j#9 < Seq#Length(bots#0) && j#9 != n#0
       ==> Set#Equal(read($Heap, $Unbox(Seq#Index(bots#0, j#9)): ref, _module.Bot.Repr), 
        read(old($Heap), $Unbox(Seq#Index(bots#0, j#9)): ref, _module.Bot.Repr)));
  free ensures (forall j#11: int :: 
    { $Unbox(Seq#Index(bots#0, j#11)): ref } 
    (LitInt(0) <= j#11 && j#11 < n#0
         ==> _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
       && (
        (LitInt(0) <= j#11 && j#11 < n#0
         ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
         ==> 
        LitInt(0) <= j#11 && j#11 < n#0
         ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref)));
  ensures (forall j#11: int :: 
    { $Unbox(Seq#Index(bots#0, j#11)): ref } 
    true
       ==> (LitInt(0) <= j#11 && j#11 < n#0
           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
         && (LitInt(0) <= j#11 && j#11 < n#0
           ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "FlyOne (correctness)"} Impl$$_module.__default.FlyOne(bots#0: Seq Box
       where $Is(bots#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(bots#0, TSeq(Tclass._module.Bot()), $Heap), 
    n#0: int)
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= n#0;
  requires n#0 < Seq#Length(bots#0);
  free requires (forall j#1: int :: 
    { $Unbox(Seq#Index(bots#0, j#1)): ref } 
    true
       ==> 
      LitInt(0) <= j#1 && j#1 < Seq#Length(bots#0)
       ==> _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#1)): ref));
  requires (forall i#1: int, j#3: int :: 
    { $Unbox(Seq#Index(bots#0, j#3)): ref, $Unbox(Seq#Index(bots#0, i#1)): ref } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < j#3 && j#3 < Seq#Length(bots#0)
       ==> Set#Disjoint(read($Heap, $Unbox(Seq#Index(bots#0, i#1)): ref, _module.Bot.Repr), 
        read($Heap, $Unbox(Seq#Index(bots#0, j#3)): ref, _module.Bot.Repr)));
  requires (forall j#5: int :: 
    { $Unbox(Seq#Index(bots#0, j#5)): ref } 
    true
       ==> (LitInt(0) <= j#5 && j#5 < n#0
           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#5)): ref))
         && (LitInt(0) <= j#5 && j#5 < n#0
           ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#5)): ref)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall j#7: int :: 
    { $Unbox(Seq#Index(bots#0, j#7)): ref } 
    LitInt(0) <= j#7 && j#7 < Seq#Length(bots#0)
       ==> _module.Bot.Valid#canCall($Heap, $Unbox(Seq#Index(bots#0, j#7)): ref));
  ensures (forall j#7: int :: 
    { $Unbox(Seq#Index(bots#0, j#7)): ref } 
    true
       ==> 
      LitInt(0) <= j#7 && j#7 < Seq#Length(bots#0)
       ==> _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, $Unbox(Seq#Index(bots#0, j#7)): ref));
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
         && !read(old($Heap), $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     && (_module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
       ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref));
  ensures _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
       || (_module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
         ==> 
        _module.Bot.arms__up#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
         ==> _module.Bot.arms__up($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
           || read($Heap, 
              read($Heap, 
                read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.left), 
                _module.Arm.polar), 
              _module.Cell.val)
             == read($Heap, 
              read($Heap, 
                read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.right), 
                _module.Arm.polar), 
              _module.Cell.val));
  ensures _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
       || (_module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
         ==> 
        _module.Bot.arms__up#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
         ==> _module.Bot.arms__up($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
           || read($Heap, 
              read($Heap, 
                read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.right), 
                _module.Arm.polar), 
              _module.Cell.val)
             == LitInt(0));
  ensures _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
     ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref)
       || read($Heap, 
          read($Heap, 
            read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.pos), 
            _module.Point.z), 
          _module.Cell.val)
         > 0;
  free ensures true;
  ensures (forall j#9: int :: 
    { $Unbox(Seq#Index(bots#0, j#9)): ref } { $Unbox(Seq#Index(bots#0, j#9)): ref } 
    true
       ==> 
      LitInt(0) <= j#9 && j#9 < Seq#Length(bots#0) && j#9 != n#0
       ==> Set#Equal(read($Heap, $Unbox(Seq#Index(bots#0, j#9)): ref, _module.Bot.Repr), 
        read(old($Heap), $Unbox(Seq#Index(bots#0, j#9)): ref, _module.Bot.Repr)));
  free ensures (forall j#11: int :: 
    { $Unbox(Seq#Index(bots#0, j#11)): ref } 
    (LitInt(0) <= j#11 && j#11 < n#0
         ==> _module.Bot.robot__inv#canCall($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
       && (
        (LitInt(0) <= j#11 && j#11 < n#0
         ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
         ==> 
        LitInt(0) <= j#11 && j#11 < n#0
         ==> _module.Bot.flying#canCall($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref)));
  ensures (forall j#11: int :: 
    { $Unbox(Seq#Index(bots#0, j#11)): ref } 
    true
       ==> (LitInt(0) <= j#11 && j#11 < n#0
           ==> _module.Bot.robot__inv($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref))
         && (LitInt(0) <= j#11 && j#11 < n#0
           ==> _module.Bot.flying($Heap, $Unbox(Seq#Index(bots#0, j#11)): ref)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "FlyOne (correctness)"} Impl$$_module.__default.FlyOne(bots#0: Seq Box, n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: FlyOne, Impl$$_module.__default.FlyOne
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]);
    $_reverifyPost := false;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(242,14)
    // TrCallStmt: Before ProcessCallStmt
    assert 0 <= n#0 && n#0 < Seq#Length(bots#0);
    assume true;
    assert $Unbox(Seq#Index(bots#0, n#0)): ref != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, $Unbox(Seq#Index(bots#0, n#0)): ref, _module.Bot.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Bot.Fly($Unbox(Seq#Index(bots#0, n#0)): ref);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "FormArmy (well-formedness)"} CheckWellFormed$$_module.__default.FormArmy(b0#0: ref
       where $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap), 
    b1#0: ref
       where $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap), 
    b2#0: ref
       where $Is(b2#0, Tclass._module.Bot()) && $IsAlloc(b2#0, Tclass._module.Bot(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "FormArmy (well-formedness)"} CheckWellFormed$$_module.__default.FormArmy(b0#0: ref, b1#0: ref, b2#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: FormArmy, CheckWellFormed$$_module.__default.FormArmy
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b2#0, _module.Bot.Repr)[$Box($o)]);
    assert b0#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b0#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b0#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0);
    assert b1#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b1#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b1#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0);
    assert b2#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b2#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b2#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b2#0);
    assert b0#0 != null;
    assert b1#0 != null;
    if (Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)))
    {
        assert b0#0 != null;
        assert b1#0 != null;
    }

    if (Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr))
       && Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)))
    {
        assert b0#0 != null;
        assert b1#0 != null;
        assert b2#0 != null;
    }

    assume Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr))
       && Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr))
       && Set#Disjoint(Set#Union(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)), 
        read($Heap, b2#0, _module.Bot.Repr));
    assert b0#0 != null;
    assert b1#0 != null;
    assert b2#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
           || read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]
           || read(old($Heap), b2#0, _module.Bot.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assert b0#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b0#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b0#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0);
    assert b1#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b1#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b1#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0);
    assert b2#0 != null;
    // assume allocatedness for receiver argument to function
    assume $IsAlloc(b2#0, Tclass._module.Bot?(), $Heap);
    assume _module.Bot.Valid#canCall($Heap, b2#0);
    assume _module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b2#0);
    assert b0#0 != null;
    assert b1#0 != null;
    if (Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)))
    {
        assert b0#0 != null;
        assert b1#0 != null;
    }

    if (Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr))
       && Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)))
    {
        assert b0#0 != null;
        assert b1#0 != null;
        assert b2#0 != null;
    }

    assume Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr))
       && Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr))
       && Set#Disjoint(Set#Union(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)), 
        read($Heap, b2#0, _module.Bot.Repr));
    assert b0#0 != null;
    assert b1#0 != null;
    assert b2#0 != null;
    assert b0#0 != null;
    assert $IsAlloc(b0#0, Tclass._module.Bot(), old($Heap));
    assert b1#0 != null;
    assert $IsAlloc(b1#0, Tclass._module.Bot(), old($Heap));
    assert b2#0 != null;
    assert $IsAlloc(b2#0, Tclass._module.Bot(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      (
            read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b2#0, _module.Bot.Repr)[$Box($o)])
           && !Set#Union(Set#Union(read(old($Heap), b0#0, _module.Bot.Repr), 
              read(old($Heap), b1#0, _module.Bot.Repr)), 
            read(old($Heap), b2#0, _module.Bot.Repr))[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
}



procedure {:verboseName "FormArmy (call)"} Call$$_module.__default.FormArmy(b0#0: ref
       where $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap), 
    b1#0: ref
       where $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap), 
    b2#0: ref
       where $Is(b2#0, Tclass._module.Bot()) && $IsAlloc(b2#0, Tclass._module.Bot(), $Heap));
  // user-defined preconditions
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b2#0);
  requires Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  requires Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  requires Set#Disjoint(Set#Union(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)), 
    read($Heap, b2#0, _module.Bot.Repr));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, b0#0)
     && (_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0)
       ==> _module.Bot.Valid#canCall($Heap, b1#0)
         && (_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0)
           ==> _module.Bot.Valid#canCall($Heap, b2#0)));
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b2#0);
  free ensures true;
  ensures Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  ensures Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  ensures Set#Disjoint(Set#Union(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)), 
    read($Heap, b2#0, _module.Bot.Repr));
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    (
          read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b2#0, _module.Bot.Repr)[$Box($o)])
         && !Set#Union(Set#Union(read(old($Heap), b0#0, _module.Bot.Repr), 
            read(old($Heap), b1#0, _module.Bot.Repr)), 
          read(old($Heap), b2#0, _module.Bot.Repr))[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
         || read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]
         || read(old($Heap), b2#0, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "FormArmy (correctness)"} Impl$$_module.__default.FormArmy(b0#0: ref
       where $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap), 
    b1#0: ref
       where $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap), 
    b2#0: ref
       where $Is(b2#0, Tclass._module.Bot()) && $IsAlloc(b2#0, Tclass._module.Bot(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  requires _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b2#0);
  requires Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  requires Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  requires Set#Disjoint(Set#Union(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)), 
    read($Heap, b2#0, _module.Bot.Repr));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Bot.Valid#canCall($Heap, b0#0)
     && (_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b0#0)
       ==> _module.Bot.Valid#canCall($Heap, b1#0)
         && (_module.Bot.Valid(StartFuel__module.Bot.Valid, $Heap, b1#0)
           ==> _module.Bot.Valid#canCall($Heap, b2#0)));
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b0#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b1#0);
  ensures _module.Bot.Valid(StartFuelAssert__module.Bot.Valid, $Heap, b2#0);
  free ensures true;
  ensures Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  ensures Set#Disjoint(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr));
  ensures Set#Disjoint(Set#Union(read($Heap, b0#0, _module.Bot.Repr), read($Heap, b1#0, _module.Bot.Repr)), 
    read($Heap, b2#0, _module.Bot.Repr));
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    (
          read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b2#0, _module.Bot.Repr)[$Box($o)])
         && !Set#Union(Set#Union(read(old($Heap), b0#0, _module.Bot.Repr), 
            read(old($Heap), b1#0, _module.Bot.Repr)), 
          read(old($Heap), b2#0, _module.Bot.Repr))[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        read(old($Heap), b0#0, _module.Bot.Repr)[$Box($o)]
         || read(old($Heap), b1#0, _module.Bot.Repr)[$Box($o)]
         || read(old($Heap), b2#0, _module.Bot.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verboseName "FormArmy (correctness)"} Impl$$_module.__default.FormArmy(b0#0: ref, b1#0: ref, b2#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var army#0: Seq Box
     where $Is(army#0, TSeq(Tclass._module.Bot()))
       && $IsAlloc(army#0, TSeq(Tclass._module.Bot()), $Heap);
  var army##0: Seq Box;
  var bots##0: Seq Box;
  var bots##1: Seq Box;
  var army##1: Seq Box;

    // AddMethodImpl: FormArmy, Impl$$_module.__default.FormArmy
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, b0#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b1#0, _module.Bot.Repr)[$Box($o)]
           || read($Heap, b2#0, _module.Bot.Repr)[$Box($o)]);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(254,12)
    assume true;
    assume true;
    army#0 := Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(b0#0)), $Box(b1#0)), $Box(b2#0));
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(255,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    army##0 := army#0;
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.ArmyRepr3(army##0);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(256,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    bots##0 := army#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && _module.__default.ArmyRepr($Heap, bots##0)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FlyRobotArmy(bots##0);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(257,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    bots##1 := army#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && _module.__default.ArmyRepr($Heap, bots##1)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FlyRobotArmy(bots##1);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(258,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    army##1 := army#0;
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.ArmyRepr3(army##1);
    // TrCallStmt: After ProcessCallStmt
}



procedure {:verboseName "ArmyRepr3 (well-formedness)"} CheckWellFormed$$_module.__default.ArmyRepr3(army#0: Seq Box
       where $Is(army#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(army#0, TSeq(Tclass._module.Bot()), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verboseName "ArmyRepr3 (well-formedness)"} CheckWellFormed$$_module.__default.ArmyRepr3(army#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##bots#0: Seq Box;

    // AddMethodImpl: ArmyRepr3, CheckWellFormed$$_module.__default.ArmyRepr3
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume Seq#Length(army#0) == LitInt(3);
    havoc $Heap;
    assume old($Heap) == $Heap;
    ##bots#0 := army#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##bots#0, TSeq(Tclass._module.Bot()), $Heap);
    assume _module.__default.ArmyRepr#canCall($Heap, army#0);
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(army#0);
    assert $Unbox(Seq#Index(army#0, LitInt(0))): ref != null;
    assert 0 <= LitInt(1) && LitInt(1) < Seq#Length(army#0);
    assert $Unbox(Seq#Index(army#0, LitInt(1))): ref != null;
    assert 0 <= LitInt(2) && LitInt(2) < Seq#Length(army#0);
    assert $Unbox(Seq#Index(army#0, LitInt(2))): ref != null;
    assume Set#Equal(_module.__default.ArmyRepr($Heap, army#0), 
      Set#Union(Set#Union(read($Heap, $Unbox(Seq#Index(army#0, LitInt(0))): ref, _module.Bot.Repr), 
          read($Heap, $Unbox(Seq#Index(army#0, LitInt(1))): ref, _module.Bot.Repr)), 
        read($Heap, $Unbox(Seq#Index(army#0, LitInt(2))): ref, _module.Bot.Repr)));
}



procedure {:verboseName "ArmyRepr3 (call)"} Call$$_module.__default.ArmyRepr3(army#0: Seq Box
       where $Is(army#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(army#0, TSeq(Tclass._module.Bot()), $Heap));
  // user-defined preconditions
  requires Seq#Length(army#0) == LitInt(3);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ArmyRepr#canCall($Heap, army#0);
  ensures Set#Equal(_module.__default.ArmyRepr($Heap, army#0), 
    Set#Union(Set#Union(read($Heap, $Unbox(Seq#Index(army#0, LitInt(0))): ref, _module.Bot.Repr), 
        read($Heap, $Unbox(Seq#Index(army#0, LitInt(1))): ref, _module.Bot.Repr)), 
      read($Heap, $Unbox(Seq#Index(army#0, LitInt(2))): ref, _module.Bot.Repr)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:verboseName "ArmyRepr3 (correctness)"} Impl$$_module.__default.ArmyRepr3(army#0: Seq Box
       where $Is(army#0, TSeq(Tclass._module.Bot()))
         && $IsAlloc(army#0, TSeq(Tclass._module.Bot()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  requires Seq#Length(army#0) == LitInt(3);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ArmyRepr#canCall($Heap, army#0);
  ensures Set#Equal(_module.__default.ArmyRepr($Heap, army#0), 
    Set#Union(Set#Union(read($Heap, $Unbox(Seq#Index(army#0, LitInt(0))): ref, _module.Bot.Repr), 
        read($Heap, $Unbox(Seq#Index(army#0, LitInt(1))): ref, _module.Bot.Repr)), 
      read($Heap, $Unbox(Seq#Index(army#0, LitInt(2))): ref, _module.Bot.Repr)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:verboseName "ArmyRepr3 (correctness)"} Impl$$_module.__default.ArmyRepr3(army#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: ArmyRepr3, Impl$$_module.__default.ArmyRepr3
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
}



procedure {:verboseName "Main (well-formedness)"} CheckWellFormed$$_module.__default.Main();
  free requires 9 == $FunctionContextHeight;
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
  free requires 9 == $FunctionContextHeight;
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
  var defass#b0#0: bool;
  var b0#0: ref
     where defass#b0#0
       ==> $Is(b0#0, Tclass._module.Bot()) && $IsAlloc(b0#0, Tclass._module.Bot(), $Heap);
  var $nw: ref;
  var defass#b1#0: bool;
  var b1#0: ref
     where defass#b1#0
       ==> $Is(b1#0, Tclass._module.Bot()) && $IsAlloc(b1#0, Tclass._module.Bot(), $Heap);
  var b0##0: ref;
  var b1##0: ref;
  var b0##1: ref;
  var b1##1: ref;
  var b0##2: ref;
  var b1##2: ref;
  var defass#b2#0: bool;
  var b2#0: ref
     where defass#b2#0
       ==> $Is(b2#0, Tclass._module.Bot()) && $IsAlloc(b2#0, Tclass._module.Bot(), $Heap);
  var b0##3: ref;
  var b1##3: ref;
  var b2##0: ref;
  var b0##4: ref;
  var b1##4: ref;
  var b2##1: ref;

    // AddMethodImpl: Main, Impl$$_module.__default.Main
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module.Bot.Valid) == StartFuel__module.Bot.Valid;
    assume AsFuelBottom(StartFuelAssert__module.Bot.Valid)
       == StartFuelAssert__module.Bot.Valid;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(271,10)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(271,13)
    // TrCallStmt: Before ProcessCallStmt
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Bot.__ctor();
    // TrCallStmt: After ProcessCallStmt
    b0#0 := $nw;
    defass#b0#0 := true;
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(272,10)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(272,13)
    // TrCallStmt: Before ProcessCallStmt
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Bot.__ctor();
    // TrCallStmt: After ProcessCallStmt
    b1#0 := $nw;
    defass#b1#0 := true;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(273,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b0##0 := b0#0;
    assert defass#b1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b1##0 := b1#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (read($Heap, b0##0, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b1##0, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FlyRobots(b0##0, b1##0);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(274,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b0##1 := b0#0;
    assert defass#b1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b1##1 := b1#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (read($Heap, b0##1, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b1##1, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FlyRobots(b0##1, b1##1);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(275,12)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b0##2 := b1#0;
    assert defass#b0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b1##2 := b0#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (read($Heap, b0##2, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b1##2, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FlyRobots(b0##2, b1##2);
    // TrCallStmt: After ProcessCallStmt
    // ----- assignment statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(277,10)
    assume true;
    // ----- init call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(277,13)
    // TrCallStmt: Before ProcessCallStmt
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Bot.__ctor();
    // TrCallStmt: After ProcessCallStmt
    b2#0 := $nw;
    defass#b2#0 := true;
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(278,11)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b0##3 := b0#0;
    assert defass#b1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b1##3 := b1#0;
    assert defass#b2#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b2##0 := b2#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            read($Heap, b0##3, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b1##3, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b2##0, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FormArmy(b0##3, b1##3, b2##0);
    // TrCallStmt: After ProcessCallStmt
    // ----- call statement ----- C:\Users\Gaurav\Doktorat\viper_lab\monomorphization\shaz_files\dafny_test_suite_selection\FlyingRobots.dfy(279,11)
    // TrCallStmt: Before ProcessCallStmt
    assert defass#b2#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b0##4 := b2#0;
    assert defass#b0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b1##4 := b0#0;
    assert defass#b1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b2##1 := b1#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            read($Heap, b0##4, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b1##4, _module.Bot.Repr)[$Box($o)]
             || read($Heap, b2##1, _module.Bot.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.FormArmy(b0##4, b1##4, b2##1);
    // TrCallStmt: After ProcessCallStmt
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

const unique tytagFamily$_tuple#3: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$Point: TyTagFamily;

const unique tytagFamily$Arm: TyTagFamily;

const unique tytagFamily$Bot: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$val: NameFamily;

const unique field$Value: NameFamily;

const unique field$Repr: NameFamily;

const unique field$x: NameFamily;

const unique field$y: NameFamily;

const unique field$z: NameFamily;

const unique field$polar: NameFamily;

const unique field$azim: NameFamily;

const unique field$pos: NameFamily;

const unique field$left: NameFamily;

const unique field$right: NameFamily;
