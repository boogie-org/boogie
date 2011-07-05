//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
import scala.collection.mutable.Set;

/*
This object computes the Boogie prelude for the translator, which consists of different
components (objects that are subtypes of PreludeComponent). It is possible to include
such components only on demand, when they are actually needed. For instance, the sequence
axiomatization is only included if sequences are used in the program at hand.
*/
object TranslatorPrelude {
  
  // adds component c to the prelude. has no effect if c is already present.
  def addComponent(c: PreludeComponent*): Unit = {
    components ++= c
  }
  
  // removes a component from the prelude. use with great care, as other parts of
  // the system could depend on the component c being present in the prelude.
  def removeComponent(c: PreludeComponent*): Unit = {
    components --= c
  }
  
  // default components
  private val components: Set[PreludeComponent] = Set(CopyrightPL, TypesPL, PermissionTypesAndConstantsPL, CreditsAndMuPL, PermissionFunctionsAndAxiomsPL, IfThenElsePL, ArithmeticPL)

  // get the prelude (with all components currently included)
  def P: String = {
    val l = components.toList.sortWith((a,b) => a compare b)
    l.foldLeft("")((s:String,a:PreludeComponent) => s + "\n" + (a text)) + 
"""

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

"""
  }

}

sealed abstract class PreludeComponent {
  // determines the order in which the components are output
  def compare(that: PreludeComponent): Boolean = {
    val order: List[PreludeComponent] = List(CopyrightPL, TypesPL, PermissionTypesAndConstantsPL, PercentageFixedDenominatorPL, PercentageFunctionPL, PercentageUninterpretedFunctionPL, CreditsAndMuPL, PermissionFunctionsAndAxiomsPL, IfThenElsePL, ArithmeticPL, AxiomatizationOfSequencesPL)
    if (!order.contains(this)) false
    else order.indexOf(this) < order.indexOf(that)
  }
  def text: String
}

object CopyrightPL extends PreludeComponent {
  val text = "// Copyright (c) 2008, Microsoft"
}
object TypesPL extends PreludeComponent {
  val text = """
type Field a;
type HeapType = <a>[ref,Field a]a;
type MaskType = <a>[ref,Field a][PermissionComponent]int;
type CreditsType = [ref]int;
type ref;
const null: ref;

var Heap: HeapType;"""
}
object PermissionTypesAndConstantsPL extends PreludeComponent {
  val text = """
type PermissionComponent;
const unique perm$R: PermissionComponent;
const unique perm$N: PermissionComponent;
var Mask: MaskType where IsGoodMask(Mask);
const Permission$denominator: int;
axiom Permission$denominator > 0;
const Permission$FullFraction: int;
const Permission$Zero: [PermissionComponent]int;
axiom Permission$Zero[perm$R] == 0 && Permission$Zero[perm$N] == 0;
const Permission$Full: [PermissionComponent]int;
axiom Permission$Full[perm$R] == Permission$FullFraction && Permission$Full[perm$N] == 0;
const ZeroMask: MaskType;
axiom (forall<T> o: ref, f: Field T, pc: PermissionComponent :: ZeroMask[o,f][pc] == 0);
axiom IsGoodMask(ZeroMask);
const unique joinable: Field int;
axiom NonPredicateField(joinable);
const unique token#t: TypeName;
const unique forkK: Field int;
axiom NonPredicateField(forkK);
const channelK: int;
const monitorK: int;
const predicateK: int;"""
}
object PercentageStandardPL extends PreludeComponent {
  val text = """
axiom (0 < channelK && 1000*channelK < Permission$denominator);
axiom (0 < monitorK && 1000*monitorK < Permission$denominator);
axiom (0 < predicateK && 1000*predicateK < Permission$denominator);
axiom Permission$FullFraction  == 100*Permission$denominator;
axiom predicateK == channelK && channelK == monitorK;"""
}
object PercentageFixedDenominatorPL extends PreludeComponent {
  val text = """
axiom Permission$denominator == 100000000000;"""
}
object PercentageFunctionPL extends PreludeComponent {
  val text = """
function Fractions(n: int): int
{
  n * Permission$denominator
}
axiom (forall x,y: int :: 0 <= x && x <= y ==> Fractions(x) <= Fractions(y));

axiom Permission$FullFraction  == Fractions(100);
axiom 0 < channelK && 1000*channelK < Fractions(1);
axiom 0 < monitorK && 1000*monitorK < Fractions(1);
axiom 0 < predicateK && 1000*predicateK < Fractions(1);
axiom predicateK == channelK && channelK == monitorK;"""
}
object PercentageUninterpretedFunctionPL extends PreludeComponent {
  val text = """
function Fractions(n: int): int;
function Fractions'(n: int): int;
axiom (forall x: int :: { Fractions(x) } Fractions(x) == Fractions'(x));
axiom (forall x,y: int :: 0 <= x && x <= y ==> Fractions'(x) <= Fractions'(y));
axiom (forall x,y: int :: { Fractions(x), Fractions(y) } Fractions(x) + Fractions(y) == Fractions'(x+y));

axiom Permission$FullFraction  == Fractions(100);
axiom 0 < channelK && 1000*channelK < Fractions(1);
axiom 0 < monitorK && 1000*monitorK < Fractions(1);
axiom 0 < predicateK && 1000*predicateK < Fractions(1);
axiom predicateK == channelK && channelK == monitorK;"""
}
object CreditsAndMuPL extends PreludeComponent {
  val text = """
var Credits: CreditsType;

function IsGoodState<T>(T) returns (bool);
function combine<T,U>(T, U) returns (T);
const nostate: HeapType;

axiom (forall<T,U> a: T, b: U :: {IsGoodState(combine(a, b))} IsGoodState(combine(a, b)) <==> IsGoodState(a) && IsGoodState(b));
axiom IsGoodState(nostate);

type ModuleName;
const CurrentModule: ModuleName;
type TypeName;
function dtype(ref) returns (TypeName);
const CanAssumeFunctionDefs: bool;

type Mu;
const unique mu: Field Mu;
axiom NonPredicateField(mu);
function MuBelow(Mu, Mu) returns (bool);  // strict partial order
axiom (forall m: Mu, n: Mu ::
  { MuBelow(m,n), MuBelow(n,m) }
  !(MuBelow(m,n) && MuBelow(n,m)));
axiom (forall m: Mu, n: Mu, o: Mu ::
  { MuBelow(m,n), MuBelow(n,o) }
  MuBelow(m,n) && MuBelow(n,o) ==> MuBelow(m,o));
const $LockBottom: Mu;
axiom (forall m, n: Mu :: MuBelow(m, n) ==> n != $LockBottom);

const unique held: Field int;
function Acquire$Heap(int) returns (HeapType);
function Acquire$Mask(int) returns (MaskType);
function Acquire$Credits(int) returns (CreditsType);
axiom NonPredicateField(held);

function LastSeen$Heap(Mu, int) returns (HeapType);
function LastSeen$Mask(Mu, int) returns (MaskType);
function LastSeen$Credits(Mu, int) returns (CreditsType);

const unique rdheld: Field bool;
axiom NonPredicateField(rdheld);
function wf(h: HeapType, m: MaskType) returns (bool);

function IsGoodInhaleState(ih: HeapType, h: HeapType,
                           m: MaskType) returns (bool)
{
  (forall<T> o: ref, f: Field T :: { ih[o, f] }  CanRead(m, o, f) ==> ih[o, f] == h[o, f]) &&
  (forall o: ref :: { ih[o, held] }  (0<ih[o, held]) == (0<h[o, held])) &&
  (forall o: ref :: { ih[o, rdheld] }  ih[o, rdheld] == h[o, rdheld]) &&
  (forall o: ref :: { h[o, held] }  (0<h[o, held]) ==> ih[o, mu] == h[o, mu]) &&
  (forall o: ref :: { h[o, rdheld] }  h[o, rdheld] ==> ih[o, mu] == h[o, mu])
}"""
}
object PermissionFunctionsAndAxiomsPL extends PreludeComponent {
  val text = """
// ---------------------------------------------------------------
// -- Permissions ------------------------------------------------
// ---------------------------------------------------------------

function {:expand false} CanRead<T>(m: MaskType, obj: ref, f: Field T) returns (bool)
{
  0 < m[obj,f][perm$R] || 0 < m[obj,f][perm$N]
}
function {:expand false} CanWrite<T>(m: MaskType, obj: ref, f: Field T) returns (bool)
{
  m[obj,f][perm$R] == Permission$FullFraction && m[obj,f][perm$N] == 0
}
function {:expand true} IsGoodMask(m: MaskType) returns (bool)
{
  (forall<T> o: ref, f: Field T ::
      0 <= m[o,f][perm$R] && 
      (NonPredicateField(f) ==> 
        (m[o,f][perm$R]<=Permission$FullFraction &&
        (0 < m[o,f][perm$N] ==> m[o,f][perm$R] < Permission$FullFraction))) &&
      (m[o,f][perm$N] < 0 ==> 0 < m[o,f][perm$R]))
}

axiom (forall h: HeapType, m: MaskType, o: ref, q: ref :: {wf(h, m), h[o, mu], h[q, mu]} wf(h, m) && o!=q && (0 < h[o, held] || h[o, rdheld]) && (0 < h[q, held] || h[q, rdheld]) ==> h[o, mu] != h[q, mu]);

function DecPerm<T>(m: MaskType, o: ref, f: Field T, howMuch: int) returns (MaskType);

axiom (forall<T,U> m: MaskType, o: ref, f: Field T, howMuch: int, q: ref, g: Field U :: {DecPerm(m, o, f, howMuch)[q, g][perm$R]}
      DecPerm(m, o, f, howMuch)[q, g][perm$R] == ite(o==q && f ==g, m[q, g][perm$R] - howMuch, m[q, g][perm$R])
);

function DecEpsilons<T>(m: MaskType, o: ref, f: Field T, howMuch: int) returns (MaskType);

axiom (forall<T,U> m: MaskType, o: ref, f: Field T, howMuch: int, q: ref, g: Field U :: {DecPerm(m, o, f, howMuch)[q, g][perm$N]}
         DecEpsilons(m, o, f, howMuch)[q, g][perm$N] == ite(o==q && f ==g, m[q, g][perm$N] - howMuch, m[q, g][perm$N])
);

function IncPerm<T>(m: MaskType, o: ref, f: Field T, howMuch: int) returns (MaskType);

axiom (forall<T,U> m: MaskType, o: ref, f: Field T, howMuch: int, q: ref, g: Field U :: {IncPerm(m, o, f, howMuch)[q, g][perm$R]}
         IncPerm(m, o, f, howMuch)[q, g][perm$R] == ite(o==q && f ==g, m[q, g][perm$R] + howMuch, m[q, g][perm$R])
);

function IncEpsilons<T>(m: MaskType, o: ref, f: Field T, howMuch: int) returns (MaskType);

axiom (forall<T,U> m: MaskType, o: ref, f: Field T, howMuch: int, q: ref, g: Field U :: {IncPerm(m, o, f, howMuch)[q, g][perm$N]}
         IncEpsilons(m, o, f, howMuch)[q, g][perm$N] == ite(o==q && f ==g, m[q, g][perm$N] + howMuch, m[q, g][perm$N])
);

function Havocing<T,U>(h: HeapType, o: ref, f: Field T, newValue: U) returns (HeapType);

axiom (forall<T,U> h: HeapType, o: ref, f: Field T, newValue: U, q: ref, g: Field U :: {Havocing(h, o, f, newValue)[q, g]}
         Havocing(h, o, f, newValue)[q, g] == ite(o==q && f ==g, newValue, h[q, g])
);

function Call$Heap(int) returns (HeapType);
function Call$Mask(int) returns (MaskType);
function Call$Credits(int) returns (CreditsType);
function Call$Args(int) returns (ArgSeq);
type ArgSeq = <T>[int]T;

function EmptyMask(m: MaskType) returns (bool);
axiom (forall m: MaskType :: {EmptyMask(m)} EmptyMask(m) <==> (forall<T> o: ref, f: Field T :: NonPredicateField(f) ==> m[o, f][perm$R]<=0 && m[o, f][perm$N]<=0));

const ZeroCredits: CreditsType;
axiom (forall o: ref :: ZeroCredits[o] == 0);
function EmptyCredits(c: CreditsType) returns (bool);
axiom (forall c: CreditsType :: {EmptyCredits(c)} EmptyCredits(c) <==> (forall o: ref :: o != null ==> c[o] == 0));

function NonPredicateField<T>(f: Field T) returns (bool);
function PredicateField<T>(f: Field T) returns (bool);
axiom (forall<T> f: Field T :: NonPredicateField(f) ==> ! PredicateField(f));
axiom (forall<T> f: Field T :: PredicateField(f) ==> ! NonPredicateField(f));

function submask(m1: MaskType, m2: MaskType) returns (bool);

axiom (forall m1: MaskType, m2: MaskType :: {submask(m1, m2)}
  submask(m1, m2) <==> (forall<T> o: ref, f: Field T :: (m1[o, f][perm$R] < m2[o, f][perm$R]) || (m1[o, f][perm$R] == m2[o, f][perm$R] && m1[o, f][perm$N] <= m2[o, f][perm$N]))
);"""
}
object IfThenElsePL extends PreludeComponent {
  val text = """
// ---------------------------------------------------------------
// -- If then else -----------------------------------------------
// ---------------------------------------------------------------

function ite<T>(bool, T, T) returns (T);
axiom (forall<T> con: bool, a: T, b: T :: {ite(con, a, b)} con ==> ite(con, a, b) == a);
axiom (forall<T> con: bool, a: T, b: T :: {ite(con, a, b)} ! con ==> ite(con, a, b) == b);"""
}
object ArithmeticPL extends PreludeComponent {
  val text = """
// ---------------------------------------------------------------
// -- Arithmetic -------------------------------------------------
// ---------------------------------------------------------------

// the connection between % and /
axiom (forall x:int, y:int :: {x % y} {x / y}  x % y == x - x / y * y);

// sign of denominator determines sign of remainder
axiom (forall x:int, y:int :: {x % y}  0 < y  ==>  0 <= x % y  &&  x % y < y);
axiom (forall x:int, y:int :: {x % y}  y < 0  ==>  y < x % y  &&  x % y <= 0);

// the following axiom has some unfortunate matching, but it does state a property about % that
// is sometime useful
axiom (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b  ==>  a + d <= b);"""
}
object AxiomatizationOfSequencesPL extends PreludeComponent {
  val text = """
// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

type Seq T;

function Seq#Length<T>(Seq T) returns (int);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>() returns (Seq T);
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T) returns (Seq T);
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, index: int, val: T, newLength: int) returns (Seq T);
axiom (forall<T> s: Seq T, i: int, v: T, len: int :: { Seq#Length(Seq#Build(s,i,v,len)) }
  0 <= len ==> Seq#Length(Seq#Build(s,i,v,len)) == len);

function Seq#Append<T>(Seq T, Seq T) returns (Seq T);
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int) returns (T);
axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
axiom (forall<T> s: Seq T, i: int, v: T, len: int, n: int :: { Seq#Index(Seq#Build(s,i,v,len),n) }
  0 <= n && n < len ==>
    (i == n ==> Seq#Index(Seq#Build(s,i,v,len),n) == v) &&
    (i != n ==> Seq#Index(Seq#Build(s,i,v,len),n) == Seq#Index(s,n)));

function Seq#Contains<T>(Seq T, T) returns (bool);
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) <==>
    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
axiom (forall x: ref ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));
axiom (forall<T> s: Seq T, i: int, v: T, len: int, x: T ::
  { Seq#Contains(Seq#Build(s, i, v, len), x) }
  Seq#Contains(Seq#Build(s, i, v, len), x) <==>
    (0 <= i && i < len && x == v)  ||  
    (exists j: int :: { Seq#Index(s,j) } 0 <= j && j < Seq#Length(s) && j < len && j!=i && Seq#Index(s,j) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T) returns (bool);
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
axiom(forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int) returns (bool);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take<T>(s: Seq T, howMany: int) returns (Seq T);
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {:weight 25}
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int) returns (Seq T);
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } {:weight 25}
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

axiom (forall<T> s, t: Seq T ::
  { Seq#Append(s, t) }
  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

function Seq#Range(min: int, max: int) returns (Seq int);

axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);

axiom (forall<T> x, y: T ::
  { Seq#Contains(Seq#Singleton(x),y) }
    Seq#Contains(Seq#Singleton(x),y) <==> x==y);"""
}
