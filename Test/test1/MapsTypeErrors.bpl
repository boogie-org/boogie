// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var m: []int;
var p: <a>[]a;

type ref;
const null: ref;

procedure P()
  requires m[] == 5;
  modifies m;
  modifies p;
  ensures m[] == 30;
  ensures p[] + p[] == 24;
  ensures p[] == null;
{
  m[] := 12;
  p[] := 12;
  p[] := true;
  assert p[] == m[];
  assert p[];
  m := m[:= 30];
  p := p[:=null];
}

procedure A()
{
  m[] := 12;  // error: illegal assignment, because m is not in modifies clause
}

procedure B()
  modifies m;
{
  m := m[];  // type error
  m[] := m;  // type error
}

procedure C()
  modifies m;
{
  m[] := true;  // type error
}

// -----

procedure Genrc<T>(x: int) returns (t: T);

procedure Caller() returns (b: bool)
{
  var y: ref;
  call y := Genrc(5);
  b := y == null;
}

// ----

type Field a;
type HeapType = <a>[ref, Field a]a;
const F0: Field int;
const F1: Field bool;
const alloc: Field bool;
var Heap: HeapType;

function LiberalEqual<a,b>(a, b) returns (bool);
function StrictEqual<a>(a,a) returns (bool);
function IntEqual(Field int,Field int) returns (bool);

procedure FrameCondition(this: ref)
  requires F0 == F1;  // error
  requires LiberalEqual(F0, F1);
  requires StrictEqual(F0, F0);
  requires StrictEqual(F0, F1);  // error
  modifies Heap;
  ensures (forall<alpha> o: ref, f: Field alpha ::
    Heap[o,f] == old(Heap)[o,f] ||
    !old(Heap)[o,alloc] ||
    (o == this && StrictEqual(f, F0)) ||  // error: f and F0 don't have the same type
    (o == this && LiberalEqual(f, f)) ||
    (o == this && IntEqual(F0, f))  // error: f and F0 don't have the same type
    );
{
}

// ---- bitvector inference ----

function Gimmie<T>() returns (T);
function Same<T>(T,T) returns (T);
procedure ConsumeAnything<T>(t: T);

procedure Bvs(x: bv31, y: int) returns (a: bv32)
{
  a := x[50 : 18];  // error
  a := y[50 : 18];  // error

  a := Gimmie();  // fine, this can be made to have at least 32 bits
  a := Gimmie()[50 : 18];  // fine, result is always 32 bits and Gimmie() can be made to have at least 50 bits
  a := Gimmie()[50 : 17];  // error, result is 33 bits (but there's nothing wrong with Gimmie())

  a := Gimmie() ++ Gimmie() ++ Gimmie();
  a := Gimmie() ++ Gimmie()[20:0];
  a := 0bv0 ++ Gimmie()[6:6] ++ Gimmie()[17:12] ++ Gimmie() ++ Gimmie() ++ Gimmie()[27:0];
  a := 0bv0 ++ Gimmie()[6:6] ++ Gimmie()[17:12] ++ Gimmie() ++ Gimmie() ++ Gimmie()[22:0];
  a := 0bv0 ++ Gimmie()[6:6] ++ Gimmie()[17:12] ++ Gimmie() ++ Gimmie()[22:0] ++ Gimmie();
  a := Gimmie() ++ 0bv0 ++ Gimmie()[6:6] ++ Gimmie()[17:12] ++ Gimmie() ++ Gimmie()[22:0];
  a := Same(Gimmie(), Gimmie());
  a := Same(Gimmie()[20:0], Gimmie());  // error, have only bv20, need bv32

  a := Same(Gimmie() ++ Gimmie()[20:0], 0bv32);
  a := Same(Gimmie() ++ Gimmie()[20:0], Gimmie());
  a := Same(Gimmie() ++ Gimmie()[20:0], Gimmie() ++ Gimmie());
  a := Same(Gimmie() ++ Gimmie()[20:0], Gimmie()[40:30] ++ Gimmie());
  call ConsumeAnything(Same(Gimmie() ++ Gimmie()[20:0], 0bv18));  // error, can't make things smaller
}

// ---- maps again ----

procedure Mmm() returns (a: [int,int]bool, b: HeapType, c: int)
{
  if (Gimmie()[null] == Gimmie()) {
    a := Same(Gimmie()[Gimmie(), Gimmie() := Gimmie()], Gimmie());
    b := Same(Gimmie()[Gimmie(), Gimmie() := Gimmie()], Gimmie());
    a := Same(Gimmie()[Gimmie(), Gimmie() := 4], Gimmie());  // error
    b := Same(Gimmie()[Gimmie(), Gimmie() := 5], Gimmie());
    b := Same(Gimmie()[Gimmie(), 6 := Gimmie()], Gimmie());  // error
  }
  c := Gimmie()[Gimmie() := 10][null];
  c := Gimmie()[Gimmie() := Gimmie()][null];
  c := Gimmie()[Gimmie() := false][null];
}
