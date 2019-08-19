// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %boogie -noinfer -freeVarLambdaLifting "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

procedure Simplest() {
  var id1, id2 : [int]int;
  id1 := (lambda x: int :: x);
  id2 := (lambda x: int :: x);
  assert id1 == id2;
  id2 := (lambda x: int :: 0);
  assert id1 == id2; // fail
}

procedure Const() {
  var v, w : [int][int]int;
  var f, g : [int, int]int;

  v := (lambda x : int :: (lambda y : int :: x));

  w := (lambda x : int :: (lambda i : int :: x));
  assert v == w;

  w := (lambda i : int :: (lambda y : int :: i));
  assert v == w;

  w := (lambda a : int :: (lambda b : int :: b));
  assert v == w; // should fail, now two different functions

  f := (lambda x : int, y : int :: x);
  assert f == (lambda p : int, q : int :: p);
  assert f == (lambda p : int, q : int :: q); // should fail, different functions
}

procedure PolyConst() {
  assert (lambda<A> x: A :: x) == (lambda<A>x: A :: x); // fails because of type parameters. this could be fixed.
  /* // more tests, when it is fixed
  var k1 : <A1>[A1]<B1>[B1]A1;
  var k2 : <A2>[A2]<B2>[B2]A2;
  k1 := (lambda<A> x: A :: (lambda<B> y: B :: x));
  k2 := (lambda<A> x: A :: (lambda<C> z: C :: x));
  assert k1 == k2;
  k2 := (lambda<X> u: X :: (lambda<Y> v: Y :: u));
  assert k1 == k2;  */
}

procedure FreeVarP() {
  var k : real;
  var m : [int]real;
  m := (lambda x:int :: k);
  assert m[0] == k;
}

procedure FreeVarQ() {
  var k : int;
  var m : [int]int;
  m := (lambda x:int :: k); // should be a different lambda from in FreeVarP, because they have different types
  assert m[0] == k;
}

procedure Quantifiers() {
  var k1 : [int]bool;
  var k2 : [int]bool;
  k1 := (lambda x: int :: (exists y: int :: x > y));
  k2 := (lambda x: int :: (exists y: int :: x > y));
  assert k1 == k2;
  k2 := (lambda x: int :: (exists z: int :: x > z));
  assert k1 == k2;
}

procedure FreeVariables() {
  var f : [bool]bool;
  var g : [bool]bool;

  var a : bool;
  var b : bool;

  f := (lambda r: bool :: a);
  g := (lambda s: bool :: b);
  if (a == b) {
    assert f == g; // should be OK
  } else {
    assert f == g; // should fail
  }
}

procedure FreeVariables2() {
  var k : [bool,bool]bool;

  var f : [bool]bool;
  var g : [bool]bool;

  var a : bool;
  var b : bool;

  f := (lambda r: bool :: k[a,b]);
  g := (lambda s: bool :: k[b,a]);
  if (a == b) {
    assert f == g; // should be OK
  } else {
    assert f == g; // should fail
  }
}

procedure FreeVariables3() {
  var m : [bool,bool,bool]bool;

  var f : [bool]bool;
  var g : [bool]bool;

  var a : bool;
  var b : bool;

  f := (lambda r: bool :: m[a,a,b]);
  g := (lambda s: bool :: m[a,b,b]);
  if (a == b) {
    assert f == g; // should fail for /freeVarLambdaLifting; OK for max-hole lambda lifting
  } else {
    assert f == g; // should fail because they are different lambda
  }
}

function f(int) : int;

procedure Triggers() {
  var a,b : [int]bool;
  a := (lambda x:int :: (forall u:int :: { f(u) } x == f(u)));
  b := (lambda y:int :: (forall v:int :: { f(v) } y == f(v)));
  assert a == b;
  b := (lambda y:int :: (forall v:int :: y == f(v)));
  assert a == b; // should fail because triggers are different
}

procedure Attributes() {
  var a,b : [int]bool;
  a := (lambda x:int :: (forall u:int :: {:attrib f(u) } x == f(u)));
  b := (lambda y:int :: (forall v:int :: {:attrib f(v) } y == f(v)));
  assert a == b;
  b := (lambda y:int :: (forall v:int :: {:battrib f(v) } y == f(v)));
  assert a == b; // should fail since attributes are different
  a := (lambda x:int :: (forall u:int :: {:battrib f(x) } x == f(u)));
  assert a == b; // should fail since attributes are different
}

procedure Old() {
  var u,v : [int]int;
  var a,b : int;
  u := (lambda x:int :: old(x+a));
  v := (lambda y:int :: old(y+b));
  if (a == b) {
    assert u == v; // ok
  } else {
    assert u == v; // fails
  }
}

type Box;
function $Box<T>(T) : Box;
function $Unbox<T>(Box) : T;

procedure Coercion() {
  assert (lambda x: Box :: $Box($Unbox(x): int))
      == (lambda y: Box :: $Box($Unbox(y): int));
}


function F(int,int): int;
const n: [int]bool;
procedure FreeVarOnlyInTrigger() {
  // The following once used to crash, because trigger expressions were not
  // visited while computing free variables.
  assert (forall m: int ::  // error
    n == (lambda x: int :: (exists y: int :: { F(m,y) } true)));
}

type TA;
type TB;
function G(TA, TB): int;
procedure MultipleTriggers() {
  // The following once used to crash, because max holes for triggers were
  // replaced in the wrong order.
  assert (forall a: TA, m: [TB]bool ::  // error
    m == (lambda y: TB :: (exists x: TB :: { G(a, x) } { m[x] } G(a, x) == 10)));
}

procedure LetBinder() {
  var m: [bool]bool;
  // The following once used to crash, because let-bound variables were not
  // considered local.
  m := (lambda b: bool :: (var u := b; u));
}
