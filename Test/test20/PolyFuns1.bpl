// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F<a>( <b>[b]a ) returns (bool);
const M:  <a>[ <b>[b]a ] bool;

procedure P()
{
  var f: <c>[c]c;
  var b: bool;

  b := F(f);  // type error
  b := M[f];  // type error
  b := (forall g: <c>[c]c :: F(g));  // type error
  b := (forall g: <c>[c]c :: M[g]);  // type error
}

type Field a;
axiom (exists<a> x:<c>[Field c]a, y:<d>[Field d]d :: x == y);   // error: not unifiable
axiom (forall<a> x:<c>[Field c]a, y:<d>[Field d]d :: x == y);   // error: not unifiable

procedure Uhu<a>(x: <c>[Field c]a, y: <d>[Field d]d);
procedure Oyeah<T>(t: T)
{
  var xx: <cc>[Field cc]T;
  var yy: <dd>[Field dd]dd;
  var zz: <ee>[Field T]ee;

  call Uhu(xx, yy);
  call Uhu(yy, yy);  // type error in argument 0
  call Uhu(xx, xx);  // type error in argument 1
  assert xx == yy;  // error: not unifiable
  assert yy == xx;  // error: not unifiable

  call Uhu(xx, zz);  // type error in argument 1
}

procedure Jitters()
{
  var x: <a>[a,a]int;
  var y: <b>[b,int]int;
  var z: <c>[int,c]int;
  assert x == y;  // error: not unifiable
  assert y == z;  // error: not unifiable
  assert x == z;  // error: not unifiable
}

procedure Nuther()
{
  var x: <a,b>[a,a,b]int;
  var y: <a,b>[a,b,b]int;
  assert x == y;  // error: not unifiable
}

type NagainCtor a;
procedure Nagain()
  requires (forall<a,b> x: a, y: b :: x == y);
  ensures (forall<a,b> x: a, y: Field b, z: NagainCtor b :: x == y && x == z);
  ensures (forall<b> y: Field b, z: NagainCtor b :: y == z);  // error: types not unifiable
{
}
