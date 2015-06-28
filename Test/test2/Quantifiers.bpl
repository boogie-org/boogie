// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// ----------------------------------------------------------------------- single trigger

function f(int, int) returns (int);

axiom (forall x: int, y: int :: f(x,y) < x+y);
axiom (forall x: int :: { f(x,10) } f(x,10) == 3);

procedure P(a: int, b: int)
  requires a <= 25 && b <= 30;
{
  start:
    assert f(a,b) <= 100;
    return;
}

procedure Q(a: int, b: int)
  requires a + 2 <= b;
{
  start:
    assert f(a,b) == 3;   // not provable with the trigger given above
    return;
}

procedure R(a: int, b: int)
  requires a + 2 <= b;
{
  start:
    assume b <= 10 && 8 <= a;
    assert f(a,b) == 3;   // now, the trigger should fire
    return;
}

// ----------------------------------------------------------------------- multi trigger

function g(int, int) returns (int);

axiom (forall x: int, y: int :: { g(x,10),g(x,y) } g(x,y) == 3);  // multi-trigger

procedure S(a: int, b: int)
  requires a + 2 <= b;
{
  start:
    assert g(a,b) == 3;   // not provable with the trigger given above
    return;
}

procedure T(a: int, b: int)
  requires a + 2 <= b;
{
  start:
    assume b <= 10 && 8 <= a;
    assert g(a,b) == 3;   // this should trigger
    return;
}

// ----------------------------------------------------------------------- several triggers

function h(int, int) returns (int);

axiom (forall y: int :: { g(y,y) } { h(y,h(y,10)) } h(y, h(y,y)) == y);  // several triggers

procedure U0(a: int)
{
  start:
    assert h(a,h(a,a)) == a;   // not provable with the triggers given above
    return;
}

procedure U1(a: int, b: int)
{
  start:
    assume g(a,b) == 5;
    assert h(a,h(a,a)) == a;   // not provable with the triggers given above
    return;
}

procedure V0(a: int, b: int)
  requires a == b;
{
  start:
    assume g(a,b) == 5;
    assert h(a,h(a,a)) == a;   // this should trigger
    return;
}

procedure V1(a: int, b: int)
{
  start:
    assume a == 10;
    assert h(a,h(a,a)) == a;   // this should trigger
    return;
}

procedure V2(a: int, b: int)
{
  start:
    assume 0 <= h(a,h(a,10));
    assume a == 17;
    assert h(a,h(a,a)) == a;   // this should trigger
    return;
}

// ----------------------------------------------------------------------- negated triggers

function ka(ref) returns (int);
function kb(ref) returns (int);
function kbSynonym(ref) returns (int);
function isA(ref, name) returns (bool);
function isB(ref, name) returns (bool);
const $T: name;

axiom (forall o: ref ::
       isA(o, $T) ==> ka(o) < ka(o));  // automatically inferred triggers can be both isA(o,$T) and ka(o)

axiom (forall o: ref ::
       {:nopats isB(o, $T) }
       isB(o, $T) ==> kb(o) < kbSynonym(o));  // prevent isB(o,$T) from being used as a trigger

axiom (forall o: ref :: kb(o) == kbSynonym(o));

procedure W(o: ref, e: int)
  requires isB(o, $T);
{
  start:
    assert e > 20;  // the isB axiom should not trigger, so this cannot be proved
    return;
}

procedure X0(o: ref, e: int)
  requires isA(o, $T);
{
  start:
    assert e > 20;  // this should trigger the isA axiom, so anything is provable
    return;
}

procedure X1(o: ref, e: int, u: int)
  requires isB(o, $T);
{
  start:
    assume f(kb(o), kb(o)) == u;
    assert e > 20;  // this should now trigger the isB axiom, so anything is provable
    return;
}

procedure X2(o: ref, e: int, u: int)
  requires isB(o, $T);
{
  start:
    assert e > 20;  // error is report here, providing evidence that the isB axiom has not been triggered
    return;
}

type name, ref;
