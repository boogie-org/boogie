// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %boogie -noinfer -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// --------------------  1-dimensional arrays  --------------------

var A: [ref]int;

procedure P0(o: ref, q: ref, y: int)
  requires o != q;
  modifies A;
  ensures A[o] == old(A[o]) + y;
  ensures (forall p: ref :: A[p] == old(A[p]) || p == o);
{
  var k: int;

  start:
    k := A[q];
    A[o] := y + A[o];
    A[q] := k;
    return;
}

procedure P1(o: ref, q: ref, y: int)
  // This procedure does not have the assumption that o != q.
  modifies A;
  // It also does not ensures anything about A[o]
  ensures (forall p: ref :: A[p] == old(A[p]) || p == o);
{
  var k: int;

  start:
    k := A[q];
    A[o] := y + A[o];
    A[q] := k;
    return;
}

procedure P2(o: ref, q: ref, y: int)
  // This procedure does not have the assumption that o != q.
  modifies A;
  ensures A[o] == old(A[o]) + y;
{
  var k: int;

  start:
    k := A[q];
    A[o] := y + A[o];
    A[q] := k;
    return;
}  // error: postcondition violated (if o == q)

// --------------------  2-dimensional arrays  --------------------

var B: [ref,name]int;
const F: name;

procedure Q0(o: ref, q: ref, y: int, G: name)
  requires o != q && F != G;
  modifies B;
  ensures B[o,F] == old(B[o,F]) + y;
  ensures (forall p: ref, f: name :: B[p,f] == old(B[p,f]) ||
                                     (p == o && f == F));
{
  var k: int;

  start:
    k := B[q,G];
    B[o,F] := y + B[o,F];
    B[q,G] := k;
    return;
}

procedure Q1(o: ref, q: ref, y: int, G: name)
  // This procedure does not have the assumption that o != q && F != G.
  modifies B;
  // It also does not ensures anything about B[o,F]
  ensures (forall p: ref, f: name :: B[p,f] == old(B[p,f]) ||
                                     (p == o && f == F));
{
  var k: int;

  start:
    k := B[q,G];
    B[o,F] := y + B[o,F];
    B[q,G] := k;
    return;
}

procedure Q2(o: ref, q: ref, y: int, G: name)
  requires F != G;
  // This procedure does not have the assumption that o != q.
  modifies B;
  ensures B[o,F] == old(B[o,F]) + y;
{
  var k: int;

  start:
    k := B[q,G];
    B[o,F] := y + B[o,F];
    B[q,G] := k;
    return;
}

procedure Q3(o: ref, q: ref, y: int, G: name)
  requires o != q;
  // This procedure does not have the assumption that F != G.
  modifies B;
  ensures B[o,F] == old(B[o,F]) + y;
{
  var k: int;

  start:
    k := B[q,G];
    B[o,F] := y + B[o,F];
    B[q,G] := k;
    return;
}

procedure Q4(o: ref, q: ref, y: int, G: name)
  // This procedure does not have either of the assumptions o != q and F != G.
  modifies B;
  ensures B[o,F] == old(B[o,F]) + y;
{
  var k: int;

  start:
    k := B[q,G];
    B[o,F] := y + B[o,F];
    B[q,G] := k;
    return;
}  // error: postcondition violated

// --------------------  more tests  --------------------

procedure Skip0(o: ref, q: ref, G: name, H: name)
  modifies A,B;
  ensures (forall p: ref :: A[p] == old(A[p]));
  ensures (forall p: ref, g: name :: B[p,g] == old(B[p,g]));
{
  start:
    return;
}

procedure Skip1(o: ref, q: ref, G: name, H: name)
  modifies A,B;
  ensures (forall p: ref :: A[p] == old(A[p]));
  ensures (forall p: ref, g: name :: B[p,g] == old(B[p,g]));
{
  var k: int;
  var l: int;

  start:
    k := A[o];
    l := A[q];
    goto oneWay, theOtherWay;

  oneWay:
    A[o] := k;
    A[q] := l;
    goto next;

  theOtherWay:
    A[q] := l;
    A[o] := k;
    goto next;

  next:
    k := B[o,G];
    l := B[q,H];
    goto Lx, Ly;

  Lx:
    B[o,G] := k;
    B[q,H] := l;
    return;

  Ly:
    B[q,H] := l;
    B[o,G] := k;
    return;
}

type name, ref;
