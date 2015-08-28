// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g0: int;
var g1: int;

var h0: [ref, name]int;
var h1: [ref, name]int;

const X: name;

procedure P(a: ref, hh: [ref, name]int) returns (b: int, hout: [ref, name]any);
  modifies h1, g0;

implementation P(a: ref, hh: [ref, name]int)
               returns (b: int, hout: [ref, name]any) {
  start:
    g0 := 5;
    g1 := 6;  // error: g1 is not in modifies clause
    a := null;  // error: in-parameters are not mutable 
    b := 12;
    goto next;
  next:
    havoc g0;
    havoc g1;  // error: g1 is not in modifies clause
    havoc a;  // error: in-parameters are not mutable
    havoc b;
    goto more;
  more:
    hh[a,X] := 101;  // error: in-parameter (hh) is not mutable
    h0[a,X] := 102;  // error: h0 is not in modifies clause
    h1[a,X] := 103;
    hh := h0;  // error: in-parameter is not mutable
    h0 := h1;  // error: h0 is not in modifies clause
    h1 := hh;
    havoc hh;  // error: in-parameter is not mutable
    havoc h0;  // error: h0 is not in modifies clause
    havoc h1;
    return;
}

procedure PX();
  modifies h1, g0;

procedure PY()
  modifies h1, g0;
{
  start:
    call PX();
    call PY();
    return;
}

procedure PZ()
  modifies h1;
{
  start:
    call PX();  // error: PX has larger frame than PZ
    return;
}

procedure Q() returns (x: int, y: int, h: [ref, name]int)
{
  start:
    return;
}

procedure QCallerBad()
{
  start:
    call g0, g1, h0 := Q();
    return;
}

procedure QCallerGood()
  modifies g0, h0;
{
  var t: int;

  start:
    call t, g0, h0 := Q();
    return;
}

procedure MismatchedTypes(x: int);

implementation MismatchedTypes(x: bool)  // error
{
  start:
    return;
}
implementation MismatchedTypes(y: bool)  // error (this time with a different name for the formal)
{
  start:
    return;
}


type ref, name, any;
const null : ref;
