// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var H: [ref,name]int;
var that: ref;

const X: name;
const Y: name;

procedure P(this: ref);
  modifies H;
  ensures H[this,X] == 5;

implementation P(this: ref) {
  start:
    H[this,X] := 5;
    return;
}

procedure Q(this: ref);
  modifies H;
  ensures (forall o: ref, F: name :: o == this && F == X ==> H[o,F] == 5);

implementation Q(this: ref) {
  start:
    H[this,X] := 5;
    return;
}

implementation Q(this: ref) {
  start:
    H[this,X] := 7;
    return;  // error
}

implementation Q(this: ref) {
  start:
    return;  // error
}

implementation Q(this: ref) {
  start:
    H[that,X] := 5;
    return;  // error
}

implementation Q(this: ref) {
  start:
    H[this,Y] := 5;
    return;  // error
}

implementation Q(this: ref) {
  start:
    call P(this);
    return;
}

implementation Q(this: ref) {
  start:
    call Q(this);
    return;
}

implementation Q(this: ref) {
  start:
    call P(this);
    call Q(this);
    return;
}

implementation Q(this: ref) {
  start:
    call P(that);
    return;  // error
}

type name, ref;
