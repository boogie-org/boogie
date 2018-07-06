// RUN: %boogie "%s" -mv:- > "%t"
// RUN: %diff "%s.expect" "%t"
type Ref;
type FieldName;
var Heap: [Ref,FieldName]int;

const unique F: FieldName;

procedure P(this: Ref, x: int, y: int) returns (r: int)
  requires 118 <= 3 * x && 4 * x < 163 && Heap[this, F] * 5 == -x;  // make output deterministic
  ensures 0 <= r;
{
  var m: int;

  assume {:captureState "top"} true;

  m := Heap[this, F];
  if (0 <= x) {
    assume {:captureState "then"} true;
    m := m + 1;
    assume {:captureState "postUpdate0"} true;
  } else {
    assume {:captureState "else"} true;
    m := (m + y) * (m + y);
    assume {:captureState "postUpdate1"} true;
  }
  r := m + m;
  m := 7;
  assume {:captureState "end"} true;
}
