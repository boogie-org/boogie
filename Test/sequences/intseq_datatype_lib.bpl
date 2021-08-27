// RUN: %parallel-boogie -lib "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Value;

function {:constructor} Integer(i: int): Value;
function {:constructor} Vector(v: Array Value): Value;

type {:datatype} Array _;
function {:constructor} Array<T>(v: Seq T): Array T;
function {:inline} EmptyArray<T>(): Array T {
    Array(Seq_Empty())
}
function {:inline} AddArray<T>(a: Array T, v: T): Array T {
    Array(Seq_Concat(v#Array(a), Seq_Unit(v)))
}
function {:inline} RemoveArray<T>(a: Array T): Array T {
    Array(Seq_Extract(v#Array(a), 0, Seq_Len(v#Array(a)) - 1))
}
function {:inline} ConcatArray<T>(a1: Array T, a2: Array T): Array T {
    Array(Seq_Concat(v#Array(a1), v#Array(a2)))
}
function {:inline} IsEmpty<T>(a: Array T): bool {
    Seq_Len(v#Array(a)) == 0
}
function {:inline} LenArray<T>(a: Array T): int {
    Seq_Len(v#Array(a))
}
function {:inline} ArrayAt<T>(a: Array T, i: int): T {
    Seq_Nth(v#Array(a), i)
}

procedure test()
{
  var s: Array Value;

  s := EmptyArray();
  assert IsEmpty(s);
  s := AddArray(s, Integer(0));
  s := AddArray(s, Integer(1));
  s := AddArray(s, Integer(2));
  assert LenArray(s) == 3;
  assert ArrayAt(s, 1) == Integer(1);
  s := RemoveArray(s);
  assert(LenArray(s)) == 2;
  s := ConcatArray(s, s);
  assert LenArray(s) == 4;
  assert ArrayAt(s, 3) == Integer(1);
}
