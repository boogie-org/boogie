// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Value;

function {:constructor} Integer(i: int): Value;
function {:constructor} Vector(v: ValueArray): Value;

type {:builtin "Seq"} Seq _;
function {:builtin "seq.empty"} Seq_Empty_Value(): Seq Value;
function {:builtin "seq.len"} Seq_Len_Value(a: Seq Value): int;
function {:builtin "seq.++"} Seq_Concat_Value(a: Seq Value, b: Seq Value): Seq Value;
function {:builtin "seq.unit"} Seq_Unit_Value(v: Value): Seq Value;
function {:builtin "seq.nth"} Seq_Nth_Value(a: Seq Value, i: int): Value;
function {:builtin "seq.extract"} Seq_Extract_Value(a: Seq Value, pos: int, length: int): Seq Value;

type {:datatype} ValueArray;
function {:constructor} ValueArray(v: Seq Value): ValueArray;
function {:inline} EmptyValueArray(): ValueArray {
    ValueArray(Seq_Empty_Value())
}
function {:inline} AddValueArray(a: ValueArray, v: Value): ValueArray {
    ValueArray(Seq_Concat_Value(v#ValueArray(a),Seq_Unit_Value(v)))
}
function {:inline} RemoveValueArray(a: ValueArray): ValueArray {
    ValueArray(Seq_Extract_Value(v#ValueArray(a), 0, Seq_Len_Value(v#ValueArray(a)) - 1))
}
function {:inline} ConcatValueArray(a1: ValueArray, a2: ValueArray): ValueArray {
    ValueArray(Seq_Concat_Value(v#ValueArray(a1), v#ValueArray(a2)))
}
function {:inline} IsEmpty(a: ValueArray): bool {
    Seq_Len_Value(v#ValueArray(a)) == 0
}
function {:inline} LenValueArray(a: ValueArray): int {
    Seq_Len_Value(v#ValueArray(a))
}
function {:inline} ValueArrayAt(a: ValueArray, i: int): Value {
    Seq_Nth_Value(v#ValueArray(a), i)
}

procedure test()
{
  var s: ValueArray;

  s := EmptyValueArray();
  assert IsEmpty(s);
  s := AddValueArray(s, Integer(0));
  s := AddValueArray(s, Integer(1));
  s := AddValueArray(s, Integer(2));
  assert LenValueArray(s) == 3;
  assert ValueArrayAt(s, 1) == Integer(1);
  s := RemoveValueArray(s);
  assert(LenValueArray(s)) == 2;
  s := ConcatValueArray(s, s);
  assert LenValueArray(s) == 4;
  assert ValueArrayAt(s, 3) == Integer(1);
}
