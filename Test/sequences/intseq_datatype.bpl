// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Value;

function {:constructor} Integer(i: int): Value;
function {:constructor} Vector(v: ValueArray): Value;

type {:builtin "(Seq T@Value)"} ValueSeq;
function {:builtin "(as seq.empty (Seq T@Value))"} EmptyValueSeq(): ValueSeq;
function {:builtin "seq.len"} ValueSeqLen(a: ValueSeq): int;
function {:builtin "seq.++"} ValueSeqConcat(a: ValueSeq, b:ValueSeq): ValueSeq;
function {:builtin "seq.unit"} ValueSeqUnit(v: Value): ValueSeq;
function {:builtin "seq.nth"} ValueSeqNth(a: ValueSeq, i: int): Value;
function {:builtin "seq.extract"} ValueSeqExtract(a: ValueSeq, pos: int, length: int): ValueSeq;

type {:datatype} {:dependson "Value"} ValueArray;
function {:constructor} ValueArray(v: ValueSeq): ValueArray;
function {:inline} EmptyValueArray(): ValueArray {
    ValueArray(EmptyValueSeq())
}
function {:inline} AddValueArray(a: ValueArray, v: Value): ValueArray {
    ValueArray(ValueSeqConcat(v#ValueArray(a),ValueSeqUnit(v)))
}
function {:inline} RemoveValueArray(a: ValueArray): ValueArray {
    ValueArray(ValueSeqExtract(v#ValueArray(a), 0, ValueSeqLen(v#ValueArray(a)) - 1))
}
function {:inline} ConcatValueArray(a1: ValueArray, a2: ValueArray): ValueArray {
    ValueArray(ValueSeqConcat(v#ValueArray(a1), v#ValueArray(a2)))
}
function {:inline} IsEmpty(a: ValueArray): bool {
    ValueSeqLen(v#ValueArray(a)) == 0
}
function {:inline} LenValueArray(a: ValueArray): int {
    ValueSeqLen(v#ValueArray(a))
}
function {:inline} ValueArrayAt(a: ValueArray, i: int): Value {
    ValueSeqNth(v#ValueArray(a), i)
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
