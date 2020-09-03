// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:builtin "(Seq Int)"} IntSeq;
function {:builtin "(as seq.empty (Seq Int))"} EmptyIntSeq(): IntSeq;
function {:builtin "seq.len"} IntSeqLen(s: IntSeq): int;
function {:builtin "seq.++"} IntSeqConcat(s1: IntSeq, s2:IntSeq): IntSeq;
function {:builtin "seq.unit"} IntSeqUnit(i: int): IntSeq;
function {:builtin "seq.nth"} IntSeqNth(s: IntSeq, i: int): int;
function {:builtin "seq.extract"} IntSeqExtract(s: IntSeq, pos: int, len: int): IntSeq;

procedure test()
{
  var s: IntSeq;

  s := IntSeqConcat(EmptyIntSeq(), IntSeqUnit(0));
  s := IntSeqConcat(s, IntSeqUnit(1));
  s := IntSeqConcat(s, IntSeqUnit(2));
  assert IntSeqLen(s) == 3;
  assert IntSeqExtract(s, 1, 2) == IntSeqConcat(IntSeqUnit(1), IntSeqUnit(2));
  assert IntSeqNth(s, 1) == 1;
}
