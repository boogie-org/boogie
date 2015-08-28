// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:HoudiniConst -z3opt:MBQI=true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} {:absdomain "IA[Intervals]"} b1(x: int) : bool;

procedure foo ()
{
  assert (forall x: int :: (0 <= x && x <= 2) ==> b1(x));
}

