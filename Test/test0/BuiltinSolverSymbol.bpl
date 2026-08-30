// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The boundary drawn by BuiltinSymbolCapture.bpl: naming one of the *solver's* symbols is the whole
// point of the attribute and stays accepted, including the IEEE predicates that have no surface syntax.

function {:builtin "fp.abs"} fabs(x: float24e8): float24e8;
function {:builtin "fp.isNaN"} isNaN(x: float24e8): bool;

procedure UsesThem(x: float24e8)
{
  assume x == 0x1.0e0f24e8;
  assert fabs(x) == 0x1.0e0f24e8;
  assert !isNaN(x);
}
