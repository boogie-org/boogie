// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The boundary drawn by BuiltinWithDefinition.bpl: a {:builtin ...} function may not have a definition,
// but an uninterpreted one is the point of the attribute, and an axiom about it is the user's to assert
// exactly as any other axiom is. A definition is the construct that is not supposed to be able to
// introduce inconsistency; an axiom always was.

function {:builtin "fp.abs"} fabs(x: float24e8): float24e8;

axiom (forall x: float24e8 :: fabs(fabs(x)) == fabs(x));

procedure UsesTheAxiom(x: float24e8)
{
  assert fabs(fabs(x)) == fabs(x);
}

procedure UsesTheSolversSymbol(x: float24e8)
{
  assume x == 0x1.0e0f24e8;
  assert fabs(x) == 0x1.0e0f24e8;  // fp.abs, from the solver's theory
}
