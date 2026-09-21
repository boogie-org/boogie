// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The constructor Boogie emits for a boxed type is named after the type: NType, plus one NTypeInv<i> per
// argument. Those names depend on the program, so no fixed list can hold them -- EmittedSymbols matches
// their shape instead.

type Ref;
type Field a;

function {:builtin "RefType"} capturesRef(): int;

function {:builtin "FieldType"} capturesField(x: int): int;

function {:builtin "FieldTypeInv0"} capturesFieldInv(x: int): int;

// Matching the shape rather than the program's own types costs a little precision: this name is rejected
// although nothing declares a GhostType. Nothing is lost by it, a {:builtin} having to name a solver
// symbol exactly and no solver naming one this way.
function {:builtin "GhostType"} overRejected(): int;

procedure P() { assert true; }
