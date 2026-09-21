// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A {:builtin ...} function IS the solver's symbol: applications of it are translated to that symbol and
// no declaration is emitted. A definition says instead that the function is some expression, and becomes
// an axiom -- which would be an axiom about the solver's symbol. So a definition that is merely wrong
// stops being a definition and becomes a way to contradict the theory:
//
//   function {:builtin "+"} plus(x: int, y: int): int { 0 }
//   procedure P(a: int, b: int) { assert a + b == 0; }        // used to verify
//
// All three ways of giving a definition are rejected. See BuiltinWithAxiom.bpl for what stays allowed.

function {:builtin "+"} plainBody(x: int, y: int): int { 0 }

function {:inline} {:builtin "fp.abs"} inlineBody(x: float24e8): float24e8 { x }

function {:define} {:builtin "fp.neg"} defineBody(x: float24e8): float24e8 { x }
