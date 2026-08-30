// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Each form of definition is rejected on a {:builtin} or {:bvbuiltin} function; an axiom is not.

function {:builtin "+"} plainBody(x: int, y: int): int { 0 }

function {:inline} {:builtin "fp.abs"} inlineBody(x: float24e8): float24e8 { x }

function {:define} {:builtin "fp.neg"} defineBody(x: float24e8): float24e8 { x }

function {:bvbuiltin "bvadd"} bvBody(x: bv8, y: bv8): bv8 { 0bv8 }

function {:builtin "fp.abs"} withAxiom(x: float24e8): float24e8 uses {
  axiom (forall x: float24e8 :: withAxiom(withAxiom(x)) == withAxiom(x));
}
