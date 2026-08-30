// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A {:builtin ...} function IS the named solver symbol, so naming one that Boogie emits for its own
// encoding makes the function share it, and an axiom about the function then constrains the encoding.
// Nothing the user writes below is inconsistent, and it proved anything:
//
//   function {:builtin "ControlFlow"} cf(x: int, y: int) : int;
//   procedure P() { assume (forall a: int, b: int :: cf(a, b) == 0); assert false; }
//
// The reserved-word list in SMTLibNameUtils does not help: it exists so a colliding Boogie *identifier*
// can be renamed to q@..., and a {:builtin} string is not an identifier. See Core/EmittedSymbols.cs.

function {:builtin "ControlFlow"} controlFlow(x: int, y: int): int;

function {:builtin "int_2_U"} box(x: int): int;

function {:builtin "MapType0Select"} mapSelect(m: int, i: int): int;

function {:builtin "T@U"} boxedSort(x: int): int;
