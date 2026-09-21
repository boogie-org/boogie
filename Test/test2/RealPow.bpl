// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %boogie -typeEncoding:p "%s" > "%t.p"
// RUN: %diff "%s.expect" "%t.p"

// "**" lowers to real_pow, whose declaration used to sit in the background predicates. Those are empty
// under the monomorphic encoding, which is the default and also what a monomorphizable program is given,
// so every program using "**" reached the solver with an undeclared symbol and died: "unknown constant
// real_pow", reported as the prover running out of memory. Checked under both encodings here, because the
// declaration has to be independent of them.
//
// real_pow carries no axioms, so it is an uninterpreted function: equal arguments give equal results and
// nothing more. Anything about its value is out of reach, which is what the third procedure records.

procedure Reflexive(x: real, y: real)
{
  assert x ** y == x ** y;
}

procedure Congruent(x: real, y: real, z: real)
{
  assume y == z;
  assert x ** y == x ** z;
}

procedure NotInterpreted()
{
  assert 2e0 ** 2e0 == 4e0;  // uninterpreted, so this is not provable
}
