// RUN: %boogie -proverOpt:PROVER_PATH=bogus-path "%s" > "%t"
// RUN: %boogie -proverOpt:bogus-option "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

procedure foo() {}
