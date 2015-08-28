// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const x: int where x < 0;  // error: where clauses not allowed on constants

