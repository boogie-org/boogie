// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "fp.add RNA"} RNA(float24e8, float24e8) returns (float24e8);
