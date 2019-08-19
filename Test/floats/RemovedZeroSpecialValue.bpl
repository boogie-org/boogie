// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo() returns (r : float24e8) {
  var d : float53e11;

  d := 0+zero53e11;
  d := 0-zero53e11;
}
