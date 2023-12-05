// RUN: %boogie /trackVerificationCoverage /enhancedErrorMessages:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P(x: int) {
  assume {:id "id1"} x < 100;
  assert {:id "id2"} x < 10;
}
