// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// These examples once crashed Boogie (see https://github.com/boogie-org/boogie/issues/111).

procedure Local() {
  var llam: [int]bool where llam == (lambda n: int :: n <= 0);
  assert llam[0];
}

var glam: [int]bool where glam == (lambda n: int :: n <= 0);
procedure Global() {
  assert glam[0];
}

procedure InParameter(inlam: [int]bool where inlam == (lambda n: int :: n <= 0)) {
  assert inlam[0];
}

procedure OutParameter() returns (outlam: [int]bool where outlam == (lambda n: int :: n <= 0)) {
  assert outlam[0];
}

procedure ProcPlusImpl(inlam: [int]bool where inlam == (lambda n: int :: n <= 0))
  returns (outlam: [int]bool where outlam == (lambda n: int :: n <= 0));
implementation ProcPlusImpl(inlam: [int]bool) returns (outlam: [int]bool)
{
}
