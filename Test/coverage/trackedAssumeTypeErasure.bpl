// RUN: %boogie /typeEncoding:a /trackVerificationCoverage "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Box;
function $Box<T>(x: T): Box;
function $Unbox<T>(b: Box): T;
function P(b: Box): bool;
function Q(b: Box): bool;

procedure M(b: Box)
  requires $Box($Unbox(b): int) == b;
{
  assume {:id "a0"} (forall x: int :: { P($Box(x)) } P($Box(x)) ==> Q($Box(x)));
  assume {:id "a1"} P(b);
  assert {:id "a2"} Q(b);
}
