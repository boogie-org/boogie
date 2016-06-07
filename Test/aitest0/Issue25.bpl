// RUN: %boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N: int;
axiom 0 <= N;

procedure vacuous_post()
ensures (forall k, l: int :: 0 <= k && k <= l && l < N ==> N < N); // Used to verify at some point (see https://github.com/boogie-org/boogie/issues/25).
{
var x: int;
x := -N;
while (x != x) {
}
}
