// RUN: %boogie -vc:block -errorLimit:1 -errorTrace:1 -logPrefix:-1block "%s" > "%t1"
// RUN: %diff "%s.e1.block.expect" "%t1"
// RUN: %boogie -vc:local -errorLimit:1 -errorTrace:1 -logPrefix:-1local "%s" > "%t2"
// RUN: %diff "%s.e1.local.expect" "%t2"
// RUN: %boogie -vc:dag -errorLimit:1 -errorTrace:1 -logPrefix:-1dag "%s" > "%t3"
// RUN: %diff "%s.e1.dag.expect" "%t3"
// RUN: %boogie -vc:local -errorLimit:10 -errorTrace:1 -logPrefix:-10local "%s" > "%t4"
// RUN: %diff "%s.e10.local.expect" "%t4"
// RUN: %boogie -vc:dag -errorLimit:10 -errorTrace:1 -logPrefix:-10dag "%s" > "%t5"
// RUN: %diff "%s.e10.dag.expect" "%t5"

// Author of this comment: mikebarnett ec02177eefb5
// The following tests are rather fickle at the moment--different errors
// may be reported during different runs.  Moreover, it is conceivable that
// the error trace would be reported in different orders, since we do not
// attempt to sort the trace labels at this time.
// An interesting thing is that /vc:local can with Simplify report more than one
// error for this file, even with /errorLimit:1.  Other than that, only
// local and dag produce VCs to which Simplify actually produces different
// counterexamples.

procedure P(x: int)
{
start:
  goto A, B;

A:
  assert 0 <= x;
  goto C;

B:
  assert x < 100;
  goto C;

C:
  assert x == 87;
  return;
}
