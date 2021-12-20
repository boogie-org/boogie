// RUN: %parallel-boogie -proverOpt:SOLVER=noop "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure P(K: int)
  ensures true;
{
}