// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure UnknownForall(P: [int]bool)
{
  assume P[0] && !P[1];
  assert {:add_to_pool "UnknownForall", 0}
    (forall {:pool "UnknownForall"} i: int :: P[i]) == P[0];
}

procedure UnknownExists(P: [int]bool)
{
  assume P[0] && !P[1];
  assert {:add_to_pool "UnknownExists", 0}
    (exists {:pool "UnknownExists"} i: int :: !P[i]) == !P[0];
}
