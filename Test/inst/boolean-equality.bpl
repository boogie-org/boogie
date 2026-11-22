// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function P(int): bool;

procedure EqualityExists(b: bool)
{
  assume b == (exists x: int :: {:add_to_pool "EqualityExists", x+1} P(x));
  assert b ==> (exists {:pool "EqualityExists"} y: int :: P(y-1));
}

procedure EqualityForall(b: bool)
{
  assume (forall x: int :: {:add_to_pool "EqualityForall", x+1} P(x)) == b;
  assert !b ==> (exists {:pool "EqualityForall"} y: int :: !P(y-1));
}

procedure DisequalityExists(b: bool)
{
  assume (exists x: int :: {:add_to_pool "DisequalityExists", x+1} P(x)) != b;
  assert !b ==> (exists {:pool "DisequalityExists"} y: int :: P(y-1));
}

procedure DisequalityForall(b: bool)
{
  assume b != (forall x: int :: {:add_to_pool "DisequalityForall", x+1} P(x));
  assert b ==> (exists {:pool "DisequalityForall"} y: int :: !P(y-1));
}

procedure NegatedEquality(b: bool)
{
  assume !(b == (forall x: int :: {:add_to_pool "NegatedEquality", x+1} P(x)));
  assert b ==> (exists {:pool "NegatedEquality"} y: int :: !P(y-1));
}

procedure NegatedDisequality(b: bool)
{
  assume !((exists x: int :: {:add_to_pool "NegatedDisequality", x+1} P(x)) != b);
  assert b ==> (exists {:pool "NegatedDisequality"} y: int :: P(y-1));
}

procedure EqualityPreservesPool(b: bool)
{
  assume b == (forall {:pool "EqualityPreservesPool"} x: int :: {P(x-1)} P(x-1));
  assert {:add_to_pool "EqualityPreservesPool", 1} b ==> P(0);
}

procedure DisequalityPreservesPool(b: bool)
{
  assume (forall {:pool "DisequalityPreservesPool"} x: int :: {P(x-1)} P(x-1)) != b;
  assert {:add_to_pool "DisequalityPreservesPool", 1} !b ==> P(0);
}
